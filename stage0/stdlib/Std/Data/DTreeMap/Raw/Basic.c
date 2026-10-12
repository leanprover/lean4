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
lean_object* l_Std_DTreeMap_instCoeTypeForall__1___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instCoeTypeForall__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_DTreeMap_instCoeTypeForall__1___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_DTreeMap_instCoeTypeForall__1___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__1(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__12(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__10));
v___x_35_ = l_Lean_mkAtom(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__13(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__12, &l_Std_DTreeMap_Raw___auto__1___closed__12_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__12);
v___x_37_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_38_ = lean_array_push(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__18(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__17));
v___x_52_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__13, &l_Std_DTreeMap_Raw___auto__1___closed__13_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__13);
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__19(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__18, &l_Std_DTreeMap_Raw___auto__1___closed__18_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__18);
v___x_55_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__11));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__20(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__19, &l_Std_DTreeMap_Raw___auto__1___closed__19_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__19);
v___x_59_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__21(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__20, &l_Std_DTreeMap_Raw___auto__1___closed__20_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__20);
v___x_62_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__22(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__21, &l_Std_DTreeMap_Raw___auto__1___closed__21_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__21);
v___x_66_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__23(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__22, &l_Std_DTreeMap_Raw___auto__1___closed__22_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__22);
v___x_69_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__7));
v___x_70_ = lean_box(2);
v___x_71_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__24(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__23, &l_Std_DTreeMap_Raw___auto__1___closed__23_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__23);
v___x_73_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__5));
v___x_74_ = lean_array_push(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1___closed__25(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__24, &l_Std_DTreeMap_Raw___auto__1___closed__24_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__24);
v___x_76_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__4));
v___x_77_ = lean_box(2);
v___x_78_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___auto__1(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_79_;
}
}
lean_object* l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg(){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l_Std_DTreeMap_Raw_instCoeWFWFInner___redArg();
stack->m_obj
 = v_res_82_;
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
lean_object* l_Std_DTreeMap_Raw_empty___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_box(1);
return v___x_96_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_97_;
v_res_97_ = l_Std_DTreeMap_Raw_empty___redArg();
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___redArg___boxed(lean_object* v___dummy_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DTreeMap_Raw_empty___redArg();
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_cmp_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(1);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_empty___boxed(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_cmp_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_DTreeMap_Raw_empty(v_00_u03b1_104_, v_00_u03b2_105_, v_cmp_106_);
lean_dec_ref(v_cmp_106_);
return v_res_107_;
}
}
lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(1);
return v___x_109_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_110_;
v_res_110_ = l_Std_DTreeMap_Raw_instEmptyCollection___redArg();
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_DTreeMap_Raw_instEmptyCollection___redArg();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_cmp_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(1);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instEmptyCollection___boxed(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_cmp_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_DTreeMap_Raw_instEmptyCollection(v_00_u03b1_117_, v_00_u03b2_118_, v_cmp_119_);
lean_dec_ref(v_cmp_119_);
return v_res_120_;
}
}
lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(1);
return v___x_122_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_123_;
v_res_123_ = l_Std_DTreeMap_Raw_instInhabited___redArg();
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_DTreeMap_Raw_instInhabited___redArg();
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_cmp_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(1);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInhabited___boxed(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_cmp_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_DTreeMap_Raw_instInhabited(v_00_u03b1_130_, v_00_u03b2_131_, v_cmp_132_);
lean_dec_ref(v_cmp_132_);
return v_res_133_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__3));
v___x_174_ = l_String_toRawSubstring_x27(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(lean_object* v_x_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_193_);
v___x_197_ = l_Lean_Syntax_isOfKind(v_x_193_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v_x_193_);
v___x_198_ = lean_box(1);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_195_);
return v___x_199_;
}
else
{
lean_object* v_quotContext_200_; lean_object* v_currMacroScope_201_; lean_object* v_ref_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_quotContext_200_ = lean_ctor_get(v_a_194_, 1);
v_currMacroScope_201_ = lean_ctor_get(v_a_194_, 2);
v_ref_202_ = lean_ctor_get(v_a_194_, 5);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Lean_Syntax_getArg(v_x_193_, v___x_203_);
v___x_205_ = lean_unsigned_to_nat(2u);
v___x_206_ = l_Lean_Syntax_getArg(v_x_193_, v___x_205_);
lean_dec(v_x_193_);
v___x_207_ = 0;
v___x_208_ = l_Lean_SourceInfo_fromRef(v_ref_202_, v___x_207_);
v___x_209_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
v___x_210_ = lean_obj_once(&l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4, &l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4_once, _init_l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__4);
v___x_211_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__5));
lean_inc(v_currMacroScope_201_);
lean_inc(v_quotContext_200_);
v___x_212_ = l_Lean_addMacroScope(v_quotContext_200_, v___x_211_, v_currMacroScope_201_);
v___x_213_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__10));
lean_inc_n(v___x_208_, 2);
v___x_214_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_214_, 0, v___x_208_);
lean_ctor_set(v___x_214_, 1, v___x_210_);
lean_ctor_set(v___x_214_, 2, v___x_212_);
lean_ctor_set(v___x_214_, 3, v___x_213_);
v___x_215_ = ((lean_object*)(l_Std_DTreeMap_Raw___auto__1___closed__9));
v___x_216_ = l_Lean_Syntax_node2(v___x_208_, v___x_215_, v___x_204_, v___x_206_);
v___x_217_ = l_Lean_Syntax_node2(v___x_208_, v___x_209_, v___x_214_, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_195_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___boxed(lean_object* v_x_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1(v_x_219_, v_a_220_, v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(lean_object* v_x_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______macroRules__Std__DTreeMap__Raw__term___x7em____1___closed__2));
lean_inc(v_x_226_);
v___x_230_ = l_Lean_Syntax_isOfKind(v_x_226_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_x_226_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v_a_228_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = l_Lean_Syntax_getArg(v_x_226_, v___x_233_);
v___x_235_ = ((lean_object*)(l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_234_);
v___x_236_ = l_Lean_Syntax_isOfKind(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v___x_234_);
lean_dec(v_x_226_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_a_228_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = l_Lean_Syntax_getArg(v_x_226_, v___x_239_);
lean_dec(v_x_226_);
v___x_241_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_240_);
v___x_242_ = l_Lean_Syntax_matchesNull(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v___x_240_);
lean_dec(v___x_234_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_a_228_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_ref_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_245_ = l_Lean_Syntax_getArg(v___x_240_, v___x_233_);
v___x_246_ = l_Lean_Syntax_getArg(v___x_240_, v___x_239_);
lean_dec(v___x_240_);
v_ref_247_ = l_Lean_replaceRef(v___x_234_, v_a_227_);
lean_dec(v___x_234_);
v___x_248_ = 0;
v___x_249_ = l_Lean_SourceInfo_fromRef(v_ref_247_, v___x_248_);
lean_dec(v_ref_247_);
v___x_250_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__4));
v___x_251_ = ((lean_object*)(l_Std_DTreeMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_249_);
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_249_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_Lean_Syntax_node3(v___x_249_, v___x_250_, v___x_245_, v___x_252_, v___x_246_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_a_228_);
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1___boxed(lean_object* v_x_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_DTreeMap_Raw___aux__Std__Data__DTreeMap__Raw__Basic______unexpand__Std__DTreeMap__Raw__Equiv__1(v_x_255_, v_a_256_, v_a_257_);
lean_dec(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert___redArg(lean_object* v_cmp_259_, lean_object* v_t_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_259_, v_a_261_, v_b_262_, v_t_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insert(lean_object* v_00_u03b1_264_, lean_object* v_00_u03b2_265_, lean_object* v_cmp_266_, lean_object* v_t_267_, lean_object* v_a_268_, lean_object* v_b_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_266_, v_a_268_, v_b_269_, v_t_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0(lean_object* v_cmp_271_, lean_object* v_e_272_){
_start:
{
lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_fst_273_ = lean_ctor_get(v_e_272_, 0);
lean_inc(v_fst_273_);
v_snd_274_ = lean_ctor_get(v_e_272_, 1);
lean_inc(v_snd_274_);
lean_dec_ref(v_e_272_);
v___x_275_ = lean_box(1);
v___x_276_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_271_, v_fst_273_, v_snd_274_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma___redArg(lean_object* v_cmp_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_278_, 0, v_cmp_277_);
return v___f_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSingletonSigma(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_cmp_281_){
_start:
{
lean_object* v___f_282_; 
v___f_282_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instSingletonSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_282_, 0, v_cmp_281_);
return v___f_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0(lean_object* v_cmp_283_, lean_object* v_e_284_, lean_object* v_s_285_){
_start:
{
lean_object* v_fst_286_; lean_object* v_snd_287_; lean_object* v___x_288_; 
v_fst_286_ = lean_ctor_get(v_e_284_, 0);
lean_inc(v_fst_286_);
v_snd_287_ = lean_ctor_get(v_e_284_, 1);
lean_inc(v_snd_287_);
lean_dec_ref(v_e_284_);
v___x_288_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_283_, v_fst_286_, v_snd_287_, v_s_285_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma___redArg(lean_object* v_cmp_289_){
_start:
{
lean_object* v___f_290_; 
v___f_290_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_290_, 0, v_cmp_289_);
return v___f_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInsertSigma(lean_object* v_00_u03b1_291_, lean_object* v_00_u03b2_292_, lean_object* v_cmp_293_){
_start:
{
lean_object* v___f_294_; 
v___f_294_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instInsertSigma___redArg___lam__0), 3, 1);
lean_closure_set(v___f_294_, 0, v_cmp_293_);
return v___f_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew___redArg(lean_object* v_cmp_295_, lean_object* v_t_296_, lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
uint8_t v___x_299_; 
lean_inc(v_t_296_);
lean_inc(v_a_297_);
lean_inc_ref(v_cmp_295_);
v___x_299_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_295_, v_a_297_, v_t_296_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_295_, v_a_297_, v_b_298_, v_t_296_);
return v___x_300_;
}
else
{
lean_dec(v_b_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_cmp_295_);
return v_t_296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertIfNew(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_cmp_303_, lean_object* v_t_304_, lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
uint8_t v___x_307_; 
lean_inc(v_t_304_);
lean_inc(v_a_305_);
lean_inc_ref(v_cmp_303_);
v___x_307_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_303_, v_a_305_, v_t_304_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_303_, v_a_305_, v_b_306_, v_t_304_);
return v___x_308_;
}
else
{
lean_dec(v_b_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_cmp_303_);
return v_t_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert___redArg(lean_object* v_cmp_309_, lean_object* v_t_310_, lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
lean_object* v_sz_313_; lean_object* v_m_314_; lean_object* v___y_316_; 
v_sz_313_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_310_);
v_m_314_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_309_, v_a_311_, v_b_312_, v_t_310_);
if (lean_obj_tag(v_m_314_) == 0)
{
lean_object* v_size_320_; 
v_size_320_ = lean_ctor_get(v_m_314_, 0);
lean_inc(v_size_320_);
v___y_316_ = v_size_320_;
goto v___jp_315_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___y_316_ = v___x_321_;
goto v___jp_315_;
}
v___jp_315_:
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_nat_dec_eq(v_sz_313_, v___y_316_);
lean_dec(v___y_316_);
lean_dec(v_sz_313_);
v___x_318_ = lean_box(v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_m_314_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsert(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_cmp_324_, lean_object* v_t_325_, lean_object* v_a_326_, lean_object* v_b_327_){
_start:
{
lean_object* v_sz_328_; lean_object* v_m_329_; lean_object* v___y_331_; 
v_sz_328_ = l_Std_DTreeMap_Internal_Impl_containsThenInsert_x21_size___redArg(v_t_325_);
v_m_329_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_324_, v_a_326_, v_b_327_, v_t_325_);
if (lean_obj_tag(v_m_329_) == 0)
{
lean_object* v_size_335_; 
v_size_335_ = lean_ctor_get(v_m_329_, 0);
lean_inc(v_size_335_);
v___y_331_ = v_size_335_;
goto v___jp_330_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(0u);
v___y_331_ = v___x_336_;
goto v___jp_330_;
}
v___jp_330_:
{
uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_nat_dec_eq(v_sz_328_, v___y_331_);
lean_dec(v___y_331_);
lean_dec(v_sz_328_);
v___x_333_ = lean_box(v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_m_329_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_cmp_337_, lean_object* v_t_338_, lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
uint8_t v___x_341_; 
lean_inc(v_t_338_);
lean_inc(v_a_339_);
lean_inc_ref(v_cmp_337_);
v___x_341_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_337_, v_a_339_, v_t_338_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_337_, v_a_339_, v_b_340_, v_t_338_);
v___x_343_ = lean_box(v___x_341_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_b_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_cmp_337_);
v___x_345_ = lean_box(v___x_341_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v_t_338_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_cmp_349_, lean_object* v_t_350_, lean_object* v_a_351_, lean_object* v_b_352_){
_start:
{
uint8_t v___x_353_; 
lean_inc(v_t_350_);
lean_inc(v_a_351_);
lean_inc_ref(v_cmp_349_);
v___x_353_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_349_, v_a_351_, v_t_350_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_349_, v_a_351_, v_b_352_, v_t_350_);
v___x_355_ = lean_box(v___x_353_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_b_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_cmp_349_);
v___x_357_ = lean_box(v___x_353_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_t_350_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_359_, lean_object* v_t_360_, lean_object* v_a_361_, lean_object* v_b_362_){
_start:
{
lean_object* v___x_363_; 
lean_inc(v_a_361_);
lean_inc(v_t_360_);
lean_inc_ref(v_cmp_359_);
v___x_363_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_359_, v_t_360_, v_a_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
uint8_t v___x_364_; 
lean_inc(v_t_360_);
lean_inc(v_a_361_);
lean_inc_ref(v_cmp_359_);
v___x_364_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_359_, v_a_361_, v_t_360_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_359_, v_a_361_, v_b_362_, v_t_360_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; 
lean_dec(v_b_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_cmp_359_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_363_);
lean_ctor_set(v___x_367_, 1, v_t_360_);
return v___x_367_;
}
}
else
{
lean_object* v___x_368_; 
lean_dec(v_b_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_cmp_359_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_363_);
lean_ctor_set(v___x_368_, 1, v_t_360_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_cmp_371_, lean_object* v_inst_372_, lean_object* v_t_373_, lean_object* v_a_374_, lean_object* v_b_375_){
_start:
{
lean_object* v___x_376_; 
lean_inc(v_a_374_);
lean_inc(v_t_373_);
lean_inc_ref(v_cmp_371_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_371_, v_t_373_, v_a_374_);
if (lean_obj_tag(v___x_376_) == 0)
{
uint8_t v___x_377_; 
lean_inc(v_t_373_);
lean_inc(v_a_374_);
lean_inc_ref(v_cmp_371_);
v___x_377_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_371_, v_a_374_, v_t_373_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_371_, v_a_374_, v_b_375_, v_t_373_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_376_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; 
lean_dec(v_b_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_cmp_371_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_376_);
lean_ctor_set(v___x_380_, 1, v_t_373_);
return v___x_380_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v_b_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_cmp_371_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_376_);
lean_ctor_set(v___x_381_, 1, v_t_373_);
return v___x_381_;
}
}
}
uint8_t l_Std_DTreeMap_Raw_contains___redArg(lean_object* v_cmp_382_, lean_object* v_t_383_, lean_object* v_a_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_382_, v_a_384_, v_t_383_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_382_ = stack[0].m_obj;
lean_object* v_t_383_ = stack[1].m_obj;
lean_object* v_a_384_ = stack[2].m_obj;
uint8_t v_res_386_;
v_res_386_ = l_Std_DTreeMap_Raw_contains___redArg(v_cmp_382_, v_t_383_, v_a_384_);
stack->m_num = v_res_386_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___redArg___boxed(lean_object* v_cmp_387_, lean_object* v_t_388_, lean_object* v_a_389_){
_start:
{
uint8_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Std_DTreeMap_Raw_contains___redArg(v_cmp_387_, v_t_388_, v_a_389_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
uint8_t l_Std_DTreeMap_Raw_contains(lean_object* v_00_u03b1_392_, lean_object* v_00_u03b2_393_, lean_object* v_cmp_394_, lean_object* v_t_395_, lean_object* v_a_396_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_394_, v_a_396_, v_t_395_);
return v___x_397_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_394_ = stack[2].m_obj;
lean_object* v_t_395_ = stack[3].m_obj;
lean_object* v_a_396_ = stack[4].m_obj;
uint8_t v_res_398_;
v_res_398_ = l_Std_DTreeMap_Raw_contains(lean_box(0), lean_box(0), v_cmp_394_, v_t_395_, v_a_396_);
stack->m_num = v_res_398_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_contains___boxed(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_cmp_401_, lean_object* v_t_402_, lean_object* v_a_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_DTreeMap_Raw_contains(v_00_u03b1_399_, v_00_u03b2_400_, v_cmp_401_, v_t_402_, v_a_403_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
lean_object* l_Std_DTreeMap_Raw_instMembership___redArg(){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
return v___x_407_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_408_;
v_res_408_ = l_Std_DTreeMap_Raw_instMembership___redArg();
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___redArg___boxed(lean_object* v___dummy_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_DTreeMap_Raw_instMembership___redArg();
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership(lean_object* v_00_u03b1_411_, lean_object* v_00_u03b2_412_, lean_object* v_cmp_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instMembership___boxed(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_cmp_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_DTreeMap_Raw_instMembership(v_00_u03b1_415_, v_00_u03b2_416_, v_cmp_417_);
lean_dec_ref(v_cmp_417_);
return v_res_418_;
}
}
uint8_t l_Std_DTreeMap_Raw_instDecidableMem___redArg(lean_object* v_cmp_419_, lean_object* v_t_420_, lean_object* v_a_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_419_, v_a_421_, v_t_420_);
return v___x_422_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_419_ = stack[0].m_obj;
lean_object* v_t_420_ = stack[1].m_obj;
lean_object* v_a_421_ = stack[2].m_obj;
uint8_t v_res_423_;
v_res_423_ = l_Std_DTreeMap_Raw_instDecidableMem___redArg(v_cmp_419_, v_t_420_, v_a_421_);
stack->m_num = v_res_423_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_cmp_424_, lean_object* v_t_425_, lean_object* v_a_426_){
_start:
{
uint8_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l_Std_DTreeMap_Raw_instDecidableMem___redArg(v_cmp_424_, v_t_425_, v_a_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
uint8_t l_Std_DTreeMap_Raw_instDecidableMem(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_cmp_431_, lean_object* v_t_432_, lean_object* v_a_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_431_, v_a_433_, v_t_432_);
return v___x_434_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_431_ = stack[2].m_obj;
lean_object* v_t_432_ = stack[3].m_obj;
lean_object* v_a_433_ = stack[4].m_obj;
uint8_t v_res_435_;
v_res_435_ = l_Std_DTreeMap_Raw_instDecidableMem(lean_box(0), lean_box(0), v_cmp_431_, v_t_432_, v_a_433_);
stack->m_num = v_res_435_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_cmp_438_, lean_object* v_t_439_, lean_object* v_a_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Std_DTreeMap_Raw_instDecidableMem(v_00_u03b1_436_, v_00_u03b2_437_, v_cmp_438_, v_t_439_, v_a_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg(lean_object* v_t_443_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___redArg___boxed(lean_object* v_t_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_DTreeMap_Raw_size___redArg(v_t_446_);
lean_dec(v_t_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_cmp_450_, lean_object* v_t_451_){
_start:
{
if (lean_obj_tag(v_t_451_) == 0)
{
lean_object* v_size_452_; 
v_size_452_ = lean_ctor_get(v_t_451_, 0);
lean_inc(v_size_452_);
return v_size_452_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = lean_unsigned_to_nat(0u);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_size___boxed(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_cmp_456_, lean_object* v_t_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_DTreeMap_Raw_size(v_00_u03b1_454_, v_00_u03b2_455_, v_cmp_456_, v_t_457_);
lean_dec(v_t_457_);
lean_dec_ref(v_cmp_456_);
return v_res_458_;
}
}
uint8_t l_Std_DTreeMap_Raw_isEmpty___redArg(lean_object* v_t_459_){
_start:
{
if (lean_obj_tag(v_t_459_) == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 1;
return v___x_461_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_459_ = stack[0].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_Std_DTreeMap_Raw_isEmpty___redArg(v_t_459_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___redArg___boxed(lean_object* v_t_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Std_DTreeMap_Raw_isEmpty___redArg(v_t_463_);
lean_dec(v_t_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
uint8_t l_Std_DTreeMap_Raw_isEmpty(lean_object* v_00_u03b1_466_, lean_object* v_00_u03b2_467_, lean_object* v_cmp_468_, lean_object* v_t_469_){
_start:
{
if (lean_obj_tag(v_t_469_) == 0)
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = 1;
return v___x_471_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_468_ = stack[2].m_obj;
lean_object* v_t_469_ = stack[3].m_obj;
uint8_t v_res_472_;
v_res_472_ = l_Std_DTreeMap_Raw_isEmpty(lean_box(0), lean_box(0), v_cmp_468_, v_t_469_);
stack->m_num = v_res_472_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_cmp_475_, lean_object* v_t_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Std_DTreeMap_Raw_isEmpty(v_00_u03b1_473_, v_00_u03b2_474_, v_cmp_475_, v_t_476_);
lean_dec(v_t_476_);
lean_dec_ref(v_cmp_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase___redArg(lean_object* v_cmp_479_, lean_object* v_t_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_479_, v_a_481_, v_t_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_erase(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b2_484_, lean_object* v_cmp_485_, lean_object* v_t_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_485_, v_a_487_, v_t_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f___redArg(lean_object* v_cmp_489_, lean_object* v_t_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_489_, v_t_490_, v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x3f(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_cmp_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_a_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_495_, v_t_497_, v_a_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get___redArg(lean_object* v_cmp_500_, lean_object* v_t_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_500_, v_t_501_, v_a_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_cmp_506_, lean_object* v_inst_507_, lean_object* v_t_508_, lean_object* v_a_509_, lean_object* v_h_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_cmp_506_, v_t_508_, v_a_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg(lean_object* v_cmp_512_, lean_object* v_t_513_, lean_object* v_a_514_, lean_object* v_inst_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_512_, v_t_513_, v_a_514_, v_inst_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___redArg___boxed(lean_object* v_cmp_517_, lean_object* v_t_518_, lean_object* v_a_519_, lean_object* v_inst_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DTreeMap_Raw_get_x21___redArg(v_cmp_517_, v_t_518_, v_a_519_, v_inst_520_);
lean_dec(v_inst_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21(lean_object* v_00_u03b1_522_, lean_object* v_00_u03b2_523_, lean_object* v_cmp_524_, lean_object* v_inst_525_, lean_object* v_t_526_, lean_object* v_a_527_, lean_object* v_inst_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_cmp_524_, v_t_526_, v_a_527_, v_inst_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_cmp_532_, lean_object* v_inst_533_, lean_object* v_t_534_, lean_object* v_a_535_, lean_object* v_inst_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_DTreeMap_Raw_get_x21(v_00_u03b1_530_, v_00_u03b2_531_, v_cmp_532_, v_inst_533_, v_t_534_, v_a_535_, v_inst_536_);
lean_dec(v_inst_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg(lean_object* v_cmp_538_, lean_object* v_t_539_, lean_object* v_a_540_, lean_object* v_fallback_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_538_, v_t_539_, v_a_540_, v_fallback_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___redArg___boxed(lean_object* v_cmp_543_, lean_object* v_t_544_, lean_object* v_a_545_, lean_object* v_fallback_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_DTreeMap_Raw_getD___redArg(v_cmp_543_, v_t_544_, v_a_545_, v_fallback_546_);
lean_dec(v_fallback_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_cmp_550_, lean_object* v_inst_551_, lean_object* v_t_552_, lean_object* v_a_553_, lean_object* v_fallback_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_cmp_550_, v_t_552_, v_a_553_, v_fallback_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getD___boxed(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_cmp_558_, lean_object* v_inst_559_, lean_object* v_t_560_, lean_object* v_a_561_, lean_object* v_fallback_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_DTreeMap_Raw_getD(v_00_u03b1_556_, v_00_u03b2_557_, v_cmp_558_, v_inst_559_, v_t_560_, v_a_561_, v_fallback_562_);
lean_dec(v_fallback_562_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f___redArg(lean_object* v_cmp_564_, lean_object* v_t_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_564_, v_t_565_, v_a_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_cmp_570_, lean_object* v_t_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_cmp_570_, v_t_571_, v_a_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry___redArg(lean_object* v_cmp_574_, lean_object* v_t_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_574_, v_t_575_, v_a_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_cmp_580_, lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_a_583_, lean_object* v_h_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_cmp_580_, v_t_582_, v_a_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg(lean_object* v_cmp_586_, lean_object* v_inst_587_, lean_object* v_t_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_586_, v_inst_587_, v_t_588_, v_a_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_cmp_591_, lean_object* v_inst_592_, lean_object* v_t_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DTreeMap_Raw_getEntry_x21___redArg(v_cmp_591_, v_inst_592_, v_t_593_, v_a_594_);
lean_dec_ref(v_inst_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21(lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_cmp_598_, lean_object* v_inst_599_, lean_object* v_t_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_cmp_598_, v_inst_599_, v_t_600_, v_a_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_cmp_605_, lean_object* v_inst_606_, lean_object* v_t_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_DTreeMap_Raw_getEntry_x21(v_00_u03b1_603_, v_00_u03b2_604_, v_cmp_605_, v_inst_606_, v_t_607_, v_a_608_);
lean_dec_ref(v_inst_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg(lean_object* v_cmp_610_, lean_object* v_t_611_, lean_object* v_a_612_, lean_object* v_fallback_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_610_, v_t_611_, v_a_612_, v_fallback_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___redArg___boxed(lean_object* v_cmp_615_, lean_object* v_t_616_, lean_object* v_a_617_, lean_object* v_fallback_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DTreeMap_Raw_getEntryD___redArg(v_cmp_615_, v_t_616_, v_a_617_, v_fallback_618_);
lean_dec_ref(v_fallback_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_cmp_622_, lean_object* v_t_623_, lean_object* v_a_624_, lean_object* v_fallback_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_cmp_622_, v_t_623_, v_a_624_, v_fallback_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_cmp_629_, lean_object* v_t_630_, lean_object* v_a_631_, lean_object* v_fallback_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DTreeMap_Raw_getEntryD(v_00_u03b1_627_, v_00_u03b2_628_, v_cmp_629_, v_t_630_, v_a_631_, v_fallback_632_);
lean_dec_ref(v_fallback_632_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f___redArg(lean_object* v_cmp_634_, lean_object* v_t_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_634_, v_t_635_, v_a_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x3f(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_cmp_640_, lean_object* v_t_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_cmp_640_, v_t_641_, v_a_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey___redArg(lean_object* v_cmp_644_, lean_object* v_t_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_644_, v_t_645_, v_a_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_cmp_650_, lean_object* v_t_651_, lean_object* v_a_652_, lean_object* v_h_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_cmp_650_, v_t_651_, v_a_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg(lean_object* v_cmp_655_, lean_object* v_inst_656_, lean_object* v_t_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_655_, v_t_657_, v_a_658_, v_inst_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___redArg___boxed(lean_object* v_cmp_660_, lean_object* v_inst_661_, lean_object* v_t_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_DTreeMap_Raw_getKey_x21___redArg(v_cmp_660_, v_inst_661_, v_t_662_, v_a_663_);
lean_dec(v_inst_661_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_cmp_667_, lean_object* v_inst_668_, lean_object* v_t_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_cmp_667_, v_t_669_, v_a_670_, v_inst_668_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_cmp_674_, lean_object* v_inst_675_, lean_object* v_t_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_DTreeMap_Raw_getKey_x21(v_00_u03b1_672_, v_00_u03b2_673_, v_cmp_674_, v_inst_675_, v_t_676_, v_a_677_);
lean_dec(v_inst_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg(lean_object* v_cmp_679_, lean_object* v_t_680_, lean_object* v_a_681_, lean_object* v_fallback_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_679_, v_t_680_, v_a_681_, v_fallback_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___redArg___boxed(lean_object* v_cmp_684_, lean_object* v_t_685_, lean_object* v_a_686_, lean_object* v_fallback_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_DTreeMap_Raw_getKeyD___redArg(v_cmp_684_, v_t_685_, v_a_686_, v_fallback_687_);
lean_dec(v_fallback_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_cmp_691_, lean_object* v_t_692_, lean_object* v_a_693_, lean_object* v_fallback_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_cmp_691_, v_t_692_, v_a_693_, v_fallback_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_cmp_698_, lean_object* v_t_699_, lean_object* v_a_700_, lean_object* v_fallback_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DTreeMap_Raw_getKeyD(v_00_u03b1_696_, v_00_u03b2_697_, v_cmp_698_, v_t_699_, v_a_700_, v_fallback_701_);
lean_dec(v_fallback_701_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg(lean_object* v_t_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___redArg___boxed(lean_object* v_t_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_DTreeMap_Raw_minEntry_x3f___redArg(v_t_705_);
lean_dec(v_t_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_cmp_709_, lean_object* v_t_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_t_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x3f___boxed(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_cmp_714_, lean_object* v_t_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_DTreeMap_Raw_minEntry_x3f(v_00_u03b1_712_, v_00_u03b2_713_, v_cmp_714_, v_t_715_);
lean_dec(v_t_715_);
lean_dec_ref(v_cmp_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg(lean_object* v_inst_717_, lean_object* v_t_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_717_, v_t_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___redArg___boxed(lean_object* v_inst_720_, lean_object* v_t_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DTreeMap_Raw_minEntry_x21___redArg(v_inst_720_, v_t_721_);
lean_dec(v_t_721_);
lean_dec_ref(v_inst_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_cmp_725_, lean_object* v_inst_726_, lean_object* v_t_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_726_, v_t_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntry_x21___boxed(lean_object* v_00_u03b1_729_, lean_object* v_00_u03b2_730_, lean_object* v_cmp_731_, lean_object* v_inst_732_, lean_object* v_t_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_DTreeMap_Raw_minEntry_x21(v_00_u03b1_729_, v_00_u03b2_730_, v_cmp_731_, v_inst_732_, v_t_733_);
lean_dec(v_t_733_);
lean_dec_ref(v_inst_732_);
lean_dec_ref(v_cmp_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg(lean_object* v_t_735_, lean_object* v_fallback_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_735_, v_fallback_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___redArg___boxed(lean_object* v_t_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_DTreeMap_Raw_minEntryD___redArg(v_t_738_, v_fallback_739_);
lean_dec_ref(v_fallback_739_);
lean_dec(v_t_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_cmp_743_, lean_object* v_t_744_, lean_object* v_fallback_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_t_744_, v_fallback_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minEntryD___boxed(lean_object* v_00_u03b1_747_, lean_object* v_00_u03b2_748_, lean_object* v_cmp_749_, lean_object* v_t_750_, lean_object* v_fallback_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_DTreeMap_Raw_minEntryD(v_00_u03b1_747_, v_00_u03b2_748_, v_cmp_749_, v_t_750_, v_fallback_751_);
lean_dec_ref(v_fallback_751_);
lean_dec(v_t_750_);
lean_dec_ref(v_cmp_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(lean_object* v_t_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___redArg___boxed(lean_object* v_t_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DTreeMap_Raw_maxEntry_x3f___redArg(v_t_755_);
lean_dec(v_t_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_cmp_759_, lean_object* v_t_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_t_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x3f___boxed(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_cmp_764_, lean_object* v_t_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DTreeMap_Raw_maxEntry_x3f(v_00_u03b1_762_, v_00_u03b2_763_, v_cmp_764_, v_t_765_);
lean_dec(v_t_765_);
lean_dec_ref(v_cmp_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg(lean_object* v_inst_767_, lean_object* v_t_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_767_, v_t_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___redArg___boxed(lean_object* v_inst_770_, lean_object* v_t_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Raw_maxEntry_x21___redArg(v_inst_770_, v_t_771_);
lean_dec(v_t_771_);
lean_dec_ref(v_inst_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21(lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_cmp_775_, lean_object* v_inst_776_, lean_object* v_t_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_776_, v_t_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntry_x21___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_cmp_781_, lean_object* v_inst_782_, lean_object* v_t_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_DTreeMap_Raw_maxEntry_x21(v_00_u03b1_779_, v_00_u03b2_780_, v_cmp_781_, v_inst_782_, v_t_783_);
lean_dec(v_t_783_);
lean_dec_ref(v_inst_782_);
lean_dec_ref(v_cmp_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg(lean_object* v_t_785_, lean_object* v_fallback_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_785_, v_fallback_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___redArg___boxed(lean_object* v_t_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_DTreeMap_Raw_maxEntryD___redArg(v_t_788_, v_fallback_789_);
lean_dec_ref(v_fallback_789_);
lean_dec(v_t_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_cmp_793_, lean_object* v_t_794_, lean_object* v_fallback_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_t_794_, v_fallback_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxEntryD___boxed(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_cmp_799_, lean_object* v_t_800_, lean_object* v_fallback_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DTreeMap_Raw_maxEntryD(v_00_u03b1_797_, v_00_u03b2_798_, v_cmp_799_, v_t_800_, v_fallback_801_);
lean_dec_ref(v_fallback_801_);
lean_dec(v_t_800_);
lean_dec_ref(v_cmp_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg(lean_object* v_t_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___redArg___boxed(lean_object* v_t_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DTreeMap_Raw_minKey_x3f___redArg(v_t_805_);
lean_dec(v_t_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f(lean_object* v_00_u03b1_807_, lean_object* v_00_u03b2_808_, lean_object* v_cmp_809_, lean_object* v_t_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_t_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x3f___boxed(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_cmp_814_, lean_object* v_t_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DTreeMap_Raw_minKey_x3f(v_00_u03b1_812_, v_00_u03b2_813_, v_cmp_814_, v_t_815_);
lean_dec(v_t_815_);
lean_dec_ref(v_cmp_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg(lean_object* v_t_817_, lean_object* v_fallback_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_817_, v_fallback_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___redArg___boxed(lean_object* v_t_820_, lean_object* v_fallback_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_Raw_minKeyD___redArg(v_t_820_, v_fallback_821_);
lean_dec(v_fallback_821_);
lean_dec(v_t_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_cmp_825_, lean_object* v_t_826_, lean_object* v_fallback_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_t_826_, v_fallback_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKeyD___boxed(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_cmp_831_, lean_object* v_t_832_, lean_object* v_fallback_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_DTreeMap_Raw_minKeyD(v_00_u03b1_829_, v_00_u03b2_830_, v_cmp_831_, v_t_832_, v_fallback_833_);
lean_dec(v_fallback_833_);
lean_dec(v_t_832_);
lean_dec_ref(v_cmp_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg(lean_object* v_inst_835_, lean_object* v_t_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_835_, v_t_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___redArg___boxed(lean_object* v_inst_838_, lean_object* v_t_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_DTreeMap_Raw_minKey_x21___redArg(v_inst_838_, v_t_839_);
lean_dec(v_t_839_);
lean_dec(v_inst_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_cmp_843_, lean_object* v_inst_844_, lean_object* v_t_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_844_, v_t_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_minKey_x21___boxed(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_cmp_849_, lean_object* v_inst_850_, lean_object* v_t_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DTreeMap_Raw_minKey_x21(v_00_u03b1_847_, v_00_u03b2_848_, v_cmp_849_, v_inst_850_, v_t_851_);
lean_dec(v_t_851_);
lean_dec(v_inst_850_);
lean_dec_ref(v_cmp_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg(lean_object* v_t_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___redArg___boxed(lean_object* v_t_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DTreeMap_Raw_maxKey_x3f___redArg(v_t_855_);
lean_dec(v_t_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_cmp_859_, lean_object* v_t_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_t_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x3f___boxed(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_cmp_864_, lean_object* v_t_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DTreeMap_Raw_maxKey_x3f(v_00_u03b1_862_, v_00_u03b2_863_, v_cmp_864_, v_t_865_);
lean_dec(v_t_865_);
lean_dec_ref(v_cmp_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg(lean_object* v_inst_867_, lean_object* v_t_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_867_, v_t_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___redArg___boxed(lean_object* v_inst_870_, lean_object* v_t_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DTreeMap_Raw_maxKey_x21___redArg(v_inst_870_, v_t_871_);
lean_dec(v_t_871_);
lean_dec(v_inst_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_cmp_875_, lean_object* v_inst_876_, lean_object* v_t_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_876_, v_t_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKey_x21___boxed(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_cmp_881_, lean_object* v_inst_882_, lean_object* v_t_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_DTreeMap_Raw_maxKey_x21(v_00_u03b1_879_, v_00_u03b2_880_, v_cmp_881_, v_inst_882_, v_t_883_);
lean_dec(v_t_883_);
lean_dec(v_inst_882_);
lean_dec_ref(v_cmp_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg(lean_object* v_t_885_, lean_object* v_fallback_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_885_, v_fallback_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___redArg___boxed(lean_object* v_t_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DTreeMap_Raw_maxKeyD___redArg(v_t_888_, v_fallback_889_);
lean_dec(v_fallback_889_);
lean_dec(v_t_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_t_894_, lean_object* v_fallback_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_t_894_, v_fallback_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_maxKeyD___boxed(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_cmp_899_, lean_object* v_t_900_, lean_object* v_fallback_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DTreeMap_Raw_maxKeyD(v_00_u03b1_897_, v_00_u03b2_898_, v_cmp_899_, v_t_900_, v_fallback_901_);
lean_dec(v_fallback_901_);
lean_dec(v_t_900_);
lean_dec_ref(v_cmp_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(lean_object* v_t_903_, lean_object* v_n_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_903_, v_n_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_906_, lean_object* v_n_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f___redArg(v_t_906_, v_n_907_);
lean_dec(v_t_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_cmp_911_, lean_object* v_t_912_, lean_object* v_n_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_t_912_, v_n_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_cmp_917_, lean_object* v_t_918_, lean_object* v_n_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Std_DTreeMap_Raw_entryAtIdx_x3f(v_00_u03b1_915_, v_00_u03b2_916_, v_cmp_917_, v_t_918_, v_n_919_);
lean_dec(v_t_918_);
lean_dec_ref(v_cmp_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(lean_object* v_inst_921_, lean_object* v_t_922_, lean_object* v_n_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_921_, v_t_922_, v_n_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_925_, lean_object* v_t_926_, lean_object* v_n_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_DTreeMap_Raw_entryAtIdx_x21___redArg(v_inst_925_, v_t_926_, v_n_927_);
lean_dec(v_t_926_);
lean_dec_ref(v_inst_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21(lean_object* v_00_u03b1_929_, lean_object* v_00_u03b2_930_, lean_object* v_cmp_931_, lean_object* v_inst_932_, lean_object* v_t_933_, lean_object* v_n_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_932_, v_t_933_, v_n_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_cmp_938_, lean_object* v_inst_939_, lean_object* v_t_940_, lean_object* v_n_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DTreeMap_Raw_entryAtIdx_x21(v_00_u03b1_936_, v_00_u03b2_937_, v_cmp_938_, v_inst_939_, v_t_940_, v_n_941_);
lean_dec(v_t_940_);
lean_dec_ref(v_inst_939_);
lean_dec_ref(v_cmp_938_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg(lean_object* v_t_943_, lean_object* v_n_944_, lean_object* v_fallback_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_943_, v_n_944_, v_fallback_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___redArg___boxed(lean_object* v_t_947_, lean_object* v_n_948_, lean_object* v_fallback_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_DTreeMap_Raw_entryAtIdxD___redArg(v_t_947_, v_n_948_, v_fallback_949_);
lean_dec_ref(v_fallback_949_);
lean_dec(v_t_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD(lean_object* v_00_u03b1_951_, lean_object* v_00_u03b2_952_, lean_object* v_cmp_953_, lean_object* v_t_954_, lean_object* v_n_955_, lean_object* v_fallback_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_t_954_, v_n_955_, v_fallback_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_entryAtIdxD___boxed(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_cmp_960_, lean_object* v_t_961_, lean_object* v_n_962_, lean_object* v_fallback_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_DTreeMap_Raw_entryAtIdxD(v_00_u03b1_958_, v_00_u03b2_959_, v_cmp_960_, v_t_961_, v_n_962_, v_fallback_963_);
lean_dec_ref(v_fallback_963_);
lean_dec(v_t_961_);
lean_dec_ref(v_cmp_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(lean_object* v_t_965_, lean_object* v_n_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_965_, v_n_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg___boxed(lean_object* v_t_968_, lean_object* v_n_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f___redArg(v_t_968_, v_n_969_);
lean_dec(v_t_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_cmp_973_, lean_object* v_t_974_, lean_object* v_n_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_t_974_, v_n_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_cmp_979_, lean_object* v_t_980_, lean_object* v_n_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_DTreeMap_Raw_keyAtIdx_x3f(v_00_u03b1_977_, v_00_u03b2_978_, v_cmp_979_, v_t_980_, v_n_981_);
lean_dec(v_t_980_);
lean_dec_ref(v_cmp_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(lean_object* v_inst_983_, lean_object* v_t_984_, lean_object* v_n_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_983_, v_t_984_, v_n_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_987_, lean_object* v_t_988_, lean_object* v_n_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_DTreeMap_Raw_keyAtIdx_x21___redArg(v_inst_987_, v_t_988_, v_n_989_);
lean_dec(v_t_988_);
lean_dec(v_inst_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_cmp_993_, lean_object* v_inst_994_, lean_object* v_t_995_, lean_object* v_n_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_994_, v_t_995_, v_n_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_cmp_1000_, lean_object* v_inst_1001_, lean_object* v_t_1002_, lean_object* v_n_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_DTreeMap_Raw_keyAtIdx_x21(v_00_u03b1_998_, v_00_u03b2_999_, v_cmp_1000_, v_inst_1001_, v_t_1002_, v_n_1003_);
lean_dec(v_t_1002_);
lean_dec(v_inst_1001_);
lean_dec_ref(v_cmp_1000_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg(lean_object* v_t_1005_, lean_object* v_n_1006_, lean_object* v_fallback_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1005_, v_n_1006_, v_fallback_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___redArg___boxed(lean_object* v_t_1009_, lean_object* v_n_1010_, lean_object* v_fallback_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DTreeMap_Raw_keyAtIdxD___redArg(v_t_1009_, v_n_1010_, v_fallback_1011_);
lean_dec(v_fallback_1011_);
lean_dec(v_t_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD(lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_cmp_1015_, lean_object* v_t_1016_, lean_object* v_n_1017_, lean_object* v_fallback_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_t_1016_, v_n_1017_, v_fallback_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keyAtIdxD___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_cmp_1022_, lean_object* v_t_1023_, lean_object* v_n_1024_, lean_object* v_fallback_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_DTreeMap_Raw_keyAtIdxD(v_00_u03b1_1020_, v_00_u03b2_1021_, v_cmp_1022_, v_t_1023_, v_n_1024_, v_fallback_1025_);
lean_dec(v_fallback_1025_);
lean_dec(v_t_1023_);
lean_dec_ref(v_cmp_1022_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f___redArg(lean_object* v_cmp_1027_, lean_object* v_t_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1027_, v_k_1029_, v___x_1030_, v_t_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x3f(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_cmp_1034_, lean_object* v_t_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1034_, v_k_1036_, v___x_1037_, v_t_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f___redArg(lean_object* v_cmp_1039_, lean_object* v_t_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_box(0);
v___x_1043_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1039_, v_k_1041_, v___x_1042_, v_t_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x3f(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_cmp_1046_, lean_object* v_t_1047_, lean_object* v_k_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1046_, v_k_1048_, v___x_1049_, v_t_1047_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f___redArg(lean_object* v_cmp_1051_, lean_object* v_t_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1051_, v_k_1053_, v___x_1054_, v_t_1052_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x3f(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_cmp_1058_, lean_object* v_t_1059_, lean_object* v_k_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1058_, v_k_1060_, v___x_1061_, v_t_1059_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f___redArg(lean_object* v_cmp_1063_, lean_object* v_t_1064_, lean_object* v_k_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1063_, v_k_1065_, v___x_1066_, v_t_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x3f(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_cmp_1070_, lean_object* v_t_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1070_, v_k_1072_, v___x_1073_, v_t_1071_);
return v___x_1074_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1078_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__2));
v___x_1079_ = lean_unsigned_to_nat(14u);
v___x_1080_ = lean_unsigned_to_nat(22u);
v___x_1081_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__1));
v___x_1082_ = ((lean_object*)(l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__0));
v___x_1083_ = l_mkPanicMessageWithDecl(v___x_1082_, v___x_1081_, v___x_1080_, v___x_1079_, v___x_1078_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(lean_object* v_cmp_1084_, lean_object* v_inst_1085_, lean_object* v_t_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1084_, v_k_1087_, v___x_1088_, v_t_1086_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1091_ = l_panic___redArg(v_inst_1085_, v___x_1090_);
return v___x_1091_;
}
else
{
lean_object* v_val_1092_; 
v_val_1092_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_val_1092_);
lean_dec_ref_known(v___x_1089_, 1);
return v_val_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1093_, lean_object* v_inst_1094_, lean_object* v_t_1095_, lean_object* v_k_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_DTreeMap_Raw_getEntryGE_x21___redArg(v_cmp_1093_, v_inst_1094_, v_t_1095_, v_k_1096_);
lean_dec_ref(v_inst_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_cmp_1100_, lean_object* v_inst_1101_, lean_object* v_t_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1100_, v_k_1103_, v___x_1104_, v_t_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1107_ = l_panic___redArg(v_inst_1101_, v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v_val_1108_; 
v_val_1108_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v___x_1105_, 1);
return v_val_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_cmp_1111_, lean_object* v_inst_1112_, lean_object* v_t_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_DTreeMap_Raw_getEntryGE_x21(v_00_u03b1_1109_, v_00_u03b2_1110_, v_cmp_1111_, v_inst_1112_, v_t_1113_, v_k_1114_);
lean_dec_ref(v_inst_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(lean_object* v_cmp_1116_, lean_object* v_inst_1117_, lean_object* v_t_1118_, lean_object* v_k_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1116_, v_k_1119_, v___x_1120_, v_t_1118_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1123_ = l_panic___redArg(v_inst_1117_, v___x_1122_);
return v___x_1123_;
}
else
{
lean_object* v_val_1124_; 
v_val_1124_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v___x_1121_, 1);
return v_val_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1125_, lean_object* v_inst_1126_, lean_object* v_t_1127_, lean_object* v_k_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_DTreeMap_Raw_getEntryGT_x21___redArg(v_cmp_1125_, v_inst_1126_, v_t_1127_, v_k_1128_);
lean_dec_ref(v_inst_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_cmp_1132_, lean_object* v_inst_1133_, lean_object* v_t_1134_, lean_object* v_k_1135_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1132_, v_k_1135_, v___x_1136_, v_t_1134_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1139_ = l_panic___redArg(v_inst_1133_, v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v_val_1140_; 
v_val_1140_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v___x_1137_, 1);
return v_val_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_cmp_1143_, lean_object* v_inst_1144_, lean_object* v_t_1145_, lean_object* v_k_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_DTreeMap_Raw_getEntryGT_x21(v_00_u03b1_1141_, v_00_u03b2_1142_, v_cmp_1143_, v_inst_1144_, v_t_1145_, v_k_1146_);
lean_dec_ref(v_inst_1144_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(lean_object* v_cmp_1148_, lean_object* v_inst_1149_, lean_object* v_t_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1148_, v_k_1151_, v___x_1152_, v_t_1150_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1155_ = l_panic___redArg(v_inst_1149_, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v_val_1156_; 
v_val_1156_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_val_1156_);
lean_dec_ref_known(v___x_1153_, 1);
return v_val_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1157_, lean_object* v_inst_1158_, lean_object* v_t_1159_, lean_object* v_k_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_DTreeMap_Raw_getEntryLE_x21___redArg(v_cmp_1157_, v_inst_1158_, v_t_1159_, v_k_1160_);
lean_dec_ref(v_inst_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_cmp_1164_, lean_object* v_inst_1165_, lean_object* v_t_1166_, lean_object* v_k_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_box(0);
v___x_1169_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1164_, v_k_1167_, v___x_1168_, v_t_1166_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1171_ = l_panic___redArg(v_inst_1165_, v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; 
v_val_1172_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_val_1172_);
lean_dec_ref_known(v___x_1169_, 1);
return v_val_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLE_x21___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_cmp_1175_, lean_object* v_inst_1176_, lean_object* v_t_1177_, lean_object* v_k_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_DTreeMap_Raw_getEntryLE_x21(v_00_u03b1_1173_, v_00_u03b2_1174_, v_cmp_1175_, v_inst_1176_, v_t_1177_, v_k_1178_);
lean_dec_ref(v_inst_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(lean_object* v_cmp_1180_, lean_object* v_inst_1181_, lean_object* v_t_1182_, lean_object* v_k_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1180_, v_k_1183_, v___x_1184_, v_t_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1187_ = l_panic___redArg(v_inst_1181_, v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v_val_1188_; 
v_val_1188_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1188_);
lean_dec_ref_known(v___x_1185_, 1);
return v_val_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_1189_, lean_object* v_inst_1190_, lean_object* v_t_1191_, lean_object* v_k_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DTreeMap_Raw_getEntryLT_x21___redArg(v_cmp_1189_, v_inst_1190_, v_t_1191_, v_k_1192_);
lean_dec_ref(v_inst_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_cmp_1196_, lean_object* v_inst_1197_, lean_object* v_t_1198_, lean_object* v_k_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1196_, v_k_1199_, v___x_1200_, v_t_1198_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1203_ = l_panic___redArg(v_inst_1197_, v___x_1202_);
return v___x_1203_;
}
else
{
lean_object* v_val_1204_; 
v_val_1204_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1201_, 1);
return v_val_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLT_x21___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_cmp_1207_, lean_object* v_inst_1208_, lean_object* v_t_1209_, lean_object* v_k_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DTreeMap_Raw_getEntryLT_x21(v_00_u03b1_1205_, v_00_u03b2_1206_, v_cmp_1207_, v_inst_1208_, v_t_1209_, v_k_1210_);
lean_dec_ref(v_inst_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg(lean_object* v_cmp_1212_, lean_object* v_t_1213_, lean_object* v_k_1214_, lean_object* v_fallback_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1212_, v_k_1214_, v___x_1216_, v_t_1213_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_inc_ref(v_fallback_1215_);
return v_fallback_1215_;
}
else
{
lean_object* v_val_1218_; 
v_val_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_val_1218_);
lean_dec_ref_known(v___x_1217_, 1);
return v_val_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___redArg___boxed(lean_object* v_cmp_1219_, lean_object* v_t_1220_, lean_object* v_k_1221_, lean_object* v_fallback_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_DTreeMap_Raw_getEntryGED___redArg(v_cmp_1219_, v_t_1220_, v_k_1221_, v_fallback_1222_);
lean_dec_ref(v_fallback_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_cmp_1226_, lean_object* v_t_1227_, lean_object* v_k_1228_, lean_object* v_fallback_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_cmp_1226_, v_k_1228_, v___x_1230_, v_t_1227_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_inc_ref(v_fallback_1229_);
return v_fallback_1229_;
}
else
{
lean_object* v_val_1232_; 
v_val_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1231_, 1);
return v_val_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGED___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_cmp_1235_, lean_object* v_t_1236_, lean_object* v_k_1237_, lean_object* v_fallback_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_DTreeMap_Raw_getEntryGED(v_00_u03b1_1233_, v_00_u03b2_1234_, v_cmp_1235_, v_t_1236_, v_k_1237_, v_fallback_1238_);
lean_dec_ref(v_fallback_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg(lean_object* v_cmp_1240_, lean_object* v_t_1241_, lean_object* v_k_1242_, lean_object* v_fallback_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_box(0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1240_, v_k_1242_, v___x_1244_, v_t_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_inc_ref(v_fallback_1243_);
return v_fallback_1243_;
}
else
{
lean_object* v_val_1246_; 
v_val_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v___x_1245_, 1);
return v_val_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___redArg___boxed(lean_object* v_cmp_1247_, lean_object* v_t_1248_, lean_object* v_k_1249_, lean_object* v_fallback_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DTreeMap_Raw_getEntryGTD___redArg(v_cmp_1247_, v_t_1248_, v_k_1249_, v_fallback_1250_);
lean_dec_ref(v_fallback_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD(lean_object* v_00_u03b1_1252_, lean_object* v_00_u03b2_1253_, lean_object* v_cmp_1254_, lean_object* v_t_1255_, lean_object* v_k_1256_, lean_object* v_fallback_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_cmp_1254_, v_k_1256_, v___x_1258_, v_t_1255_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_inc_ref(v_fallback_1257_);
return v_fallback_1257_;
}
else
{
lean_object* v_val_1260_; 
v_val_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_val_1260_);
lean_dec_ref_known(v___x_1259_, 1);
return v_val_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryGTD___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_cmp_1263_, lean_object* v_t_1264_, lean_object* v_k_1265_, lean_object* v_fallback_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DTreeMap_Raw_getEntryGTD(v_00_u03b1_1261_, v_00_u03b2_1262_, v_cmp_1263_, v_t_1264_, v_k_1265_, v_fallback_1266_);
lean_dec_ref(v_fallback_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg(lean_object* v_cmp_1268_, lean_object* v_t_1269_, lean_object* v_k_1270_, lean_object* v_fallback_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_box(0);
v___x_1273_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1268_, v_k_1270_, v___x_1272_, v_t_1269_);
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
lean_dec_ref_known(v___x_1273_, 1);
return v_val_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___redArg___boxed(lean_object* v_cmp_1275_, lean_object* v_t_1276_, lean_object* v_k_1277_, lean_object* v_fallback_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_DTreeMap_Raw_getEntryLED___redArg(v_cmp_1275_, v_t_1276_, v_k_1277_, v_fallback_1278_);
lean_dec_ref(v_fallback_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_cmp_1282_, lean_object* v_t_1283_, lean_object* v_k_1284_, lean_object* v_fallback_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_box(0);
v___x_1287_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_cmp_1282_, v_k_1284_, v___x_1286_, v_t_1283_);
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
lean_dec_ref_known(v___x_1287_, 1);
return v_val_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLED___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_cmp_1291_, lean_object* v_t_1292_, lean_object* v_k_1293_, lean_object* v_fallback_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_DTreeMap_Raw_getEntryLED(v_00_u03b1_1289_, v_00_u03b2_1290_, v_cmp_1291_, v_t_1292_, v_k_1293_, v_fallback_1294_);
lean_dec_ref(v_fallback_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg(lean_object* v_cmp_1296_, lean_object* v_t_1297_, lean_object* v_k_1298_, lean_object* v_fallback_1299_){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1296_, v_k_1298_, v___x_1300_, v_t_1297_);
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
lean_dec_ref_known(v___x_1301_, 1);
return v_val_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___redArg___boxed(lean_object* v_cmp_1303_, lean_object* v_t_1304_, lean_object* v_k_1305_, lean_object* v_fallback_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DTreeMap_Raw_getEntryLTD___redArg(v_cmp_1303_, v_t_1304_, v_k_1305_, v_fallback_1306_);
lean_dec_ref(v_fallback_1306_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_cmp_1310_, lean_object* v_t_1311_, lean_object* v_k_1312_, lean_object* v_fallback_1313_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_cmp_1310_, v_k_1312_, v___x_1314_, v_t_1311_);
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
lean_dec_ref_known(v___x_1315_, 1);
return v_val_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getEntryLTD___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_cmp_1319_, lean_object* v_t_1320_, lean_object* v_k_1321_, lean_object* v_fallback_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_DTreeMap_Raw_getEntryLTD(v_00_u03b1_1317_, v_00_u03b2_1318_, v_cmp_1319_, v_t_1320_, v_k_1321_, v_fallback_1322_);
lean_dec_ref(v_fallback_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f___redArg(lean_object* v_cmp_1324_, lean_object* v_t_1325_, lean_object* v_k_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1324_, v_k_1326_, v___x_1327_, v_t_1325_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x3f(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_cmp_1331_, lean_object* v_t_1332_, lean_object* v_k_1333_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1331_, v_k_1333_, v___x_1334_, v_t_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f___redArg(lean_object* v_cmp_1336_, lean_object* v_t_1337_, lean_object* v_k_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1336_, v_k_1338_, v___x_1339_, v_t_1337_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x3f(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_cmp_1343_, lean_object* v_t_1344_, lean_object* v_k_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1343_, v_k_1345_, v___x_1346_, v_t_1344_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f___redArg(lean_object* v_cmp_1348_, lean_object* v_t_1349_, lean_object* v_k_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1348_, v_k_1350_, v___x_1351_, v_t_1349_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x3f(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_cmp_1355_, lean_object* v_t_1356_, lean_object* v_k_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1355_, v_k_1357_, v___x_1358_, v_t_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f___redArg(lean_object* v_cmp_1360_, lean_object* v_t_1361_, lean_object* v_k_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1360_, v_k_1362_, v___x_1363_, v_t_1361_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x3f(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_cmp_1367_, lean_object* v_t_1368_, lean_object* v_k_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1367_, v_k_1369_, v___x_1370_, v_t_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(lean_object* v_cmp_1372_, lean_object* v_inst_1373_, lean_object* v_t_1374_, lean_object* v_k_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1372_, v_k_1375_, v___x_1376_, v_t_1374_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1379_ = l_panic___redArg(v_inst_1373_, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; 
v_val_1380_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v___x_1377_, 1);
return v_val_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___redArg___boxed(lean_object* v_cmp_1381_, lean_object* v_inst_1382_, lean_object* v_t_1383_, lean_object* v_k_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_DTreeMap_Raw_getKeyGE_x21___redArg(v_cmp_1381_, v_inst_1382_, v_t_1383_, v_k_1384_);
lean_dec(v_inst_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21(lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_cmp_1388_, lean_object* v_inst_1389_, lean_object* v_t_1390_, lean_object* v_k_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1388_, v_k_1391_, v___x_1392_, v_t_1390_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1395_ = l_panic___redArg(v_inst_1389_, v___x_1394_);
return v___x_1395_;
}
else
{
lean_object* v_val_1396_; 
v_val_1396_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1396_);
lean_dec_ref_known(v___x_1393_, 1);
return v_val_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGE_x21___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_cmp_1399_, lean_object* v_inst_1400_, lean_object* v_t_1401_, lean_object* v_k_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_DTreeMap_Raw_getKeyGE_x21(v_00_u03b1_1397_, v_00_u03b2_1398_, v_cmp_1399_, v_inst_1400_, v_t_1401_, v_k_1402_);
lean_dec(v_inst_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(lean_object* v_cmp_1404_, lean_object* v_inst_1405_, lean_object* v_t_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1404_, v_k_1407_, v___x_1408_, v_t_1406_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1411_ = l_panic___redArg(v_inst_1405_, v___x_1410_);
return v___x_1411_;
}
else
{
lean_object* v_val_1412_; 
v_val_1412_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___x_1409_, 1);
return v_val_1412_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___redArg___boxed(lean_object* v_cmp_1413_, lean_object* v_inst_1414_, lean_object* v_t_1415_, lean_object* v_k_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_DTreeMap_Raw_getKeyGT_x21___redArg(v_cmp_1413_, v_inst_1414_, v_t_1415_, v_k_1416_);
lean_dec(v_inst_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21(lean_object* v_00_u03b1_1418_, lean_object* v_00_u03b2_1419_, lean_object* v_cmp_1420_, lean_object* v_inst_1421_, lean_object* v_t_1422_, lean_object* v_k_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1420_, v_k_1423_, v___x_1424_, v_t_1422_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1427_ = l_panic___redArg(v_inst_1421_, v___x_1426_);
return v___x_1427_;
}
else
{
lean_object* v_val_1428_; 
v_val_1428_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_val_1428_);
lean_dec_ref_known(v___x_1425_, 1);
return v_val_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGT_x21___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_cmp_1431_, lean_object* v_inst_1432_, lean_object* v_t_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Std_DTreeMap_Raw_getKeyGT_x21(v_00_u03b1_1429_, v_00_u03b2_1430_, v_cmp_1431_, v_inst_1432_, v_t_1433_, v_k_1434_);
lean_dec(v_inst_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(lean_object* v_cmp_1436_, lean_object* v_inst_1437_, lean_object* v_t_1438_, lean_object* v_k_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1436_, v_k_1439_, v___x_1440_, v_t_1438_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1443_ = l_panic___redArg(v_inst_1437_, v___x_1442_);
return v___x_1443_;
}
else
{
lean_object* v_val_1444_; 
v_val_1444_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v___x_1441_, 1);
return v_val_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___redArg___boxed(lean_object* v_cmp_1445_, lean_object* v_inst_1446_, lean_object* v_t_1447_, lean_object* v_k_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_DTreeMap_Raw_getKeyLE_x21___redArg(v_cmp_1445_, v_inst_1446_, v_t_1447_, v_k_1448_);
lean_dec(v_inst_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_cmp_1452_, lean_object* v_inst_1453_, lean_object* v_t_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1452_, v_k_1455_, v___x_1456_, v_t_1454_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1459_ = l_panic___redArg(v_inst_1453_, v___x_1458_);
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; 
v_val_1460_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v___x_1457_, 1);
return v_val_1460_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLE_x21___boxed(lean_object* v_00_u03b1_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_cmp_1463_, lean_object* v_inst_1464_, lean_object* v_t_1465_, lean_object* v_k_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Std_DTreeMap_Raw_getKeyLE_x21(v_00_u03b1_1461_, v_00_u03b2_1462_, v_cmp_1463_, v_inst_1464_, v_t_1465_, v_k_1466_);
lean_dec(v_inst_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(lean_object* v_cmp_1468_, lean_object* v_inst_1469_, lean_object* v_t_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1468_, v_k_1471_, v___x_1472_, v_t_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1475_ = l_panic___redArg(v_inst_1469_, v___x_1474_);
return v___x_1475_;
}
else
{
lean_object* v_val_1476_; 
v_val_1476_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1476_);
lean_dec_ref_known(v___x_1473_, 1);
return v_val_1476_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___redArg___boxed(lean_object* v_cmp_1477_, lean_object* v_inst_1478_, lean_object* v_t_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_DTreeMap_Raw_getKeyLT_x21___redArg(v_cmp_1477_, v_inst_1478_, v_t_1479_, v_k_1480_);
lean_dec(v_inst_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21(lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_cmp_1484_, lean_object* v_inst_1485_, lean_object* v_t_1486_, lean_object* v_k_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1484_, v_k_1487_, v___x_1488_, v_t_1486_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1491_ = l_panic___redArg(v_inst_1485_, v___x_1490_);
return v___x_1491_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1489_, 1);
return v_val_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLT_x21___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_cmp_1495_, lean_object* v_inst_1496_, lean_object* v_t_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_DTreeMap_Raw_getKeyLT_x21(v_00_u03b1_1493_, v_00_u03b2_1494_, v_cmp_1495_, v_inst_1496_, v_t_1497_, v_k_1498_);
lean_dec(v_inst_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg(lean_object* v_cmp_1500_, lean_object* v_t_1501_, lean_object* v_k_1502_, lean_object* v_fallback_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1500_, v_k_1502_, v___x_1504_, v_t_1501_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_inc(v_fallback_1503_);
return v_fallback_1503_;
}
else
{
lean_object* v_val_1506_; 
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1505_, 1);
return v_val_1506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___redArg___boxed(lean_object* v_cmp_1507_, lean_object* v_t_1508_, lean_object* v_k_1509_, lean_object* v_fallback_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_DTreeMap_Raw_getKeyGED___redArg(v_cmp_1507_, v_t_1508_, v_k_1509_, v_fallback_1510_);
lean_dec(v_fallback_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED(lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_cmp_1514_, lean_object* v_t_1515_, lean_object* v_k_1516_, lean_object* v_fallback_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_cmp_1514_, v_k_1516_, v___x_1518_, v_t_1515_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_inc(v_fallback_1517_);
return v_fallback_1517_;
}
else
{
lean_object* v_val_1520_; 
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec_ref_known(v___x_1519_, 1);
return v_val_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGED___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_cmp_1523_, lean_object* v_t_1524_, lean_object* v_k_1525_, lean_object* v_fallback_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Std_DTreeMap_Raw_getKeyGED(v_00_u03b1_1521_, v_00_u03b2_1522_, v_cmp_1523_, v_t_1524_, v_k_1525_, v_fallback_1526_);
lean_dec(v_fallback_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg(lean_object* v_cmp_1528_, lean_object* v_t_1529_, lean_object* v_k_1530_, lean_object* v_fallback_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1528_, v_k_1530_, v___x_1532_, v_t_1529_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_inc(v_fallback_1531_);
return v_fallback_1531_;
}
else
{
lean_object* v_val_1534_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
return v_val_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___redArg___boxed(lean_object* v_cmp_1535_, lean_object* v_t_1536_, lean_object* v_k_1537_, lean_object* v_fallback_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DTreeMap_Raw_getKeyGTD___redArg(v_cmp_1535_, v_t_1536_, v_k_1537_, v_fallback_1538_);
lean_dec(v_fallback_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD(lean_object* v_00_u03b1_1540_, lean_object* v_00_u03b2_1541_, lean_object* v_cmp_1542_, lean_object* v_t_1543_, lean_object* v_k_1544_, lean_object* v_fallback_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_box(0);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_cmp_1542_, v_k_1544_, v___x_1546_, v_t_1543_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_inc(v_fallback_1545_);
return v_fallback_1545_;
}
else
{
lean_object* v_val_1548_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v___x_1547_, 1);
return v_val_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyGTD___boxed(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_cmp_1551_, lean_object* v_t_1552_, lean_object* v_k_1553_, lean_object* v_fallback_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_DTreeMap_Raw_getKeyGTD(v_00_u03b1_1549_, v_00_u03b2_1550_, v_cmp_1551_, v_t_1552_, v_k_1553_, v_fallback_1554_);
lean_dec(v_fallback_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg(lean_object* v_cmp_1556_, lean_object* v_t_1557_, lean_object* v_k_1558_, lean_object* v_fallback_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1556_, v_k_1558_, v___x_1560_, v_t_1557_);
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
lean_dec_ref_known(v___x_1561_, 1);
return v_val_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___redArg___boxed(lean_object* v_cmp_1563_, lean_object* v_t_1564_, lean_object* v_k_1565_, lean_object* v_fallback_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_DTreeMap_Raw_getKeyLED___redArg(v_cmp_1563_, v_t_1564_, v_k_1565_, v_fallback_1566_);
lean_dec(v_fallback_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_cmp_1570_, lean_object* v_t_1571_, lean_object* v_k_1572_, lean_object* v_fallback_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_cmp_1570_, v_k_1572_, v___x_1574_, v_t_1571_);
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
lean_dec_ref_known(v___x_1575_, 1);
return v_val_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLED___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_cmp_1579_, lean_object* v_t_1580_, lean_object* v_k_1581_, lean_object* v_fallback_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Std_DTreeMap_Raw_getKeyLED(v_00_u03b1_1577_, v_00_u03b2_1578_, v_cmp_1579_, v_t_1580_, v_k_1581_, v_fallback_1582_);
lean_dec(v_fallback_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg(lean_object* v_cmp_1584_, lean_object* v_t_1585_, lean_object* v_k_1586_, lean_object* v_fallback_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1584_, v_k_1586_, v___x_1588_, v_t_1585_);
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
lean_dec_ref_known(v___x_1589_, 1);
return v_val_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___redArg___boxed(lean_object* v_cmp_1591_, lean_object* v_t_1592_, lean_object* v_k_1593_, lean_object* v_fallback_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_DTreeMap_Raw_getKeyLTD___redArg(v_cmp_1591_, v_t_1592_, v_k_1593_, v_fallback_1594_);
lean_dec(v_fallback_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_cmp_1598_, lean_object* v_t_1599_, lean_object* v_k_1600_, lean_object* v_fallback_1601_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_box(0);
v___x_1603_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_cmp_1598_, v_k_1600_, v___x_1602_, v_t_1599_);
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
lean_dec_ref_known(v___x_1603_, 1);
return v_val_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_getKeyLTD___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_cmp_1607_, lean_object* v_t_1608_, lean_object* v_k_1609_, lean_object* v_fallback_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Std_DTreeMap_Raw_getKeyLTD(v_00_u03b1_1605_, v_00_u03b2_1606_, v_cmp_1607_, v_t_1608_, v_k_1609_, v_fallback_1610_);
lean_dec(v_fallback_1610_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_cmp_1612_, lean_object* v_t_1613_, lean_object* v_a_1614_, lean_object* v_b_1615_){
_start:
{
lean_object* v___x_1616_; 
lean_inc(v_a_1614_);
lean_inc(v_t_1613_);
lean_inc_ref(v_cmp_1612_);
v___x_1616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1612_, v_t_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
uint8_t v___x_1617_; 
lean_inc(v_t_1613_);
lean_inc(v_a_1614_);
lean_inc_ref(v_cmp_1612_);
v___x_1617_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1612_, v_a_1614_, v_t_1613_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1612_, v_a_1614_, v_b_1615_, v_t_1613_);
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
lean_dec_ref(v_cmp_1612_);
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
lean_dec_ref(v_cmp_1612_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1616_);
lean_ctor_set(v___x_1621_, 1, v_t_1613_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1622_, lean_object* v_cmp_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_t_1625_, lean_object* v_a_1626_, lean_object* v_b_1627_){
_start:
{
lean_object* v___x_1628_; 
lean_inc(v_a_1626_);
lean_inc(v_t_1625_);
lean_inc_ref(v_cmp_1623_);
v___x_1628_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1623_, v_t_1625_, v_a_1626_);
if (lean_obj_tag(v___x_1628_) == 0)
{
uint8_t v___x_1629_; 
lean_inc(v_t_1625_);
lean_inc(v_a_1626_);
lean_inc_ref(v_cmp_1623_);
v___x_1629_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_1623_, v_a_1626_, v_t_1625_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_1623_, v_a_1626_, v_b_1627_, v_t_1625_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1628_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; 
lean_dec(v_b_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_cmp_1623_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1628_);
lean_ctor_set(v___x_1632_, 1, v_t_1625_);
return v___x_1632_;
}
}
else
{
lean_object* v___x_1633_; 
lean_dec(v_b_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_cmp_1623_);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1628_);
lean_ctor_set(v___x_1633_, 1, v_t_1625_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f___redArg(lean_object* v_cmp_1634_, lean_object* v_t_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1634_, v_t_1635_, v_a_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_1638_, lean_object* v_cmp_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_t_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_1639_, v_t_1641_, v_a_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get___redArg(lean_object* v_cmp_1644_, lean_object* v_t_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1644_, v_t_1645_, v_a_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get(lean_object* v_00_u03b1_1648_, lean_object* v_cmp_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_t_1651_, lean_object* v_a_1652_, lean_object* v_h_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_cmp_1649_, v_t_1651_, v_a_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg(lean_object* v_cmp_1655_, lean_object* v_inst_1656_, lean_object* v_t_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1655_, v_inst_1656_, v_t_1657_, v_a_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_cmp_1660_, lean_object* v_inst_1661_, lean_object* v_t_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_DTreeMap_Raw_Const_get_x21___redArg(v_cmp_1660_, v_inst_1661_, v_t_1662_, v_a_1663_);
lean_dec(v_inst_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1665_, lean_object* v_cmp_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_inst_1668_, lean_object* v_t_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_cmp_1666_, v_inst_1668_, v_t_1669_, v_a_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_cmp_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_inst_1675_, lean_object* v_t_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DTreeMap_Raw_Const_get_x21(v_00_u03b1_1672_, v_cmp_1673_, v_00_u03b2_1674_, v_inst_1675_, v_t_1676_, v_a_1677_);
lean_dec(v_inst_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg(lean_object* v_cmp_1679_, lean_object* v_t_1680_, lean_object* v_a_1681_, lean_object* v_fallback_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1679_, v_t_1680_, v_a_1681_, v_fallback_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___redArg___boxed(lean_object* v_cmp_1684_, lean_object* v_t_1685_, lean_object* v_a_1686_, lean_object* v_fallback_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_DTreeMap_Raw_Const_getD___redArg(v_cmp_1684_, v_t_1685_, v_a_1686_, v_fallback_1687_);
lean_dec(v_fallback_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD(lean_object* v_00_u03b1_1689_, lean_object* v_cmp_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_t_1692_, lean_object* v_a_1693_, lean_object* v_fallback_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_cmp_1690_, v_t_1692_, v_a_1693_, v_fallback_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_cmp_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_t_1699_, lean_object* v_a_1700_, lean_object* v_fallback_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_DTreeMap_Raw_Const_getD(v_00_u03b1_1696_, v_cmp_1697_, v_00_u03b2_1698_, v_t_1699_, v_a_1700_, v_fallback_1701_);
lean_dec(v_fallback_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(lean_object* v_t_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg___boxed(lean_object* v_t_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f___redArg(v_t_1705_);
lean_dec(v_t_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f(lean_object* v_00_u03b1_1707_, lean_object* v_cmp_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_t_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_t_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_cmp_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_t_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_DTreeMap_Raw_Const_minEntry_x3f(v_00_u03b1_1712_, v_cmp_1713_, v_00_u03b2_1714_, v_t_1715_);
lean_dec(v_t_1715_);
lean_dec_ref(v_cmp_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(lean_object* v_inst_1717_, lean_object* v_t_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1717_, v_t_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_1720_, lean_object* v_t_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DTreeMap_Raw_Const_minEntry_x21___redArg(v_inst_1720_, v_t_1721_);
lean_dec(v_t_1721_);
lean_dec_ref(v_inst_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21(lean_object* v_00_u03b1_1723_, lean_object* v_cmp_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_inst_1726_, lean_object* v_t_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_1726_, v_t_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_cmp_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_inst_1732_, lean_object* v_t_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Std_DTreeMap_Raw_Const_minEntry_x21(v_00_u03b1_1729_, v_cmp_1730_, v_00_u03b2_1731_, v_inst_1732_, v_t_1733_);
lean_dec(v_t_1733_);
lean_dec_ref(v_inst_1732_);
lean_dec_ref(v_cmp_1730_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg(lean_object* v_t_1735_, lean_object* v_fallback_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1735_, v_fallback_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___redArg___boxed(lean_object* v_t_1738_, lean_object* v_fallback_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_DTreeMap_Raw_Const_minEntryD___redArg(v_t_1738_, v_fallback_1739_);
lean_dec_ref(v_fallback_1739_);
lean_dec(v_t_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD(lean_object* v_00_u03b1_1741_, lean_object* v_cmp_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_t_1744_, lean_object* v_fallback_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_t_1744_, v_fallback_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_minEntryD___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_cmp_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_t_1750_, lean_object* v_fallback_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Std_DTreeMap_Raw_Const_minEntryD(v_00_u03b1_1747_, v_cmp_1748_, v_00_u03b2_1749_, v_t_1750_, v_fallback_1751_);
lean_dec_ref(v_fallback_1751_);
lean_dec(v_t_1750_);
lean_dec_ref(v_cmp_1748_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(lean_object* v_t_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg___boxed(lean_object* v_t_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f___redArg(v_t_1755_);
lean_dec(v_t_1755_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f(lean_object* v_00_u03b1_1757_, lean_object* v_cmp_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_t_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_t_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_cmp_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_t_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_DTreeMap_Raw_Const_maxEntry_x3f(v_00_u03b1_1762_, v_cmp_1763_, v_00_u03b2_1764_, v_t_1765_);
lean_dec(v_t_1765_);
lean_dec_ref(v_cmp_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(lean_object* v_inst_1767_, lean_object* v_t_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1767_, v_t_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_1770_, lean_object* v_t_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21___redArg(v_inst_1770_, v_t_1771_);
lean_dec(v_t_1771_);
lean_dec_ref(v_inst_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21(lean_object* v_00_u03b1_1773_, lean_object* v_cmp_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_inst_1776_, lean_object* v_t_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_1776_, v_t_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_cmp_1780_, lean_object* v_00_u03b2_1781_, lean_object* v_inst_1782_, lean_object* v_t_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DTreeMap_Raw_Const_maxEntry_x21(v_00_u03b1_1779_, v_cmp_1780_, v_00_u03b2_1781_, v_inst_1782_, v_t_1783_);
lean_dec(v_t_1783_);
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_cmp_1780_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(lean_object* v_t_1785_, lean_object* v_fallback_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1785_, v_fallback_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___redArg___boxed(lean_object* v_t_1788_, lean_object* v_fallback_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DTreeMap_Raw_Const_maxEntryD___redArg(v_t_1788_, v_fallback_1789_);
lean_dec_ref(v_fallback_1789_);
lean_dec(v_t_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD(lean_object* v_00_u03b1_1791_, lean_object* v_cmp_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_t_1794_, lean_object* v_fallback_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_t_1794_, v_fallback_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_maxEntryD___boxed(lean_object* v_00_u03b1_1797_, lean_object* v_cmp_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_t_1800_, lean_object* v_fallback_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_DTreeMap_Raw_Const_maxEntryD(v_00_u03b1_1797_, v_cmp_1798_, v_00_u03b2_1799_, v_t_1800_, v_fallback_1801_);
lean_dec_ref(v_fallback_1801_);
lean_dec(v_t_1800_);
lean_dec_ref(v_cmp_1798_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(lean_object* v_t_1803_, lean_object* v_n_1804_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1803_, v_n_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_t_1806_, lean_object* v_n_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___redArg(v_t_1806_, v_n_1807_);
lean_dec(v_t_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_1809_, lean_object* v_cmp_1810_, lean_object* v_00_u03b2_1811_, lean_object* v_t_1812_, lean_object* v_n_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_t_1812_, v_n_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_cmp_1816_, lean_object* v_00_u03b2_1817_, lean_object* v_t_1818_, lean_object* v_n_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x3f(v_00_u03b1_1815_, v_cmp_1816_, v_00_u03b2_1817_, v_t_1818_, v_n_1819_);
lean_dec(v_t_1818_);
lean_dec_ref(v_cmp_1816_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(lean_object* v_inst_1821_, lean_object* v_t_1822_, lean_object* v_n_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1821_, v_t_1822_, v_n_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_1825_, lean_object* v_t_1826_, lean_object* v_n_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___redArg(v_inst_1825_, v_t_1826_, v_n_1827_);
lean_dec(v_t_1826_);
lean_dec_ref(v_inst_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(lean_object* v_00_u03b1_1829_, lean_object* v_cmp_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_inst_1832_, lean_object* v_t_1833_, lean_object* v_n_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_1832_, v_t_1833_, v_n_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_cmp_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_inst_1839_, lean_object* v_t_1840_, lean_object* v_n_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Std_DTreeMap_Raw_Const_entryAtIdx_x21(v_00_u03b1_1836_, v_cmp_1837_, v_00_u03b2_1838_, v_inst_1839_, v_t_1840_, v_n_1841_);
lean_dec(v_t_1840_);
lean_dec_ref(v_inst_1839_);
lean_dec_ref(v_cmp_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(lean_object* v_t_1843_, lean_object* v_n_1844_, lean_object* v_fallback_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1843_, v_n_1844_, v_fallback_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg___boxed(lean_object* v_t_1847_, lean_object* v_n_1848_, lean_object* v_fallback_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD___redArg(v_t_1847_, v_n_1848_, v_fallback_1849_);
lean_dec_ref(v_fallback_1849_);
lean_dec(v_t_1847_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD(lean_object* v_00_u03b1_1851_, lean_object* v_cmp_1852_, lean_object* v_00_u03b2_1853_, lean_object* v_t_1854_, lean_object* v_n_1855_, lean_object* v_fallback_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_t_1854_, v_n_1855_, v_fallback_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_cmp_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_t_1861_, lean_object* v_n_1862_, lean_object* v_fallback_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_DTreeMap_Raw_Const_entryAtIdxD(v_00_u03b1_1858_, v_cmp_1859_, v_00_u03b2_1860_, v_t_1861_, v_n_1862_, v_fallback_1863_);
lean_dec_ref(v_fallback_1863_);
lean_dec(v_t_1861_);
lean_dec_ref(v_cmp_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f___redArg(lean_object* v_cmp_1865_, lean_object* v_t_1866_, lean_object* v_k_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1865_, v_k_1867_, v___x_1868_, v_t_1866_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x3f(lean_object* v_00_u03b1_1870_, lean_object* v_cmp_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_t_1873_, lean_object* v_k_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1871_, v_k_1874_, v___x_1875_, v_t_1873_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f___redArg(lean_object* v_cmp_1877_, lean_object* v_t_1878_, lean_object* v_k_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1877_, v_k_1879_, v___x_1880_, v_t_1878_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x3f(lean_object* v_00_u03b1_1882_, lean_object* v_cmp_1883_, lean_object* v_00_u03b2_1884_, lean_object* v_t_1885_, lean_object* v_k_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_box(0);
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1883_, v_k_1886_, v___x_1887_, v_t_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f___redArg(lean_object* v_cmp_1889_, lean_object* v_t_1890_, lean_object* v_k_1891_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1889_, v_k_1891_, v___x_1892_, v_t_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x3f(lean_object* v_00_u03b1_1894_, lean_object* v_cmp_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_t_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1895_, v_k_1898_, v___x_1899_, v_t_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f___redArg(lean_object* v_cmp_1901_, lean_object* v_t_1902_, lean_object* v_k_1903_){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_box(0);
v___x_1905_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1901_, v_k_1903_, v___x_1904_, v_t_1902_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x3f(lean_object* v_00_u03b1_1906_, lean_object* v_cmp_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_t_1909_, lean_object* v_k_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_1907_, v_k_1910_, v___x_1911_, v_t_1909_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(lean_object* v_cmp_1913_, lean_object* v_inst_1914_, lean_object* v_t_1915_, lean_object* v_k_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_box(0);
v___x_1918_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1913_, v_k_1916_, v___x_1917_, v_t_1915_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1920_ = l_panic___redArg(v_inst_1914_, v___x_1919_);
return v___x_1920_;
}
else
{
lean_object* v_val_1921_; 
v_val_1921_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_val_1921_);
lean_dec_ref_known(v___x_1918_, 1);
return v_val_1921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg___boxed(lean_object* v_cmp_1922_, lean_object* v_inst_1923_, lean_object* v_t_1924_, lean_object* v_k_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21___redArg(v_cmp_1922_, v_inst_1923_, v_t_1924_, v_k_1925_);
lean_dec_ref(v_inst_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21(lean_object* v_00_u03b1_1927_, lean_object* v_cmp_1928_, lean_object* v_00_u03b2_1929_, lean_object* v_inst_1930_, lean_object* v_t_1931_, lean_object* v_k_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_box(0);
v___x_1934_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_1928_, v_k_1932_, v___x_1933_, v_t_1931_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1936_ = l_panic___redArg(v_inst_1930_, v___x_1935_);
return v___x_1936_;
}
else
{
lean_object* v_val_1937_; 
v_val_1937_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v___x_1934_, 1);
return v_val_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_1938_, lean_object* v_cmp_1939_, lean_object* v_00_u03b2_1940_, lean_object* v_inst_1941_, lean_object* v_t_1942_, lean_object* v_k_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_DTreeMap_Raw_Const_getEntryGE_x21(v_00_u03b1_1938_, v_cmp_1939_, v_00_u03b2_1940_, v_inst_1941_, v_t_1942_, v_k_1943_);
lean_dec_ref(v_inst_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(lean_object* v_cmp_1945_, lean_object* v_inst_1946_, lean_object* v_t_1947_, lean_object* v_k_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1945_, v_k_1948_, v___x_1949_, v_t_1947_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1952_ = l_panic___redArg(v_inst_1946_, v___x_1951_);
return v___x_1952_;
}
else
{
lean_object* v_val_1953_; 
v_val_1953_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_val_1953_);
lean_dec_ref_known(v___x_1950_, 1);
return v_val_1953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg___boxed(lean_object* v_cmp_1954_, lean_object* v_inst_1955_, lean_object* v_t_1956_, lean_object* v_k_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21___redArg(v_cmp_1954_, v_inst_1955_, v_t_1956_, v_k_1957_);
lean_dec_ref(v_inst_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21(lean_object* v_00_u03b1_1959_, lean_object* v_cmp_1960_, lean_object* v_00_u03b2_1961_, lean_object* v_inst_1962_, lean_object* v_t_1963_, lean_object* v_k_1964_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_box(0);
v___x_1966_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_1960_, v_k_1964_, v___x_1965_, v_t_1963_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1968_ = l_panic___redArg(v_inst_1962_, v___x_1967_);
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; 
v_val_1969_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v___x_1966_, 1);
return v_val_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_1970_, lean_object* v_cmp_1971_, lean_object* v_00_u03b2_1972_, lean_object* v_inst_1973_, lean_object* v_t_1974_, lean_object* v_k_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Std_DTreeMap_Raw_Const_getEntryGT_x21(v_00_u03b1_1970_, v_cmp_1971_, v_00_u03b2_1972_, v_inst_1973_, v_t_1974_, v_k_1975_);
lean_dec_ref(v_inst_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(lean_object* v_cmp_1977_, lean_object* v_inst_1978_, lean_object* v_t_1979_, lean_object* v_k_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1977_, v_k_1980_, v___x_1981_, v_t_1979_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_1984_ = l_panic___redArg(v_inst_1978_, v___x_1983_);
return v___x_1984_;
}
else
{
lean_object* v_val_1985_; 
v_val_1985_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v___x_1982_, 1);
return v_val_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg___boxed(lean_object* v_cmp_1986_, lean_object* v_inst_1987_, lean_object* v_t_1988_, lean_object* v_k_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21___redArg(v_cmp_1986_, v_inst_1987_, v_t_1988_, v_k_1989_);
lean_dec_ref(v_inst_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21(lean_object* v_00_u03b1_1991_, lean_object* v_cmp_1992_, lean_object* v_00_u03b2_1993_, lean_object* v_inst_1994_, lean_object* v_t_1995_, lean_object* v_k_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_1992_, v_k_1996_, v___x_1997_, v_t_1995_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2000_ = l_panic___redArg(v_inst_1994_, v___x_1999_);
return v___x_2000_;
}
else
{
lean_object* v_val_2001_; 
v_val_2001_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v___x_1998_, 1);
return v_val_2001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2002_, lean_object* v_cmp_2003_, lean_object* v_00_u03b2_2004_, lean_object* v_inst_2005_, lean_object* v_t_2006_, lean_object* v_k_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Std_DTreeMap_Raw_Const_getEntryLE_x21(v_00_u03b1_2002_, v_cmp_2003_, v_00_u03b2_2004_, v_inst_2005_, v_t_2006_, v_k_2007_);
lean_dec_ref(v_inst_2005_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(lean_object* v_cmp_2009_, lean_object* v_inst_2010_, lean_object* v_t_2011_, lean_object* v_k_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_box(0);
v___x_2014_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2009_, v_k_2012_, v___x_2013_, v_t_2011_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2016_ = l_panic___redArg(v_inst_2010_, v___x_2015_);
return v___x_2016_;
}
else
{
lean_object* v_val_2017_; 
v_val_2017_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v___x_2014_, 1);
return v_val_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg___boxed(lean_object* v_cmp_2018_, lean_object* v_inst_2019_, lean_object* v_t_2020_, lean_object* v_k_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21___redArg(v_cmp_2018_, v_inst_2019_, v_t_2020_, v_k_2021_);
lean_dec_ref(v_inst_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21(lean_object* v_00_u03b1_2023_, lean_object* v_cmp_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_inst_2026_, lean_object* v_t_2027_, lean_object* v_k_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2024_, v_k_2028_, v___x_2029_, v_t_2027_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_obj_once(&l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Raw_getEntryGE_x21___redArg___closed__3);
v___x_2032_ = l_panic___redArg(v_inst_2026_, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v_val_2033_; 
v_val_2033_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_val_2033_);
lean_dec_ref_known(v___x_2030_, 1);
return v_val_2033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2034_, lean_object* v_cmp_2035_, lean_object* v_00_u03b2_2036_, lean_object* v_inst_2037_, lean_object* v_t_2038_, lean_object* v_k_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_DTreeMap_Raw_Const_getEntryLT_x21(v_00_u03b1_2034_, v_cmp_2035_, v_00_u03b2_2036_, v_inst_2037_, v_t_2038_, v_k_2039_);
lean_dec_ref(v_inst_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(lean_object* v_cmp_2041_, lean_object* v_t_2042_, lean_object* v_k_2043_, lean_object* v_fallback_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2041_, v_k_2043_, v___x_2045_, v_t_2042_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_inc_ref(v_fallback_2044_);
return v_fallback_2044_;
}
else
{
lean_object* v_val_2047_; 
v_val_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v___x_2046_, 1);
return v_val_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___redArg___boxed(lean_object* v_cmp_2048_, lean_object* v_t_2049_, lean_object* v_k_2050_, lean_object* v_fallback_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_DTreeMap_Raw_Const_getEntryGED___redArg(v_cmp_2048_, v_t_2049_, v_k_2050_, v_fallback_2051_);
lean_dec_ref(v_fallback_2051_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED(lean_object* v_00_u03b1_2053_, lean_object* v_cmp_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_t_2056_, lean_object* v_k_2057_, lean_object* v_fallback_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_cmp_2054_, v_k_2057_, v___x_2059_, v_t_2056_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_inc_ref(v_fallback_2058_);
return v_fallback_2058_;
}
else
{
lean_object* v_val_2061_; 
v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_val_2061_);
lean_dec_ref_known(v___x_2060_, 1);
return v_val_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGED___boxed(lean_object* v_00_u03b1_2062_, lean_object* v_cmp_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_t_2065_, lean_object* v_k_2066_, lean_object* v_fallback_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_DTreeMap_Raw_Const_getEntryGED(v_00_u03b1_2062_, v_cmp_2063_, v_00_u03b2_2064_, v_t_2065_, v_k_2066_, v_fallback_2067_);
lean_dec_ref(v_fallback_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(lean_object* v_cmp_2069_, lean_object* v_t_2070_, lean_object* v_k_2071_, lean_object* v_fallback_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2069_, v_k_2071_, v___x_2073_, v_t_2070_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_inc_ref(v_fallback_2072_);
return v_fallback_2072_;
}
else
{
lean_object* v_val_2075_; 
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2074_, 1);
return v_val_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg___boxed(lean_object* v_cmp_2076_, lean_object* v_t_2077_, lean_object* v_k_2078_, lean_object* v_fallback_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Std_DTreeMap_Raw_Const_getEntryGTD___redArg(v_cmp_2076_, v_t_2077_, v_k_2078_, v_fallback_2079_);
lean_dec_ref(v_fallback_2079_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD(lean_object* v_00_u03b1_2081_, lean_object* v_cmp_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_t_2084_, lean_object* v_k_2085_, lean_object* v_fallback_2086_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_cmp_2082_, v_k_2085_, v___x_2087_, v_t_2084_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_inc_ref(v_fallback_2086_);
return v_fallback_2086_;
}
else
{
lean_object* v_val_2089_; 
v_val_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_val_2089_);
lean_dec_ref_known(v___x_2088_, 1);
return v_val_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_cmp_2091_, lean_object* v_00_u03b2_2092_, lean_object* v_t_2093_, lean_object* v_k_2094_, lean_object* v_fallback_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_DTreeMap_Raw_Const_getEntryGTD(v_00_u03b1_2090_, v_cmp_2091_, v_00_u03b2_2092_, v_t_2093_, v_k_2094_, v_fallback_2095_);
lean_dec_ref(v_fallback_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(lean_object* v_cmp_2097_, lean_object* v_t_2098_, lean_object* v_k_2099_, lean_object* v_fallback_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2097_, v_k_2099_, v___x_2101_, v_t_2098_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_inc_ref(v_fallback_2100_);
return v_fallback_2100_;
}
else
{
lean_object* v_val_2103_; 
v_val_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_val_2103_);
lean_dec_ref_known(v___x_2102_, 1);
return v_val_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___redArg___boxed(lean_object* v_cmp_2104_, lean_object* v_t_2105_, lean_object* v_k_2106_, lean_object* v_fallback_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Std_DTreeMap_Raw_Const_getEntryLED___redArg(v_cmp_2104_, v_t_2105_, v_k_2106_, v_fallback_2107_);
lean_dec_ref(v_fallback_2107_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED(lean_object* v_00_u03b1_2109_, lean_object* v_cmp_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_t_2112_, lean_object* v_k_2113_, lean_object* v_fallback_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_box(0);
v___x_2116_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_cmp_2110_, v_k_2113_, v___x_2115_, v_t_2112_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_inc_ref(v_fallback_2114_);
return v_fallback_2114_;
}
else
{
lean_object* v_val_2117_; 
v_val_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v___x_2116_, 1);
return v_val_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLED___boxed(lean_object* v_00_u03b1_2118_, lean_object* v_cmp_2119_, lean_object* v_00_u03b2_2120_, lean_object* v_t_2121_, lean_object* v_k_2122_, lean_object* v_fallback_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_DTreeMap_Raw_Const_getEntryLED(v_00_u03b1_2118_, v_cmp_2119_, v_00_u03b2_2120_, v_t_2121_, v_k_2122_, v_fallback_2123_);
lean_dec_ref(v_fallback_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(lean_object* v_cmp_2125_, lean_object* v_t_2126_, lean_object* v_k_2127_, lean_object* v_fallback_2128_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2125_, v_k_2127_, v___x_2129_, v_t_2126_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_inc_ref(v_fallback_2128_);
return v_fallback_2128_;
}
else
{
lean_object* v_val_2131_; 
v_val_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v___x_2130_, 1);
return v_val_2131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg___boxed(lean_object* v_cmp_2132_, lean_object* v_t_2133_, lean_object* v_k_2134_, lean_object* v_fallback_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Std_DTreeMap_Raw_Const_getEntryLTD___redArg(v_cmp_2132_, v_t_2133_, v_k_2134_, v_fallback_2135_);
lean_dec_ref(v_fallback_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD(lean_object* v_00_u03b1_2137_, lean_object* v_cmp_2138_, lean_object* v_00_u03b2_2139_, lean_object* v_t_2140_, lean_object* v_k_2141_, lean_object* v_fallback_2142_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_box(0);
v___x_2144_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_cmp_2138_, v_k_2141_, v___x_2143_, v_t_2140_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_inc_ref(v_fallback_2142_);
return v_fallback_2142_;
}
else
{
lean_object* v_val_2145_; 
v_val_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2144_, 1);
return v_val_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_cmp_2147_, lean_object* v_00_u03b2_2148_, lean_object* v_t_2149_, lean_object* v_k_2150_, lean_object* v_fallback_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_DTreeMap_Raw_Const_getEntryLTD(v_00_u03b1_2146_, v_cmp_2147_, v_00_u03b2_2148_, v_t_2149_, v_k_2150_, v_fallback_2151_);
lean_dec_ref(v_fallback_2151_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___redArg(lean_object* v_f_2153_, lean_object* v_t_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2153_, v_t_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter(lean_object* v_00_u03b1_2156_, lean_object* v_00_u03b2_2157_, lean_object* v_cmp_2158_, lean_object* v_f_2159_, lean_object* v_t_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Std_DTreeMap_Internal_Impl_filter_x21___redArg(v_f_2159_, v_t_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_filter___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_00_u03b2_2163_, lean_object* v_cmp_2164_, lean_object* v_f_2165_, lean_object* v_t_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Std_DTreeMap_Raw_filter(v_00_u03b1_2162_, v_00_u03b2_2163_, v_cmp_2164_, v_f_2165_, v_t_2166_);
lean_dec_ref(v_cmp_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___redArg(lean_object* v_inst_2168_, lean_object* v_f_2169_, lean_object* v_init_2170_, lean_object* v_t_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2168_, v_f_2169_, v_init_2170_, v_t_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM(lean_object* v_00_u03b1_2173_, lean_object* v_00_u03b2_2174_, lean_object* v_cmp_2175_, lean_object* v_00_u03b4_2176_, lean_object* v_m_2177_, lean_object* v_inst_2178_, lean_object* v_f_2179_, lean_object* v_init_2180_, lean_object* v_t_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2178_, v_f_2179_, v_init_2180_, v_t_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldlM___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_cmp_2185_, lean_object* v_00_u03b4_2186_, lean_object* v_m_2187_, lean_object* v_inst_2188_, lean_object* v_f_2189_, lean_object* v_init_2190_, lean_object* v_t_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Std_DTreeMap_Raw_foldlM(v_00_u03b1_2183_, v_00_u03b2_2184_, v_cmp_2185_, v_00_u03b4_2186_, v_m_2187_, v_inst_2188_, v_f_2189_, v_init_2190_, v_t_2191_);
lean_dec_ref(v_cmp_2185_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___redArg(lean_object* v_f_2193_, lean_object* v_init_2194_, lean_object* v_t_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2193_, v_init_2194_, v_t_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl(lean_object* v_00_u03b1_2197_, lean_object* v_00_u03b2_2198_, lean_object* v_cmp_2199_, lean_object* v_00_u03b4_2200_, lean_object* v_f_2201_, lean_object* v_init_2202_, lean_object* v_t_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_2201_, v_init_2202_, v_t_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldl___boxed(lean_object* v_00_u03b1_2205_, lean_object* v_00_u03b2_2206_, lean_object* v_cmp_2207_, lean_object* v_00_u03b4_2208_, lean_object* v_f_2209_, lean_object* v_init_2210_, lean_object* v_t_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Std_DTreeMap_Raw_foldl(v_00_u03b1_2205_, v_00_u03b2_2206_, v_cmp_2207_, v_00_u03b4_2208_, v_f_2209_, v_init_2210_, v_t_2211_);
lean_dec_ref(v_cmp_2207_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___redArg(lean_object* v_inst_2213_, lean_object* v_f_2214_, lean_object* v_init_2215_, lean_object* v_t_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2213_, v_f_2214_, v_init_2215_, v_t_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_cmp_2220_, lean_object* v_00_u03b4_2221_, lean_object* v_m_2222_, lean_object* v_inst_2223_, lean_object* v_f_2224_, lean_object* v_init_2225_, lean_object* v_t_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_2223_, v_f_2224_, v_init_2225_, v_t_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldrM___boxed(lean_object* v_00_u03b1_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_cmp_2230_, lean_object* v_00_u03b4_2231_, lean_object* v_m_2232_, lean_object* v_inst_2233_, lean_object* v_f_2234_, lean_object* v_init_2235_, lean_object* v_t_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Std_DTreeMap_Raw_foldrM(v_00_u03b1_2228_, v_00_u03b2_2229_, v_cmp_2230_, v_00_u03b4_2231_, v_m_2232_, v_inst_2233_, v_f_2234_, v_init_2235_, v_t_2236_);
lean_dec_ref(v_cmp_2230_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg___lam__0(lean_object* v_f_2238_, lean_object* v_x1_2239_, lean_object* v_x2_2240_, lean_object* v_x3_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_apply_3(v_f_2238_, v_x1_2239_, v_x2_2240_, v_x3_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___redArg(lean_object* v_f_2262_, lean_object* v_init_2263_, lean_object* v_t_2264_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr(lean_object* v_00_u03b1_2268_, lean_object* v_00_u03b2_2269_, lean_object* v_cmp_2270_, lean_object* v_00_u03b4_2271_, lean_object* v_f_2272_, lean_object* v_init_2273_, lean_object* v_t_2274_){
_start:
{
lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___f_2275_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_foldr___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2275_, 0, v_f_2272_);
v___x_2276_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2277_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2276_, v___f_2275_, v_init_2273_, v_t_2274_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_foldr___boxed(lean_object* v_00_u03b1_2278_, lean_object* v_00_u03b2_2279_, lean_object* v_cmp_2280_, lean_object* v_00_u03b4_2281_, lean_object* v_f_2282_, lean_object* v_init_2283_, lean_object* v_t_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Std_DTreeMap_Raw_foldr(v_00_u03b1_2278_, v_00_u03b2_2279_, v_cmp_2280_, v_00_u03b4_2281_, v_f_2282_, v_init_2283_, v_t_2284_);
lean_dec_ref(v_cmp_2280_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg___lam__0(lean_object* v_f_2286_, lean_object* v_cmp_2287_, lean_object* v_x_2288_, lean_object* v_a_2289_, lean_object* v_b_2290_){
_start:
{
lean_object* v_fst_2291_; lean_object* v_snd_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2306_; 
v_fst_2291_ = lean_ctor_get(v_x_2288_, 0);
v_snd_2292_ = lean_ctor_get(v_x_2288_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_x_2288_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2294_ = v_x_2288_;
v_isShared_2295_ = v_isSharedCheck_2306_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_snd_2292_);
lean_inc(v_fst_2291_);
lean_dec(v_x_2288_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2306_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
lean_inc(v_b_2290_);
lean_inc(v_a_2289_);
v___x_2296_ = lean_apply_2(v_f_2286_, v_a_2289_, v_b_2290_);
v___x_2297_ = lean_unbox(v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2287_, v_a_2289_, v_b_2290_, v_snd_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2298_);
v___x_2300_ = v___x_2294_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_2287_, v_a_2289_, v_b_2290_, v_fst_2291_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2302_);
v___x_2304_ = v___x_2294_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_snd_2292_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition___redArg(lean_object* v_cmp_2309_, lean_object* v_f_2310_, lean_object* v_t_2311_){
_start:
{
lean_object* v___f_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___f_2312_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2312_, 0, v_f_2310_);
lean_closure_set(v___f_2312_, 1, v_cmp_2309_);
v___x_2313_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2314_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2312_, v___x_2313_, v_t_2311_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_partition(lean_object* v_00_u03b1_2315_, lean_object* v_00_u03b2_2316_, lean_object* v_cmp_2317_, lean_object* v_f_2318_, lean_object* v_t_2319_){
_start:
{
lean_object* v___f_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___f_2320_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_partition___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2320_, 0, v_f_2318_);
lean_closure_set(v___f_2320_, 1, v_cmp_2317_);
v___x_2321_ = ((lean_object*)(l_Std_DTreeMap_Raw_partition___redArg___closed__0));
v___x_2322_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2320_, v___x_2321_, v_t_2319_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg___lam__0(lean_object* v_f_2323_, lean_object* v_x_2324_, lean_object* v_k_2325_, lean_object* v_v_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_apply_2(v_f_2323_, v_k_2325_, v_v_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___redArg(lean_object* v_inst_2328_, lean_object* v_f_2329_, lean_object* v_t_2330_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM(lean_object* v_00_u03b1_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_cmp_2336_, lean_object* v_m_2337_, lean_object* v_inst_2338_, lean_object* v_f_2339_, lean_object* v_t_2340_){
_start:
{
lean_object* v___f_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___f_2341_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2341_, 0, v_f_2339_);
v___x_2342_ = lean_box(0);
v___x_2343_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2338_, v___f_2341_, v___x_2342_, v_t_2340_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forM___boxed(lean_object* v_00_u03b1_2344_, lean_object* v_00_u03b2_2345_, lean_object* v_cmp_2346_, lean_object* v_m_2347_, lean_object* v_inst_2348_, lean_object* v_f_2349_, lean_object* v_t_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Std_DTreeMap_Raw_forM(v_00_u03b1_2344_, v_00_u03b2_2345_, v_cmp_2346_, v_m_2347_, v_inst_2348_, v_f_2349_, v_t_2350_);
lean_dec_ref(v_cmp_2346_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg___lam__0(lean_object* v_toPure_2352_, lean_object* v_____do__lift_2353_){
_start:
{
lean_object* v_a_2354_; lean_object* v___x_2355_; 
v_a_2354_ = lean_ctor_get(v_____do__lift_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v_____do__lift_2353_);
v___x_2355_ = lean_apply_2(v_toPure_2352_, lean_box(0), v_a_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___redArg(lean_object* v_inst_2356_, lean_object* v_f_2357_, lean_object* v_init_2358_, lean_object* v_t_2359_){
_start:
{
lean_object* v_toApplicative_2360_; lean_object* v_toBind_2361_; lean_object* v_toPure_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; 
v_toApplicative_2360_ = lean_ctor_get(v_inst_2356_, 0);
v_toBind_2361_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc(v_toBind_2361_);
v_toPure_2362_ = lean_ctor_get(v_toApplicative_2360_, 1);
lean_inc(v_toPure_2362_);
v___x_2363_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2356_, v_f_2357_, v_init_2358_, v_t_2359_);
v___f_2364_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2364_, 0, v_toPure_2362_);
v___x_2365_ = lean_apply_4(v_toBind_2361_, lean_box(0), lean_box(0), v___x_2363_, v___f_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn(lean_object* v_00_u03b1_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_cmp_2368_, lean_object* v_00_u03b4_2369_, lean_object* v_m_2370_, lean_object* v_inst_2371_, lean_object* v_f_2372_, lean_object* v_init_2373_, lean_object* v_t_2374_){
_start:
{
lean_object* v_toApplicative_2375_; lean_object* v_toBind_2376_; lean_object* v_toPure_2377_; lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; 
v_toApplicative_2375_ = lean_ctor_get(v_inst_2371_, 0);
v_toBind_2376_ = lean_ctor_get(v_inst_2371_, 1);
lean_inc(v_toBind_2376_);
v_toPure_2377_ = lean_ctor_get(v_toApplicative_2375_, 1);
lean_inc(v_toPure_2377_);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2371_, v_f_2372_, v_init_2373_, v_t_2374_);
v___f_2379_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2379_, 0, v_toPure_2377_);
v___x_2380_ = lean_apply_4(v_toBind_2376_, lean_box(0), lean_box(0), v___x_2378_, v___f_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_forIn___boxed(lean_object* v_00_u03b1_2381_, lean_object* v_00_u03b2_2382_, lean_object* v_cmp_2383_, lean_object* v_00_u03b4_2384_, lean_object* v_m_2385_, lean_object* v_inst_2386_, lean_object* v_f_2387_, lean_object* v_init_2388_, lean_object* v_t_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Std_DTreeMap_Raw_forIn(v_00_u03b1_2381_, v_00_u03b2_2382_, v_cmp_2383_, v_00_u03b4_2384_, v_m_2385_, v_inst_2386_, v_f_2387_, v_init_2388_, v_t_2389_);
lean_dec_ref(v_cmp_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0(lean_object* v_f_2391_, lean_object* v_x_2392_, lean_object* v_k_2393_, lean_object* v_v_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_k_2393_);
lean_ctor_set(v___x_2395_, 1, v_v_2394_);
v___x_2396_ = lean_apply_1(v_f_2391_, v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1(lean_object* v_inst_2397_, lean_object* v_t_2398_, lean_object* v_f_2399_){
_start:
{
lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___f_2400_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2400_, 0, v_f_2399_);
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2397_, v___f_2400_, v___x_2401_, v_t_2398_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg(lean_object* v_inst_2403_){
_start:
{
lean_object* v___f_2404_; 
v___f_2404_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2404_, 0, v_inst_2403_);
return v___f_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad(lean_object* v_00_u03b1_2405_, lean_object* v_00_u03b2_2406_, lean_object* v_cmp_2407_, lean_object* v_m_2408_, lean_object* v_inst_2409_){
_start:
{
lean_object* v___f_2410_; 
v___f_2410_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForMSigmaOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_2410_, 0, v_inst_2409_);
return v___f_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForMSigmaOfMonad___boxed(lean_object* v_00_u03b1_2411_, lean_object* v_00_u03b2_2412_, lean_object* v_cmp_2413_, lean_object* v_m_2414_, lean_object* v_inst_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Std_DTreeMap_Raw_instForMSigmaOfMonad(v_00_u03b1_2411_, v_00_u03b2_2412_, v_cmp_2413_, v_m_2414_, v_inst_2415_);
lean_dec_ref(v_cmp_2413_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_2417_, lean_object* v_a_2418_, lean_object* v_b_2419_, lean_object* v_acc_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_a_2418_);
lean_ctor_set(v___x_2421_, 1, v_b_2419_);
v___x_2422_ = lean_apply_2(v_f_2417_, v___x_2421_, v_acc_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_2423_, lean_object* v_00_u03b2_2424_, lean_object* v_t_2425_, lean_object* v_init_2426_, lean_object* v_f_2427_){
_start:
{
lean_object* v_toApplicative_2428_; lean_object* v_toBind_2429_; lean_object* v_toPure_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v_toApplicative_2428_ = lean_ctor_get(v_inst_2423_, 0);
v_toBind_2429_ = lean_ctor_get(v_inst_2423_, 1);
lean_inc(v_toBind_2429_);
v_toPure_2430_ = lean_ctor_get(v_toApplicative_2428_, 1);
lean_inc(v_toPure_2430_);
v___f_2431_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2431_, 0, v_f_2427_);
v___x_2432_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2423_, v___f_2431_, v_init_2426_, v_t_2425_);
v___f_2433_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2433_, 0, v_toPure_2430_);
v___x_2434_ = lean_apply_4(v_toBind_2429_, lean_box(0), lean_box(0), v___x_2432_, v___f_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg(lean_object* v_inst_2435_){
_start:
{
lean_object* v___f_2436_; 
v___f_2436_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2436_, 0, v_inst_2435_);
return v___f_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad(lean_object* v_00_u03b1_2437_, lean_object* v_00_u03b2_2438_, lean_object* v_cmp_2439_, lean_object* v_m_2440_, lean_object* v_inst_2441_){
_start:
{
lean_object* v___f_2442_; 
v___f_2442_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2442_, 0, v_inst_2441_);
return v___f_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instForInSigmaOfMonad___boxed(lean_object* v_00_u03b1_2443_, lean_object* v_00_u03b2_2444_, lean_object* v_cmp_2445_, lean_object* v_m_2446_, lean_object* v_inst_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Std_DTreeMap_Raw_instForInSigmaOfMonad(v_00_u03b1_2443_, v_00_u03b2_2444_, v_cmp_2445_, v_m_2446_, v_inst_2447_);
lean_dec_ref(v_cmp_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2449_, lean_object* v_x_2450_, lean_object* v_k_2451_, lean_object* v_v_2452_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_k_2451_);
lean_ctor_set(v___x_2453_, 1, v_v_2452_);
v___x_2454_ = lean_apply_1(v_f_2449_, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_2455_, lean_object* v_f_2456_, lean_object* v_t_2457_){
_start:
{
lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___f_2458_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2458_, 0, v_f_2456_);
v___x_2459_ = lean_box(0);
v___x_2460_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2455_, v___f_2458_, v___x_2459_, v_t_2457_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_2461_, lean_object* v_cmp_2462_, lean_object* v_m_2463_, lean_object* v_inst_2464_, lean_object* v_00_u03b2_2465_, lean_object* v_f_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___f_2468_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2468_, 0, v_f_2466_);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_2464_, v___f_2468_, v___x_2469_, v_t_2467_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forMUncurried___boxed(lean_object* v_00_u03b1_2471_, lean_object* v_cmp_2472_, lean_object* v_m_2473_, lean_object* v_inst_2474_, lean_object* v_00_u03b2_2475_, lean_object* v_f_2476_, lean_object* v_t_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Std_DTreeMap_Raw_Const_forMUncurried(v_00_u03b1_2471_, v_cmp_2472_, v_m_2473_, v_inst_2474_, v_00_u03b2_2475_, v_f_2476_, v_t_2477_);
lean_dec_ref(v_cmp_2472_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2479_, lean_object* v_a_2480_, lean_object* v_b_2481_, lean_object* v_d_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2480_);
lean_ctor_set(v___x_2483_, 1, v_b_2481_);
v___x_2484_ = lean_apply_2(v_f_2479_, v___x_2483_, v_d_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_2485_, lean_object* v_f_2486_, lean_object* v_init_2487_, lean_object* v_t_2488_){
_start:
{
lean_object* v_toApplicative_2489_; lean_object* v_toBind_2490_; lean_object* v_toPure_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___x_2495_; 
v_toApplicative_2489_ = lean_ctor_get(v_inst_2485_, 0);
v_toBind_2490_ = lean_ctor_get(v_inst_2485_, 1);
lean_inc(v_toBind_2490_);
v_toPure_2491_ = lean_ctor_get(v_toApplicative_2489_, 1);
lean_inc(v_toPure_2491_);
v___f_2492_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2492_, 0, v_f_2486_);
v___x_2493_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2485_, v___f_2492_, v_init_2487_, v_t_2488_);
v___f_2494_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2494_, 0, v_toPure_2491_);
v___x_2495_ = lean_apply_4(v_toBind_2490_, lean_box(0), lean_box(0), v___x_2493_, v___f_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_2496_, lean_object* v_cmp_2497_, lean_object* v_00_u03b4_2498_, lean_object* v_m_2499_, lean_object* v_inst_2500_, lean_object* v_00_u03b2_2501_, lean_object* v_f_2502_, lean_object* v_init_2503_, lean_object* v_t_2504_){
_start:
{
lean_object* v_toApplicative_2505_; lean_object* v_toBind_2506_; lean_object* v_toPure_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; 
v_toApplicative_2505_ = lean_ctor_get(v_inst_2500_, 0);
v_toBind_2506_ = lean_ctor_get(v_inst_2500_, 1);
lean_inc(v_toBind_2506_);
v_toPure_2507_ = lean_ctor_get(v_toApplicative_2505_, 1);
lean_inc(v_toPure_2507_);
v___f_2508_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2508_, 0, v_f_2502_);
v___x_2509_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_2500_, v___f_2508_, v_init_2503_, v_t_2504_);
v___f_2510_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2510_, 0, v_toPure_2507_);
v___x_2511_ = lean_apply_4(v_toBind_2506_, lean_box(0), lean_box(0), v___x_2509_, v___f_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_forInUncurried___boxed(lean_object* v_00_u03b1_2512_, lean_object* v_cmp_2513_, lean_object* v_00_u03b4_2514_, lean_object* v_m_2515_, lean_object* v_inst_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_f_2518_, lean_object* v_init_2519_, lean_object* v_t_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Std_DTreeMap_Raw_Const_forInUncurried(v_00_u03b1_2512_, v_cmp_2513_, v_00_u03b4_2514_, v_m_2515_, v_inst_2516_, v_00_u03b2_2517_, v_f_2518_, v_init_2519_, v_t_2520_);
lean_dec_ref(v_cmp_2513_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0(lean_object* v_p_2522_, lean_object* v___x_2523_, lean_object* v___x_2524_, lean_object* v_a_2525_, lean_object* v_b_2526_, lean_object* v_acc_2527_){
_start:
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = lean_apply_2(v_p_2522_, v_a_2525_, v_b_2526_);
v___x_2529_ = lean_unbox(v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2523_);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec_ref(v___x_2523_);
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2528_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___x_2524_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_2534_, lean_object* v___x_2535_, lean_object* v___x_2536_, lean_object* v_a_2537_, lean_object* v_b_2538_, lean_object* v_acc_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Std_DTreeMap_Raw_any___redArg___lam__0(v_p_2534_, v___x_2535_, v___x_2536_, v_a_2537_, v_b_2538_, v_acc_2539_);
lean_dec_ref(v_acc_2539_);
return v_res_2540_;
}
}
uint8_t l_Std_DTreeMap_Raw_any___redArg(lean_object* v_t_2544_, lean_object* v_p_2545_){
_start:
{
lean_object* v___y_2547_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; lean_object* v_a_2557_; 
v___x_2552_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2553_ = lean_box(0);
v___x_2554_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2555_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2555_, 0, v_p_2545_);
lean_closure_set(v___f_2555_, 1, v___x_2554_);
lean_closure_set(v___f_2555_, 2, v___x_2553_);
v___x_2556_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2552_, v___f_2555_, v___x_2554_, v_t_2544_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___y_2547_ = v_a_2557_;
goto v___jp_2546_;
v___jp_2546_:
{
lean_object* v_fst_2548_; 
v_fst_2548_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_fst_2548_);
lean_dec_ref(v___y_2547_);
if (lean_obj_tag(v_fst_2548_) == 0)
{
uint8_t v___x_2549_; 
v___x_2549_ = 0;
return v___x_2549_;
}
else
{
lean_object* v_val_2550_; uint8_t v___x_2551_; 
v_val_2550_ = lean_ctor_get(v_fst_2548_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v_fst_2548_, 1);
v___x_2551_ = lean_unbox(v_val_2550_);
lean_dec(v_val_2550_);
return v___x_2551_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2544_ = stack[0].m_obj;
lean_object* v_p_2545_ = stack[1].m_obj;
uint8_t v_res_2558_;
v_res_2558_ = l_Std_DTreeMap_Raw_any___redArg(v_t_2544_, v_p_2545_);
stack->m_num = v_res_2558_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___redArg___boxed(lean_object* v_t_2559_, lean_object* v_p_2560_){
_start:
{
uint8_t v_res_2561_; lean_object* v_r_2562_; 
v_res_2561_ = l_Std_DTreeMap_Raw_any___redArg(v_t_2559_, v_p_2560_);
v_r_2562_ = lean_box(v_res_2561_);
return v_r_2562_;
}
}
uint8_t l_Std_DTreeMap_Raw_any(lean_object* v_00_u03b1_2563_, lean_object* v_00_u03b2_2564_, lean_object* v_cmp_2565_, lean_object* v_t_2566_, lean_object* v_p_2567_){
_start:
{
lean_object* v___y_2569_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v_a_2579_; 
v___x_2574_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2575_ = lean_box(0);
v___x_2576_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2577_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2577_, 0, v_p_2567_);
lean_closure_set(v___f_2577_, 1, v___x_2576_);
lean_closure_set(v___f_2577_, 2, v___x_2575_);
v___x_2578_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2574_, v___f_2577_, v___x_2576_, v_t_2566_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___y_2569_ = v_a_2579_;
goto v___jp_2568_;
v___jp_2568_:
{
lean_object* v_fst_2570_; 
v_fst_2570_ = lean_ctor_get(v___y_2569_, 0);
lean_inc(v_fst_2570_);
lean_dec_ref(v___y_2569_);
if (lean_obj_tag(v_fst_2570_) == 0)
{
uint8_t v___x_2571_; 
v___x_2571_ = 0;
return v___x_2571_;
}
else
{
lean_object* v_val_2572_; uint8_t v___x_2573_; 
v_val_2572_ = lean_ctor_get(v_fst_2570_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v_fst_2570_, 1);
v___x_2573_ = lean_unbox(v_val_2572_);
lean_dec(v_val_2572_);
return v___x_2573_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2565_ = stack[2].m_obj;
lean_object* v_t_2566_ = stack[3].m_obj;
lean_object* v_p_2567_ = stack[4].m_obj;
uint8_t v_res_2580_;
v_res_2580_ = l_Std_DTreeMap_Raw_any(lean_box(0), lean_box(0), v_cmp_2565_, v_t_2566_, v_p_2567_);
stack->m_num = v_res_2580_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_any___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_00_u03b2_2582_, lean_object* v_cmp_2583_, lean_object* v_t_2584_, lean_object* v_p_2585_){
_start:
{
uint8_t v_res_2586_; lean_object* v_r_2587_; 
v_res_2586_ = l_Std_DTreeMap_Raw_any(v_00_u03b1_2581_, v_00_u03b2_2582_, v_cmp_2583_, v_t_2584_, v_p_2585_);
lean_dec_ref(v_cmp_2583_);
v_r_2587_ = lean_box(v_res_2586_);
return v_r_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0(lean_object* v_p_2588_, lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v_a_2591_, lean_object* v_b_2592_, lean_object* v_acc_2593_){
_start:
{
lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = lean_apply_2(v_p_2588_, v_a_2591_, v_b_2592_);
v___x_2595_ = lean_unbox(v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec_ref(v___x_2590_);
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v___x_2589_);
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2590_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_2600_, lean_object* v___x_2601_, lean_object* v___x_2602_, lean_object* v_a_2603_, lean_object* v_b_2604_, lean_object* v_acc_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Std_DTreeMap_Raw_all___redArg___lam__0(v_p_2600_, v___x_2601_, v___x_2602_, v_a_2603_, v_b_2604_, v_acc_2605_);
lean_dec_ref(v_acc_2605_);
return v_res_2606_;
}
}
uint8_t l_Std_DTreeMap_Raw_all___redArg(lean_object* v_t_2607_, lean_object* v_p_2608_){
_start:
{
lean_object* v___y_2610_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v_a_2620_; 
v___x_2615_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2616_ = lean_box(0);
v___x_2617_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2618_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2618_, 0, v_p_2608_);
lean_closure_set(v___f_2618_, 1, v___x_2616_);
lean_closure_set(v___f_2618_, 2, v___x_2617_);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2615_, v___f_2618_, v___x_2617_, v_t_2607_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___y_2610_ = v_a_2620_;
goto v___jp_2609_;
v___jp_2609_:
{
lean_object* v_fst_2611_; 
v_fst_2611_ = lean_ctor_get(v___y_2610_, 0);
lean_inc(v_fst_2611_);
lean_dec_ref(v___y_2610_);
if (lean_obj_tag(v_fst_2611_) == 0)
{
uint8_t v___x_2612_; 
v___x_2612_ = 1;
return v___x_2612_;
}
else
{
lean_object* v_val_2613_; uint8_t v___x_2614_; 
v_val_2613_ = lean_ctor_get(v_fst_2611_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v_fst_2611_, 1);
v___x_2614_ = lean_unbox(v_val_2613_);
lean_dec(v_val_2613_);
return v___x_2614_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_2607_ = stack[0].m_obj;
lean_object* v_p_2608_ = stack[1].m_obj;
uint8_t v_res_2621_;
v_res_2621_ = l_Std_DTreeMap_Raw_all___redArg(v_t_2607_, v_p_2608_);
stack->m_num = v_res_2621_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___redArg___boxed(lean_object* v_t_2622_, lean_object* v_p_2623_){
_start:
{
uint8_t v_res_2624_; lean_object* v_r_2625_; 
v_res_2624_ = l_Std_DTreeMap_Raw_all___redArg(v_t_2622_, v_p_2623_);
v_r_2625_ = lean_box(v_res_2624_);
return v_r_2625_;
}
}
uint8_t l_Std_DTreeMap_Raw_all(lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_cmp_2628_, lean_object* v_t_2629_, lean_object* v_p_2630_){
_start:
{
lean_object* v___y_2632_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___f_2640_; lean_object* v___x_2641_; lean_object* v_a_2642_; 
v___x_2637_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2638_ = lean_box(0);
v___x_2639_ = ((lean_object*)(l_Std_DTreeMap_Raw_any___redArg___closed__0));
v___f_2640_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2640_, 0, v_p_2630_);
lean_closure_set(v___f_2640_, 1, v___x_2638_);
lean_closure_set(v___f_2640_, 2, v___x_2639_);
v___x_2641_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_2637_, v___f_2640_, v___x_2639_, v_t_2629_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___y_2632_ = v_a_2642_;
goto v___jp_2631_;
v___jp_2631_:
{
lean_object* v_fst_2633_; 
v_fst_2633_ = lean_ctor_get(v___y_2632_, 0);
lean_inc(v_fst_2633_);
lean_dec_ref(v___y_2632_);
if (lean_obj_tag(v_fst_2633_) == 0)
{
uint8_t v___x_2634_; 
v___x_2634_ = 1;
return v___x_2634_;
}
else
{
lean_object* v_val_2635_; uint8_t v___x_2636_; 
v_val_2635_ = lean_ctor_get(v_fst_2633_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v_fst_2633_, 1);
v___x_2636_ = lean_unbox(v_val_2635_);
lean_dec(v_val_2635_);
return v___x_2636_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2628_ = stack[2].m_obj;
lean_object* v_t_2629_ = stack[3].m_obj;
lean_object* v_p_2630_ = stack[4].m_obj;
uint8_t v_res_2643_;
v_res_2643_ = l_Std_DTreeMap_Raw_all(lean_box(0), lean_box(0), v_cmp_2628_, v_t_2629_, v_p_2630_);
stack->m_num = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_all___boxed(lean_object* v_00_u03b1_2644_, lean_object* v_00_u03b2_2645_, lean_object* v_cmp_2646_, lean_object* v_t_2647_, lean_object* v_p_2648_){
_start:
{
uint8_t v_res_2649_; lean_object* v_r_2650_; 
v_res_2649_ = l_Std_DTreeMap_Raw_all(v_00_u03b1_2644_, v_00_u03b2_2645_, v_cmp_2646_, v_t_2647_, v_p_2648_);
lean_dec_ref(v_cmp_2646_);
v_r_2650_ = lean_box(v_res_2649_);
return v_r_2650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0(lean_object* v_x1_2651_, lean_object* v_x2_2652_, lean_object* v_x3_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2654_, 0, v_x1_2651_);
lean_ctor_set(v___x_2654_, 1, v_x3_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_2655_, lean_object* v_x2_2656_, lean_object* v_x3_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_DTreeMap_Raw_keys___redArg___lam__0(v_x1_2655_, v_x2_2656_, v_x3_2657_);
lean_dec(v_x2_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___redArg(lean_object* v_t_2660_){
_start:
{
lean_object* v___f_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___f_2661_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2662_ = lean_box(0);
v___x_2663_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2664_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2663_, v___f_2661_, v___x_2662_, v_t_2660_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys(lean_object* v_00_u03b1_2665_, lean_object* v_00_u03b2_2666_, lean_object* v_cmp_2667_, lean_object* v_t_2668_){
_start:
{
lean_object* v___f_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___f_2669_ = ((lean_object*)(l_Std_DTreeMap_Raw_keys___redArg___closed__0));
v___x_2670_ = lean_box(0);
v___x_2671_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2672_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2671_, v___f_2669_, v___x_2670_, v_t_2668_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keys___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_00_u03b2_2674_, lean_object* v_cmp_2675_, lean_object* v_t_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Std_DTreeMap_Raw_keys(v_00_u03b1_2673_, v_00_u03b2_2674_, v_cmp_2675_, v_t_2676_);
lean_dec_ref(v_cmp_2675_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(lean_object* v_l_2678_, lean_object* v_k_2679_, lean_object* v_x_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_array_push(v_l_2678_, v_k_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_l_2682_, lean_object* v_k_2683_, lean_object* v_x_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Std_DTreeMap_Raw_keysArray___redArg___lam__0(v_l_2682_, v_k_2683_, v_x_2684_);
lean_dec(v_x_2684_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___redArg(lean_object* v_t_2687_){
_start:
{
lean_object* v___f_2688_; lean_object* v___y_2690_; 
v___f_2688_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2687_) == 0)
{
lean_object* v_size_2693_; 
v_size_2693_ = lean_ctor_get(v_t_2687_, 0);
lean_inc(v_size_2693_);
v___y_2690_ = v_size_2693_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_unsigned_to_nat(0u);
v___y_2690_ = v___x_2694_;
goto v___jp_2689_;
}
v___jp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = lean_mk_empty_array_with_capacity(v___y_2690_);
lean_dec(v___y_2690_);
v___x_2692_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2688_, v___x_2691_, v_t_2687_);
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray(lean_object* v_00_u03b1_2695_, lean_object* v_00_u03b2_2696_, lean_object* v_cmp_2697_, lean_object* v_t_2698_){
_start:
{
lean_object* v___f_2699_; lean_object* v___y_2701_; 
v___f_2699_ = ((lean_object*)(l_Std_DTreeMap_Raw_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_2698_) == 0)
{
lean_object* v_size_2704_; 
v_size_2704_ = lean_ctor_get(v_t_2698_, 0);
lean_inc(v_size_2704_);
v___y_2701_ = v_size_2704_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_unsigned_to_nat(0u);
v___y_2701_ = v___x_2705_;
goto v___jp_2700_;
}
v___jp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_mk_empty_array_with_capacity(v___y_2701_);
lean_dec(v___y_2701_);
v___x_2703_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2699_, v___x_2702_, v_t_2698_);
return v___x_2703_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_keysArray___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_00_u03b2_2707_, lean_object* v_cmp_2708_, lean_object* v_t_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Std_DTreeMap_Raw_keysArray(v_00_u03b1_2706_, v_00_u03b2_2707_, v_cmp_2708_, v_t_2709_);
lean_dec_ref(v_cmp_2708_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0(lean_object* v_x1_2711_, lean_object* v_x2_2712_, lean_object* v_x3_2713_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_x2_2712_);
lean_ctor_set(v___x_2714_, 1, v_x3_2713_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2715_, lean_object* v_x2_2716_, lean_object* v_x3_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Std_DTreeMap_Raw_values___redArg___lam__0(v_x1_2715_, v_x2_2716_, v_x3_2717_);
lean_dec(v_x1_2715_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___redArg(lean_object* v_t_2720_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___f_2721_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2722_ = lean_box(0);
v___x_2723_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2724_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2723_, v___f_2721_, v___x_2722_, v_t_2720_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values(lean_object* v_00_u03b1_2725_, lean_object* v_cmp_2726_, lean_object* v_00_u03b2_2727_, lean_object* v_t_2728_){
_start:
{
lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___f_2729_ = ((lean_object*)(l_Std_DTreeMap_Raw_values___redArg___closed__0));
v___x_2730_ = lean_box(0);
v___x_2731_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2732_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2731_, v___f_2729_, v___x_2730_, v_t_2728_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_values___boxed(lean_object* v_00_u03b1_2733_, lean_object* v_cmp_2734_, lean_object* v_00_u03b2_2735_, lean_object* v_t_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Std_DTreeMap_Raw_values(v_00_u03b1_2733_, v_cmp_2734_, v_00_u03b2_2735_, v_t_2736_);
lean_dec_ref(v_cmp_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(lean_object* v_l_2738_, lean_object* v_x_2739_, lean_object* v_v_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_array_push(v_l_2738_, v_v_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_l_2742_, lean_object* v_x_2743_, lean_object* v_v_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Std_DTreeMap_Raw_valuesArray___redArg___lam__0(v_l_2742_, v_x_2743_, v_v_2744_);
lean_dec(v_x_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___redArg(lean_object* v_t_2747_){
_start:
{
lean_object* v___f_2748_; lean_object* v___y_2750_; 
v___f_2748_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2747_) == 0)
{
lean_object* v_size_2753_; 
v_size_2753_ = lean_ctor_get(v_t_2747_, 0);
lean_inc(v_size_2753_);
v___y_2750_ = v_size_2753_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_unsigned_to_nat(0u);
v___y_2750_ = v___x_2754_;
goto v___jp_2749_;
}
v___jp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_mk_empty_array_with_capacity(v___y_2750_);
lean_dec(v___y_2750_);
v___x_2752_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2748_, v___x_2751_, v_t_2747_);
return v___x_2752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray(lean_object* v_00_u03b1_2755_, lean_object* v_cmp_2756_, lean_object* v_00_u03b2_2757_, lean_object* v_t_2758_){
_start:
{
lean_object* v___f_2759_; lean_object* v___y_2761_; 
v___f_2759_ = ((lean_object*)(l_Std_DTreeMap_Raw_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_2758_) == 0)
{
lean_object* v_size_2764_; 
v_size_2764_ = lean_ctor_get(v_t_2758_, 0);
lean_inc(v_size_2764_);
v___y_2761_ = v_size_2764_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_unsigned_to_nat(0u);
v___y_2761_ = v___x_2765_;
goto v___jp_2760_;
}
v___jp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_mk_empty_array_with_capacity(v___y_2761_);
lean_dec(v___y_2761_);
v___x_2763_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2759_, v___x_2762_, v_t_2758_);
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_valuesArray___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_cmp_2767_, lean_object* v_00_u03b2_2768_, lean_object* v_t_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Std_DTreeMap_Raw_valuesArray(v_00_u03b1_2766_, v_cmp_2767_, v_00_u03b2_2768_, v_t_2769_);
lean_dec_ref(v_cmp_2767_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg___lam__0(lean_object* v_x1_2771_, lean_object* v_x2_2772_, lean_object* v_x3_2773_){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v_x1_2771_);
lean_ctor_set(v___x_2774_, 1, v_x2_2772_);
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_x3_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___redArg(lean_object* v_t_2777_){
_start:
{
lean_object* v___f_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___f_2778_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2779_ = lean_box(0);
v___x_2780_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2781_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2780_, v___f_2778_, v___x_2779_, v_t_2777_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList(lean_object* v_00_u03b1_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_cmp_2784_, lean_object* v_t_2785_){
_start:
{
lean_object* v___f_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___f_2786_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_2787_ = lean_box(0);
v___x_2788_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2789_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2788_, v___f_2786_, v___x_2787_, v_t_2785_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toList___boxed(lean_object* v_00_u03b1_2790_, lean_object* v_00_u03b2_2791_, lean_object* v_cmp_2792_, lean_object* v_t_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Std_DTreeMap_Raw_toList(v_00_u03b1_2790_, v_00_u03b2_2791_, v_cmp_2792_, v_t_2793_);
lean_dec_ref(v_cmp_2792_);
return v_res_2794_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofList___auto__1(void){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___lam__0(lean_object* v_cmp_2796_, lean_object* v_a_2797_, lean_object* v_x_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_fst_2800_; lean_object* v_snd_2801_; lean_object* v_r_2802_; lean_object* v___x_2803_; 
v_fst_2800_ = lean_ctor_get(v_a_2797_, 0);
lean_inc(v_fst_2800_);
v_snd_2801_ = lean_ctor_get(v_a_2797_, 1);
lean_inc(v_snd_2801_);
lean_dec_ref(v_a_2797_);
v_r_2802_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2796_, v_fst_2800_, v_snd_2801_, v___y_2799_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_r_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg(lean_object* v_l_2804_, lean_object* v_cmp_2805_){
_start:
{
lean_object* v___f_2806_; lean_object* v___x_2807_; lean_object* v_r_2808_; lean_object* v___x_2809_; 
v___f_2806_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2806_, 0, v_cmp_2805_);
v___x_2807_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2808_ = lean_box(1);
v___x_2809_ = l_List_forIn_x27_loop___redArg(v___x_2807_, v___f_2806_, v_l_2804_, v_r_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___redArg___boxed(lean_object* v_l_2810_, lean_object* v_cmp_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_DTreeMap_Raw_ofList___redArg(v_l_2810_, v_cmp_2811_);
lean_dec(v_l_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList(lean_object* v_00_u03b1_2813_, lean_object* v_00_u03b2_2814_, lean_object* v_l_2815_, lean_object* v_cmp_2816_){
_start:
{
lean_object* v___f_2817_; lean_object* v___x_2818_; lean_object* v_r_2819_; lean_object* v___x_2820_; 
v___f_2817_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2817_, 0, v_cmp_2816_);
v___x_2818_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2819_ = lean_box(1);
v___x_2820_ = l_List_forIn_x27_loop___redArg(v___x_2818_, v___f_2817_, v_l_2815_, v_r_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofList___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_00_u03b2_2822_, lean_object* v_l_2823_, lean_object* v_cmp_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Std_DTreeMap_Raw_ofList(v_00_u03b1_2821_, v_00_u03b2_2822_, v_l_2823_, v_cmp_2824_);
lean_dec(v_l_2823_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg___lam__0(lean_object* v_l_2826_, lean_object* v_k_2827_, lean_object* v_v_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_k_2827_);
lean_ctor_set(v___x_2829_, 1, v_v_2828_);
v___x_2830_ = lean_array_push(v_l_2826_, v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___redArg(lean_object* v_t_2832_){
_start:
{
lean_object* v___f_2833_; lean_object* v___y_2835_; 
v___f_2833_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2832_) == 0)
{
lean_object* v_size_2838_; 
v_size_2838_ = lean_ctor_get(v_t_2832_, 0);
lean_inc(v_size_2838_);
v___y_2835_ = v_size_2838_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_unsigned_to_nat(0u);
v___y_2835_ = v___x_2839_;
goto v___jp_2834_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_mk_empty_array_with_capacity(v___y_2835_);
lean_dec(v___y_2835_);
v___x_2837_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2833_, v___x_2836_, v_t_2832_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray(lean_object* v_00_u03b1_2840_, lean_object* v_00_u03b2_2841_, lean_object* v_cmp_2842_, lean_object* v_t_2843_){
_start:
{
lean_object* v___f_2844_; lean_object* v___y_2846_; 
v___f_2844_ = ((lean_object*)(l_Std_DTreeMap_Raw_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_2843_) == 0)
{
lean_object* v_size_2849_; 
v_size_2849_ = lean_ctor_get(v_t_2843_, 0);
lean_inc(v_size_2849_);
v___y_2846_ = v_size_2849_;
goto v___jp_2845_;
}
else
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_unsigned_to_nat(0u);
v___y_2846_ = v___x_2850_;
goto v___jp_2845_;
}
v___jp_2845_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_mk_empty_array_with_capacity(v___y_2846_);
lean_dec(v___y_2846_);
v___x_2848_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2844_, v___x_2847_, v_t_2843_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_toArray___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_00_u03b2_2852_, lean_object* v_cmp_2853_, lean_object* v_t_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Std_DTreeMap_Raw_toArray(v_00_u03b1_2851_, v_00_u03b2_2852_, v_cmp_2853_, v_t_2854_);
lean_dec_ref(v_cmp_2853_);
return v_res_2855_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_ofArray___auto__1(void){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray___redArg(lean_object* v_a_2857_, lean_object* v_cmp_2858_){
_start:
{
lean_object* v___f_2859_; lean_object* v___x_2860_; lean_object* v_r_2861_; size_t v_sz_2862_; size_t v___x_2863_; lean_object* v___x_2864_; 
v___f_2859_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2859_, 0, v_cmp_2858_);
v___x_2860_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2861_ = lean_box(1);
v_sz_2862_ = lean_array_size(v_a_2857_);
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2860_, v_a_2857_, v___f_2859_, v_sz_2862_, v___x_2863_, v_r_2861_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_ofArray(lean_object* v_00_u03b1_2865_, lean_object* v_00_u03b2_2866_, lean_object* v_a_2867_, lean_object* v_cmp_2868_){
_start:
{
lean_object* v___f_2869_; lean_object* v___x_2870_; lean_object* v_r_2871_; size_t v_sz_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v___f_2869_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2869_, 0, v_cmp_2868_);
v___x_2870_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2871_ = lean_box(1);
v_sz_2872_ = lean_array_size(v_a_2867_);
v___x_2873_ = ((size_t)0ULL);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2870_, v_a_2867_, v___f_2869_, v_sz_2872_, v___x_2873_, v_r_2871_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify___redArg(lean_object* v_cmp_2875_, lean_object* v_t_2876_, lean_object* v_a_2877_, lean_object* v_f_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2875_, v_a_2877_, v_f_2878_, v_t_2876_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_modify(lean_object* v_00_u03b1_2880_, lean_object* v_00_u03b2_2881_, lean_object* v_cmp_2882_, lean_object* v_inst_2883_, lean_object* v_t_2884_, lean_object* v_a_2885_, lean_object* v_f_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Std_DTreeMap_Internal_Impl_modify___redArg(v_cmp_2882_, v_a_2885_, v_f_2886_, v_t_2884_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter___redArg(lean_object* v_cmp_2888_, lean_object* v_t_2889_, lean_object* v_a_2890_, lean_object* v_f_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2888_, v_a_2890_, v_f_2891_, v_t_2889_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_alter(lean_object* v_00_u03b1_2893_, lean_object* v_00_u03b2_2894_, lean_object* v_cmp_2895_, lean_object* v_inst_2896_, lean_object* v_t_2897_, lean_object* v_a_2898_, lean_object* v_f_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2895_, v_a_2898_, v_f_2899_, v_t_2897_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0(lean_object* v_b_u2082_2901_, lean_object* v_mergeFn_2902_, lean_object* v_a_2903_, lean_object* v_x_2904_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_a_2903_);
lean_dec(v_mergeFn_2902_);
v___x_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_b_u2082_2901_);
return v___x_2905_;
}
else
{
lean_object* v_val_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2914_; 
v_val_2906_ = lean_ctor_get(v_x_2904_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_x_2904_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2908_ = v_x_2904_;
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_val_2906_);
lean_dec(v_x_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2914_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = lean_apply_3(v_mergeFn_2902_, v_a_2903_, v_val_2906_, v_b_u2082_2901_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1(lean_object* v_mergeFn_2915_, lean_object* v_cmp_2916_, lean_object* v_t_2917_, lean_object* v_a_2918_, lean_object* v_b_u2082_2919_){
_start:
{
lean_object* v___f_2920_; lean_object* v___x_2921_; 
lean_inc(v_a_2918_);
v___f_2920_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2920_, 0, v_b_u2082_2919_);
lean_closure_set(v___f_2920_, 1, v_mergeFn_2915_);
lean_closure_set(v___f_2920_, 2, v_a_2918_);
v___x_2921_ = l_Std_DTreeMap_Internal_Impl_alter_x21___redArg(v_cmp_2916_, v_a_2918_, v___f_2920_, v_t_2917_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith___redArg(lean_object* v_cmp_2922_, lean_object* v_mergeFn_2923_, lean_object* v_t_u2081_2924_, lean_object* v_t_u2082_2925_){
_start:
{
lean_object* v___f_2926_; lean_object* v___x_2927_; 
v___f_2926_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2926_, 0, v_mergeFn_2923_);
lean_closure_set(v___f_2926_, 1, v_cmp_2922_);
v___x_2927_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2926_, v_t_u2081_2924_, v_t_u2082_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_mergeWith(lean_object* v_00_u03b1_2928_, lean_object* v_00_u03b2_2929_, lean_object* v_cmp_2930_, lean_object* v_inst_2931_, lean_object* v_mergeFn_2932_, lean_object* v_t_u2081_2933_, lean_object* v_t_u2082_2934_){
_start:
{
lean_object* v___f_2935_; lean_object* v___x_2936_; 
v___f_2935_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_2935_, 0, v_mergeFn_2932_);
lean_closure_set(v___f_2935_, 1, v_cmp_2930_);
v___x_2936_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_2935_, v_t_u2081_2933_, v_t_u2082_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_2937_, lean_object* v_x2_2938_, lean_object* v_x3_2939_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_x1_2937_);
lean_ctor_set(v___x_2940_, 1, v_x2_2938_);
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_x3_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___redArg(lean_object* v_t_2943_){
_start:
{
lean_object* v___f_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___f_2944_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2945_ = lean_box(0);
v___x_2946_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2947_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2946_, v___f_2944_, v___x_2945_, v_t_2943_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList(lean_object* v_00_u03b1_2948_, lean_object* v_cmp_2949_, lean_object* v_00_u03b2_2950_, lean_object* v_t_2951_){
_start:
{
lean_object* v___f_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___f_2952_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toList___redArg___closed__0));
v___x_2953_ = lean_box(0);
v___x_2954_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_2955_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_2954_, v___f_2952_, v___x_2953_, v_t_2951_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_cmp_2957_, lean_object* v_00_u03b2_2958_, lean_object* v_t_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Std_DTreeMap_Raw_Const_toList(v_00_u03b1_2956_, v_cmp_2957_, v_00_u03b2_2958_, v_t_2959_);
lean_dec_ref(v_cmp_2957_);
return v_res_2960_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofList___auto__1(void){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0(lean_object* v_cmp_2962_, lean_object* v_a_2963_, lean_object* v_x_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_fst_2966_; lean_object* v_snd_2967_; lean_object* v_r_2968_; lean_object* v___x_2969_; 
v_fst_2966_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_fst_2966_);
v_snd_2967_ = lean_ctor_get(v_a_2963_, 1);
lean_inc(v_snd_2967_);
lean_dec_ref(v_a_2963_);
v_r_2968_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2962_, v_fst_2966_, v_snd_2967_, v___y_2965_);
v___x_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_r_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg(lean_object* v_l_2970_, lean_object* v_cmp_2971_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v_r_2974_; lean_object* v___x_2975_; 
v___f_2972_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2972_, 0, v_cmp_2971_);
v___x_2973_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2974_ = lean_box(1);
v___x_2975_ = l_List_forIn_x27_loop___redArg(v___x_2973_, v___f_2972_, v_l_2970_, v_r_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___redArg___boxed(lean_object* v_l_2976_, lean_object* v_cmp_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Std_DTreeMap_Raw_Const_ofList___redArg(v_l_2976_, v_cmp_2977_);
lean_dec(v_l_2976_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList(lean_object* v_00_u03b1_2979_, lean_object* v_00_u03b2_2980_, lean_object* v_l_2981_, lean_object* v_cmp_2982_){
_start:
{
lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v_r_2985_; lean_object* v___x_2986_; 
v___f_2983_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2983_, 0, v_cmp_2982_);
v___x_2984_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_2985_ = lean_box(1);
v___x_2986_ = l_List_forIn_x27_loop___redArg(v___x_2984_, v___f_2983_, v_l_2981_, v_r_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofList___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_00_u03b2_2988_, lean_object* v_l_2989_, lean_object* v_cmp_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Std_DTreeMap_Raw_Const_ofList(v_00_u03b1_2987_, v_00_u03b2_2988_, v_l_2989_, v_cmp_2990_);
lean_dec(v_l_2989_);
return v_res_2991_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfList___auto__1(void){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0(lean_object* v_cmp_2993_, lean_object* v_a_2994_, lean_object* v_x_2995_, lean_object* v___y_2996_){
_start:
{
uint8_t v___x_2997_; 
lean_inc(v___y_2996_);
lean_inc(v_a_2994_);
lean_inc_ref(v_cmp_2993_);
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_2993_, v_a_2994_, v___y_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2998_ = lean_box(0);
v___x_2999_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_2993_, v_a_2994_, v___x_2998_, v___y_2996_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; 
lean_dec(v_a_2994_);
lean_dec_ref(v_cmp_2993_);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___y_2996_);
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg(lean_object* v_l_3002_, lean_object* v_cmp_3003_){
_start:
{
lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v_r_3006_; lean_object* v___x_3007_; 
v___f_3004_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3004_, 0, v_cmp_3003_);
v___x_3005_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3006_ = lean_box(1);
v___x_3007_ = l_List_forIn_x27_loop___redArg(v___x_3005_, v___f_3004_, v_l_3002_, v_r_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___redArg___boxed(lean_object* v_l_3008_, lean_object* v_cmp_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Std_DTreeMap_Raw_Const_unitOfList___redArg(v_l_3008_, v_cmp_3009_);
lean_dec(v_l_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_3011_, lean_object* v_l_3012_, lean_object* v_cmp_3013_){
_start:
{
lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v_r_3016_; lean_object* v___x_3017_; 
v___f_3014_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3014_, 0, v_cmp_3013_);
v___x_3015_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3016_ = lean_box(1);
v___x_3017_ = l_List_forIn_x27_loop___redArg(v___x_3015_, v___f_3014_, v_l_3012_, v_r_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfList___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_l_3019_, lean_object* v_cmp_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Std_DTreeMap_Raw_Const_unitOfList(v_00_u03b1_3018_, v_l_3019_, v_cmp_3020_);
lean_dec(v_l_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_l_3022_, lean_object* v_k_3023_, lean_object* v_v_3024_){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_k_3023_);
lean_ctor_set(v___x_3025_, 1, v_v_3024_);
v___x_3026_ = lean_array_push(v_l_3022_, v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___redArg(lean_object* v_t_3028_){
_start:
{
lean_object* v___f_3029_; lean_object* v___y_3031_; 
v___f_3029_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3028_) == 0)
{
lean_object* v_size_3034_; 
v_size_3034_ = lean_ctor_get(v_t_3028_, 0);
lean_inc(v_size_3034_);
v___y_3031_ = v_size_3034_;
goto v___jp_3030_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_unsigned_to_nat(0u);
v___y_3031_ = v___x_3035_;
goto v___jp_3030_;
}
v___jp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_mk_empty_array_with_capacity(v___y_3031_);
lean_dec(v___y_3031_);
v___x_3033_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3029_, v___x_3032_, v_t_3028_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray(lean_object* v_00_u03b1_3036_, lean_object* v_cmp_3037_, lean_object* v_00_u03b2_3038_, lean_object* v_t_3039_){
_start:
{
lean_object* v___f_3040_; lean_object* v___y_3042_; 
v___f_3040_ = ((lean_object*)(l_Std_DTreeMap_Raw_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_3039_) == 0)
{
lean_object* v_size_3045_; 
v_size_3045_ = lean_ctor_get(v_t_3039_, 0);
lean_inc(v_size_3045_);
v___y_3042_ = v_size_3045_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_unsigned_to_nat(0u);
v___y_3042_ = v___x_3046_;
goto v___jp_3041_;
}
v___jp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_mk_empty_array_with_capacity(v___y_3042_);
lean_dec(v___y_3042_);
v___x_3044_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3040_, v___x_3043_, v_t_3039_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_toArray___boxed(lean_object* v_00_u03b1_3047_, lean_object* v_cmp_3048_, lean_object* v_00_u03b2_3049_, lean_object* v_t_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Std_DTreeMap_Raw_Const_toArray(v_00_u03b1_3047_, v_cmp_3048_, v_00_u03b2_3049_, v_t_3050_);
lean_dec_ref(v_cmp_3048_);
return v_res_3051_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_ofArray___auto__1(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray___redArg(lean_object* v_a_3053_, lean_object* v_cmp_3054_){
_start:
{
lean_object* v___f_3055_; lean_object* v___x_3056_; lean_object* v_r_3057_; size_t v_sz_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v___f_3055_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3055_, 0, v_cmp_3054_);
v___x_3056_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3057_ = lean_box(1);
v_sz_3058_ = lean_array_size(v_a_3053_);
v___x_3059_ = ((size_t)0ULL);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3056_, v_a_3053_, v___f_3055_, v_sz_3058_, v___x_3059_, v_r_3057_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_ofArray(lean_object* v_00_u03b1_3061_, lean_object* v_00_u03b2_3062_, lean_object* v_a_3063_, lean_object* v_cmp_3064_){
_start:
{
lean_object* v___f_3065_; lean_object* v___x_3066_; lean_object* v_r_3067_; size_t v_sz_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___f_3065_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_ofList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3065_, 0, v_cmp_3064_);
v___x_3066_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3067_ = lean_box(1);
v_sz_3068_ = lean_array_size(v_a_3063_);
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3066_, v_a_3063_, v___f_3065_, v_sz_3068_, v___x_3069_, v_r_3067_);
return v___x_3070_;
}
}
static lean_object* _init_l_Std_DTreeMap_Raw_Const_unitOfArray___auto__1(void){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_obj_once(&l_Std_DTreeMap_Raw___auto__1___closed__25, &l_Std_DTreeMap_Raw___auto__1___closed__25_once, _init_l_Std_DTreeMap_Raw___auto__1___closed__25);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray___redArg(lean_object* v_a_3072_, lean_object* v_cmp_3073_){
_start:
{
lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v_r_3076_; size_t v_sz_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___f_3074_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3074_, 0, v_cmp_3073_);
v___x_3075_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3076_ = lean_box(1);
v_sz_3077_ = lean_array_size(v_a_3072_);
v___x_3078_ = ((size_t)0ULL);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3075_, v_a_3072_, v___f_3074_, v_sz_3077_, v___x_3078_, v_r_3076_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_3080_, lean_object* v_a_3081_, lean_object* v_cmp_3082_){
_start:
{
lean_object* v___f_3083_; lean_object* v___x_3084_; lean_object* v_r_3085_; size_t v_sz_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v___f_3083_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_unitOfList___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3083_, 0, v_cmp_3082_);
v___x_3084_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v_r_3085_ = lean_box(1);
v_sz_3086_ = lean_array_size(v_a_3081_);
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3084_, v_a_3081_, v___f_3083_, v_sz_3086_, v___x_3087_, v_r_3085_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify___redArg(lean_object* v_cmp_3089_, lean_object* v_t_3090_, lean_object* v_a_3091_, lean_object* v_f_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3089_, v_a_3091_, v_f_3092_, v_t_3090_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_modify(lean_object* v_00_u03b1_3094_, lean_object* v_cmp_3095_, lean_object* v_00_u03b2_3096_, lean_object* v_t_3097_, lean_object* v_a_3098_, lean_object* v_f_3099_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v_cmp_3095_, v_a_3098_, v_f_3099_, v_t_3097_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter___redArg(lean_object* v_cmp_3101_, lean_object* v_t_3102_, lean_object* v_a_3103_, lean_object* v_f_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3101_, v_a_3103_, v_f_3104_, v_t_3102_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_alter(lean_object* v_00_u03b1_3106_, lean_object* v_cmp_3107_, lean_object* v_00_u03b2_3108_, lean_object* v_t_3109_, lean_object* v_a_3110_, lean_object* v_f_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3107_, v_a_3110_, v_f_3111_, v_t_3109_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1(lean_object* v_mergeFn_3113_, lean_object* v_cmp_3114_, lean_object* v_t_3115_, lean_object* v_a_3116_, lean_object* v_b_u2082_3117_){
_start:
{
lean_object* v___f_3118_; lean_object* v___x_3119_; 
lean_inc(v_a_3116_);
v___f_3118_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_mergeWith___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3118_, 0, v_b_u2082_3117_);
lean_closure_set(v___f_3118_, 1, v_mergeFn_3113_);
lean_closure_set(v___f_3118_, 2, v_a_3116_);
v___x_3119_ = l_Std_DTreeMap_Internal_Impl_Const_alter_x21___redArg(v_cmp_3114_, v_a_3116_, v___f_3118_, v_t_3115_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith___redArg(lean_object* v_cmp_3120_, lean_object* v_mergeFn_3121_, lean_object* v_t_u2081_3122_, lean_object* v_t_u2082_3123_){
_start:
{
lean_object* v___f_3124_; lean_object* v___x_3125_; 
v___f_3124_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3124_, 0, v_mergeFn_3121_);
lean_closure_set(v___f_3124_, 1, v_cmp_3120_);
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3124_, v_t_u2081_3122_, v_t_u2082_3123_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_mergeWith(lean_object* v_00_u03b1_3126_, lean_object* v_cmp_3127_, lean_object* v_00_u03b2_3128_, lean_object* v_mergeFn_3129_, lean_object* v_t_u2081_3130_, lean_object* v_t_u2082_3131_){
_start:
{
lean_object* v___f_3132_; lean_object* v___x_3133_; 
v___f_3132_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_mergeWith___redArg___lam__1), 5, 2);
lean_closure_set(v___f_3132_, 0, v_mergeFn_3129_);
lean_closure_set(v___f_3132_, 1, v_cmp_3127_);
v___x_3133_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3132_, v_t_u2081_3130_, v_t_u2082_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg___lam__0(lean_object* v_cmp_3134_, lean_object* v_x_3135_, lean_object* v_____s_3136_){
_start:
{
lean_object* v_fst_3137_; lean_object* v_snd_3138_; lean_object* v_r_3139_; lean_object* v___x_3140_; 
v_fst_3137_ = lean_ctor_get(v_x_3135_, 0);
lean_inc(v_fst_3137_);
v_snd_3138_ = lean_ctor_get(v_x_3135_, 1);
lean_inc(v_snd_3138_);
lean_dec_ref(v_x_3135_);
v_r_3139_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_3134_, v_fst_3137_, v_snd_3138_, v_____s_3136_);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_r_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany___redArg(lean_object* v_cmp_3141_, lean_object* v_inst_3142_, lean_object* v_t_3143_, lean_object* v_l_3144_){
_start:
{
lean_object* v___f_3145_; lean_object* v___x_3146_; 
v___f_3145_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3145_, 0, v_cmp_3141_);
v___x_3146_ = lean_apply_4(v_inst_3142_, lean_box(0), v_l_3144_, v_t_3143_, v___f_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_insertMany(lean_object* v_00_u03b1_3147_, lean_object* v_00_u03b2_3148_, lean_object* v_cmp_3149_, lean_object* v_00_u03c1_3150_, lean_object* v_inst_3151_, lean_object* v_t_3152_, lean_object* v_l_3153_){
_start:
{
lean_object* v___f_3154_; lean_object* v___x_3155_; 
v___f_3154_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3154_, 0, v_cmp_3149_);
v___x_3155_ = lean_apply_4(v_inst_3151_, lean_box(0), v_l_3153_, v_t_3152_, v___f_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3156_){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_box(1);
v___x_3158_ = lean_panic_fn_borrowed(v___x_3157_, v_msg_3156_);
return v___x_3158_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3162_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2));
v___x_3163_ = lean_unsigned_to_nat(35u);
v___x_3164_ = lean_unsigned_to_nat(182u);
v___x_3165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1));
v___x_3166_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3167_ = l_mkPanicMessageWithDecl(v___x_3166_, v___x_3165_, v___x_3164_, v___x_3163_, v___x_3162_);
return v___x_3167_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3168_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__2));
v___x_3169_ = lean_unsigned_to_nat(21u);
v___x_3170_ = lean_unsigned_to_nat(183u);
v___x_3171_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__1));
v___x_3172_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3173_ = l_mkPanicMessageWithDecl(v___x_3172_, v___x_3171_, v___x_3170_, v___x_3169_, v___x_3168_);
return v___x_3173_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3176_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6));
v___x_3177_ = lean_unsigned_to_nat(35u);
v___x_3178_ = lean_unsigned_to_nat(276u);
v___x_3179_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5));
v___x_3180_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3181_ = l_mkPanicMessageWithDecl(v___x_3180_, v___x_3179_, v___x_3178_, v___x_3177_, v___x_3176_);
return v___x_3181_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__6));
v___x_3183_ = lean_unsigned_to_nat(21u);
v___x_3184_ = lean_unsigned_to_nat(277u);
v___x_3185_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__5));
v___x_3186_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__0));
v___x_3187_ = l_mkPanicMessageWithDecl(v___x_3186_, v___x_3185_, v___x_3184_, v___x_3183_, v___x_3182_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(lean_object* v_cmp_3188_, lean_object* v_k_3189_, lean_object* v_v_3190_, lean_object* v_t_3191_){
_start:
{
if (lean_obj_tag(v_t_3191_) == 0)
{
lean_object* v_size_3192_; lean_object* v_k_3193_; lean_object* v_v_3194_; lean_object* v_l_3195_; lean_object* v_r_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3553_; 
v_size_3192_ = lean_ctor_get(v_t_3191_, 0);
v_k_3193_ = lean_ctor_get(v_t_3191_, 1);
v_v_3194_ = lean_ctor_get(v_t_3191_, 2);
v_l_3195_ = lean_ctor_get(v_t_3191_, 3);
v_r_3196_ = lean_ctor_get(v_t_3191_, 4);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_t_3191_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3198_ = v_t_3191_;
v_isShared_3199_ = v_isSharedCheck_3553_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_r_3196_);
lean_inc(v_l_3195_);
lean_inc(v_v_3194_);
lean_inc(v_k_3193_);
lean_inc(v_size_3192_);
lean_dec(v_t_3191_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3553_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; uint8_t v___x_3201_; 
lean_inc_ref(v_cmp_3188_);
lean_inc(v_k_3193_);
lean_inc(v_k_3189_);
v___x_3200_ = lean_apply_2(v_cmp_3188_, v_k_3189_, v_k_3193_);
v___x_3201_ = lean_unbox(v___x_3200_);
switch(v___x_3201_)
{
case 0:
{
lean_object* v___x_3202_; 
lean_dec(v_size_3192_);
v___x_3202_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3188_, v_k_3189_, v_v_3190_, v_l_3195_);
if (lean_obj_tag(v_r_3196_) == 0)
{
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_size_3203_; lean_object* v_size_3204_; lean_object* v_k_3205_; lean_object* v_v_3206_; lean_object* v_l_3207_; lean_object* v_r_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_size_3203_ = lean_ctor_get(v_r_3196_, 0);
v_size_3204_ = lean_ctor_get(v___x_3202_, 0);
v_k_3205_ = lean_ctor_get(v___x_3202_, 1);
v_v_3206_ = lean_ctor_get(v___x_3202_, 2);
v_l_3207_ = lean_ctor_get(v___x_3202_, 3);
v_r_3208_ = lean_ctor_get(v___x_3202_, 4);
lean_inc(v_r_3208_);
v___x_3209_ = lean_unsigned_to_nat(3u);
v___x_3210_ = lean_nat_mul(v___x_3209_, v_size_3203_);
v___x_3211_ = lean_nat_dec_lt(v___x_3210_, v_size_3204_);
lean_dec(v___x_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
lean_dec(v_r_3208_);
v___x_3212_ = lean_unsigned_to_nat(1u);
v___x_3213_ = lean_nat_add(v___x_3212_, v_size_3204_);
v___x_3214_ = lean_nat_add(v___x_3213_, v_size_3203_);
lean_dec(v___x_3213_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 3, v___x_3202_);
lean_ctor_set(v___x_3198_, 0, v___x_3214_);
v___x_3216_ = v___x_3198_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3217_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3217_, 3, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3217_, 4, v_r_3196_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
else
{
lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3289_; 
lean_inc(v_l_3207_);
lean_inc(v_v_3206_);
lean_inc(v_k_3205_);
lean_inc(v_size_3204_);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; lean_object* v_unused_3291_; lean_object* v_unused_3292_; lean_object* v_unused_3293_; lean_object* v_unused_3294_; 
v_unused_3290_ = lean_ctor_get(v___x_3202_, 4);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v___x_3202_, 3);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v___x_3202_, 2);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v___x_3202_, 1);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v___x_3202_, 0);
lean_dec(v_unused_3294_);
v___x_3219_ = v___x_3202_;
v_isShared_3220_ = v_isSharedCheck_3289_;
goto v_resetjp_3218_;
}
else
{
lean_dec(v___x_3202_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3289_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
if (lean_obj_tag(v_l_3207_) == 0)
{
if (lean_obj_tag(v_r_3208_) == 0)
{
lean_object* v_size_3221_; lean_object* v_size_3222_; lean_object* v_k_3223_; lean_object* v_v_3224_; lean_object* v_l_3225_; lean_object* v_r_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v_size_3221_ = lean_ctor_get(v_l_3207_, 0);
v_size_3222_ = lean_ctor_get(v_r_3208_, 0);
v_k_3223_ = lean_ctor_get(v_r_3208_, 1);
v_v_3224_ = lean_ctor_get(v_r_3208_, 2);
v_l_3225_ = lean_ctor_get(v_r_3208_, 3);
v_r_3226_ = lean_ctor_get(v_r_3208_, 4);
v___x_3227_ = lean_unsigned_to_nat(2u);
v___x_3228_ = lean_nat_mul(v___x_3227_, v_size_3221_);
v___x_3229_ = lean_nat_dec_lt(v_size_3222_, v___x_3228_);
lean_dec(v___x_3228_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3259_; 
lean_inc(v_r_3226_);
lean_inc(v_l_3225_);
lean_inc(v_v_3224_);
lean_inc(v_k_3223_);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_r_3208_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; lean_object* v_unused_3261_; lean_object* v_unused_3262_; lean_object* v_unused_3263_; lean_object* v_unused_3264_; 
v_unused_3260_ = lean_ctor_get(v_r_3208_, 4);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_r_3208_, 3);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_r_3208_, 2);
lean_dec(v_unused_3262_);
v_unused_3263_ = lean_ctor_get(v_r_3208_, 1);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_r_3208_, 0);
lean_dec(v_unused_3264_);
v___x_3231_ = v_r_3208_;
v_isShared_3232_ = v_isSharedCheck_3259_;
goto v_resetjp_3230_;
}
else
{
lean_dec(v_r_3208_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3259_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___x_3247_; lean_object* v___y_3249_; 
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_nat_add(v___x_3233_, v_size_3204_);
lean_dec(v_size_3204_);
v___x_3235_ = lean_nat_add(v___x_3234_, v_size_3203_);
lean_dec(v___x_3234_);
v___x_3247_ = lean_nat_add(v___x_3233_, v_size_3221_);
if (lean_obj_tag(v_l_3225_) == 0)
{
lean_object* v_size_3257_; 
v_size_3257_ = lean_ctor_get(v_l_3225_, 0);
lean_inc(v_size_3257_);
v___y_3249_ = v_size_3257_;
goto v___jp_3248_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_unsigned_to_nat(0u);
v___y_3249_ = v___x_3258_;
goto v___jp_3248_;
}
v___jp_3236_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3240_ = lean_nat_add(v___y_3237_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec(v___y_3237_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 4, v_r_3196_);
lean_ctor_set(v___x_3231_, 3, v_r_3226_);
lean_ctor_set(v___x_3231_, 2, v_v_3194_);
lean_ctor_set(v___x_3231_, 1, v_k_3193_);
lean_ctor_set(v___x_3231_, 0, v___x_3240_);
v___x_3242_ = v___x_3231_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_r_3226_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_r_3196_);
v___x_3242_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 4, v___x_3242_);
lean_ctor_set(v___x_3219_, 3, v___y_3238_);
lean_ctor_set(v___x_3219_, 2, v_v_3224_);
lean_ctor_set(v___x_3219_, 1, v_k_3223_);
lean_ctor_set(v___x_3219_, 0, v___x_3235_);
v___x_3244_ = v___x_3219_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_k_3223_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_v_3224_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v___y_3238_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
v___jp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = lean_nat_add(v___x_3247_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec(v___x_3247_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v_l_3225_);
lean_ctor_set(v___x_3198_, 3, v_l_3207_);
lean_ctor_set(v___x_3198_, 2, v_v_3206_);
lean_ctor_set(v___x_3198_, 1, v_k_3205_);
lean_ctor_set(v___x_3198_, 0, v___x_3250_);
v___x_3252_ = v___x_3198_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_l_3207_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v_l_3225_);
v___x_3252_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_nat_add(v___x_3233_, v_size_3203_);
if (lean_obj_tag(v_r_3226_) == 0)
{
lean_object* v_size_3254_; 
v_size_3254_ = lean_ctor_get(v_r_3226_, 0);
lean_inc(v_size_3254_);
v___y_3237_ = v___x_3253_;
v___y_3238_ = v___x_3252_;
v___y_3239_ = v_size_3254_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_unsigned_to_nat(0u);
v___y_3237_ = v___x_3253_;
v___y_3238_ = v___x_3252_;
v___y_3239_ = v___x_3255_;
goto v___jp_3236_;
}
}
}
}
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
lean_del_object(v___x_3198_);
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = lean_nat_add(v___x_3265_, v_size_3204_);
lean_dec(v_size_3204_);
v___x_3267_ = lean_nat_add(v___x_3266_, v_size_3203_);
lean_dec(v___x_3266_);
v___x_3268_ = lean_nat_add(v___x_3265_, v_size_3203_);
v___x_3269_ = lean_nat_add(v___x_3268_, v_size_3222_);
lean_dec(v___x_3268_);
lean_inc_ref(v_r_3196_);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 4, v_r_3196_);
lean_ctor_set(v___x_3219_, 3, v_r_3208_);
lean_ctor_set(v___x_3219_, 2, v_v_3194_);
lean_ctor_set(v___x_3219_, 1, v_k_3193_);
lean_ctor_set(v___x_3219_, 0, v___x_3269_);
v___x_3271_ = v___x_3219_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_r_3208_);
lean_ctor_set(v_reuseFailAlloc_3284_, 4, v_r_3196_);
v___x_3271_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
v_isSharedCheck_3278_ = !lean_is_exclusive(v_r_3196_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; lean_object* v_unused_3280_; lean_object* v_unused_3281_; lean_object* v_unused_3282_; lean_object* v_unused_3283_; 
v_unused_3279_ = lean_ctor_get(v_r_3196_, 4);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_r_3196_, 3);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_r_3196_, 2);
lean_dec(v_unused_3281_);
v_unused_3282_ = lean_ctor_get(v_r_3196_, 1);
lean_dec(v_unused_3282_);
v_unused_3283_ = lean_ctor_get(v_r_3196_, 0);
lean_dec(v_unused_3283_);
v___x_3273_ = v_r_3196_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_dec(v_r_3196_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 4, v___x_3271_);
lean_ctor_set(v___x_3273_, 3, v_l_3207_);
lean_ctor_set(v___x_3273_, 2, v_v_3206_);
lean_ctor_set(v___x_3273_, 1, v_k_3205_);
lean_ctor_set(v___x_3273_, 0, v___x_3267_);
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v_l_3207_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v___x_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec_ref_known(v_l_3207_, 5);
lean_del_object(v___x_3219_);
lean_dec(v_v_3206_);
lean_dec(v_k_3205_);
lean_dec(v_size_3204_);
lean_dec_ref_known(v_r_3196_, 5);
lean_del_object(v___x_3198_);
lean_dec(v_v_3194_);
lean_dec(v_k_3193_);
v___x_3285_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_3286_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3285_);
return v___x_3286_;
}
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_del_object(v___x_3219_);
lean_dec(v_r_3208_);
lean_dec(v_v_3206_);
lean_dec(v_k_3205_);
lean_dec(v_size_3204_);
lean_dec_ref_known(v_r_3196_, 5);
lean_del_object(v___x_3198_);
lean_dec(v_v_3194_);
lean_dec(v_k_3193_);
v___x_3287_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_3288_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3287_);
return v___x_3288_;
}
}
}
}
else
{
lean_object* v_size_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3299_; 
v_size_3295_ = lean_ctor_get(v_r_3196_, 0);
v___x_3296_ = lean_unsigned_to_nat(1u);
v___x_3297_ = lean_nat_add(v___x_3296_, v_size_3295_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 3, v___x_3202_);
lean_ctor_set(v___x_3198_, 0, v___x_3297_);
v___x_3299_ = v___x_3198_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_r_3196_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
else
{
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_l_3301_; 
v_l_3301_ = lean_ctor_get(v___x_3202_, 3);
if (lean_obj_tag(v_l_3301_) == 0)
{
lean_object* v_r_3302_; 
lean_inc_ref(v_l_3301_);
v_r_3302_ = lean_ctor_get(v___x_3202_, 4);
lean_inc(v_r_3302_);
if (lean_obj_tag(v_r_3302_) == 0)
{
lean_object* v_size_3303_; lean_object* v_k_3304_; lean_object* v_v_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3319_; 
v_size_3303_ = lean_ctor_get(v___x_3202_, 0);
v_k_3304_ = lean_ctor_get(v___x_3202_, 1);
v_v_3305_ = lean_ctor_get(v___x_3202_, 2);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; lean_object* v_unused_3321_; 
v_unused_3320_ = lean_ctor_get(v___x_3202_, 4);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v___x_3202_, 3);
lean_dec(v_unused_3321_);
v___x_3307_ = v___x_3202_;
v_isShared_3308_ = v_isSharedCheck_3319_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_v_3305_);
lean_inc(v_k_3304_);
lean_inc(v_size_3303_);
lean_dec(v___x_3202_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3319_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v_size_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v_size_3309_ = lean_ctor_get(v_r_3302_, 0);
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_nat_add(v___x_3310_, v_size_3303_);
lean_dec(v_size_3303_);
v___x_3312_ = lean_nat_add(v___x_3310_, v_size_3309_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 4, v_r_3196_);
lean_ctor_set(v___x_3307_, 3, v_r_3302_);
lean_ctor_set(v___x_3307_, 2, v_v_3194_);
lean_ctor_set(v___x_3307_, 1, v_k_3193_);
lean_ctor_set(v___x_3307_, 0, v___x_3312_);
v___x_3314_ = v___x_3307_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_r_3302_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_r_3196_);
v___x_3314_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3316_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3314_);
lean_ctor_set(v___x_3198_, 3, v_l_3301_);
lean_ctor_set(v___x_3198_, 2, v_v_3305_);
lean_ctor_set(v___x_3198_, 1, v_k_3304_);
lean_ctor_set(v___x_3198_, 0, v___x_3311_);
v___x_3316_ = v___x_3198_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_k_3304_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_v_3305_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_l_3301_);
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
else
{
lean_object* v_k_3322_; lean_object* v_v_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3335_; 
v_k_3322_ = lean_ctor_get(v___x_3202_, 1);
v_v_3323_ = lean_ctor_get(v___x_3202_, 2);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; lean_object* v_unused_3337_; lean_object* v_unused_3338_; 
v_unused_3336_ = lean_ctor_get(v___x_3202_, 4);
lean_dec(v_unused_3336_);
v_unused_3337_ = lean_ctor_get(v___x_3202_, 3);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v___x_3202_, 0);
lean_dec(v_unused_3338_);
v___x_3325_ = v___x_3202_;
v_isShared_3326_ = v_isSharedCheck_3335_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_v_3323_);
lean_inc(v_k_3322_);
lean_dec(v___x_3202_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3335_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3327_ = lean_unsigned_to_nat(3u);
v___x_3328_ = lean_unsigned_to_nat(1u);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 3, v_r_3302_);
lean_ctor_set(v___x_3325_, 2, v_v_3194_);
lean_ctor_set(v___x_3325_, 1, v_k_3193_);
lean_ctor_set(v___x_3325_, 0, v___x_3328_);
v___x_3330_ = v___x_3325_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_r_3302_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_r_3302_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3330_);
lean_ctor_set(v___x_3198_, 3, v_l_3301_);
lean_ctor_set(v___x_3198_, 2, v_v_3323_);
lean_ctor_set(v___x_3198_, 1, v_k_3322_);
lean_ctor_set(v___x_3198_, 0, v___x_3327_);
v___x_3332_ = v___x_3198_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_k_3322_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_v_3323_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v_l_3301_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
else
{
lean_object* v_r_3339_; 
v_r_3339_ = lean_ctor_get(v___x_3202_, 4);
lean_inc(v_r_3339_);
if (lean_obj_tag(v_r_3339_) == 0)
{
lean_object* v_k_3340_; lean_object* v_v_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3365_; 
lean_inc(v_l_3301_);
v_k_3340_ = lean_ctor_get(v___x_3202_, 1);
v_v_3341_ = lean_ctor_get(v___x_3202_, 2);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; lean_object* v_unused_3367_; lean_object* v_unused_3368_; 
v_unused_3366_ = lean_ctor_get(v___x_3202_, 4);
lean_dec(v_unused_3366_);
v_unused_3367_ = lean_ctor_get(v___x_3202_, 3);
lean_dec(v_unused_3367_);
v_unused_3368_ = lean_ctor_get(v___x_3202_, 0);
lean_dec(v_unused_3368_);
v___x_3343_ = v___x_3202_;
v_isShared_3344_ = v_isSharedCheck_3365_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_v_3341_);
lean_inc(v_k_3340_);
lean_dec(v___x_3202_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3365_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_k_3345_; lean_object* v_v_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3361_; 
v_k_3345_ = lean_ctor_get(v_r_3339_, 1);
v_v_3346_ = lean_ctor_get(v_r_3339_, 2);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_r_3339_);
if (v_isSharedCheck_3361_ == 0)
{
lean_object* v_unused_3362_; lean_object* v_unused_3363_; lean_object* v_unused_3364_; 
v_unused_3362_ = lean_ctor_get(v_r_3339_, 4);
lean_dec(v_unused_3362_);
v_unused_3363_ = lean_ctor_get(v_r_3339_, 3);
lean_dec(v_unused_3363_);
v_unused_3364_ = lean_ctor_get(v_r_3339_, 0);
lean_dec(v_unused_3364_);
v___x_3348_ = v_r_3339_;
v_isShared_3349_ = v_isSharedCheck_3361_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_v_3346_);
lean_inc(v_k_3345_);
lean_dec(v_r_3339_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3361_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3350_ = lean_unsigned_to_nat(3u);
v___x_3351_ = lean_unsigned_to_nat(1u);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 4, v_l_3301_);
lean_ctor_set(v___x_3348_, 3, v_l_3301_);
lean_ctor_set(v___x_3348_, 2, v_v_3341_);
lean_ctor_set(v___x_3348_, 1, v_k_3340_);
lean_ctor_set(v___x_3348_, 0, v___x_3351_);
v___x_3353_ = v___x_3348_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_k_3340_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_v_3341_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v_l_3301_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v_l_3301_);
v___x_3353_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3355_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_l_3301_);
lean_ctor_set(v___x_3343_, 2, v_v_3194_);
lean_ctor_set(v___x_3343_, 1, v_k_3193_);
lean_ctor_set(v___x_3343_, 0, v___x_3351_);
v___x_3355_ = v___x_3343_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3359_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3359_, 3, v_l_3301_);
lean_ctor_set(v_reuseFailAlloc_3359_, 4, v_l_3301_);
v___x_3355_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3357_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3355_);
lean_ctor_set(v___x_3198_, 3, v___x_3353_);
lean_ctor_set(v___x_3198_, 2, v_v_3346_);
lean_ctor_set(v___x_3198_, 1, v_k_3345_);
lean_ctor_set(v___x_3198_, 0, v___x_3350_);
v___x_3357_ = v___x_3198_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_k_3345_);
lean_ctor_set(v_reuseFailAlloc_3358_, 2, v_v_3346_);
lean_ctor_set(v_reuseFailAlloc_3358_, 3, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3358_, 4, v___x_3355_);
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
}
}
else
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_unsigned_to_nat(2u);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v_r_3339_);
lean_ctor_set(v___x_3198_, 3, v___x_3202_);
lean_ctor_set(v___x_3198_, 0, v___x_3369_);
v___x_3371_ = v___x_3198_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3372_, 3, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3372_, 4, v_r_3339_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_unsigned_to_nat(1u);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3202_);
lean_ctor_set(v___x_3198_, 3, v___x_3202_);
lean_ctor_set(v___x_3198_, 0, v___x_3373_);
v___x_3375_ = v___x_3198_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3376_, 3, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3376_, 4, v___x_3202_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
case 1:
{
lean_object* v___x_3378_; 
lean_dec(v_v_3194_);
lean_dec(v_k_3193_);
lean_dec_ref(v_cmp_3188_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 2, v_v_3190_);
lean_ctor_set(v___x_3198_, 1, v_k_3189_);
v___x_3378_ = v___x_3198_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_size_3192_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3189_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3190_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_l_3195_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_r_3196_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
default: 
{
lean_object* v___x_3380_; 
lean_dec(v_size_3192_);
v___x_3380_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3188_, v_k_3189_, v_v_3190_, v_r_3196_);
if (lean_obj_tag(v_l_3195_) == 0)
{
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_size_3381_; lean_object* v_size_3382_; lean_object* v_k_3383_; lean_object* v_v_3384_; lean_object* v_l_3385_; lean_object* v_r_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v_size_3381_ = lean_ctor_get(v_l_3195_, 0);
v_size_3382_ = lean_ctor_get(v___x_3380_, 0);
v_k_3383_ = lean_ctor_get(v___x_3380_, 1);
v_v_3384_ = lean_ctor_get(v___x_3380_, 2);
v_l_3385_ = lean_ctor_get(v___x_3380_, 3);
lean_inc(v_l_3385_);
v_r_3386_ = lean_ctor_get(v___x_3380_, 4);
v___x_3387_ = lean_unsigned_to_nat(3u);
v___x_3388_ = lean_nat_mul(v___x_3387_, v_size_3381_);
v___x_3389_ = lean_nat_dec_lt(v___x_3388_, v_size_3382_);
lean_dec(v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_dec(v_l_3385_);
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_nat_add(v___x_3390_, v_size_3381_);
v___x_3392_ = lean_nat_add(v___x_3391_, v_size_3382_);
lean_dec(v___x_3391_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3380_);
lean_ctor_set(v___x_3198_, 0, v___x_3392_);
v___x_3394_ = v___x_3198_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_l_3195_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v___x_3380_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
else
{
lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3465_; 
lean_inc(v_r_3386_);
lean_inc(v_v_3384_);
lean_inc(v_k_3383_);
lean_inc(v_size_3382_);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; lean_object* v_unused_3467_; lean_object* v_unused_3468_; lean_object* v_unused_3469_; lean_object* v_unused_3470_; 
v_unused_3466_ = lean_ctor_get(v___x_3380_, 4);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v___x_3380_, 3);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v___x_3380_, 2);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v___x_3380_, 1);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3470_);
v___x_3397_ = v___x_3380_;
v_isShared_3398_ = v_isSharedCheck_3465_;
goto v_resetjp_3396_;
}
else
{
lean_dec(v___x_3380_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3465_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
if (lean_obj_tag(v_l_3385_) == 0)
{
if (lean_obj_tag(v_r_3386_) == 0)
{
lean_object* v_size_3399_; lean_object* v_k_3400_; lean_object* v_v_3401_; lean_object* v_l_3402_; lean_object* v_r_3403_; lean_object* v_size_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_size_3399_ = lean_ctor_get(v_l_3385_, 0);
v_k_3400_ = lean_ctor_get(v_l_3385_, 1);
v_v_3401_ = lean_ctor_get(v_l_3385_, 2);
v_l_3402_ = lean_ctor_get(v_l_3385_, 3);
v_r_3403_ = lean_ctor_get(v_l_3385_, 4);
v_size_3404_ = lean_ctor_get(v_r_3386_, 0);
v___x_3405_ = lean_unsigned_to_nat(2u);
v___x_3406_ = lean_nat_mul(v___x_3405_, v_size_3404_);
v___x_3407_ = lean_nat_dec_lt(v_size_3399_, v___x_3406_);
lean_dec(v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3436_; 
lean_inc(v_r_3403_);
lean_inc(v_l_3402_);
lean_inc(v_v_3401_);
lean_inc(v_k_3400_);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_l_3385_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; lean_object* v_unused_3438_; lean_object* v_unused_3439_; lean_object* v_unused_3440_; lean_object* v_unused_3441_; 
v_unused_3437_ = lean_ctor_get(v_l_3385_, 4);
lean_dec(v_unused_3437_);
v_unused_3438_ = lean_ctor_get(v_l_3385_, 3);
lean_dec(v_unused_3438_);
v_unused_3439_ = lean_ctor_get(v_l_3385_, 2);
lean_dec(v_unused_3439_);
v_unused_3440_ = lean_ctor_get(v_l_3385_, 1);
lean_dec(v_unused_3440_);
v_unused_3441_ = lean_ctor_get(v_l_3385_, 0);
lean_dec(v_unused_3441_);
v___x_3409_ = v_l_3385_;
v_isShared_3410_ = v_isSharedCheck_3436_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v_l_3385_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3436_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3426_; 
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = lean_nat_add(v___x_3411_, v_size_3381_);
v___x_3413_ = lean_nat_add(v___x_3412_, v_size_3382_);
lean_dec(v_size_3382_);
if (lean_obj_tag(v_l_3402_) == 0)
{
lean_object* v_size_3434_; 
v_size_3434_ = lean_ctor_get(v_l_3402_, 0);
lean_inc(v_size_3434_);
v___y_3426_ = v_size_3434_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v___y_3426_ = v___x_3435_;
goto v___jp_3425_;
}
v___jp_3414_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = lean_nat_add(v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec(v___y_3416_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 4, v_r_3386_);
lean_ctor_set(v___x_3409_, 3, v_r_3403_);
lean_ctor_set(v___x_3409_, 2, v_v_3384_);
lean_ctor_set(v___x_3409_, 1, v_k_3383_);
lean_ctor_set(v___x_3409_, 0, v___x_3418_);
v___x_3420_ = v___x_3409_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3383_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3384_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_r_3403_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_r_3386_);
v___x_3420_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 4, v___x_3420_);
lean_ctor_set(v___x_3397_, 3, v___y_3415_);
lean_ctor_set(v___x_3397_, 2, v_v_3401_);
lean_ctor_set(v___x_3397_, 1, v_k_3400_);
lean_ctor_set(v___x_3397_, 0, v___x_3413_);
v___x_3422_ = v___x_3397_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_k_3400_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_v_3401_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v___y_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
v___jp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3427_ = lean_nat_add(v___x_3412_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec(v___x_3412_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v_l_3402_);
lean_ctor_set(v___x_3198_, 0, v___x_3427_);
v___x_3429_ = v___x_3198_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v_l_3195_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v_l_3402_);
v___x_3429_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_nat_add(v___x_3411_, v_size_3404_);
if (lean_obj_tag(v_r_3403_) == 0)
{
lean_object* v_size_3431_; 
v_size_3431_ = lean_ctor_get(v_r_3403_, 0);
lean_inc(v_size_3431_);
v___y_3415_ = v___x_3429_;
v___y_3416_ = v___x_3430_;
v___y_3417_ = v_size_3431_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___y_3415_ = v___x_3429_;
v___y_3416_ = v___x_3430_;
v___y_3417_ = v___x_3432_;
goto v___jp_3414_;
}
}
}
}
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
lean_del_object(v___x_3198_);
v___x_3442_ = lean_unsigned_to_nat(1u);
v___x_3443_ = lean_nat_add(v___x_3442_, v_size_3381_);
v___x_3444_ = lean_nat_add(v___x_3443_, v_size_3382_);
lean_dec(v_size_3382_);
v___x_3445_ = lean_nat_add(v___x_3443_, v_size_3399_);
lean_dec(v___x_3443_);
lean_inc_ref(v_l_3195_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 4, v_l_3385_);
lean_ctor_set(v___x_3397_, 3, v_l_3195_);
lean_ctor_set(v___x_3397_, 2, v_v_3194_);
lean_ctor_set(v___x_3397_, 1, v_k_3193_);
lean_ctor_set(v___x_3397_, 0, v___x_3445_);
v___x_3447_ = v___x_3397_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3460_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3460_, 3, v_l_3195_);
lean_ctor_set(v_reuseFailAlloc_3460_, 4, v_l_3385_);
v___x_3447_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_isSharedCheck_3454_ = !lean_is_exclusive(v_l_3195_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; lean_object* v_unused_3456_; lean_object* v_unused_3457_; lean_object* v_unused_3458_; lean_object* v_unused_3459_; 
v_unused_3455_ = lean_ctor_get(v_l_3195_, 4);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_l_3195_, 3);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_l_3195_, 2);
lean_dec(v_unused_3457_);
v_unused_3458_ = lean_ctor_get(v_l_3195_, 1);
lean_dec(v_unused_3458_);
v_unused_3459_ = lean_ctor_get(v_l_3195_, 0);
lean_dec(v_unused_3459_);
v___x_3449_ = v_l_3195_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v_l_3195_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 4, v_r_3386_);
lean_ctor_set(v___x_3449_, 3, v___x_3447_);
lean_ctor_set(v___x_3449_, 2, v_v_3384_);
lean_ctor_set(v___x_3449_, 1, v_k_3383_);
lean_ctor_set(v___x_3449_, 0, v___x_3444_);
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3383_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3384_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_r_3386_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec_ref_known(v_l_3385_, 5);
lean_del_object(v___x_3397_);
lean_dec(v_v_3384_);
lean_dec(v_k_3383_);
lean_dec(v_size_3382_);
lean_dec_ref_known(v_l_3195_, 5);
lean_del_object(v___x_3198_);
lean_dec(v_v_3194_);
lean_dec(v_k_3193_);
v___x_3461_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_3462_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3461_);
return v___x_3462_;
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_del_object(v___x_3397_);
lean_dec(v_r_3386_);
lean_dec(v_v_3384_);
lean_dec(v_k_3383_);
lean_dec(v_size_3382_);
lean_dec_ref_known(v_l_3195_, 5);
lean_del_object(v___x_3198_);
lean_dec(v_v_3194_);
lean_dec(v_k_3193_);
v___x_3463_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_3464_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_3463_);
return v___x_3464_;
}
}
}
}
else
{
lean_object* v_size_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3475_; 
v_size_3471_ = lean_ctor_get(v_l_3195_, 0);
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v___x_3472_, v_size_3471_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3380_);
lean_ctor_set(v___x_3198_, 0, v___x_3473_);
v___x_3475_ = v___x_3198_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3476_, 3, v_l_3195_);
lean_ctor_set(v_reuseFailAlloc_3476_, 4, v___x_3380_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
else
{
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_l_3477_; 
v_l_3477_ = lean_ctor_get(v___x_3380_, 3);
lean_inc(v_l_3477_);
if (lean_obj_tag(v_l_3477_) == 0)
{
lean_object* v_r_3478_; 
v_r_3478_ = lean_ctor_get(v___x_3380_, 4);
lean_inc(v_r_3478_);
if (lean_obj_tag(v_r_3478_) == 0)
{
lean_object* v_size_3479_; lean_object* v_k_3480_; lean_object* v_v_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3495_; 
v_size_3479_ = lean_ctor_get(v___x_3380_, 0);
v_k_3480_ = lean_ctor_get(v___x_3380_, 1);
v_v_3481_ = lean_ctor_get(v___x_3380_, 2);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; lean_object* v_unused_3497_; 
v_unused_3496_ = lean_ctor_get(v___x_3380_, 4);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v___x_3380_, 3);
lean_dec(v_unused_3497_);
v___x_3483_ = v___x_3380_;
v_isShared_3484_ = v_isSharedCheck_3495_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_v_3481_);
lean_inc(v_k_3480_);
lean_inc(v_size_3479_);
lean_dec(v___x_3380_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3495_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v_size_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v_size_3485_ = lean_ctor_get(v_l_3477_, 0);
v___x_3486_ = lean_unsigned_to_nat(1u);
v___x_3487_ = lean_nat_add(v___x_3486_, v_size_3479_);
lean_dec(v_size_3479_);
v___x_3488_ = lean_nat_add(v___x_3486_, v_size_3485_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 4, v_l_3477_);
lean_ctor_set(v___x_3483_, 3, v_l_3195_);
lean_ctor_set(v___x_3483_, 2, v_v_3194_);
lean_ctor_set(v___x_3483_, 1, v_k_3193_);
lean_ctor_set(v___x_3483_, 0, v___x_3488_);
v___x_3490_ = v___x_3483_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_l_3195_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v_l_3477_);
v___x_3490_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v_r_3478_);
lean_ctor_set(v___x_3198_, 3, v___x_3490_);
lean_ctor_set(v___x_3198_, 2, v_v_3481_);
lean_ctor_set(v___x_3198_, 1, v_k_3480_);
lean_ctor_set(v___x_3198_, 0, v___x_3487_);
v___x_3492_ = v___x_3198_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3487_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_k_3480_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_v_3481_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_r_3478_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_k_3498_; lean_object* v_v_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3523_; 
v_k_3498_ = lean_ctor_get(v___x_3380_, 1);
v_v_3499_ = lean_ctor_get(v___x_3380_, 2);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; lean_object* v_unused_3525_; lean_object* v_unused_3526_; 
v_unused_3524_ = lean_ctor_get(v___x_3380_, 4);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v___x_3380_, 3);
lean_dec(v_unused_3525_);
v_unused_3526_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3526_);
v___x_3501_ = v___x_3380_;
v_isShared_3502_ = v_isSharedCheck_3523_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_v_3499_);
lean_inc(v_k_3498_);
lean_dec(v___x_3380_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3523_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v_k_3503_; lean_object* v_v_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3519_; 
v_k_3503_ = lean_ctor_get(v_l_3477_, 1);
v_v_3504_ = lean_ctor_get(v_l_3477_, 2);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_l_3477_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; lean_object* v_unused_3521_; lean_object* v_unused_3522_; 
v_unused_3520_ = lean_ctor_get(v_l_3477_, 4);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v_l_3477_, 3);
lean_dec(v_unused_3521_);
v_unused_3522_ = lean_ctor_get(v_l_3477_, 0);
lean_dec(v_unused_3522_);
v___x_3506_ = v_l_3477_;
v_isShared_3507_ = v_isSharedCheck_3519_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_v_3504_);
lean_inc(v_k_3503_);
lean_dec(v_l_3477_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3519_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3508_ = lean_unsigned_to_nat(3u);
v___x_3509_ = lean_unsigned_to_nat(1u);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 4, v_r_3478_);
lean_ctor_set(v___x_3506_, 3, v_r_3478_);
lean_ctor_set(v___x_3506_, 2, v_v_3194_);
lean_ctor_set(v___x_3506_, 1, v_k_3193_);
lean_ctor_set(v___x_3506_, 0, v___x_3509_);
v___x_3511_ = v___x_3506_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3518_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3518_, 3, v_r_3478_);
lean_ctor_set(v_reuseFailAlloc_3518_, 4, v_r_3478_);
v___x_3511_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 3, v_r_3478_);
lean_ctor_set(v___x_3501_, 0, v___x_3509_);
v___x_3513_ = v___x_3501_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3498_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3499_);
lean_ctor_set(v_reuseFailAlloc_3517_, 3, v_r_3478_);
lean_ctor_set(v_reuseFailAlloc_3517_, 4, v_r_3478_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3515_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3513_);
lean_ctor_set(v___x_3198_, 3, v___x_3511_);
lean_ctor_set(v___x_3198_, 2, v_v_3504_);
lean_ctor_set(v___x_3198_, 1, v_k_3503_);
lean_ctor_set(v___x_3198_, 0, v___x_3508_);
v___x_3515_ = v___x_3198_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_k_3503_);
lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_v_3504_);
lean_ctor_set(v_reuseFailAlloc_3516_, 3, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3516_, 4, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3527_; 
v_r_3527_ = lean_ctor_get(v___x_3380_, 4);
lean_inc(v_r_3527_);
if (lean_obj_tag(v_r_3527_) == 0)
{
lean_object* v_k_3528_; lean_object* v_v_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3541_; 
v_k_3528_ = lean_ctor_get(v___x_3380_, 1);
v_v_3529_ = lean_ctor_get(v___x_3380_, 2);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; lean_object* v_unused_3543_; lean_object* v_unused_3544_; 
v_unused_3542_ = lean_ctor_get(v___x_3380_, 4);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v___x_3380_, 3);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3544_);
v___x_3531_ = v___x_3380_;
v_isShared_3532_ = v_isSharedCheck_3541_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_v_3529_);
lean_inc(v_k_3528_);
lean_dec(v___x_3380_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3541_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3533_ = lean_unsigned_to_nat(3u);
v___x_3534_ = lean_unsigned_to_nat(1u);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 4, v_l_3477_);
lean_ctor_set(v___x_3531_, 2, v_v_3194_);
lean_ctor_set(v___x_3531_, 1, v_k_3193_);
lean_ctor_set(v___x_3531_, 0, v___x_3534_);
v___x_3536_ = v___x_3531_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_l_3477_);
lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_l_3477_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v_r_3527_);
lean_ctor_set(v___x_3198_, 3, v___x_3536_);
lean_ctor_set(v___x_3198_, 2, v_v_3529_);
lean_ctor_set(v___x_3198_, 1, v_k_3528_);
lean_ctor_set(v___x_3198_, 0, v___x_3533_);
v___x_3538_ = v___x_3198_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_k_3528_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_v_3529_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3539_, 4, v_r_3527_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3545_ = lean_unsigned_to_nat(2u);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3380_);
lean_ctor_set(v___x_3198_, 3, v_r_3527_);
lean_ctor_set(v___x_3198_, 0, v___x_3545_);
v___x_3547_ = v___x_3198_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_r_3527_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v___x_3380_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_unsigned_to_nat(1u);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___x_3380_);
lean_ctor_set(v___x_3198_, 3, v___x_3380_);
lean_ctor_set(v___x_3198_, 0, v___x_3549_);
v___x_3551_ = v___x_3198_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_k_3193_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_v_3194_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v___x_3380_);
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
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec_ref(v_cmp_3188_);
v___x_3554_ = lean_unsigned_to_nat(1u);
v___x_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v_k_3189_);
lean_ctor_set(v___x_3555_, 2, v_v_3190_);
lean_ctor_set(v___x_3555_, 3, v_t_3191_);
lean_ctor_set(v___x_3555_, 4, v_t_3191_);
return v___x_3555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(lean_object* v_cmp_3556_, lean_object* v_init_3557_, lean_object* v_x_3558_){
_start:
{
if (lean_obj_tag(v_x_3558_) == 0)
{
lean_object* v_k_3559_; lean_object* v_v_3560_; lean_object* v_l_3561_; lean_object* v_r_3562_; lean_object* v___x_3563_; lean_object* v_a_3564_; lean_object* v_r_3565_; 
v_k_3559_ = lean_ctor_get(v_x_3558_, 1);
lean_inc(v_k_3559_);
v_v_3560_ = lean_ctor_get(v_x_3558_, 2);
lean_inc(v_v_3560_);
v_l_3561_ = lean_ctor_get(v_x_3558_, 3);
lean_inc(v_l_3561_);
v_r_3562_ = lean_ctor_get(v_x_3558_, 4);
lean_inc(v_r_3562_);
lean_dec_ref_known(v_x_3558_, 5);
lean_inc_ref_n(v_cmp_3556_, 2);
v___x_3563_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3556_, v_init_3557_, v_l_3561_);
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
lean_dec_ref(v___x_3563_);
v_r_3565_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3556_, v_k_3559_, v_v_3560_, v_a_3564_);
v_init_3557_ = v_r_3565_;
v_x_3558_ = v_r_3562_;
goto _start;
}
else
{
lean_object* v___x_3567_; 
lean_dec_ref(v_cmp_3556_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_init_3557_);
return v___x_3567_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(lean_object* v_cmp_3568_, lean_object* v_k_3569_, lean_object* v_t_3570_){
_start:
{
if (lean_obj_tag(v_t_3570_) == 0)
{
lean_object* v_k_3571_; lean_object* v_l_3572_; lean_object* v_r_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v_k_3571_ = lean_ctor_get(v_t_3570_, 1);
lean_inc(v_k_3571_);
v_l_3572_ = lean_ctor_get(v_t_3570_, 3);
lean_inc(v_l_3572_);
v_r_3573_ = lean_ctor_get(v_t_3570_, 4);
lean_inc(v_r_3573_);
lean_dec_ref_known(v_t_3570_, 5);
lean_inc_ref(v_cmp_3568_);
lean_inc(v_k_3569_);
v___x_3574_ = lean_apply_2(v_cmp_3568_, v_k_3569_, v_k_3571_);
v___x_3575_ = lean_unbox(v___x_3574_);
switch(v___x_3575_)
{
case 0:
{
lean_dec(v_r_3573_);
v_t_3570_ = v_l_3572_;
goto _start;
}
case 1:
{
uint8_t v___x_3577_; 
lean_dec(v_r_3573_);
lean_dec(v_l_3572_);
lean_dec(v_k_3569_);
lean_dec_ref(v_cmp_3568_);
v___x_3577_ = 1;
return v___x_3577_;
}
default: 
{
lean_dec(v_l_3572_);
v_t_3570_ = v_r_3573_;
goto _start;
}
}
}
else
{
uint8_t v___x_3579_; 
lean_dec(v_k_3569_);
lean_dec_ref(v_cmp_3568_);
v___x_3579_ = 0;
return v___x_3579_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3568_ = stack[0].m_obj;
lean_object* v_k_3569_ = stack[1].m_obj;
lean_object* v_t_3570_ = stack[2].m_obj;
uint8_t v_res_3580_;
v_res_3580_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3568_, v_k_3569_, v_t_3570_);
stack->m_num = v_res_3580_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_3581_, lean_object* v_k_3582_, lean_object* v_t_3583_){
_start:
{
uint8_t v_res_3584_; lean_object* v_r_3585_; 
v_res_3584_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3581_, v_k_3582_, v_t_3583_);
v_r_3585_ = lean_box(v_res_3584_);
return v_r_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(lean_object* v_cmp_3586_, lean_object* v_init_3587_, lean_object* v_x_3588_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
lean_object* v_k_3589_; lean_object* v_v_3590_; lean_object* v_l_3591_; lean_object* v_r_3592_; lean_object* v___x_3593_; lean_object* v_a_3594_; uint8_t v___x_3595_; 
v_k_3589_ = lean_ctor_get(v_x_3588_, 1);
lean_inc_n(v_k_3589_, 2);
v_v_3590_ = lean_ctor_get(v_x_3588_, 2);
lean_inc(v_v_3590_);
v_l_3591_ = lean_ctor_get(v_x_3588_, 3);
lean_inc(v_l_3591_);
v_r_3592_ = lean_ctor_get(v_x_3588_, 4);
lean_inc(v_r_3592_);
lean_dec_ref_known(v_x_3588_, 5);
lean_inc_ref_n(v_cmp_3586_, 2);
v___x_3593_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3586_, v_init_3587_, v_l_3591_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_n(v_a_3594_, 2);
lean_dec_ref(v___x_3593_);
v___x_3595_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3586_, v_k_3589_, v_a_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; 
lean_inc_ref(v_cmp_3586_);
v___x_3596_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3586_, v_k_3589_, v_v_3590_, v_a_3594_);
v_init_3587_ = v___x_3596_;
v_x_3588_ = v_r_3592_;
goto _start;
}
else
{
lean_dec(v_v_3590_);
lean_dec(v_k_3589_);
v_init_3587_ = v_a_3594_;
v_x_3588_ = v_r_3592_;
goto _start;
}
}
else
{
lean_object* v___x_3599_; 
lean_dec_ref(v_cmp_3586_);
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v_init_3587_);
return v___x_3599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(lean_object* v_cmp_3600_, lean_object* v_t_u2081_3601_, lean_object* v_t_u2082_3602_){
_start:
{
lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3612_; 
if (lean_obj_tag(v_t_u2081_3601_) == 0)
{
lean_object* v_size_3615_; 
v_size_3615_ = lean_ctor_get(v_t_u2081_3601_, 0);
lean_inc(v_size_3615_);
v___y_3612_ = v_size_3615_;
goto v___jp_3611_;
}
else
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_unsigned_to_nat(0u);
v___y_3612_ = v___x_3616_;
goto v___jp_3611_;
}
v___jp_3603_:
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_nat_dec_le(v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec(v___y_3604_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v_a_3608_; 
v___x_3607_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3600_, v_t_u2081_3601_, v_t_u2082_3602_);
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v___x_3607_);
return v_a_3608_;
}
else
{
lean_object* v___x_3609_; lean_object* v_a_3610_; 
v___x_3609_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3600_, v_t_u2082_3602_, v_t_u2081_3601_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3609_);
return v_a_3610_;
}
}
v___jp_3611_:
{
if (lean_obj_tag(v_t_u2082_3602_) == 0)
{
lean_object* v_size_3613_; 
v_size_3613_ = lean_ctor_get(v_t_u2082_3602_, 0);
lean_inc(v_size_3613_);
v___y_3604_ = v___y_3612_;
v___y_3605_ = v_size_3613_;
goto v___jp_3603_;
}
else
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_unsigned_to_nat(0u);
v___y_3604_ = v___y_3612_;
v___y_3605_ = v___x_3614_;
goto v___jp_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union___redArg(lean_object* v_cmp_3617_, lean_object* v_t_u2081_3618_, lean_object* v_t_u2082_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3617_, v_t_u2081_3618_, v_t_u2082_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_union(lean_object* v_00_u03b1_3621_, lean_object* v_00_u03b2_3622_, lean_object* v_cmp_3623_, lean_object* v_t_u2081_3624_, lean_object* v_t_u2082_3625_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3623_, v_t_u2081_3624_, v_t_u2082_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0(lean_object* v_00_u03b1_3627_, lean_object* v_cmp_3628_, lean_object* v_00_u03b2_3629_, lean_object* v_t_u2081_3630_, lean_object* v_t_u2082_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0___redArg(v_cmp_3628_, v_t_u2081_3630_, v_t_u2082_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3633_, lean_object* v_00_u03b2_3634_, lean_object* v_msg_3635_){
_start:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v_msg_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0(lean_object* v_00_u03b1_3637_, lean_object* v_cmp_3638_, lean_object* v_00_u03b2_3639_, lean_object* v_k_3640_, lean_object* v_v_3641_, lean_object* v_t_3642_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg(v_cmp_3638_, v_k_3640_, v_v_3641_, v_t_3642_);
return v___x_3643_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_object* v_00_u03b1_3644_, lean_object* v_cmp_3645_, lean_object* v_00_u03b2_3646_, lean_object* v_k_3647_, lean_object* v_t_3648_){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_3645_, v_k_3647_, v_t_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_3645_ = stack[1].m_obj;
lean_object* v_k_3647_ = stack[3].m_obj;
lean_object* v_t_3648_ = stack[4].m_obj;
uint8_t v_res_3650_;
v_res_3650_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(lean_box(0), v_cmp_3645_, lean_box(0), v_k_3647_, v_t_3648_);
stack->m_num = v_res_3650_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3651_, lean_object* v_cmp_3652_, lean_object* v_00_u03b2_3653_, lean_object* v_k_3654_, lean_object* v_t_3655_){
_start:
{
uint8_t v_res_3656_; lean_object* v_r_3657_; 
v_res_3656_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1(v_00_u03b1_3651_, v_cmp_3652_, v_00_u03b2_3653_, v_k_3654_, v_t_3655_);
v_r_3657_ = lean_box(v_res_3656_);
return v_r_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2(lean_object* v_00_u03b1_3658_, lean_object* v_00_u03b2_3659_, lean_object* v_cmp_3660_, lean_object* v_init_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__2___redArg(v_cmp_3660_, v_init_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3(lean_object* v_00_u03b1_3664_, lean_object* v_00_u03b2_3665_, lean_object* v_cmp_3666_, lean_object* v_init_3667_, lean_object* v_x_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__3___redArg(v_cmp_3666_, v_init_3667_, v_x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion___redArg(lean_object* v_cmp_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3671_, 0, lean_box(0));
lean_closure_set(v___x_3671_, 1, lean_box(0));
lean_closure_set(v___x_3671_, 2, v_cmp_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instUnion(lean_object* v_00_u03b1_3672_, lean_object* v_00_u03b2_3673_, lean_object* v_cmp_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_union), 5, 3);
lean_closure_set(v___x_3675_, 0, lean_box(0));
lean_closure_set(v___x_3675_, 1, lean_box(0));
lean_closure_set(v___x_3675_, 2, v_cmp_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(lean_object* v_cmp_3676_, lean_object* v_k_3677_, lean_object* v_v_3678_, lean_object* v_t_3679_){
_start:
{
if (lean_obj_tag(v_t_3679_) == 0)
{
lean_object* v_size_3680_; lean_object* v_k_3681_; lean_object* v_v_3682_; lean_object* v_l_3683_; lean_object* v_r_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3965_; 
v_size_3680_ = lean_ctor_get(v_t_3679_, 0);
v_k_3681_ = lean_ctor_get(v_t_3679_, 1);
v_v_3682_ = lean_ctor_get(v_t_3679_, 2);
v_l_3683_ = lean_ctor_get(v_t_3679_, 3);
v_r_3684_ = lean_ctor_get(v_t_3679_, 4);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_t_3679_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3686_ = v_t_3679_;
v_isShared_3687_ = v_isSharedCheck_3965_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_r_3684_);
lean_inc(v_l_3683_);
lean_inc(v_v_3682_);
lean_inc(v_k_3681_);
lean_inc(v_size_3680_);
lean_dec(v_t_3679_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3965_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; uint8_t v___x_3689_; 
lean_inc_ref(v_cmp_3676_);
lean_inc(v_k_3681_);
lean_inc(v_k_3677_);
v___x_3688_ = lean_apply_2(v_cmp_3676_, v_k_3677_, v_k_3681_);
v___x_3689_ = lean_unbox(v___x_3688_);
switch(v___x_3689_)
{
case 0:
{
lean_object* v_impl_3690_; lean_object* v___x_3691_; 
lean_dec(v_size_3680_);
v_impl_3690_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3676_, v_k_3677_, v_v_3678_, v_l_3683_);
v___x_3691_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3684_) == 0)
{
lean_object* v_size_3692_; lean_object* v_size_3693_; lean_object* v_k_3694_; lean_object* v_v_3695_; lean_object* v_l_3696_; lean_object* v_r_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v_size_3692_ = lean_ctor_get(v_r_3684_, 0);
v_size_3693_ = lean_ctor_get(v_impl_3690_, 0);
v_k_3694_ = lean_ctor_get(v_impl_3690_, 1);
v_v_3695_ = lean_ctor_get(v_impl_3690_, 2);
v_l_3696_ = lean_ctor_get(v_impl_3690_, 3);
v_r_3697_ = lean_ctor_get(v_impl_3690_, 4);
lean_inc(v_r_3697_);
v___x_3698_ = lean_unsigned_to_nat(3u);
v___x_3699_ = lean_nat_mul(v___x_3698_, v_size_3692_);
v___x_3700_ = lean_nat_dec_lt(v___x_3699_, v_size_3693_);
lean_dec(v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
lean_dec(v_r_3697_);
v___x_3701_ = lean_nat_add(v___x_3691_, v_size_3693_);
v___x_3702_ = lean_nat_add(v___x_3701_, v_size_3692_);
lean_dec(v___x_3701_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 3, v_impl_3690_);
lean_ctor_set(v___x_3686_, 0, v___x_3702_);
v___x_3704_ = v___x_3686_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_impl_3690_);
lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_r_3684_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3771_; 
lean_inc(v_l_3696_);
lean_inc(v_v_3695_);
lean_inc(v_k_3694_);
lean_inc(v_size_3693_);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_impl_3690_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; lean_object* v_unused_3773_; lean_object* v_unused_3774_; lean_object* v_unused_3775_; lean_object* v_unused_3776_; 
v_unused_3772_ = lean_ctor_get(v_impl_3690_, 4);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_impl_3690_, 3);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_impl_3690_, 2);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_impl_3690_, 1);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v_impl_3690_, 0);
lean_dec(v_unused_3776_);
v___x_3707_ = v_impl_3690_;
v_isShared_3708_ = v_isSharedCheck_3771_;
goto v_resetjp_3706_;
}
else
{
lean_dec(v_impl_3690_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3771_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v_size_3709_; lean_object* v_size_3710_; lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v_l_3713_; lean_object* v_r_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v_size_3709_ = lean_ctor_get(v_l_3696_, 0);
v_size_3710_ = lean_ctor_get(v_r_3697_, 0);
v_k_3711_ = lean_ctor_get(v_r_3697_, 1);
v_v_3712_ = lean_ctor_get(v_r_3697_, 2);
v_l_3713_ = lean_ctor_get(v_r_3697_, 3);
v_r_3714_ = lean_ctor_get(v_r_3697_, 4);
v___x_3715_ = lean_unsigned_to_nat(2u);
v___x_3716_ = lean_nat_mul(v___x_3715_, v_size_3709_);
v___x_3717_ = lean_nat_dec_lt(v_size_3710_, v___x_3716_);
lean_dec(v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3746_; 
lean_inc(v_r_3714_);
lean_inc(v_l_3713_);
lean_inc(v_v_3712_);
lean_inc(v_k_3711_);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_r_3697_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; 
v_unused_3747_ = lean_ctor_get(v_r_3697_, 4);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_r_3697_, 3);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_r_3697_, 2);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_r_3697_, 1);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_r_3697_, 0);
lean_dec(v_unused_3751_);
v___x_3719_ = v_r_3697_;
v_isShared_3720_ = v_isSharedCheck_3746_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v_r_3697_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3746_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___x_3734_; lean_object* v___y_3736_; 
v___x_3721_ = lean_nat_add(v___x_3691_, v_size_3693_);
lean_dec(v_size_3693_);
v___x_3722_ = lean_nat_add(v___x_3721_, v_size_3692_);
lean_dec(v___x_3721_);
v___x_3734_ = lean_nat_add(v___x_3691_, v_size_3709_);
if (lean_obj_tag(v_l_3713_) == 0)
{
lean_object* v_size_3744_; 
v_size_3744_ = lean_ctor_get(v_l_3713_, 0);
lean_inc(v_size_3744_);
v___y_3736_ = v_size_3744_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_unsigned_to_nat(0u);
v___y_3736_ = v___x_3745_;
goto v___jp_3735_;
}
v___jp_3723_:
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3727_ = lean_nat_add(v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec(v___y_3725_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 4, v_r_3684_);
lean_ctor_set(v___x_3719_, 3, v_r_3714_);
lean_ctor_set(v___x_3719_, 2, v_v_3682_);
lean_ctor_set(v___x_3719_, 1, v_k_3681_);
lean_ctor_set(v___x_3719_, 0, v___x_3727_);
v___x_3729_ = v___x_3719_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_r_3714_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_r_3684_);
v___x_3729_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 4, v___x_3729_);
lean_ctor_set(v___x_3707_, 3, v___y_3724_);
lean_ctor_set(v___x_3707_, 2, v_v_3712_);
lean_ctor_set(v___x_3707_, 1, v_k_3711_);
lean_ctor_set(v___x_3707_, 0, v___x_3722_);
v___x_3731_ = v___x_3707_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v___y_3724_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
v___jp_3735_:
{
lean_object* v___x_3737_; lean_object* v___x_3739_; 
v___x_3737_ = lean_nat_add(v___x_3734_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec(v___x_3734_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_l_3713_);
lean_ctor_set(v___x_3686_, 3, v_l_3696_);
lean_ctor_set(v___x_3686_, 2, v_v_3695_);
lean_ctor_set(v___x_3686_, 1, v_k_3694_);
lean_ctor_set(v___x_3686_, 0, v___x_3737_);
v___x_3739_ = v___x_3686_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_k_3694_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_v_3695_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_l_3696_);
lean_ctor_set(v_reuseFailAlloc_3743_, 4, v_l_3713_);
v___x_3739_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_nat_add(v___x_3691_, v_size_3692_);
if (lean_obj_tag(v_r_3714_) == 0)
{
lean_object* v_size_3741_; 
v_size_3741_ = lean_ctor_get(v_r_3714_, 0);
lean_inc(v_size_3741_);
v___y_3724_ = v___x_3739_;
v___y_3725_ = v___x_3740_;
v___y_3726_ = v_size_3741_;
goto v___jp_3723_;
}
else
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_unsigned_to_nat(0u);
v___y_3724_ = v___x_3739_;
v___y_3725_ = v___x_3740_;
v___y_3726_ = v___x_3742_;
goto v___jp_3723_;
}
}
}
}
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_del_object(v___x_3686_);
v___x_3752_ = lean_nat_add(v___x_3691_, v_size_3693_);
lean_dec(v_size_3693_);
v___x_3753_ = lean_nat_add(v___x_3752_, v_size_3692_);
lean_dec(v___x_3752_);
v___x_3754_ = lean_nat_add(v___x_3691_, v_size_3692_);
v___x_3755_ = lean_nat_add(v___x_3754_, v_size_3710_);
lean_dec(v___x_3754_);
lean_inc_ref(v_r_3684_);
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 4, v_r_3684_);
lean_ctor_set(v___x_3707_, 3, v_r_3697_);
lean_ctor_set(v___x_3707_, 2, v_v_3682_);
lean_ctor_set(v___x_3707_, 1, v_k_3681_);
lean_ctor_set(v___x_3707_, 0, v___x_3755_);
v___x_3757_ = v___x_3707_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_r_3697_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_r_3684_);
v___x_3757_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
v_isSharedCheck_3764_ = !lean_is_exclusive(v_r_3684_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3765_ = lean_ctor_get(v_r_3684_, 4);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_r_3684_, 3);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_r_3684_, 2);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_r_3684_, 1);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_r_3684_, 0);
lean_dec(v_unused_3769_);
v___x_3759_ = v_r_3684_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_dec(v_r_3684_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 4, v___x_3757_);
lean_ctor_set(v___x_3759_, 3, v_l_3696_);
lean_ctor_set(v___x_3759_, 2, v_v_3695_);
lean_ctor_set(v___x_3759_, 1, v_k_3694_);
lean_ctor_set(v___x_3759_, 0, v___x_3753_);
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_k_3694_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_v_3695_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_l_3696_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v___x_3757_);
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
}
}
else
{
lean_object* v_l_3777_; 
v_l_3777_ = lean_ctor_get(v_impl_3690_, 3);
if (lean_obj_tag(v_l_3777_) == 0)
{
lean_object* v_r_3778_; lean_object* v_k_3779_; lean_object* v_v_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3791_; 
lean_inc_ref(v_l_3777_);
v_r_3778_ = lean_ctor_get(v_impl_3690_, 4);
v_k_3779_ = lean_ctor_get(v_impl_3690_, 1);
v_v_3780_ = lean_ctor_get(v_impl_3690_, 2);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_impl_3690_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; 
v_unused_3792_ = lean_ctor_get(v_impl_3690_, 3);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_impl_3690_, 0);
lean_dec(v_unused_3793_);
v___x_3782_ = v_impl_3690_;
v_isShared_3783_ = v_isSharedCheck_3791_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_r_3778_);
lean_inc(v_v_3780_);
lean_inc(v_k_3779_);
lean_dec(v_impl_3690_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3791_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3778_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 3, v_r_3778_);
lean_ctor_set(v___x_3782_, 2, v_v_3682_);
lean_ctor_set(v___x_3782_, 1, v_k_3681_);
lean_ctor_set(v___x_3782_, 0, v___x_3691_);
v___x_3786_ = v___x_3782_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_r_3778_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_r_3778_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v___x_3786_);
lean_ctor_set(v___x_3686_, 3, v_l_3777_);
lean_ctor_set(v___x_3686_, 2, v_v_3780_);
lean_ctor_set(v___x_3686_, 1, v_k_3779_);
lean_ctor_set(v___x_3686_, 0, v___x_3784_);
v___x_3788_ = v___x_3686_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3779_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3780_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_l_3777_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
else
{
lean_object* v_r_3794_; 
v_r_3794_ = lean_ctor_get(v_impl_3690_, 4);
lean_inc(v_r_3794_);
if (lean_obj_tag(v_r_3794_) == 0)
{
lean_object* v_k_3795_; lean_object* v_v_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3819_; 
lean_inc(v_l_3777_);
v_k_3795_ = lean_ctor_get(v_impl_3690_, 1);
v_v_3796_ = lean_ctor_get(v_impl_3690_, 2);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_impl_3690_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; lean_object* v_unused_3821_; lean_object* v_unused_3822_; 
v_unused_3820_ = lean_ctor_get(v_impl_3690_, 4);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_impl_3690_, 3);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v_impl_3690_, 0);
lean_dec(v_unused_3822_);
v___x_3798_ = v_impl_3690_;
v_isShared_3799_ = v_isSharedCheck_3819_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_v_3796_);
lean_inc(v_k_3795_);
lean_dec(v_impl_3690_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3819_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v_k_3800_; lean_object* v_v_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3815_; 
v_k_3800_ = lean_ctor_get(v_r_3794_, 1);
v_v_3801_ = lean_ctor_get(v_r_3794_, 2);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_r_3794_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; 
v_unused_3816_ = lean_ctor_get(v_r_3794_, 4);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_r_3794_, 3);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_r_3794_, 0);
lean_dec(v_unused_3818_);
v___x_3803_ = v_r_3794_;
v_isShared_3804_ = v_isSharedCheck_3815_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_v_3801_);
lean_inc(v_k_3800_);
lean_dec(v_r_3794_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3815_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = lean_unsigned_to_nat(3u);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 4, v_l_3777_);
lean_ctor_set(v___x_3803_, 3, v_l_3777_);
lean_ctor_set(v___x_3803_, 2, v_v_3796_);
lean_ctor_set(v___x_3803_, 1, v_k_3795_);
lean_ctor_set(v___x_3803_, 0, v___x_3691_);
v___x_3807_ = v___x_3803_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_k_3795_);
lean_ctor_set(v_reuseFailAlloc_3814_, 2, v_v_3796_);
lean_ctor_set(v_reuseFailAlloc_3814_, 3, v_l_3777_);
lean_ctor_set(v_reuseFailAlloc_3814_, 4, v_l_3777_);
v___x_3807_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3809_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 4, v_l_3777_);
lean_ctor_set(v___x_3798_, 2, v_v_3682_);
lean_ctor_set(v___x_3798_, 1, v_k_3681_);
lean_ctor_set(v___x_3798_, 0, v___x_3691_);
v___x_3809_ = v___x_3798_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_l_3777_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_l_3777_);
v___x_3809_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3811_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v___x_3809_);
lean_ctor_set(v___x_3686_, 3, v___x_3807_);
lean_ctor_set(v___x_3686_, 2, v_v_3801_);
lean_ctor_set(v___x_3686_, 1, v_k_3800_);
lean_ctor_set(v___x_3686_, 0, v___x_3805_);
v___x_3811_ = v___x_3686_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_k_3800_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_v_3801_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
else
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = lean_unsigned_to_nat(2u);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_r_3794_);
lean_ctor_set(v___x_3686_, 3, v_impl_3690_);
lean_ctor_set(v___x_3686_, 0, v___x_3823_);
v___x_3825_ = v___x_3686_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3826_, 3, v_impl_3690_);
lean_ctor_set(v_reuseFailAlloc_3826_, 4, v_r_3794_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3828_; 
lean_dec(v_v_3682_);
lean_dec(v_k_3681_);
lean_dec_ref(v_cmp_3676_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 2, v_v_3678_);
lean_ctor_set(v___x_3686_, 1, v_k_3677_);
v___x_3828_ = v___x_3686_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_size_3680_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_k_3677_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_v_3678_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_l_3683_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v_r_3684_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
default: 
{
lean_object* v_impl_3830_; lean_object* v___x_3831_; 
lean_dec(v_size_3680_);
v_impl_3830_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3676_, v_k_3677_, v_v_3678_, v_r_3684_);
v___x_3831_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3683_) == 0)
{
lean_object* v_size_3832_; lean_object* v_size_3833_; lean_object* v_k_3834_; lean_object* v_v_3835_; lean_object* v_l_3836_; lean_object* v_r_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_size_3832_ = lean_ctor_get(v_l_3683_, 0);
v_size_3833_ = lean_ctor_get(v_impl_3830_, 0);
v_k_3834_ = lean_ctor_get(v_impl_3830_, 1);
v_v_3835_ = lean_ctor_get(v_impl_3830_, 2);
v_l_3836_ = lean_ctor_get(v_impl_3830_, 3);
lean_inc(v_l_3836_);
v_r_3837_ = lean_ctor_get(v_impl_3830_, 4);
v___x_3838_ = lean_unsigned_to_nat(3u);
v___x_3839_ = lean_nat_mul(v___x_3838_, v_size_3832_);
v___x_3840_ = lean_nat_dec_lt(v___x_3839_, v_size_3833_);
lean_dec(v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_dec(v_l_3836_);
v___x_3841_ = lean_nat_add(v___x_3831_, v_size_3832_);
v___x_3842_ = lean_nat_add(v___x_3841_, v_size_3833_);
lean_dec(v___x_3841_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_impl_3830_);
lean_ctor_set(v___x_3686_, 0, v___x_3842_);
v___x_3844_ = v___x_3686_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v_l_3683_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_impl_3830_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
else
{
lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3909_; 
lean_inc(v_r_3837_);
lean_inc(v_v_3835_);
lean_inc(v_k_3834_);
lean_inc(v_size_3833_);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_impl_3830_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; lean_object* v_unused_3913_; lean_object* v_unused_3914_; 
v_unused_3910_ = lean_ctor_get(v_impl_3830_, 4);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_impl_3830_, 3);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_impl_3830_, 2);
lean_dec(v_unused_3912_);
v_unused_3913_ = lean_ctor_get(v_impl_3830_, 1);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_impl_3830_, 0);
lean_dec(v_unused_3914_);
v___x_3847_ = v_impl_3830_;
v_isShared_3848_ = v_isSharedCheck_3909_;
goto v_resetjp_3846_;
}
else
{
lean_dec(v_impl_3830_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3909_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_size_3849_; lean_object* v_k_3850_; lean_object* v_v_3851_; lean_object* v_l_3852_; lean_object* v_r_3853_; lean_object* v_size_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v_size_3849_ = lean_ctor_get(v_l_3836_, 0);
v_k_3850_ = lean_ctor_get(v_l_3836_, 1);
v_v_3851_ = lean_ctor_get(v_l_3836_, 2);
v_l_3852_ = lean_ctor_get(v_l_3836_, 3);
v_r_3853_ = lean_ctor_get(v_l_3836_, 4);
v_size_3854_ = lean_ctor_get(v_r_3837_, 0);
v___x_3855_ = lean_unsigned_to_nat(2u);
v___x_3856_ = lean_nat_mul(v___x_3855_, v_size_3854_);
v___x_3857_ = lean_nat_dec_lt(v_size_3849_, v___x_3856_);
lean_dec(v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3885_; 
lean_inc(v_r_3853_);
lean_inc(v_l_3852_);
lean_inc(v_v_3851_);
lean_inc(v_k_3850_);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_l_3836_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; 
v_unused_3886_ = lean_ctor_get(v_l_3836_, 4);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_l_3836_, 3);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_l_3836_, 2);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_l_3836_, 1);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_l_3836_, 0);
lean_dec(v_unused_3890_);
v___x_3859_ = v_l_3836_;
v_isShared_3860_ = v_isSharedCheck_3885_;
goto v_resetjp_3858_;
}
else
{
lean_dec(v_l_3836_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3885_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3875_; 
v___x_3861_ = lean_nat_add(v___x_3831_, v_size_3832_);
v___x_3862_ = lean_nat_add(v___x_3861_, v_size_3833_);
lean_dec(v_size_3833_);
if (lean_obj_tag(v_l_3852_) == 0)
{
lean_object* v_size_3883_; 
v_size_3883_ = lean_ctor_get(v_l_3852_, 0);
lean_inc(v_size_3883_);
v___y_3875_ = v_size_3883_;
goto v___jp_3874_;
}
else
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_unsigned_to_nat(0u);
v___y_3875_ = v___x_3884_;
goto v___jp_3874_;
}
v___jp_3863_:
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = lean_nat_add(v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec(v___y_3865_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_3837_);
lean_ctor_set(v___x_3859_, 3, v_r_3853_);
lean_ctor_set(v___x_3859_, 2, v_v_3835_);
lean_ctor_set(v___x_3859_, 1, v_k_3834_);
lean_ctor_set(v___x_3859_, 0, v___x_3867_);
v___x_3869_ = v___x_3859_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_k_3834_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_v_3835_);
lean_ctor_set(v_reuseFailAlloc_3873_, 3, v_r_3853_);
lean_ctor_set(v_reuseFailAlloc_3873_, 4, v_r_3837_);
v___x_3869_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3871_; 
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 4, v___x_3869_);
lean_ctor_set(v___x_3847_, 3, v___y_3864_);
lean_ctor_set(v___x_3847_, 2, v_v_3851_);
lean_ctor_set(v___x_3847_, 1, v_k_3850_);
lean_ctor_set(v___x_3847_, 0, v___x_3862_);
v___x_3871_ = v___x_3847_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3850_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3851_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v___y_3864_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
v___jp_3874_:
{
lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3876_ = lean_nat_add(v___x_3861_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec(v___x_3861_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_l_3852_);
lean_ctor_set(v___x_3686_, 0, v___x_3876_);
v___x_3878_ = v___x_3686_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_l_3683_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v_l_3852_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_nat_add(v___x_3831_, v_size_3854_);
if (lean_obj_tag(v_r_3853_) == 0)
{
lean_object* v_size_3880_; 
v_size_3880_ = lean_ctor_get(v_r_3853_, 0);
lean_inc(v_size_3880_);
v___y_3864_ = v___x_3878_;
v___y_3865_ = v___x_3879_;
v___y_3866_ = v_size_3880_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___y_3864_ = v___x_3878_;
v___y_3865_ = v___x_3879_;
v___y_3866_ = v___x_3881_;
goto v___jp_3863_;
}
}
}
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
lean_del_object(v___x_3686_);
v___x_3891_ = lean_nat_add(v___x_3831_, v_size_3832_);
v___x_3892_ = lean_nat_add(v___x_3891_, v_size_3833_);
lean_dec(v_size_3833_);
v___x_3893_ = lean_nat_add(v___x_3891_, v_size_3849_);
lean_dec(v___x_3891_);
lean_inc_ref(v_l_3683_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 4, v_l_3836_);
lean_ctor_set(v___x_3847_, 3, v_l_3683_);
lean_ctor_set(v___x_3847_, 2, v_v_3682_);
lean_ctor_set(v___x_3847_, 1, v_k_3681_);
lean_ctor_set(v___x_3847_, 0, v___x_3893_);
v___x_3895_ = v___x_3847_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_l_3683_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_l_3836_);
v___x_3895_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
v_isSharedCheck_3902_ = !lean_is_exclusive(v_l_3683_);
if (v_isSharedCheck_3902_ == 0)
{
lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; lean_object* v_unused_3907_; 
v_unused_3903_ = lean_ctor_get(v_l_3683_, 4);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_l_3683_, 3);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_l_3683_, 2);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_l_3683_, 1);
lean_dec(v_unused_3906_);
v_unused_3907_ = lean_ctor_get(v_l_3683_, 0);
lean_dec(v_unused_3907_);
v___x_3897_ = v_l_3683_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_dec(v_l_3683_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 4, v_r_3837_);
lean_ctor_set(v___x_3897_, 3, v___x_3895_);
lean_ctor_set(v___x_3897_, 2, v_v_3835_);
lean_ctor_set(v___x_3897_, 1, v_k_3834_);
lean_ctor_set(v___x_3897_, 0, v___x_3892_);
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3834_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3835_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_r_3837_);
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
else
{
lean_object* v_l_3915_; 
v_l_3915_ = lean_ctor_get(v_impl_3830_, 3);
lean_inc(v_l_3915_);
if (lean_obj_tag(v_l_3915_) == 0)
{
lean_object* v_r_3916_; lean_object* v_k_3917_; lean_object* v_v_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3941_; 
v_r_3916_ = lean_ctor_get(v_impl_3830_, 4);
v_k_3917_ = lean_ctor_get(v_impl_3830_, 1);
v_v_3918_ = lean_ctor_get(v_impl_3830_, 2);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_impl_3830_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; lean_object* v_unused_3943_; 
v_unused_3942_ = lean_ctor_get(v_impl_3830_, 3);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_impl_3830_, 0);
lean_dec(v_unused_3943_);
v___x_3920_ = v_impl_3830_;
v_isShared_3921_ = v_isSharedCheck_3941_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_r_3916_);
lean_inc(v_v_3918_);
lean_inc(v_k_3917_);
lean_dec(v_impl_3830_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3941_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v_k_3922_; lean_object* v_v_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3937_; 
v_k_3922_ = lean_ctor_get(v_l_3915_, 1);
v_v_3923_ = lean_ctor_get(v_l_3915_, 2);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_l_3915_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; 
v_unused_3938_ = lean_ctor_get(v_l_3915_, 4);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_l_3915_, 3);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_l_3915_, 0);
lean_dec(v_unused_3940_);
v___x_3925_ = v_l_3915_;
v_isShared_3926_ = v_isSharedCheck_3937_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_v_3923_);
lean_inc(v_k_3922_);
lean_dec(v_l_3915_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3937_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3916_, 2);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 4, v_r_3916_);
lean_ctor_set(v___x_3925_, 3, v_r_3916_);
lean_ctor_set(v___x_3925_, 2, v_v_3682_);
lean_ctor_set(v___x_3925_, 1, v_k_3681_);
lean_ctor_set(v___x_3925_, 0, v___x_3831_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_r_3916_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_r_3916_);
v___x_3929_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3931_; 
lean_inc(v_r_3916_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 3, v_r_3916_);
lean_ctor_set(v___x_3920_, 0, v___x_3831_);
v___x_3931_ = v___x_3920_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_k_3917_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_v_3918_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v_r_3916_);
lean_ctor_set(v_reuseFailAlloc_3935_, 4, v_r_3916_);
v___x_3931_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3933_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v___x_3931_);
lean_ctor_set(v___x_3686_, 3, v___x_3929_);
lean_ctor_set(v___x_3686_, 2, v_v_3923_);
lean_ctor_set(v___x_3686_, 1, v_k_3922_);
lean_ctor_set(v___x_3686_, 0, v___x_3927_);
v___x_3933_ = v___x_3686_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_k_3922_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_v_3923_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v___x_3931_);
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
else
{
lean_object* v_r_3944_; 
v_r_3944_ = lean_ctor_get(v_impl_3830_, 4);
lean_inc(v_r_3944_);
if (lean_obj_tag(v_r_3944_) == 0)
{
lean_object* v_k_3945_; lean_object* v_v_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3957_; 
v_k_3945_ = lean_ctor_get(v_impl_3830_, 1);
v_v_3946_ = lean_ctor_get(v_impl_3830_, 2);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_impl_3830_);
if (v_isSharedCheck_3957_ == 0)
{
lean_object* v_unused_3958_; lean_object* v_unused_3959_; lean_object* v_unused_3960_; 
v_unused_3958_ = lean_ctor_get(v_impl_3830_, 4);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_impl_3830_, 3);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_impl_3830_, 0);
lean_dec(v_unused_3960_);
v___x_3948_ = v_impl_3830_;
v_isShared_3949_ = v_isSharedCheck_3957_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_v_3946_);
lean_inc(v_k_3945_);
lean_dec(v_impl_3830_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3957_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3950_ = lean_unsigned_to_nat(3u);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 4, v_l_3915_);
lean_ctor_set(v___x_3948_, 2, v_v_3682_);
lean_ctor_set(v___x_3948_, 1, v_k_3681_);
lean_ctor_set(v___x_3948_, 0, v___x_3831_);
v___x_3952_ = v___x_3948_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3956_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3956_, 3, v_l_3915_);
lean_ctor_set(v_reuseFailAlloc_3956_, 4, v_l_3915_);
v___x_3952_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3954_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_r_3944_);
lean_ctor_set(v___x_3686_, 3, v___x_3952_);
lean_ctor_set(v___x_3686_, 2, v_v_3946_);
lean_ctor_set(v___x_3686_, 1, v_k_3945_);
lean_ctor_set(v___x_3686_, 0, v___x_3950_);
v___x_3954_ = v___x_3686_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_k_3945_);
lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_v_3946_);
lean_ctor_set(v_reuseFailAlloc_3955_, 3, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3955_, 4, v_r_3944_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3961_ = lean_unsigned_to_nat(2u);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_impl_3830_);
lean_ctor_set(v___x_3686_, 3, v_r_3944_);
lean_ctor_set(v___x_3686_, 0, v___x_3961_);
v___x_3963_ = v___x_3686_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_r_3944_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_impl_3830_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
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
lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec_ref(v_cmp_3676_);
v___x_3966_ = lean_unsigned_to_nat(1u);
v___x_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
lean_ctor_set(v___x_3967_, 1, v_k_3677_);
lean_ctor_set(v___x_3967_, 2, v_v_3678_);
lean_ctor_set(v___x_3967_, 3, v_t_3679_);
lean_ctor_set(v___x_3967_, 4, v_t_3679_);
return v___x_3967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_3968_, lean_object* v_t_3969_, lean_object* v_k_3970_){
_start:
{
if (lean_obj_tag(v_t_3969_) == 0)
{
lean_object* v_k_3971_; lean_object* v_v_3972_; lean_object* v_l_3973_; lean_object* v_r_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v_k_3971_ = lean_ctor_get(v_t_3969_, 1);
lean_inc_n(v_k_3971_, 2);
v_v_3972_ = lean_ctor_get(v_t_3969_, 2);
lean_inc(v_v_3972_);
v_l_3973_ = lean_ctor_get(v_t_3969_, 3);
lean_inc(v_l_3973_);
v_r_3974_ = lean_ctor_get(v_t_3969_, 4);
lean_inc(v_r_3974_);
lean_dec_ref_known(v_t_3969_, 5);
lean_inc_ref(v_cmp_3968_);
lean_inc(v_k_3970_);
v___x_3975_ = lean_apply_2(v_cmp_3968_, v_k_3970_, v_k_3971_);
v___x_3976_ = lean_unbox(v___x_3975_);
switch(v___x_3976_)
{
case 0:
{
lean_dec(v_r_3974_);
lean_dec(v_v_3972_);
lean_dec(v_k_3971_);
v_t_3969_ = v_l_3973_;
goto _start;
}
case 1:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_dec(v_r_3974_);
lean_dec(v_l_3973_);
lean_dec(v_k_3970_);
lean_dec_ref(v_cmp_3968_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_k_3971_);
lean_ctor_set(v___x_3978_, 1, v_v_3972_);
v___x_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
default: 
{
lean_dec(v_l_3973_);
lean_dec(v_v_3972_);
lean_dec(v_k_3971_);
v_t_3969_ = v_r_3974_;
goto _start;
}
}
}
else
{
lean_object* v___x_3981_; 
lean_dec(v_k_3970_);
lean_dec_ref(v_cmp_3968_);
v___x_3981_ = lean_box(0);
return v___x_3981_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_cmp_3982_, lean_object* v_m_u2081_3983_, lean_object* v_init_3984_, lean_object* v_x_3985_){
_start:
{
if (lean_obj_tag(v_x_3985_) == 0)
{
lean_object* v_k_3986_; lean_object* v_l_3987_; lean_object* v_r_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_k_3986_ = lean_ctor_get(v_x_3985_, 1);
lean_inc(v_k_3986_);
v_l_3987_ = lean_ctor_get(v_x_3985_, 3);
lean_inc(v_l_3987_);
v_r_3988_ = lean_ctor_get(v_x_3985_, 4);
lean_inc(v_r_3988_);
lean_dec_ref_known(v_x_3985_, 5);
lean_inc_n(v_m_u2081_3983_, 2);
lean_inc_ref_n(v_cmp_3982_, 2);
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3982_, v_m_u2081_3983_, v_init_3984_, v_l_3987_);
v___x_3990_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_3982_, v_m_u2081_3983_, v_k_3986_);
if (lean_obj_tag(v___x_3990_) == 0)
{
v_init_3984_ = v___x_3989_;
v_x_3985_ = v_r_3988_;
goto _start;
}
else
{
lean_object* v_val_3992_; lean_object* v_fst_3993_; lean_object* v_snd_3994_; lean_object* v_impl_3995_; 
v_val_3992_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_val_3992_);
lean_dec_ref_known(v___x_3990_, 1);
v_fst_3993_ = lean_ctor_get(v_val_3992_, 0);
lean_inc(v_fst_3993_);
v_snd_3994_ = lean_ctor_get(v_val_3992_, 1);
lean_inc(v_snd_3994_);
lean_dec(v_val_3992_);
lean_inc_ref(v_cmp_3982_);
v_impl_3995_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_3982_, v_fst_3993_, v_snd_3994_, v___x_3989_);
v_init_3984_ = v_impl_3995_;
v_x_3985_ = v_r_3988_;
goto _start;
}
}
else
{
lean_dec(v_m_u2081_3983_);
lean_dec_ref(v_cmp_3982_);
return v_init_3984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(lean_object* v_cmp_3997_, lean_object* v_m_u2081_3998_, lean_object* v_m_u2082_3999_){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_box(1);
v___x_4001_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_3997_, v_m_u2081_3998_, v___x_4000_, v_m_u2082_3999_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(lean_object* v_cmp_4002_, lean_object* v_m_u2082_4003_, lean_object* v_t_4004_){
_start:
{
if (lean_obj_tag(v_t_4004_) == 0)
{
lean_object* v_k_4005_; lean_object* v_v_4006_; lean_object* v_l_4007_; lean_object* v_r_4008_; uint8_t v___x_4009_; 
v_k_4005_ = lean_ctor_get(v_t_4004_, 1);
lean_inc_n(v_k_4005_, 2);
v_v_4006_ = lean_ctor_get(v_t_4004_, 2);
lean_inc(v_v_4006_);
v_l_4007_ = lean_ctor_get(v_t_4004_, 3);
lean_inc(v_l_4007_);
v_r_4008_ = lean_ctor_get(v_t_4004_, 4);
lean_inc(v_r_4008_);
lean_dec_ref_known(v_t_4004_, 5);
lean_inc(v_m_u2082_4003_);
lean_inc_ref(v_cmp_4002_);
v___x_4009_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_4002_, v_k_4005_, v_m_u2082_4003_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec(v_v_4006_);
lean_dec(v_k_4005_);
lean_inc(v_m_u2082_4003_);
lean_inc_ref(v_cmp_4002_);
v___x_4010_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4002_, v_m_u2082_4003_, v_l_4007_);
v___x_4011_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4002_, v_m_u2082_4003_, v_r_4008_);
v___x_4012_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_4010_, v___x_4011_);
return v___x_4012_;
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_inc(v_m_u2082_4003_);
lean_inc_ref(v_cmp_4002_);
v___x_4013_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4002_, v_m_u2082_4003_, v_l_4007_);
v___x_4014_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4002_, v_m_u2082_4003_, v_r_4008_);
v___x_4015_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_4005_, v_v_4006_, v___x_4013_, v___x_4014_);
return v___x_4015_;
}
}
else
{
lean_dec(v_m_u2082_4003_);
lean_dec_ref(v_cmp_4002_);
return v_t_4004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(lean_object* v_cmp_4016_, lean_object* v_m_u2081_4017_, lean_object* v_m_u2082_4018_){
_start:
{
lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4026_; 
if (lean_obj_tag(v_m_u2081_4017_) == 0)
{
lean_object* v_size_4029_; 
v_size_4029_ = lean_ctor_get(v_m_u2081_4017_, 0);
lean_inc(v_size_4029_);
v___y_4026_ = v_size_4029_;
goto v___jp_4025_;
}
else
{
lean_object* v___x_4030_; 
v___x_4030_ = lean_unsigned_to_nat(0u);
v___y_4026_ = v___x_4030_;
goto v___jp_4025_;
}
v___jp_4019_:
{
uint8_t v___x_4022_; 
v___x_4022_ = lean_nat_dec_le(v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec(v___y_4020_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_4016_, v_m_u2081_4017_, v_m_u2082_4018_);
return v___x_4023_;
}
else
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4016_, v_m_u2082_4018_, v_m_u2081_4017_);
return v___x_4024_;
}
}
v___jp_4025_:
{
if (lean_obj_tag(v_m_u2082_4018_) == 0)
{
lean_object* v_size_4027_; 
v_size_4027_ = lean_ctor_get(v_m_u2082_4018_, 0);
lean_inc(v_size_4027_);
v___y_4020_ = v___y_4026_;
v___y_4021_ = v_size_4027_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4028_; 
v___x_4028_ = lean_unsigned_to_nat(0u);
v___y_4020_ = v___y_4026_;
v___y_4021_ = v___x_4028_;
goto v___jp_4019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter___redArg(lean_object* v_cmp_4031_, lean_object* v_t_u2081_4032_, lean_object* v_t_u2082_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4031_, v_t_u2081_4032_, v_t_u2082_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_inter(lean_object* v_00_u03b1_4035_, lean_object* v_00_u03b2_4036_, lean_object* v_cmp_4037_, lean_object* v_t_u2081_4038_, lean_object* v_t_u2082_4039_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4037_, v_t_u2081_4038_, v_t_u2082_4039_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0(lean_object* v_00_u03b1_4041_, lean_object* v_cmp_4042_, lean_object* v_00_u03b2_4043_, lean_object* v_m_u2081_4044_, lean_object* v_m_u2082_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0___redArg(v_cmp_4042_, v_m_u2081_4044_, v_m_u2082_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0(lean_object* v_00_u03b1_4047_, lean_object* v_cmp_4048_, lean_object* v_00_u03b2_4049_, lean_object* v_m_u2081_4050_, lean_object* v_m_u2082_4051_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0___redArg(v_cmp_4048_, v_m_u2081_4050_, v_m_u2082_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1(lean_object* v_00_u03b1_4053_, lean_object* v_00_u03b2_4054_, lean_object* v_cmp_4055_, lean_object* v_m_u2082_4056_, lean_object* v_t_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__1___redArg(v_cmp_4055_, v_m_u2082_4056_, v_t_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4059_, lean_object* v_cmp_4060_, lean_object* v_00_u03b2_4061_, lean_object* v_t_4062_, lean_object* v_k_4063_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__1___redArg(v_cmp_4060_, v_t_4062_, v_k_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_4065_, lean_object* v_cmp_4066_, lean_object* v_00_u03b2_4067_, lean_object* v_k_4068_, lean_object* v_v_4069_, lean_object* v_t_4070_, lean_object* v_hl_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__2___redArg(v_cmp_4066_, v_k_4068_, v_v_4069_, v_t_4070_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3___redArg(lean_object* v_cmp_4073_, lean_object* v_m_u2081_4074_, lean_object* v_init_4075_, lean_object* v_t_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4073_, v_m_u2081_4074_, v_init_4075_, v_t_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4078_, lean_object* v_00_u03b2_4079_, lean_object* v_cmp_4080_, lean_object* v_m_u2081_4081_, lean_object* v_init_4082_, lean_object* v_t_4083_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4080_, v_m_u2081_4081_, v_init_4082_, v_t_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b1_4085_, lean_object* v_00_u03b2_4086_, lean_object* v_cmp_4087_, lean_object* v_m_u2081_4088_, lean_object* v_init_4089_, lean_object* v_x_4090_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Std_DTreeMap_Internal_Impl_interSmaller___at___00Std_DTreeMap_Internal_Impl_inter_x21___at___00Std_DTreeMap_Raw_inter_spec__0_spec__0_spec__3_spec__4___redArg(v_cmp_4087_, v_m_u2081_4088_, v_init_4089_, v_x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter___redArg(lean_object* v_cmp_4092_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4093_, 0, lean_box(0));
lean_closure_set(v___x_4093_, 1, lean_box(0));
lean_closure_set(v___x_4093_, 2, v_cmp_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instInter(lean_object* v_00_u03b1_4094_, lean_object* v_00_u03b2_4095_, lean_object* v_cmp_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_inter), 5, 3);
lean_closure_set(v___x_4097_, 0, lean_box(0));
lean_closure_set(v___x_4097_, 1, lean_box(0));
lean_closure_set(v___x_4097_, 2, v_cmp_4096_);
return v___x_4097_;
}
}
uint8_t l_Std_DTreeMap_Raw_beq___redArg(lean_object* v_cmp_4098_, lean_object* v_inst_4099_, lean_object* v_t_u2081_4100_, lean_object* v_t_u2082_4101_){
_start:
{
uint8_t v___x_4102_; 
v___x_4102_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4098_, v_inst_4099_, v_t_u2081_4100_, v_t_u2082_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_4098_ = stack[0].m_obj;
lean_object* v_inst_4099_ = stack[1].m_obj;
lean_object* v_t_u2081_4100_ = stack[2].m_obj;
lean_object* v_t_u2082_4101_ = stack[3].m_obj;
uint8_t v_res_4103_;
v_res_4103_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_4098_, v_inst_4099_, v_t_u2081_4100_, v_t_u2082_4101_);
stack->m_num = v_res_4103_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___redArg___boxed(lean_object* v_cmp_4104_, lean_object* v_inst_4105_, lean_object* v_t_u2081_4106_, lean_object* v_t_u2082_4107_){
_start:
{
uint8_t v_res_4108_; lean_object* v_r_4109_; 
v_res_4108_ = l_Std_DTreeMap_Raw_beq___redArg(v_cmp_4104_, v_inst_4105_, v_t_u2081_4106_, v_t_u2082_4107_);
v_r_4109_ = lean_box(v_res_4108_);
return v_r_4109_;
}
}
uint8_t l_Std_DTreeMap_Raw_beq(lean_object* v_00_u03b1_4110_, lean_object* v_00_u03b2_4111_, lean_object* v_cmp_4112_, lean_object* v_inst_4113_, lean_object* v_inst_4114_, lean_object* v_t_u2081_4115_, lean_object* v_t_u2082_4116_){
_start:
{
uint8_t v___x_4117_; 
v___x_4117_ = l_Std_DTreeMap_Internal_Impl_beq___redArg(v_cmp_4112_, v_inst_4114_, v_t_u2081_4115_, v_t_u2082_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_4112_ = stack[2].m_obj;
lean_object* v_inst_4114_ = stack[4].m_obj;
lean_object* v_t_u2081_4115_ = stack[5].m_obj;
lean_object* v_t_u2082_4116_ = stack[6].m_obj;
uint8_t v_res_4118_;
v_res_4118_ = l_Std_DTreeMap_Raw_beq(lean_box(0), lean_box(0), v_cmp_4112_, lean_box(0), v_inst_4114_, v_t_u2081_4115_, v_t_u2082_4116_);
stack->m_num = v_res_4118_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_beq___boxed(lean_object* v_00_u03b1_4119_, lean_object* v_00_u03b2_4120_, lean_object* v_cmp_4121_, lean_object* v_inst_4122_, lean_object* v_inst_4123_, lean_object* v_t_u2081_4124_, lean_object* v_t_u2082_4125_){
_start:
{
uint8_t v_res_4126_; lean_object* v_r_4127_; 
v_res_4126_ = l_Std_DTreeMap_Raw_beq(v_00_u03b1_4119_, v_00_u03b2_4120_, v_cmp_4121_, v_inst_4122_, v_inst_4123_, v_t_u2081_4124_, v_t_u2082_4125_);
v_r_4127_ = lean_box(v_res_4126_);
return v_r_4127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp___redArg(lean_object* v_cmp_4128_, lean_object* v_inst_4129_){
_start:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4130_, 0, lean_box(0));
lean_closure_set(v___x_4130_, 1, lean_box(0));
lean_closure_set(v___x_4130_, 2, v_cmp_4128_);
lean_closure_set(v___x_4130_, 3, lean_box(0));
lean_closure_set(v___x_4130_, 4, v_inst_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instBEqOfLawfulEqCmp(lean_object* v_00_u03b1_4131_, lean_object* v_00_u03b2_4132_, lean_object* v_cmp_4133_, lean_object* v_inst_4134_, lean_object* v_inst_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_4136_, 0, lean_box(0));
lean_closure_set(v___x_4136_, 1, lean_box(0));
lean_closure_set(v___x_4136_, 2, v_cmp_4133_);
lean_closure_set(v___x_4136_, 3, lean_box(0));
lean_closure_set(v___x_4136_, 4, v_inst_4135_);
return v___x_4136_;
}
}
uint8_t l_Std_DTreeMap_Raw_Const_beq___redArg(lean_object* v_cmp_4137_, lean_object* v_inst_4138_, lean_object* v_t_u2081_4139_, lean_object* v_t_u2082_4140_){
_start:
{
uint8_t v___x_4141_; 
v___x_4141_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4137_, v_inst_4138_, v_t_u2081_4139_, v_t_u2082_4140_);
return v___x_4141_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_Const_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_4137_ = stack[0].m_obj;
lean_object* v_inst_4138_ = stack[1].m_obj;
lean_object* v_t_u2081_4139_ = stack[2].m_obj;
lean_object* v_t_u2082_4140_ = stack[3].m_obj;
uint8_t v_res_4142_;
v_res_4142_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_4137_, v_inst_4138_, v_t_u2081_4139_, v_t_u2082_4140_);
stack->m_num = v_res_4142_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___redArg___boxed(lean_object* v_cmp_4143_, lean_object* v_inst_4144_, lean_object* v_t_u2081_4145_, lean_object* v_t_u2082_4146_){
_start:
{
uint8_t v_res_4147_; lean_object* v_r_4148_; 
v_res_4147_ = l_Std_DTreeMap_Raw_Const_beq___redArg(v_cmp_4143_, v_inst_4144_, v_t_u2081_4145_, v_t_u2082_4146_);
v_r_4148_ = lean_box(v_res_4147_);
return v_r_4148_;
}
}
uint8_t l_Std_DTreeMap_Raw_Const_beq(lean_object* v_00_u03b1_4149_, lean_object* v_cmp_4150_, lean_object* v_00_u03b2_4151_, lean_object* v_inst_4152_, lean_object* v_t_u2081_4153_, lean_object* v_t_u2082_4154_){
_start:
{
uint8_t v___x_4155_; 
v___x_4155_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v_cmp_4150_, v_inst_4152_, v_t_u2081_4153_, v_t_u2082_4154_);
return v___x_4155_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Raw_Const_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_4150_ = stack[1].m_obj;
lean_object* v_inst_4152_ = stack[3].m_obj;
lean_object* v_t_u2081_4153_ = stack[4].m_obj;
lean_object* v_t_u2082_4154_ = stack[5].m_obj;
uint8_t v_res_4156_;
v_res_4156_ = l_Std_DTreeMap_Raw_Const_beq(lean_box(0), v_cmp_4150_, lean_box(0), v_inst_4152_, v_t_u2081_4153_, v_t_u2082_4154_);
stack->m_num = v_res_4156_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_4157_, lean_object* v_cmp_4158_, lean_object* v_00_u03b2_4159_, lean_object* v_inst_4160_, lean_object* v_t_u2081_4161_, lean_object* v_t_u2082_4162_){
_start:
{
uint8_t v_res_4163_; lean_object* v_r_4164_; 
v_res_4163_ = l_Std_DTreeMap_Raw_Const_beq(v_00_u03b1_4157_, v_cmp_4158_, v_00_u03b2_4159_, v_inst_4160_, v_t_u2081_4161_, v_t_u2082_4162_);
v_r_4164_ = lean_box(v_res_4163_);
return v_r_4164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(lean_object* v_cmp_4165_, lean_object* v_t_u2082_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v_t_4169_){
_start:
{
if (lean_obj_tag(v_t_4169_) == 0)
{
lean_object* v_k_4170_; lean_object* v_v_4171_; lean_object* v_l_4172_; lean_object* v_r_4173_; uint8_t v___x_4178_; 
v_k_4170_ = lean_ctor_get(v_t_4169_, 1);
lean_inc_n(v_k_4170_, 2);
v_v_4171_ = lean_ctor_get(v_t_4169_, 2);
lean_inc(v_v_4171_);
v_l_4172_ = lean_ctor_get(v_t_4169_, 3);
lean_inc(v_l_4172_);
v_r_4173_ = lean_ctor_get(v_t_4169_, 4);
lean_inc(v_r_4173_);
lean_dec_ref_known(v_t_4169_, 5);
lean_inc(v_t_u2082_4166_);
lean_inc_ref(v_cmp_4165_);
v___x_4178_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__1___redArg(v_cmp_4165_, v_k_4170_, v_t_u2082_4166_);
if (v___x_4178_ == 0)
{
uint8_t v___x_4179_; 
v___x_4179_ = lean_nat_dec_le(v___y_4167_, v___y_4168_);
if (v___x_4179_ == 0)
{
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
goto v___jp_4174_;
}
else
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_inc(v_t_u2082_4166_);
lean_inc_ref(v_cmp_4165_);
v___x_4180_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4165_, v_t_u2082_4166_, v___y_4167_, v___y_4168_, v_l_4172_);
v___x_4181_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4165_, v_t_u2082_4166_, v___y_4167_, v___y_4168_, v_r_4173_);
v___x_4182_ = l_Std_DTreeMap_Internal_Impl_link_x21___redArg(v_k_4170_, v_v_4171_, v___x_4180_, v___x_4181_);
return v___x_4182_;
}
}
else
{
lean_dec(v_v_4171_);
lean_dec(v_k_4170_);
goto v___jp_4174_;
}
v___jp_4174_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
lean_inc(v_t_u2082_4166_);
lean_inc_ref(v_cmp_4165_);
v___x_4175_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4165_, v_t_u2082_4166_, v___y_4167_, v___y_4168_, v_l_4172_);
v___x_4176_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4165_, v_t_u2082_4166_, v___y_4167_, v___y_4168_, v_r_4173_);
v___x_4177_ = l_Std_DTreeMap_Internal_Impl_link2_x21___redArg(v___x_4175_, v___x_4176_);
return v___x_4177_;
}
}
else
{
lean_dec(v_t_u2082_4166_);
lean_dec_ref(v_cmp_4165_);
return v_t_4169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg___boxed(lean_object* v_cmp_4183_, lean_object* v_t_u2082_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v_t_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4183_, v_t_u2082_4184_, v___y_4185_, v___y_4186_, v_t_4187_);
lean_dec(v___y_4186_);
lean_dec(v___y_4185_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(lean_object* v_cmp_4189_, lean_object* v_k_4190_, lean_object* v_t_4191_){
_start:
{
if (lean_obj_tag(v_t_4191_) == 0)
{
lean_object* v_k_4192_; lean_object* v_v_4193_; lean_object* v_l_4194_; lean_object* v_r_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4885_; 
v_k_4192_ = lean_ctor_get(v_t_4191_, 1);
v_v_4193_ = lean_ctor_get(v_t_4191_, 2);
v_l_4194_ = lean_ctor_get(v_t_4191_, 3);
v_r_4195_ = lean_ctor_get(v_t_4191_, 4);
v_isSharedCheck_4885_ = !lean_is_exclusive(v_t_4191_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; 
v_unused_4886_ = lean_ctor_get(v_t_4191_, 0);
lean_dec(v_unused_4886_);
v___x_4197_ = v_t_4191_;
v_isShared_4198_ = v_isSharedCheck_4885_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_r_4195_);
lean_inc(v_l_4194_);
lean_inc(v_v_4193_);
lean_inc(v_k_4192_);
lean_dec(v_t_4191_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4885_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; uint8_t v___x_4200_; 
lean_inc_ref(v_cmp_4189_);
lean_inc(v_k_4192_);
lean_inc(v_k_4190_);
v___x_4199_ = lean_apply_2(v_cmp_4189_, v_k_4190_, v_k_4192_);
v___x_4200_ = lean_unbox(v___x_4199_);
switch(v___x_4200_)
{
case 0:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4189_, v_k_4190_, v_l_4194_);
if (lean_obj_tag(v___x_4201_) == 0)
{
if (lean_obj_tag(v_r_4195_) == 0)
{
lean_object* v_size_4202_; lean_object* v_size_4203_; lean_object* v_k_4204_; lean_object* v_v_4205_; lean_object* v_l_4206_; lean_object* v_r_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v_size_4202_ = lean_ctor_get(v___x_4201_, 0);
v_size_4203_ = lean_ctor_get(v_r_4195_, 0);
v_k_4204_ = lean_ctor_get(v_r_4195_, 1);
v_v_4205_ = lean_ctor_get(v_r_4195_, 2);
v_l_4206_ = lean_ctor_get(v_r_4195_, 3);
lean_inc(v_l_4206_);
v_r_4207_ = lean_ctor_get(v_r_4195_, 4);
v___x_4208_ = lean_unsigned_to_nat(3u);
v___x_4209_ = lean_nat_mul(v___x_4208_, v_size_4202_);
v___x_4210_ = lean_nat_dec_lt(v___x_4209_, v_size_4203_);
lean_dec(v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_dec(v_l_4206_);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_nat_add(v___x_4211_, v_size_4202_);
v___x_4213_ = lean_nat_add(v___x_4212_, v_size_4203_);
lean_dec(v___x_4212_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 3, v___x_4201_);
lean_ctor_set(v___x_4197_, 0, v___x_4213_);
v___x_4215_ = v___x_4197_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v_r_4195_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4286_; 
lean_inc(v_r_4207_);
lean_inc(v_v_4205_);
lean_inc(v_k_4204_);
lean_inc(v_size_4203_);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; lean_object* v_unused_4288_; lean_object* v_unused_4289_; lean_object* v_unused_4290_; lean_object* v_unused_4291_; 
v_unused_4287_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4287_);
v_unused_4288_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4288_);
v_unused_4289_ = lean_ctor_get(v_r_4195_, 2);
lean_dec(v_unused_4289_);
v_unused_4290_ = lean_ctor_get(v_r_4195_, 1);
lean_dec(v_unused_4290_);
v_unused_4291_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4291_);
v___x_4218_ = v_r_4195_;
v_isShared_4219_ = v_isSharedCheck_4286_;
goto v_resetjp_4217_;
}
else
{
lean_dec(v_r_4195_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4286_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
if (lean_obj_tag(v_l_4206_) == 0)
{
if (lean_obj_tag(v_r_4207_) == 0)
{
lean_object* v_size_4220_; lean_object* v_k_4221_; lean_object* v_v_4222_; lean_object* v_l_4223_; lean_object* v_r_4224_; lean_object* v_size_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v_size_4220_ = lean_ctor_get(v_l_4206_, 0);
v_k_4221_ = lean_ctor_get(v_l_4206_, 1);
v_v_4222_ = lean_ctor_get(v_l_4206_, 2);
v_l_4223_ = lean_ctor_get(v_l_4206_, 3);
v_r_4224_ = lean_ctor_get(v_l_4206_, 4);
v_size_4225_ = lean_ctor_get(v_r_4207_, 0);
v___x_4226_ = lean_unsigned_to_nat(2u);
v___x_4227_ = lean_nat_mul(v___x_4226_, v_size_4225_);
v___x_4228_ = lean_nat_dec_lt(v_size_4220_, v___x_4227_);
lean_dec(v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4257_; 
lean_inc(v_r_4224_);
lean_inc(v_l_4223_);
lean_inc(v_v_4222_);
lean_inc(v_k_4221_);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_l_4206_);
if (v_isSharedCheck_4257_ == 0)
{
lean_object* v_unused_4258_; lean_object* v_unused_4259_; lean_object* v_unused_4260_; lean_object* v_unused_4261_; lean_object* v_unused_4262_; 
v_unused_4258_ = lean_ctor_get(v_l_4206_, 4);
lean_dec(v_unused_4258_);
v_unused_4259_ = lean_ctor_get(v_l_4206_, 3);
lean_dec(v_unused_4259_);
v_unused_4260_ = lean_ctor_get(v_l_4206_, 2);
lean_dec(v_unused_4260_);
v_unused_4261_ = lean_ctor_get(v_l_4206_, 1);
lean_dec(v_unused_4261_);
v_unused_4262_ = lean_ctor_get(v_l_4206_, 0);
lean_dec(v_unused_4262_);
v___x_4230_ = v_l_4206_;
v_isShared_4231_ = v_isSharedCheck_4257_;
goto v_resetjp_4229_;
}
else
{
lean_dec(v_l_4206_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4257_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4247_; 
v___x_4232_ = lean_unsigned_to_nat(1u);
v___x_4233_ = lean_nat_add(v___x_4232_, v_size_4202_);
v___x_4234_ = lean_nat_add(v___x_4233_, v_size_4203_);
lean_dec(v_size_4203_);
if (lean_obj_tag(v_l_4223_) == 0)
{
lean_object* v_size_4255_; 
v_size_4255_ = lean_ctor_get(v_l_4223_, 0);
lean_inc(v_size_4255_);
v___y_4247_ = v_size_4255_;
goto v___jp_4246_;
}
else
{
lean_object* v___x_4256_; 
v___x_4256_ = lean_unsigned_to_nat(0u);
v___y_4247_ = v___x_4256_;
goto v___jp_4246_;
}
v___jp_4235_:
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4239_ = lean_nat_add(v___y_4236_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec(v___y_4236_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 4, v_r_4207_);
lean_ctor_set(v___x_4230_, 3, v_r_4224_);
lean_ctor_set(v___x_4230_, 2, v_v_4205_);
lean_ctor_set(v___x_4230_, 1, v_k_4204_);
lean_ctor_set(v___x_4230_, 0, v___x_4239_);
v___x_4241_ = v___x_4230_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v_k_4204_);
lean_ctor_set(v_reuseFailAlloc_4245_, 2, v_v_4205_);
lean_ctor_set(v_reuseFailAlloc_4245_, 3, v_r_4224_);
lean_ctor_set(v_reuseFailAlloc_4245_, 4, v_r_4207_);
v___x_4241_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4243_; 
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 4, v___x_4241_);
lean_ctor_set(v___x_4218_, 3, v___y_4237_);
lean_ctor_set(v___x_4218_, 2, v_v_4222_);
lean_ctor_set(v___x_4218_, 1, v_k_4221_);
lean_ctor_set(v___x_4218_, 0, v___x_4234_);
v___x_4243_ = v___x_4218_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_k_4221_);
lean_ctor_set(v_reuseFailAlloc_4244_, 2, v_v_4222_);
lean_ctor_set(v_reuseFailAlloc_4244_, 3, v___y_4237_);
lean_ctor_set(v_reuseFailAlloc_4244_, 4, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
v___jp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = lean_nat_add(v___x_4233_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec(v___x_4233_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v_l_4223_);
lean_ctor_set(v___x_4197_, 3, v___x_4201_);
lean_ctor_set(v___x_4197_, 0, v___x_4248_);
v___x_4250_ = v___x_4197_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4248_);
lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4254_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4254_, 3, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4254_, 4, v_l_4223_);
v___x_4250_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_nat_add(v___x_4232_, v_size_4225_);
if (lean_obj_tag(v_r_4224_) == 0)
{
lean_object* v_size_4252_; 
v_size_4252_ = lean_ctor_get(v_r_4224_, 0);
lean_inc(v_size_4252_);
v___y_4236_ = v___x_4251_;
v___y_4237_ = v___x_4250_;
v___y_4238_ = v_size_4252_;
goto v___jp_4235_;
}
else
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_unsigned_to_nat(0u);
v___y_4236_ = v___x_4251_;
v___y_4237_ = v___x_4250_;
v___y_4238_ = v___x_4253_;
goto v___jp_4235_;
}
}
}
}
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
lean_del_object(v___x_4197_);
v___x_4263_ = lean_unsigned_to_nat(1u);
v___x_4264_ = lean_nat_add(v___x_4263_, v_size_4202_);
v___x_4265_ = lean_nat_add(v___x_4264_, v_size_4203_);
lean_dec(v_size_4203_);
v___x_4266_ = lean_nat_add(v___x_4264_, v_size_4220_);
lean_dec(v___x_4264_);
lean_inc_ref(v___x_4201_);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 4, v_l_4206_);
lean_ctor_set(v___x_4218_, 3, v___x_4201_);
lean_ctor_set(v___x_4218_, 2, v_v_4193_);
lean_ctor_set(v___x_4218_, 1, v_k_4192_);
lean_ctor_set(v___x_4218_, 0, v___x_4266_);
v___x_4268_ = v___x_4218_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4281_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4281_, 3, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4281_, 4, v_l_4206_);
v___x_4268_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4275_ == 0)
{
lean_object* v_unused_4276_; lean_object* v_unused_4277_; lean_object* v_unused_4278_; lean_object* v_unused_4279_; lean_object* v_unused_4280_; 
v_unused_4276_ = lean_ctor_get(v___x_4201_, 4);
lean_dec(v_unused_4276_);
v_unused_4277_ = lean_ctor_get(v___x_4201_, 3);
lean_dec(v_unused_4277_);
v_unused_4278_ = lean_ctor_get(v___x_4201_, 2);
lean_dec(v_unused_4278_);
v_unused_4279_ = lean_ctor_get(v___x_4201_, 1);
lean_dec(v_unused_4279_);
v_unused_4280_ = lean_ctor_get(v___x_4201_, 0);
lean_dec(v_unused_4280_);
v___x_4270_ = v___x_4201_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_dec(v___x_4201_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 4, v_r_4207_);
lean_ctor_set(v___x_4270_, 3, v___x_4268_);
lean_ctor_set(v___x_4270_, 2, v_v_4205_);
lean_ctor_set(v___x_4270_, 1, v_k_4204_);
lean_ctor_set(v___x_4270_, 0, v___x_4265_);
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4265_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_k_4204_);
lean_ctor_set(v_reuseFailAlloc_4274_, 2, v_v_4205_);
lean_ctor_set(v_reuseFailAlloc_4274_, 3, v___x_4268_);
lean_ctor_set(v_reuseFailAlloc_4274_, 4, v_r_4207_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
lean_dec_ref_known(v_l_4206_, 5);
lean_del_object(v___x_4218_);
lean_dec(v_v_4205_);
lean_dec(v_k_4204_);
lean_dec(v_size_4203_);
lean_dec_ref_known(v___x_4201_, 5);
lean_del_object(v___x_4197_);
lean_dec(v_v_4193_);
lean_dec(v_k_4192_);
v___x_4282_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_4283_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4282_);
return v___x_4283_;
}
}
else
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
lean_del_object(v___x_4218_);
lean_dec(v_r_4207_);
lean_dec(v_v_4205_);
lean_dec(v_k_4204_);
lean_dec(v_size_4203_);
lean_dec_ref_known(v___x_4201_, 5);
lean_del_object(v___x_4197_);
lean_dec(v_v_4193_);
lean_dec(v_k_4192_);
v___x_4284_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_4285_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4284_);
return v___x_4285_;
}
}
}
}
else
{
lean_object* v_size_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4296_; 
v_size_4292_ = lean_ctor_get(v___x_4201_, 0);
v___x_4293_ = lean_unsigned_to_nat(1u);
v___x_4294_ = lean_nat_add(v___x_4293_, v_size_4292_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 3, v___x_4201_);
lean_ctor_set(v___x_4197_, 0, v___x_4294_);
v___x_4296_ = v___x_4197_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4297_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4297_, 3, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4297_, 4, v_r_4195_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
else
{
if (lean_obj_tag(v_r_4195_) == 0)
{
lean_object* v_l_4298_; 
v_l_4298_ = lean_ctor_get(v_r_4195_, 3);
lean_inc(v_l_4298_);
if (lean_obj_tag(v_l_4298_) == 0)
{
lean_object* v_r_4299_; 
v_r_4299_ = lean_ctor_get(v_r_4195_, 4);
lean_inc(v_r_4299_);
if (lean_obj_tag(v_r_4299_) == 0)
{
lean_object* v_size_4300_; lean_object* v_k_4301_; lean_object* v_v_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4316_; 
v_size_4300_ = lean_ctor_get(v_r_4195_, 0);
v_k_4301_ = lean_ctor_get(v_r_4195_, 1);
v_v_4302_ = lean_ctor_get(v_r_4195_, 2);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4316_ == 0)
{
lean_object* v_unused_4317_; lean_object* v_unused_4318_; 
v_unused_4317_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4317_);
v_unused_4318_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4318_);
v___x_4304_ = v_r_4195_;
v_isShared_4305_ = v_isSharedCheck_4316_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_v_4302_);
lean_inc(v_k_4301_);
lean_inc(v_size_4300_);
lean_dec(v_r_4195_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4316_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v_size_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4311_; 
v_size_4306_ = lean_ctor_get(v_l_4298_, 0);
v___x_4307_ = lean_unsigned_to_nat(1u);
v___x_4308_ = lean_nat_add(v___x_4307_, v_size_4300_);
lean_dec(v_size_4300_);
v___x_4309_ = lean_nat_add(v___x_4307_, v_size_4306_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 4, v_l_4298_);
lean_ctor_set(v___x_4304_, 3, v___x_4201_);
lean_ctor_set(v___x_4304_, 2, v_v_4193_);
lean_ctor_set(v___x_4304_, 1, v_k_4192_);
lean_ctor_set(v___x_4304_, 0, v___x_4309_);
v___x_4311_ = v___x_4304_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4309_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4315_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4315_, 3, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4315_, 4, v_l_4298_);
v___x_4311_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4313_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v_r_4299_);
lean_ctor_set(v___x_4197_, 3, v___x_4311_);
lean_ctor_set(v___x_4197_, 2, v_v_4302_);
lean_ctor_set(v___x_4197_, 1, v_k_4301_);
lean_ctor_set(v___x_4197_, 0, v___x_4308_);
v___x_4313_ = v___x_4197_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4314_, 1, v_k_4301_);
lean_ctor_set(v_reuseFailAlloc_4314_, 2, v_v_4302_);
lean_ctor_set(v_reuseFailAlloc_4314_, 3, v___x_4311_);
lean_ctor_set(v_reuseFailAlloc_4314_, 4, v_r_4299_);
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
else
{
lean_object* v_k_4319_; lean_object* v_v_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4344_; 
v_k_4319_ = lean_ctor_get(v_r_4195_, 1);
v_v_4320_ = lean_ctor_get(v_r_4195_, 2);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; lean_object* v_unused_4346_; lean_object* v_unused_4347_; 
v_unused_4345_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4345_);
v_unused_4346_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4346_);
v_unused_4347_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4347_);
v___x_4322_ = v_r_4195_;
v_isShared_4323_ = v_isSharedCheck_4344_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_v_4320_);
lean_inc(v_k_4319_);
lean_dec(v_r_4195_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4344_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v_k_4324_; lean_object* v_v_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4340_; 
v_k_4324_ = lean_ctor_get(v_l_4298_, 1);
v_v_4325_ = lean_ctor_get(v_l_4298_, 2);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_l_4298_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; lean_object* v_unused_4342_; lean_object* v_unused_4343_; 
v_unused_4341_ = lean_ctor_get(v_l_4298_, 4);
lean_dec(v_unused_4341_);
v_unused_4342_ = lean_ctor_get(v_l_4298_, 3);
lean_dec(v_unused_4342_);
v_unused_4343_ = lean_ctor_get(v_l_4298_, 0);
lean_dec(v_unused_4343_);
v___x_4327_ = v_l_4298_;
v_isShared_4328_ = v_isSharedCheck_4340_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_v_4325_);
lean_inc(v_k_4324_);
lean_dec(v_l_4298_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4340_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4329_ = lean_unsigned_to_nat(3u);
v___x_4330_ = lean_unsigned_to_nat(1u);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 4, v_r_4299_);
lean_ctor_set(v___x_4327_, 3, v_r_4299_);
lean_ctor_set(v___x_4327_, 2, v_v_4193_);
lean_ctor_set(v___x_4327_, 1, v_k_4192_);
lean_ctor_set(v___x_4327_, 0, v___x_4330_);
v___x_4332_ = v___x_4327_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4339_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4339_, 3, v_r_4299_);
lean_ctor_set(v_reuseFailAlloc_4339_, 4, v_r_4299_);
v___x_4332_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4334_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 3, v_r_4299_);
lean_ctor_set(v___x_4322_, 0, v___x_4330_);
v___x_4334_ = v___x_4322_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_k_4319_);
lean_ctor_set(v_reuseFailAlloc_4338_, 2, v_v_4320_);
lean_ctor_set(v_reuseFailAlloc_4338_, 3, v_r_4299_);
lean_ctor_set(v_reuseFailAlloc_4338_, 4, v_r_4299_);
v___x_4334_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4336_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v___x_4334_);
lean_ctor_set(v___x_4197_, 3, v___x_4332_);
lean_ctor_set(v___x_4197_, 2, v_v_4325_);
lean_ctor_set(v___x_4197_, 1, v_k_4324_);
lean_ctor_set(v___x_4197_, 0, v___x_4329_);
v___x_4336_ = v___x_4197_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v_k_4324_);
lean_ctor_set(v_reuseFailAlloc_4337_, 2, v_v_4325_);
lean_ctor_set(v_reuseFailAlloc_4337_, 3, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4337_, 4, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4348_; 
v_r_4348_ = lean_ctor_get(v_r_4195_, 4);
lean_inc(v_r_4348_);
if (lean_obj_tag(v_r_4348_) == 0)
{
lean_object* v_k_4349_; lean_object* v_v_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4362_; 
v_k_4349_ = lean_ctor_get(v_r_4195_, 1);
v_v_4350_ = lean_ctor_get(v_r_4195_, 2);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; lean_object* v_unused_4364_; lean_object* v_unused_4365_; 
v_unused_4363_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4363_);
v_unused_4364_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4364_);
v_unused_4365_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4365_);
v___x_4352_ = v_r_4195_;
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_v_4350_);
lean_inc(v_k_4349_);
lean_dec(v_r_4195_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4354_ = lean_unsigned_to_nat(3u);
v___x_4355_ = lean_unsigned_to_nat(1u);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 4, v_l_4298_);
lean_ctor_set(v___x_4352_, 2, v_v_4193_);
lean_ctor_set(v___x_4352_, 1, v_k_4192_);
lean_ctor_set(v___x_4352_, 0, v___x_4355_);
v___x_4357_ = v___x_4352_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4361_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4361_, 3, v_l_4298_);
lean_ctor_set(v_reuseFailAlloc_4361_, 4, v_l_4298_);
v___x_4357_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4359_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v_r_4348_);
lean_ctor_set(v___x_4197_, 3, v___x_4357_);
lean_ctor_set(v___x_4197_, 2, v_v_4350_);
lean_ctor_set(v___x_4197_, 1, v_k_4349_);
lean_ctor_set(v___x_4197_, 0, v___x_4354_);
v___x_4359_ = v___x_4197_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4354_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_k_4349_);
lean_ctor_set(v_reuseFailAlloc_4360_, 2, v_v_4350_);
lean_ctor_set(v_reuseFailAlloc_4360_, 3, v___x_4357_);
lean_ctor_set(v_reuseFailAlloc_4360_, 4, v_r_4348_);
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
else
{
lean_object* v___x_4366_; lean_object* v___x_4368_; 
v___x_4366_ = lean_unsigned_to_nat(2u);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 3, v_r_4348_);
lean_ctor_set(v___x_4197_, 0, v___x_4366_);
v___x_4368_ = v___x_4197_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4369_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4369_, 3, v_r_4348_);
lean_ctor_set(v_reuseFailAlloc_4369_, 4, v_r_4195_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_object* v___x_4370_; lean_object* v___x_4372_; 
v___x_4370_ = lean_unsigned_to_nat(1u);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 3, v_r_4195_);
lean_ctor_set(v___x_4197_, 0, v___x_4370_);
v___x_4372_ = v___x_4197_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4373_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4373_, 3, v_r_4195_);
lean_ctor_set(v_reuseFailAlloc_4373_, 4, v_r_4195_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
case 1:
{
lean_del_object(v___x_4197_);
lean_dec(v_v_4193_);
lean_dec(v_k_4192_);
lean_dec(v_k_4190_);
lean_dec_ref(v_cmp_4189_);
if (lean_obj_tag(v_l_4194_) == 0)
{
if (lean_obj_tag(v_r_4195_) == 0)
{
lean_object* v_size_4374_; lean_object* v_k_4375_; lean_object* v_v_4376_; lean_object* v_l_4377_; lean_object* v_r_4378_; lean_object* v_size_4379_; lean_object* v_k_4380_; lean_object* v_v_4381_; lean_object* v_l_4382_; lean_object* v_r_4383_; uint8_t v___x_4384_; 
v_size_4374_ = lean_ctor_get(v_l_4194_, 0);
v_k_4375_ = lean_ctor_get(v_l_4194_, 1);
v_v_4376_ = lean_ctor_get(v_l_4194_, 2);
v_l_4377_ = lean_ctor_get(v_l_4194_, 3);
v_r_4378_ = lean_ctor_get(v_l_4194_, 4);
lean_inc(v_r_4378_);
v_size_4379_ = lean_ctor_get(v_r_4195_, 0);
v_k_4380_ = lean_ctor_get(v_r_4195_, 1);
v_v_4381_ = lean_ctor_get(v_r_4195_, 2);
v_l_4382_ = lean_ctor_get(v_r_4195_, 3);
lean_inc(v_l_4382_);
v_r_4383_ = lean_ctor_get(v_r_4195_, 4);
v___x_4384_ = lean_nat_dec_lt(v_size_4374_, v_size_4379_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4536_; 
lean_inc(v_l_4377_);
lean_inc(v_v_4376_);
lean_inc(v_k_4375_);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4536_ == 0)
{
lean_object* v_unused_4537_; lean_object* v_unused_4538_; lean_object* v_unused_4539_; lean_object* v_unused_4540_; lean_object* v_unused_4541_; 
v_unused_4537_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4537_);
v_unused_4538_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4538_);
v_unused_4539_ = lean_ctor_get(v_l_4194_, 2);
lean_dec(v_unused_4539_);
v_unused_4540_ = lean_ctor_get(v_l_4194_, 1);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4541_);
v___x_4386_ = v_l_4194_;
v_isShared_4387_ = v_isSharedCheck_4536_;
goto v_resetjp_4385_;
}
else
{
lean_dec(v_l_4194_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4536_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v_d_4388_; lean_object* v_tree_4389_; 
v_d_4388_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(v_k_4375_, v_v_4376_, v_l_4377_, v_r_4378_);
v_tree_4389_ = lean_ctor_get(v_d_4388_, 2);
if (lean_obj_tag(v_tree_4389_) == 0)
{
lean_object* v_k_4390_; lean_object* v_v_4391_; lean_object* v_size_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
lean_inc_ref(v_tree_4389_);
v_k_4390_ = lean_ctor_get(v_d_4388_, 0);
lean_inc(v_k_4390_);
v_v_4391_ = lean_ctor_get(v_d_4388_, 1);
lean_inc(v_v_4391_);
lean_dec_ref(v_d_4388_);
v_size_4392_ = lean_ctor_get(v_tree_4389_, 0);
v___x_4393_ = lean_unsigned_to_nat(3u);
v___x_4394_ = lean_nat_mul(v___x_4393_, v_size_4392_);
v___x_4395_ = lean_nat_dec_lt(v___x_4394_, v_size_4379_);
lean_dec(v___x_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
lean_dec(v_l_4382_);
v___x_4396_ = lean_unsigned_to_nat(1u);
v___x_4397_ = lean_nat_add(v___x_4396_, v_size_4392_);
v___x_4398_ = lean_nat_add(v___x_4397_, v_size_4379_);
lean_dec(v___x_4397_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v_r_4195_);
lean_ctor_set(v___x_4386_, 3, v_tree_4389_);
lean_ctor_set(v___x_4386_, 2, v_v_4391_);
lean_ctor_set(v___x_4386_, 1, v_k_4390_);
lean_ctor_set(v___x_4386_, 0, v___x_4398_);
v___x_4400_ = v___x_4386_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_k_4390_);
lean_ctor_set(v_reuseFailAlloc_4401_, 2, v_v_4391_);
lean_ctor_set(v_reuseFailAlloc_4401_, 3, v_tree_4389_);
lean_ctor_set(v_reuseFailAlloc_4401_, 4, v_r_4195_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
else
{
lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4462_; 
lean_inc(v_r_4383_);
lean_inc(v_v_4381_);
lean_inc(v_k_4380_);
lean_inc(v_size_4379_);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4462_ == 0)
{
lean_object* v_unused_4463_; lean_object* v_unused_4464_; lean_object* v_unused_4465_; lean_object* v_unused_4466_; lean_object* v_unused_4467_; 
v_unused_4463_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4463_);
v_unused_4464_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4464_);
v_unused_4465_ = lean_ctor_get(v_r_4195_, 2);
lean_dec(v_unused_4465_);
v_unused_4466_ = lean_ctor_get(v_r_4195_, 1);
lean_dec(v_unused_4466_);
v_unused_4467_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4467_);
v___x_4403_ = v_r_4195_;
v_isShared_4404_ = v_isSharedCheck_4462_;
goto v_resetjp_4402_;
}
else
{
lean_dec(v_r_4195_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4462_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
if (lean_obj_tag(v_l_4382_) == 0)
{
if (lean_obj_tag(v_r_4383_) == 0)
{
lean_object* v_size_4405_; lean_object* v_k_4406_; lean_object* v_v_4407_; lean_object* v_l_4408_; lean_object* v_r_4409_; lean_object* v_size_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; 
v_size_4405_ = lean_ctor_get(v_l_4382_, 0);
v_k_4406_ = lean_ctor_get(v_l_4382_, 1);
v_v_4407_ = lean_ctor_get(v_l_4382_, 2);
v_l_4408_ = lean_ctor_get(v_l_4382_, 3);
v_r_4409_ = lean_ctor_get(v_l_4382_, 4);
v_size_4410_ = lean_ctor_get(v_r_4383_, 0);
v___x_4411_ = lean_unsigned_to_nat(2u);
v___x_4412_ = lean_nat_mul(v___x_4411_, v_size_4410_);
v___x_4413_ = lean_nat_dec_lt(v_size_4405_, v___x_4412_);
lean_dec(v___x_4412_);
if (v___x_4413_ == 0)
{
lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4442_; 
lean_inc(v_r_4409_);
lean_inc(v_l_4408_);
lean_inc(v_v_4407_);
lean_inc(v_k_4406_);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_l_4382_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; lean_object* v_unused_4444_; lean_object* v_unused_4445_; lean_object* v_unused_4446_; lean_object* v_unused_4447_; 
v_unused_4443_ = lean_ctor_get(v_l_4382_, 4);
lean_dec(v_unused_4443_);
v_unused_4444_ = lean_ctor_get(v_l_4382_, 3);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_l_4382_, 2);
lean_dec(v_unused_4445_);
v_unused_4446_ = lean_ctor_get(v_l_4382_, 1);
lean_dec(v_unused_4446_);
v_unused_4447_ = lean_ctor_get(v_l_4382_, 0);
lean_dec(v_unused_4447_);
v___x_4415_ = v_l_4382_;
v_isShared_4416_ = v_isSharedCheck_4442_;
goto v_resetjp_4414_;
}
else
{
lean_dec(v_l_4382_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4442_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4432_; 
v___x_4417_ = lean_unsigned_to_nat(1u);
v___x_4418_ = lean_nat_add(v___x_4417_, v_size_4392_);
v___x_4419_ = lean_nat_add(v___x_4418_, v_size_4379_);
lean_dec(v_size_4379_);
if (lean_obj_tag(v_l_4408_) == 0)
{
lean_object* v_size_4440_; 
v_size_4440_ = lean_ctor_get(v_l_4408_, 0);
lean_inc(v_size_4440_);
v___y_4432_ = v_size_4440_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_unsigned_to_nat(0u);
v___y_4432_ = v___x_4441_;
goto v___jp_4431_;
}
v___jp_4420_:
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4424_ = lean_nat_add(v___y_4421_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec(v___y_4421_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 4, v_r_4383_);
lean_ctor_set(v___x_4415_, 3, v_r_4409_);
lean_ctor_set(v___x_4415_, 2, v_v_4381_);
lean_ctor_set(v___x_4415_, 1, v_k_4380_);
lean_ctor_set(v___x_4415_, 0, v___x_4424_);
v___x_4426_ = v___x_4415_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v_k_4380_);
lean_ctor_set(v_reuseFailAlloc_4430_, 2, v_v_4381_);
lean_ctor_set(v_reuseFailAlloc_4430_, 3, v_r_4409_);
lean_ctor_set(v_reuseFailAlloc_4430_, 4, v_r_4383_);
v___x_4426_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
lean_object* v___x_4428_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 4, v___x_4426_);
lean_ctor_set(v___x_4403_, 3, v___y_4422_);
lean_ctor_set(v___x_4403_, 2, v_v_4407_);
lean_ctor_set(v___x_4403_, 1, v_k_4406_);
lean_ctor_set(v___x_4403_, 0, v___x_4419_);
v___x_4428_ = v___x_4403_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4429_, 1, v_k_4406_);
lean_ctor_set(v_reuseFailAlloc_4429_, 2, v_v_4407_);
lean_ctor_set(v_reuseFailAlloc_4429_, 3, v___y_4422_);
lean_ctor_set(v_reuseFailAlloc_4429_, 4, v___x_4426_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
v___jp_4431_:
{
lean_object* v___x_4433_; lean_object* v___x_4435_; 
v___x_4433_ = lean_nat_add(v___x_4418_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec(v___x_4418_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v_l_4408_);
lean_ctor_set(v___x_4386_, 3, v_tree_4389_);
lean_ctor_set(v___x_4386_, 2, v_v_4391_);
lean_ctor_set(v___x_4386_, 1, v_k_4390_);
lean_ctor_set(v___x_4386_, 0, v___x_4433_);
v___x_4435_ = v___x_4386_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v_k_4390_);
lean_ctor_set(v_reuseFailAlloc_4439_, 2, v_v_4391_);
lean_ctor_set(v_reuseFailAlloc_4439_, 3, v_tree_4389_);
lean_ctor_set(v_reuseFailAlloc_4439_, 4, v_l_4408_);
v___x_4435_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
lean_object* v___x_4436_; 
v___x_4436_ = lean_nat_add(v___x_4417_, v_size_4410_);
if (lean_obj_tag(v_r_4409_) == 0)
{
lean_object* v_size_4437_; 
v_size_4437_ = lean_ctor_get(v_r_4409_, 0);
lean_inc(v_size_4437_);
v___y_4421_ = v___x_4436_;
v___y_4422_ = v___x_4435_;
v___y_4423_ = v_size_4437_;
goto v___jp_4420_;
}
else
{
lean_object* v___x_4438_; 
v___x_4438_ = lean_unsigned_to_nat(0u);
v___y_4421_ = v___x_4436_;
v___y_4422_ = v___x_4435_;
v___y_4423_ = v___x_4438_;
goto v___jp_4420_;
}
}
}
}
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v___x_4448_ = lean_unsigned_to_nat(1u);
v___x_4449_ = lean_nat_add(v___x_4448_, v_size_4392_);
v___x_4450_ = lean_nat_add(v___x_4449_, v_size_4379_);
lean_dec(v_size_4379_);
v___x_4451_ = lean_nat_add(v___x_4449_, v_size_4405_);
lean_dec(v___x_4449_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 4, v_l_4382_);
lean_ctor_set(v___x_4403_, 3, v_tree_4389_);
lean_ctor_set(v___x_4403_, 2, v_v_4391_);
lean_ctor_set(v___x_4403_, 1, v_k_4390_);
lean_ctor_set(v___x_4403_, 0, v___x_4451_);
v___x_4453_ = v___x_4403_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4451_);
lean_ctor_set(v_reuseFailAlloc_4457_, 1, v_k_4390_);
lean_ctor_set(v_reuseFailAlloc_4457_, 2, v_v_4391_);
lean_ctor_set(v_reuseFailAlloc_4457_, 3, v_tree_4389_);
lean_ctor_set(v_reuseFailAlloc_4457_, 4, v_l_4382_);
v___x_4453_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v_r_4383_);
lean_ctor_set(v___x_4386_, 3, v___x_4453_);
lean_ctor_set(v___x_4386_, 2, v_v_4381_);
lean_ctor_set(v___x_4386_, 1, v_k_4380_);
lean_ctor_set(v___x_4386_, 0, v___x_4450_);
v___x_4455_ = v___x_4386_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4450_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_k_4380_);
lean_ctor_set(v_reuseFailAlloc_4456_, 2, v_v_4381_);
lean_ctor_set(v_reuseFailAlloc_4456_, 3, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4456_, 4, v_r_4383_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_dec_ref_known(v_l_4382_, 5);
lean_del_object(v___x_4403_);
lean_dec(v_v_4391_);
lean_dec_ref_known(v_tree_4389_, 5);
lean_dec(v_k_4390_);
lean_del_object(v___x_4386_);
lean_dec(v_v_4381_);
lean_dec(v_k_4380_);
lean_dec(v_size_4379_);
v___x_4458_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__7);
v___x_4459_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4458_);
return v___x_4459_;
}
}
else
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_del_object(v___x_4403_);
lean_dec(v_v_4391_);
lean_dec_ref_known(v_tree_4389_, 5);
lean_dec(v_k_4390_);
lean_del_object(v___x_4386_);
lean_dec(v_r_4383_);
lean_dec(v_v_4381_);
lean_dec(v_k_4380_);
lean_dec(v_size_4379_);
v___x_4460_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__8);
v___x_4461_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4460_);
return v___x_4461_;
}
}
}
}
else
{
lean_inc(v_r_4383_);
if (lean_obj_tag(v_l_4382_) == 0)
{
lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4505_; 
lean_inc(v_v_4381_);
lean_inc(v_k_4380_);
lean_inc(v_size_4379_);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4505_ == 0)
{
lean_object* v_unused_4506_; lean_object* v_unused_4507_; lean_object* v_unused_4508_; lean_object* v_unused_4509_; lean_object* v_unused_4510_; 
v_unused_4506_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4506_);
v_unused_4507_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4507_);
v_unused_4508_ = lean_ctor_get(v_r_4195_, 2);
lean_dec(v_unused_4508_);
v_unused_4509_ = lean_ctor_get(v_r_4195_, 1);
lean_dec(v_unused_4509_);
v_unused_4510_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4510_);
v___x_4469_ = v_r_4195_;
v_isShared_4470_ = v_isSharedCheck_4505_;
goto v_resetjp_4468_;
}
else
{
lean_dec(v_r_4195_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4505_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
if (lean_obj_tag(v_r_4383_) == 0)
{
lean_object* v_k_4471_; lean_object* v_v_4472_; lean_object* v_size_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4478_; 
lean_inc(v_tree_4389_);
v_k_4471_ = lean_ctor_get(v_d_4388_, 0);
lean_inc(v_k_4471_);
v_v_4472_ = lean_ctor_get(v_d_4388_, 1);
lean_inc(v_v_4472_);
lean_dec_ref(v_d_4388_);
v_size_4473_ = lean_ctor_get(v_l_4382_, 0);
v___x_4474_ = lean_unsigned_to_nat(1u);
v___x_4475_ = lean_nat_add(v___x_4474_, v_size_4379_);
lean_dec(v_size_4379_);
v___x_4476_ = lean_nat_add(v___x_4474_, v_size_4473_);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 4, v_l_4382_);
lean_ctor_set(v___x_4469_, 3, v_tree_4389_);
lean_ctor_set(v___x_4469_, 2, v_v_4472_);
lean_ctor_set(v___x_4469_, 1, v_k_4471_);
lean_ctor_set(v___x_4469_, 0, v___x_4476_);
v___x_4478_ = v___x_4469_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4476_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_k_4471_);
lean_ctor_set(v_reuseFailAlloc_4482_, 2, v_v_4472_);
lean_ctor_set(v_reuseFailAlloc_4482_, 3, v_tree_4389_);
lean_ctor_set(v_reuseFailAlloc_4482_, 4, v_l_4382_);
v___x_4478_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
lean_object* v___x_4480_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v_r_4383_);
lean_ctor_set(v___x_4386_, 3, v___x_4478_);
lean_ctor_set(v___x_4386_, 2, v_v_4381_);
lean_ctor_set(v___x_4386_, 1, v_k_4380_);
lean_ctor_set(v___x_4386_, 0, v___x_4475_);
v___x_4480_ = v___x_4386_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_k_4380_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_v_4381_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4481_, 4, v_r_4383_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
else
{
lean_object* v_k_4483_; lean_object* v_v_4484_; lean_object* v_k_4485_; lean_object* v_v_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_size_4379_);
v_k_4483_ = lean_ctor_get(v_d_4388_, 0);
lean_inc(v_k_4483_);
v_v_4484_ = lean_ctor_get(v_d_4388_, 1);
lean_inc(v_v_4484_);
lean_dec_ref(v_d_4388_);
v_k_4485_ = lean_ctor_get(v_l_4382_, 1);
v_v_4486_ = lean_ctor_get(v_l_4382_, 2);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_l_4382_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; lean_object* v_unused_4503_; lean_object* v_unused_4504_; 
v_unused_4502_ = lean_ctor_get(v_l_4382_, 4);
lean_dec(v_unused_4502_);
v_unused_4503_ = lean_ctor_get(v_l_4382_, 3);
lean_dec(v_unused_4503_);
v_unused_4504_ = lean_ctor_get(v_l_4382_, 0);
lean_dec(v_unused_4504_);
v___x_4488_ = v_l_4382_;
v_isShared_4489_ = v_isSharedCheck_4501_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_v_4486_);
lean_inc(v_k_4485_);
lean_dec(v_l_4382_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4501_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4490_ = lean_unsigned_to_nat(3u);
v___x_4491_ = lean_unsigned_to_nat(1u);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 4, v_r_4383_);
lean_ctor_set(v___x_4488_, 3, v_r_4383_);
lean_ctor_set(v___x_4488_, 2, v_v_4484_);
lean_ctor_set(v___x_4488_, 1, v_k_4483_);
lean_ctor_set(v___x_4488_, 0, v___x_4491_);
v___x_4493_ = v___x_4488_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_k_4483_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_v_4484_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v_r_4383_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_r_4383_);
v___x_4493_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4495_; 
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 3, v_r_4383_);
lean_ctor_set(v___x_4469_, 0, v___x_4491_);
v___x_4495_ = v___x_4469_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_k_4380_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_v_4381_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v_r_4383_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v_r_4383_);
v___x_4495_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4497_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v___x_4495_);
lean_ctor_set(v___x_4386_, 3, v___x_4493_);
lean_ctor_set(v___x_4386_, 2, v_v_4486_);
lean_ctor_set(v___x_4386_, 1, v_k_4485_);
lean_ctor_set(v___x_4386_, 0, v___x_4490_);
v___x_4497_ = v___x_4386_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_k_4485_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_v_4486_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v___x_4493_);
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
}
}
}
else
{
if (lean_obj_tag(v_r_4383_) == 0)
{
lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4524_; 
lean_inc(v_v_4381_);
lean_inc(v_k_4380_);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4524_ == 0)
{
lean_object* v_unused_4525_; lean_object* v_unused_4526_; lean_object* v_unused_4527_; lean_object* v_unused_4528_; lean_object* v_unused_4529_; 
v_unused_4525_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4525_);
v_unused_4526_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4526_);
v_unused_4527_ = lean_ctor_get(v_r_4195_, 2);
lean_dec(v_unused_4527_);
v_unused_4528_ = lean_ctor_get(v_r_4195_, 1);
lean_dec(v_unused_4528_);
v_unused_4529_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4529_);
v___x_4512_ = v_r_4195_;
v_isShared_4513_ = v_isSharedCheck_4524_;
goto v_resetjp_4511_;
}
else
{
lean_dec(v_r_4195_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4524_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v_k_4514_; lean_object* v_v_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4519_; 
v_k_4514_ = lean_ctor_get(v_d_4388_, 0);
lean_inc(v_k_4514_);
v_v_4515_ = lean_ctor_get(v_d_4388_, 1);
lean_inc(v_v_4515_);
lean_dec_ref(v_d_4388_);
v___x_4516_ = lean_unsigned_to_nat(3u);
v___x_4517_ = lean_unsigned_to_nat(1u);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 4, v_l_4382_);
lean_ctor_set(v___x_4512_, 2, v_v_4515_);
lean_ctor_set(v___x_4512_, 1, v_k_4514_);
lean_ctor_set(v___x_4512_, 0, v___x_4517_);
v___x_4519_ = v___x_4512_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_k_4514_);
lean_ctor_set(v_reuseFailAlloc_4523_, 2, v_v_4515_);
lean_ctor_set(v_reuseFailAlloc_4523_, 3, v_l_4382_);
lean_ctor_set(v_reuseFailAlloc_4523_, 4, v_l_4382_);
v___x_4519_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4521_; 
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v_r_4383_);
lean_ctor_set(v___x_4386_, 3, v___x_4519_);
lean_ctor_set(v___x_4386_, 2, v_v_4381_);
lean_ctor_set(v___x_4386_, 1, v_k_4380_);
lean_ctor_set(v___x_4386_, 0, v___x_4516_);
v___x_4521_ = v___x_4386_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4516_);
lean_ctor_set(v_reuseFailAlloc_4522_, 1, v_k_4380_);
lean_ctor_set(v_reuseFailAlloc_4522_, 2, v_v_4381_);
lean_ctor_set(v_reuseFailAlloc_4522_, 3, v___x_4519_);
lean_ctor_set(v_reuseFailAlloc_4522_, 4, v_r_4383_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
else
{
lean_object* v_k_4530_; lean_object* v_v_4531_; lean_object* v___x_4532_; lean_object* v___x_4534_; 
v_k_4530_ = lean_ctor_get(v_d_4388_, 0);
lean_inc(v_k_4530_);
v_v_4531_ = lean_ctor_get(v_d_4388_, 1);
lean_inc(v_v_4531_);
lean_dec_ref(v_d_4388_);
v___x_4532_ = lean_unsigned_to_nat(2u);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 4, v_r_4195_);
lean_ctor_set(v___x_4386_, 3, v_r_4383_);
lean_ctor_set(v___x_4386_, 2, v_v_4531_);
lean_ctor_set(v___x_4386_, 1, v_k_4530_);
lean_ctor_set(v___x_4386_, 0, v___x_4532_);
v___x_4534_ = v___x_4386_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v_k_4530_);
lean_ctor_set(v_reuseFailAlloc_4535_, 2, v_v_4531_);
lean_ctor_set(v_reuseFailAlloc_4535_, 3, v_r_4383_);
lean_ctor_set(v_reuseFailAlloc_4535_, 4, v_r_4195_);
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
lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4704_; 
lean_inc(v_r_4383_);
lean_inc(v_v_4381_);
lean_inc(v_k_4380_);
v_isSharedCheck_4704_ = !lean_is_exclusive(v_r_4195_);
if (v_isSharedCheck_4704_ == 0)
{
lean_object* v_unused_4705_; lean_object* v_unused_4706_; lean_object* v_unused_4707_; lean_object* v_unused_4708_; lean_object* v_unused_4709_; 
v_unused_4705_ = lean_ctor_get(v_r_4195_, 4);
lean_dec(v_unused_4705_);
v_unused_4706_ = lean_ctor_get(v_r_4195_, 3);
lean_dec(v_unused_4706_);
v_unused_4707_ = lean_ctor_get(v_r_4195_, 2);
lean_dec(v_unused_4707_);
v_unused_4708_ = lean_ctor_get(v_r_4195_, 1);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_r_4195_, 0);
lean_dec(v_unused_4709_);
v___x_4543_ = v_r_4195_;
v_isShared_4544_ = v_isSharedCheck_4704_;
goto v_resetjp_4542_;
}
else
{
lean_dec(v_r_4195_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4704_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v_d_4545_; lean_object* v_tree_4546_; 
v_d_4545_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(v_k_4380_, v_v_4381_, v_l_4382_, v_r_4383_);
v_tree_4546_ = lean_ctor_get(v_d_4545_, 2);
lean_inc(v_tree_4546_);
if (lean_obj_tag(v_tree_4546_) == 0)
{
lean_object* v_k_4547_; lean_object* v_v_4548_; lean_object* v_size_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; 
v_k_4547_ = lean_ctor_get(v_d_4545_, 0);
lean_inc(v_k_4547_);
v_v_4548_ = lean_ctor_get(v_d_4545_, 1);
lean_inc(v_v_4548_);
lean_dec_ref(v_d_4545_);
v_size_4549_ = lean_ctor_get(v_tree_4546_, 0);
v___x_4550_ = lean_unsigned_to_nat(3u);
v___x_4551_ = lean_nat_mul(v___x_4550_, v_size_4549_);
v___x_4552_ = lean_nat_dec_lt(v___x_4551_, v_size_4374_);
lean_dec(v___x_4551_);
if (v___x_4552_ == 0)
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4557_; 
lean_dec(v_r_4378_);
v___x_4553_ = lean_unsigned_to_nat(1u);
v___x_4554_ = lean_nat_add(v___x_4553_, v_size_4374_);
v___x_4555_ = lean_nat_add(v___x_4554_, v_size_4549_);
lean_dec(v___x_4554_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_tree_4546_);
lean_ctor_set(v___x_4543_, 3, v_l_4194_);
lean_ctor_set(v___x_4543_, 2, v_v_4548_);
lean_ctor_set(v___x_4543_, 1, v_k_4547_);
lean_ctor_set(v___x_4543_, 0, v___x_4555_);
v___x_4557_ = v___x_4543_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4555_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_k_4547_);
lean_ctor_set(v_reuseFailAlloc_4558_, 2, v_v_4548_);
lean_ctor_set(v_reuseFailAlloc_4558_, 3, v_l_4194_);
lean_ctor_set(v_reuseFailAlloc_4558_, 4, v_tree_4546_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
else
{
lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4630_; 
lean_inc(v_l_4377_);
lean_inc(v_v_4376_);
lean_inc(v_k_4375_);
lean_inc(v_size_4374_);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; lean_object* v_unused_4632_; lean_object* v_unused_4633_; lean_object* v_unused_4634_; lean_object* v_unused_4635_; 
v_unused_4631_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4631_);
v_unused_4632_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4632_);
v_unused_4633_ = lean_ctor_get(v_l_4194_, 2);
lean_dec(v_unused_4633_);
v_unused_4634_ = lean_ctor_get(v_l_4194_, 1);
lean_dec(v_unused_4634_);
v_unused_4635_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4635_);
v___x_4560_ = v_l_4194_;
v_isShared_4561_ = v_isSharedCheck_4630_;
goto v_resetjp_4559_;
}
else
{
lean_dec(v_l_4194_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4630_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
if (lean_obj_tag(v_l_4377_) == 0)
{
if (lean_obj_tag(v_r_4378_) == 0)
{
lean_object* v_size_4562_; lean_object* v_size_4563_; lean_object* v_k_4564_; lean_object* v_v_4565_; lean_object* v_l_4566_; lean_object* v_r_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v_size_4562_ = lean_ctor_get(v_l_4377_, 0);
v_size_4563_ = lean_ctor_get(v_r_4378_, 0);
v_k_4564_ = lean_ctor_get(v_r_4378_, 1);
v_v_4565_ = lean_ctor_get(v_r_4378_, 2);
v_l_4566_ = lean_ctor_get(v_r_4378_, 3);
v_r_4567_ = lean_ctor_get(v_r_4378_, 4);
v___x_4568_ = lean_unsigned_to_nat(2u);
v___x_4569_ = lean_nat_mul(v___x_4568_, v_size_4562_);
v___x_4570_ = lean_nat_dec_lt(v_size_4563_, v___x_4569_);
lean_dec(v___x_4569_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4609_; 
lean_inc(v_r_4567_);
lean_inc(v_l_4566_);
lean_inc(v_v_4565_);
lean_inc(v_k_4564_);
lean_del_object(v___x_4560_);
v_isSharedCheck_4609_ = !lean_is_exclusive(v_r_4378_);
if (v_isSharedCheck_4609_ == 0)
{
lean_object* v_unused_4610_; lean_object* v_unused_4611_; lean_object* v_unused_4612_; lean_object* v_unused_4613_; lean_object* v_unused_4614_; 
v_unused_4610_ = lean_ctor_get(v_r_4378_, 4);
lean_dec(v_unused_4610_);
v_unused_4611_ = lean_ctor_get(v_r_4378_, 3);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_r_4378_, 2);
lean_dec(v_unused_4612_);
v_unused_4613_ = lean_ctor_get(v_r_4378_, 1);
lean_dec(v_unused_4613_);
v_unused_4614_ = lean_ctor_get(v_r_4378_, 0);
lean_dec(v_unused_4614_);
v___x_4572_ = v_r_4378_;
v_isShared_4573_ = v_isSharedCheck_4609_;
goto v_resetjp_4571_;
}
else
{
lean_dec(v_r_4378_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4609_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___x_4597_; lean_object* v___y_4599_; 
v___x_4574_ = lean_unsigned_to_nat(1u);
v___x_4575_ = lean_nat_add(v___x_4574_, v_size_4374_);
lean_dec(v_size_4374_);
v___x_4576_ = lean_nat_add(v___x_4575_, v_size_4549_);
lean_dec(v___x_4575_);
v___x_4597_ = lean_nat_add(v___x_4574_, v_size_4562_);
if (lean_obj_tag(v_l_4566_) == 0)
{
lean_object* v_size_4607_; 
v_size_4607_ = lean_ctor_get(v_l_4566_, 0);
lean_inc(v_size_4607_);
v___y_4599_ = v_size_4607_;
goto v___jp_4598_;
}
else
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_unsigned_to_nat(0u);
v___y_4599_ = v___x_4608_;
goto v___jp_4598_;
}
v___jp_4577_:
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4581_ = lean_nat_add(v___y_4578_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec(v___y_4578_);
lean_inc_ref(v_tree_4546_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 4, v_tree_4546_);
lean_ctor_set(v___x_4572_, 3, v_r_4567_);
lean_ctor_set(v___x_4572_, 2, v_v_4548_);
lean_ctor_set(v___x_4572_, 1, v_k_4547_);
lean_ctor_set(v___x_4572_, 0, v___x_4581_);
v___x_4583_ = v___x_4572_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_k_4547_);
lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_v_4548_);
lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_r_4567_);
lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_tree_4546_);
v___x_4583_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
v_isSharedCheck_4590_ = !lean_is_exclusive(v_tree_4546_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; lean_object* v_unused_4592_; lean_object* v_unused_4593_; lean_object* v_unused_4594_; lean_object* v_unused_4595_; 
v_unused_4591_ = lean_ctor_get(v_tree_4546_, 4);
lean_dec(v_unused_4591_);
v_unused_4592_ = lean_ctor_get(v_tree_4546_, 3);
lean_dec(v_unused_4592_);
v_unused_4593_ = lean_ctor_get(v_tree_4546_, 2);
lean_dec(v_unused_4593_);
v_unused_4594_ = lean_ctor_get(v_tree_4546_, 1);
lean_dec(v_unused_4594_);
v_unused_4595_ = lean_ctor_get(v_tree_4546_, 0);
lean_dec(v_unused_4595_);
v___x_4585_ = v_tree_4546_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_dec(v_tree_4546_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 4, v___x_4583_);
lean_ctor_set(v___x_4585_, 3, v___y_4579_);
lean_ctor_set(v___x_4585_, 2, v_v_4565_);
lean_ctor_set(v___x_4585_, 1, v_k_4564_);
lean_ctor_set(v___x_4585_, 0, v___x_4576_);
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_k_4564_);
lean_ctor_set(v_reuseFailAlloc_4589_, 2, v_v_4565_);
lean_ctor_set(v_reuseFailAlloc_4589_, 3, v___y_4579_);
lean_ctor_set(v_reuseFailAlloc_4589_, 4, v___x_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
v___jp_4598_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = lean_nat_add(v___x_4597_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec(v___x_4597_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_l_4566_);
lean_ctor_set(v___x_4543_, 3, v_l_4377_);
lean_ctor_set(v___x_4543_, 2, v_v_4376_);
lean_ctor_set(v___x_4543_, 1, v_k_4375_);
lean_ctor_set(v___x_4543_, 0, v___x_4600_);
v___x_4602_ = v___x_4543_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v_l_4377_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v_l_4566_);
v___x_4602_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_nat_add(v___x_4574_, v_size_4549_);
if (lean_obj_tag(v_r_4567_) == 0)
{
lean_object* v_size_4604_; 
v_size_4604_ = lean_ctor_get(v_r_4567_, 0);
lean_inc(v_size_4604_);
v___y_4578_ = v___x_4603_;
v___y_4579_ = v___x_4602_;
v___y_4580_ = v_size_4604_;
goto v___jp_4577_;
}
else
{
lean_object* v___x_4605_; 
v___x_4605_ = lean_unsigned_to_nat(0u);
v___y_4578_ = v___x_4603_;
v___y_4579_ = v___x_4602_;
v___y_4580_ = v___x_4605_;
goto v___jp_4577_;
}
}
}
}
}
else
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4615_ = lean_unsigned_to_nat(1u);
v___x_4616_ = lean_nat_add(v___x_4615_, v_size_4374_);
lean_dec(v_size_4374_);
v___x_4617_ = lean_nat_add(v___x_4616_, v_size_4549_);
lean_dec(v___x_4616_);
v___x_4618_ = lean_nat_add(v___x_4615_, v_size_4549_);
v___x_4619_ = lean_nat_add(v___x_4618_, v_size_4563_);
lean_dec(v___x_4618_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_tree_4546_);
lean_ctor_set(v___x_4543_, 3, v_r_4378_);
lean_ctor_set(v___x_4543_, 2, v_v_4548_);
lean_ctor_set(v___x_4543_, 1, v_k_4547_);
lean_ctor_set(v___x_4543_, 0, v___x_4619_);
v___x_4621_ = v___x_4543_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4619_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_k_4547_);
lean_ctor_set(v_reuseFailAlloc_4625_, 2, v_v_4548_);
lean_ctor_set(v_reuseFailAlloc_4625_, 3, v_r_4378_);
lean_ctor_set(v_reuseFailAlloc_4625_, 4, v_tree_4546_);
v___x_4621_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4623_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 4, v___x_4621_);
lean_ctor_set(v___x_4560_, 0, v___x_4617_);
v___x_4623_ = v___x_4560_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4624_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4624_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4624_, 3, v_l_4377_);
lean_ctor_set(v_reuseFailAlloc_4624_, 4, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
lean_dec_ref_known(v_l_4377_, 5);
lean_del_object(v___x_4560_);
lean_dec(v_v_4548_);
lean_dec_ref_known(v_tree_4546_, 5);
lean_dec(v_k_4547_);
lean_del_object(v___x_4543_);
lean_dec(v_v_4376_);
lean_dec(v_k_4375_);
lean_dec(v_size_4374_);
v___x_4626_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_4627_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4626_);
return v___x_4627_;
}
}
else
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_del_object(v___x_4560_);
lean_dec(v_v_4548_);
lean_dec(v_k_4547_);
lean_dec_ref_known(v_tree_4546_, 5);
lean_del_object(v___x_4543_);
lean_dec(v_r_4378_);
lean_dec(v_v_4376_);
lean_dec(v_k_4375_);
lean_dec(v_size_4374_);
v___x_4628_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_4629_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4628_);
return v___x_4629_;
}
}
}
}
else
{
if (lean_obj_tag(v_l_4377_) == 0)
{
lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4661_; 
lean_inc_ref(v_l_4377_);
lean_inc(v_v_4376_);
lean_inc(v_k_4375_);
lean_inc(v_size_4374_);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; lean_object* v_unused_4663_; lean_object* v_unused_4664_; lean_object* v_unused_4665_; lean_object* v_unused_4666_; 
v_unused_4662_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4662_);
v_unused_4663_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4663_);
v_unused_4664_ = lean_ctor_get(v_l_4194_, 2);
lean_dec(v_unused_4664_);
v_unused_4665_ = lean_ctor_get(v_l_4194_, 1);
lean_dec(v_unused_4665_);
v_unused_4666_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4666_);
v___x_4637_ = v_l_4194_;
v_isShared_4638_ = v_isSharedCheck_4661_;
goto v_resetjp_4636_;
}
else
{
lean_dec(v_l_4194_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4661_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
if (lean_obj_tag(v_r_4378_) == 0)
{
lean_object* v_k_4639_; lean_object* v_v_4640_; lean_object* v_size_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4646_; 
v_k_4639_ = lean_ctor_get(v_d_4545_, 0);
lean_inc(v_k_4639_);
v_v_4640_ = lean_ctor_get(v_d_4545_, 1);
lean_inc(v_v_4640_);
lean_dec_ref(v_d_4545_);
v_size_4641_ = lean_ctor_get(v_r_4378_, 0);
v___x_4642_ = lean_unsigned_to_nat(1u);
v___x_4643_ = lean_nat_add(v___x_4642_, v_size_4374_);
lean_dec(v_size_4374_);
v___x_4644_ = lean_nat_add(v___x_4642_, v_size_4641_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_tree_4546_);
lean_ctor_set(v___x_4543_, 3, v_r_4378_);
lean_ctor_set(v___x_4543_, 2, v_v_4640_);
lean_ctor_set(v___x_4543_, 1, v_k_4639_);
lean_ctor_set(v___x_4543_, 0, v___x_4644_);
v___x_4646_ = v___x_4543_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v_k_4639_);
lean_ctor_set(v_reuseFailAlloc_4650_, 2, v_v_4640_);
lean_ctor_set(v_reuseFailAlloc_4650_, 3, v_r_4378_);
lean_ctor_set(v_reuseFailAlloc_4650_, 4, v_tree_4546_);
v___x_4646_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
lean_object* v___x_4648_; 
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 4, v___x_4646_);
lean_ctor_set(v___x_4637_, 0, v___x_4643_);
v___x_4648_ = v___x_4637_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4643_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4649_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_l_4377_);
lean_ctor_set(v_reuseFailAlloc_4649_, 4, v___x_4646_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
else
{
lean_object* v_k_4651_; lean_object* v_v_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4656_; 
lean_dec(v_size_4374_);
v_k_4651_ = lean_ctor_get(v_d_4545_, 0);
lean_inc(v_k_4651_);
v_v_4652_ = lean_ctor_get(v_d_4545_, 1);
lean_inc(v_v_4652_);
lean_dec_ref(v_d_4545_);
v___x_4653_ = lean_unsigned_to_nat(3u);
v___x_4654_ = lean_unsigned_to_nat(1u);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_r_4378_);
lean_ctor_set(v___x_4543_, 3, v_r_4378_);
lean_ctor_set(v___x_4543_, 2, v_v_4652_);
lean_ctor_set(v___x_4543_, 1, v_k_4651_);
lean_ctor_set(v___x_4543_, 0, v___x_4654_);
v___x_4656_ = v___x_4543_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4654_);
lean_ctor_set(v_reuseFailAlloc_4660_, 1, v_k_4651_);
lean_ctor_set(v_reuseFailAlloc_4660_, 2, v_v_4652_);
lean_ctor_set(v_reuseFailAlloc_4660_, 3, v_r_4378_);
lean_ctor_set(v_reuseFailAlloc_4660_, 4, v_r_4378_);
v___x_4656_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4658_; 
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 4, v___x_4656_);
lean_ctor_set(v___x_4637_, 0, v___x_4653_);
v___x_4658_ = v___x_4637_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4659_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4659_, 3, v_l_4377_);
lean_ctor_set(v_reuseFailAlloc_4659_, 4, v___x_4656_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_4378_) == 0)
{
lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4692_; 
lean_inc(v_l_4377_);
lean_inc(v_v_4376_);
lean_inc(v_k_4375_);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4692_ == 0)
{
lean_object* v_unused_4693_; lean_object* v_unused_4694_; lean_object* v_unused_4695_; lean_object* v_unused_4696_; lean_object* v_unused_4697_; 
v_unused_4693_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4693_);
v_unused_4694_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4694_);
v_unused_4695_ = lean_ctor_get(v_l_4194_, 2);
lean_dec(v_unused_4695_);
v_unused_4696_ = lean_ctor_get(v_l_4194_, 1);
lean_dec(v_unused_4696_);
v_unused_4697_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4697_);
v___x_4668_ = v_l_4194_;
v_isShared_4669_ = v_isSharedCheck_4692_;
goto v_resetjp_4667_;
}
else
{
lean_dec(v_l_4194_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4692_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v_k_4670_; lean_object* v_v_4671_; lean_object* v_k_4672_; lean_object* v_v_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4688_; 
v_k_4670_ = lean_ctor_get(v_d_4545_, 0);
lean_inc(v_k_4670_);
v_v_4671_ = lean_ctor_get(v_d_4545_, 1);
lean_inc(v_v_4671_);
lean_dec_ref(v_d_4545_);
v_k_4672_ = lean_ctor_get(v_r_4378_, 1);
v_v_4673_ = lean_ctor_get(v_r_4378_, 2);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_r_4378_);
if (v_isSharedCheck_4688_ == 0)
{
lean_object* v_unused_4689_; lean_object* v_unused_4690_; lean_object* v_unused_4691_; 
v_unused_4689_ = lean_ctor_get(v_r_4378_, 4);
lean_dec(v_unused_4689_);
v_unused_4690_ = lean_ctor_get(v_r_4378_, 3);
lean_dec(v_unused_4690_);
v_unused_4691_ = lean_ctor_get(v_r_4378_, 0);
lean_dec(v_unused_4691_);
v___x_4675_ = v_r_4378_;
v_isShared_4676_ = v_isSharedCheck_4688_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_v_4673_);
lean_inc(v_k_4672_);
lean_dec(v_r_4378_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4688_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4680_; 
v___x_4677_ = lean_unsigned_to_nat(3u);
v___x_4678_ = lean_unsigned_to_nat(1u);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 4, v_l_4377_);
lean_ctor_set(v___x_4675_, 3, v_l_4377_);
lean_ctor_set(v___x_4675_, 2, v_v_4376_);
lean_ctor_set(v___x_4675_, 1, v_k_4375_);
lean_ctor_set(v___x_4675_, 0, v___x_4678_);
v___x_4680_ = v___x_4675_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_k_4375_);
lean_ctor_set(v_reuseFailAlloc_4687_, 2, v_v_4376_);
lean_ctor_set(v_reuseFailAlloc_4687_, 3, v_l_4377_);
lean_ctor_set(v_reuseFailAlloc_4687_, 4, v_l_4377_);
v___x_4680_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
lean_object* v___x_4682_; 
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_l_4377_);
lean_ctor_set(v___x_4543_, 3, v_l_4377_);
lean_ctor_set(v___x_4543_, 2, v_v_4671_);
lean_ctor_set(v___x_4543_, 1, v_k_4670_);
lean_ctor_set(v___x_4543_, 0, v___x_4678_);
v___x_4682_ = v___x_4543_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v_k_4670_);
lean_ctor_set(v_reuseFailAlloc_4686_, 2, v_v_4671_);
lean_ctor_set(v_reuseFailAlloc_4686_, 3, v_l_4377_);
lean_ctor_set(v_reuseFailAlloc_4686_, 4, v_l_4377_);
v___x_4682_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4684_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 4, v___x_4682_);
lean_ctor_set(v___x_4668_, 3, v___x_4680_);
lean_ctor_set(v___x_4668_, 2, v_v_4673_);
lean_ctor_set(v___x_4668_, 1, v_k_4672_);
lean_ctor_set(v___x_4668_, 0, v___x_4677_);
v___x_4684_ = v___x_4668_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4677_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v_k_4672_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_v_4673_);
lean_ctor_set(v_reuseFailAlloc_4685_, 3, v___x_4680_);
lean_ctor_set(v_reuseFailAlloc_4685_, 4, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
}
else
{
lean_object* v_k_4698_; lean_object* v_v_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; 
v_k_4698_ = lean_ctor_get(v_d_4545_, 0);
lean_inc(v_k_4698_);
v_v_4699_ = lean_ctor_get(v_d_4545_, 1);
lean_inc(v_v_4699_);
lean_dec_ref(v_d_4545_);
v___x_4700_ = lean_unsigned_to_nat(2u);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v_r_4378_);
lean_ctor_set(v___x_4543_, 3, v_l_4194_);
lean_ctor_set(v___x_4543_, 2, v_v_4699_);
lean_ctor_set(v___x_4543_, 1, v_k_4698_);
lean_ctor_set(v___x_4543_, 0, v___x_4700_);
v___x_4702_ = v___x_4543_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_k_4698_);
lean_ctor_set(v_reuseFailAlloc_4703_, 2, v_v_4699_);
lean_ctor_set(v_reuseFailAlloc_4703_, 3, v_l_4194_);
lean_ctor_set(v_reuseFailAlloc_4703_, 4, v_r_4378_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
}
}
else
{
return v_l_4194_;
}
}
else
{
return v_r_4195_;
}
}
default: 
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4189_, v_k_4190_, v_r_4195_);
if (lean_obj_tag(v___x_4710_) == 0)
{
if (lean_obj_tag(v_l_4194_) == 0)
{
lean_object* v_size_4711_; lean_object* v_size_4712_; lean_object* v_k_4713_; lean_object* v_v_4714_; lean_object* v_l_4715_; lean_object* v_r_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; uint8_t v___x_4719_; 
v_size_4711_ = lean_ctor_get(v___x_4710_, 0);
v_size_4712_ = lean_ctor_get(v_l_4194_, 0);
v_k_4713_ = lean_ctor_get(v_l_4194_, 1);
v_v_4714_ = lean_ctor_get(v_l_4194_, 2);
v_l_4715_ = lean_ctor_get(v_l_4194_, 3);
v_r_4716_ = lean_ctor_get(v_l_4194_, 4);
lean_inc(v_r_4716_);
v___x_4717_ = lean_unsigned_to_nat(3u);
v___x_4718_ = lean_nat_mul(v___x_4717_, v_size_4711_);
v___x_4719_ = lean_nat_dec_lt(v___x_4718_, v_size_4712_);
lean_dec(v___x_4718_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; 
lean_dec(v_r_4716_);
v___x_4720_ = lean_unsigned_to_nat(1u);
v___x_4721_ = lean_nat_add(v___x_4720_, v_size_4712_);
v___x_4722_ = lean_nat_add(v___x_4721_, v_size_4711_);
lean_dec(v___x_4721_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v___x_4710_);
lean_ctor_set(v___x_4197_, 0, v___x_4722_);
v___x_4724_ = v___x_4197_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_l_4194_);
lean_ctor_set(v_reuseFailAlloc_4725_, 4, v___x_4710_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
else
{
lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4797_; 
lean_inc(v_l_4715_);
lean_inc(v_v_4714_);
lean_inc(v_k_4713_);
lean_inc(v_size_4712_);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4797_ == 0)
{
lean_object* v_unused_4798_; lean_object* v_unused_4799_; lean_object* v_unused_4800_; lean_object* v_unused_4801_; lean_object* v_unused_4802_; 
v_unused_4798_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4798_);
v_unused_4799_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4799_);
v_unused_4800_ = lean_ctor_get(v_l_4194_, 2);
lean_dec(v_unused_4800_);
v_unused_4801_ = lean_ctor_get(v_l_4194_, 1);
lean_dec(v_unused_4801_);
v_unused_4802_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4802_);
v___x_4727_ = v_l_4194_;
v_isShared_4728_ = v_isSharedCheck_4797_;
goto v_resetjp_4726_;
}
else
{
lean_dec(v_l_4194_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4797_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
if (lean_obj_tag(v_l_4715_) == 0)
{
if (lean_obj_tag(v_r_4716_) == 0)
{
lean_object* v_size_4729_; lean_object* v_size_4730_; lean_object* v_k_4731_; lean_object* v_v_4732_; lean_object* v_l_4733_; lean_object* v_r_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; uint8_t v___x_4737_; 
v_size_4729_ = lean_ctor_get(v_l_4715_, 0);
v_size_4730_ = lean_ctor_get(v_r_4716_, 0);
v_k_4731_ = lean_ctor_get(v_r_4716_, 1);
v_v_4732_ = lean_ctor_get(v_r_4716_, 2);
v_l_4733_ = lean_ctor_get(v_r_4716_, 3);
v_r_4734_ = lean_ctor_get(v_r_4716_, 4);
v___x_4735_ = lean_unsigned_to_nat(2u);
v___x_4736_ = lean_nat_mul(v___x_4735_, v_size_4729_);
v___x_4737_ = lean_nat_dec_lt(v_size_4730_, v___x_4736_);
lean_dec(v___x_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4767_; 
lean_inc(v_r_4734_);
lean_inc(v_l_4733_);
lean_inc(v_v_4732_);
lean_inc(v_k_4731_);
v_isSharedCheck_4767_ = !lean_is_exclusive(v_r_4716_);
if (v_isSharedCheck_4767_ == 0)
{
lean_object* v_unused_4768_; lean_object* v_unused_4769_; lean_object* v_unused_4770_; lean_object* v_unused_4771_; lean_object* v_unused_4772_; 
v_unused_4768_ = lean_ctor_get(v_r_4716_, 4);
lean_dec(v_unused_4768_);
v_unused_4769_ = lean_ctor_get(v_r_4716_, 3);
lean_dec(v_unused_4769_);
v_unused_4770_ = lean_ctor_get(v_r_4716_, 2);
lean_dec(v_unused_4770_);
v_unused_4771_ = lean_ctor_get(v_r_4716_, 1);
lean_dec(v_unused_4771_);
v_unused_4772_ = lean_ctor_get(v_r_4716_, 0);
lean_dec(v_unused_4772_);
v___x_4739_ = v_r_4716_;
v_isShared_4740_ = v_isSharedCheck_4767_;
goto v_resetjp_4738_;
}
else
{
lean_dec(v_r_4716_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4767_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___x_4755_; lean_object* v___y_4757_; 
v___x_4741_ = lean_unsigned_to_nat(1u);
v___x_4742_ = lean_nat_add(v___x_4741_, v_size_4712_);
lean_dec(v_size_4712_);
v___x_4743_ = lean_nat_add(v___x_4742_, v_size_4711_);
lean_dec(v___x_4742_);
v___x_4755_ = lean_nat_add(v___x_4741_, v_size_4729_);
if (lean_obj_tag(v_l_4733_) == 0)
{
lean_object* v_size_4765_; 
v_size_4765_ = lean_ctor_get(v_l_4733_, 0);
lean_inc(v_size_4765_);
v___y_4757_ = v_size_4765_;
goto v___jp_4756_;
}
else
{
lean_object* v___x_4766_; 
v___x_4766_ = lean_unsigned_to_nat(0u);
v___y_4757_ = v___x_4766_;
goto v___jp_4756_;
}
v___jp_4744_:
{
lean_object* v___x_4748_; lean_object* v___x_4750_; 
v___x_4748_ = lean_nat_add(v___y_4745_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec(v___y_4745_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 4, v___x_4710_);
lean_ctor_set(v___x_4739_, 3, v_r_4734_);
lean_ctor_set(v___x_4739_, 2, v_v_4193_);
lean_ctor_set(v___x_4739_, 1, v_k_4192_);
lean_ctor_set(v___x_4739_, 0, v___x_4748_);
v___x_4750_ = v___x_4739_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4748_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_r_4734_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v___x_4710_);
v___x_4750_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4752_; 
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 4, v___x_4750_);
lean_ctor_set(v___x_4727_, 3, v___y_4746_);
lean_ctor_set(v___x_4727_, 2, v_v_4732_);
lean_ctor_set(v___x_4727_, 1, v_k_4731_);
lean_ctor_set(v___x_4727_, 0, v___x_4743_);
v___x_4752_ = v___x_4727_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_k_4731_);
lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_v_4732_);
lean_ctor_set(v_reuseFailAlloc_4753_, 3, v___y_4746_);
lean_ctor_set(v_reuseFailAlloc_4753_, 4, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
v___jp_4756_:
{
lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4758_ = lean_nat_add(v___x_4755_, v___y_4757_);
lean_dec(v___y_4757_);
lean_dec(v___x_4755_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v_l_4733_);
lean_ctor_set(v___x_4197_, 3, v_l_4715_);
lean_ctor_set(v___x_4197_, 2, v_v_4714_);
lean_ctor_set(v___x_4197_, 1, v_k_4713_);
lean_ctor_set(v___x_4197_, 0, v___x_4758_);
v___x_4760_ = v___x_4197_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_k_4713_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_v_4714_);
lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_l_4715_);
lean_ctor_set(v_reuseFailAlloc_4764_, 4, v_l_4733_);
v___x_4760_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4761_; 
v___x_4761_ = lean_nat_add(v___x_4741_, v_size_4711_);
if (lean_obj_tag(v_r_4734_) == 0)
{
lean_object* v_size_4762_; 
v_size_4762_ = lean_ctor_get(v_r_4734_, 0);
lean_inc(v_size_4762_);
v___y_4745_ = v___x_4761_;
v___y_4746_ = v___x_4760_;
v___y_4747_ = v_size_4762_;
goto v___jp_4744_;
}
else
{
lean_object* v___x_4763_; 
v___x_4763_ = lean_unsigned_to_nat(0u);
v___y_4745_ = v___x_4761_;
v___y_4746_ = v___x_4760_;
v___y_4747_ = v___x_4763_;
goto v___jp_4744_;
}
}
}
}
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
lean_del_object(v___x_4197_);
v___x_4773_ = lean_unsigned_to_nat(1u);
v___x_4774_ = lean_nat_add(v___x_4773_, v_size_4712_);
lean_dec(v_size_4712_);
v___x_4775_ = lean_nat_add(v___x_4774_, v_size_4711_);
lean_dec(v___x_4774_);
v___x_4776_ = lean_nat_add(v___x_4773_, v_size_4711_);
v___x_4777_ = lean_nat_add(v___x_4776_, v_size_4730_);
lean_dec(v___x_4776_);
lean_inc_ref(v___x_4710_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 4, v___x_4710_);
lean_ctor_set(v___x_4727_, 3, v_r_4716_);
lean_ctor_set(v___x_4727_, 2, v_v_4193_);
lean_ctor_set(v___x_4727_, 1, v_k_4192_);
lean_ctor_set(v___x_4727_, 0, v___x_4777_);
v___x_4779_ = v___x_4727_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4777_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4792_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4792_, 3, v_r_4716_);
lean_ctor_set(v_reuseFailAlloc_4792_, 4, v___x_4710_);
v___x_4779_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4786_ == 0)
{
lean_object* v_unused_4787_; lean_object* v_unused_4788_; lean_object* v_unused_4789_; lean_object* v_unused_4790_; lean_object* v_unused_4791_; 
v_unused_4787_ = lean_ctor_get(v___x_4710_, 4);
lean_dec(v_unused_4787_);
v_unused_4788_ = lean_ctor_get(v___x_4710_, 3);
lean_dec(v_unused_4788_);
v_unused_4789_ = lean_ctor_get(v___x_4710_, 2);
lean_dec(v_unused_4789_);
v_unused_4790_ = lean_ctor_get(v___x_4710_, 1);
lean_dec(v_unused_4790_);
v_unused_4791_ = lean_ctor_get(v___x_4710_, 0);
lean_dec(v_unused_4791_);
v___x_4781_ = v___x_4710_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_dec(v___x_4710_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
lean_ctor_set(v___x_4781_, 4, v___x_4779_);
lean_ctor_set(v___x_4781_, 3, v_l_4715_);
lean_ctor_set(v___x_4781_, 2, v_v_4714_);
lean_ctor_set(v___x_4781_, 1, v_k_4713_);
lean_ctor_set(v___x_4781_, 0, v___x_4775_);
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4775_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_k_4713_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_v_4714_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_l_4715_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v___x_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_dec_ref_known(v_l_4715_, 5);
lean_del_object(v___x_4727_);
lean_dec(v_v_4714_);
lean_dec(v_k_4713_);
lean_dec(v_size_4712_);
lean_dec_ref_known(v___x_4710_, 5);
lean_del_object(v___x_4197_);
lean_dec(v_v_4193_);
lean_dec(v_k_4192_);
v___x_4793_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__3);
v___x_4794_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4793_);
return v___x_4794_;
}
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_del_object(v___x_4727_);
lean_dec(v_r_4716_);
lean_dec(v_v_4714_);
lean_dec(v_k_4713_);
lean_dec(v_size_4712_);
lean_dec_ref_known(v___x_4710_, 5);
lean_del_object(v___x_4197_);
lean_dec(v_v_4193_);
lean_dec(v_k_4192_);
v___x_4795_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0___redArg___closed__4);
v___x_4796_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Std_DTreeMap_Internal_Impl_union_x21___at___00Std_DTreeMap_Raw_union_spec__0_spec__0_spec__1___redArg(v___x_4795_);
return v___x_4796_;
}
}
}
}
else
{
lean_object* v_size_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v_size_4803_ = lean_ctor_get(v___x_4710_, 0);
v___x_4804_ = lean_unsigned_to_nat(1u);
v___x_4805_ = lean_nat_add(v___x_4804_, v_size_4803_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v___x_4710_);
lean_ctor_set(v___x_4197_, 0, v___x_4805_);
v___x_4807_ = v___x_4197_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4808_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4808_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4808_, 3, v_l_4194_);
lean_ctor_set(v_reuseFailAlloc_4808_, 4, v___x_4710_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
else
{
if (lean_obj_tag(v_l_4194_) == 0)
{
lean_object* v_l_4809_; 
v_l_4809_ = lean_ctor_get(v_l_4194_, 3);
if (lean_obj_tag(v_l_4809_) == 0)
{
lean_object* v_r_4810_; 
lean_inc_ref(v_l_4809_);
v_r_4810_ = lean_ctor_get(v_l_4194_, 4);
lean_inc(v_r_4810_);
if (lean_obj_tag(v_r_4810_) == 0)
{
lean_object* v_size_4811_; lean_object* v_k_4812_; lean_object* v_v_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4827_; 
v_size_4811_ = lean_ctor_get(v_l_4194_, 0);
v_k_4812_ = lean_ctor_get(v_l_4194_, 1);
v_v_4813_ = lean_ctor_get(v_l_4194_, 2);
v_isSharedCheck_4827_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4827_ == 0)
{
lean_object* v_unused_4828_; lean_object* v_unused_4829_; 
v_unused_4828_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4828_);
v_unused_4829_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4829_);
v___x_4815_ = v_l_4194_;
v_isShared_4816_ = v_isSharedCheck_4827_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_v_4813_);
lean_inc(v_k_4812_);
lean_inc(v_size_4811_);
lean_dec(v_l_4194_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4827_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v_size_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
v_size_4817_ = lean_ctor_get(v_r_4810_, 0);
v___x_4818_ = lean_unsigned_to_nat(1u);
v___x_4819_ = lean_nat_add(v___x_4818_, v_size_4811_);
lean_dec(v_size_4811_);
v___x_4820_ = lean_nat_add(v___x_4818_, v_size_4817_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 4, v___x_4710_);
lean_ctor_set(v___x_4815_, 3, v_r_4810_);
lean_ctor_set(v___x_4815_, 2, v_v_4193_);
lean_ctor_set(v___x_4815_, 1, v_k_4192_);
lean_ctor_set(v___x_4815_, 0, v___x_4820_);
v___x_4822_ = v___x_4815_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4820_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4826_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4826_, 3, v_r_4810_);
lean_ctor_set(v_reuseFailAlloc_4826_, 4, v___x_4710_);
v___x_4822_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
lean_object* v___x_4824_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v___x_4822_);
lean_ctor_set(v___x_4197_, 3, v_l_4809_);
lean_ctor_set(v___x_4197_, 2, v_v_4813_);
lean_ctor_set(v___x_4197_, 1, v_k_4812_);
lean_ctor_set(v___x_4197_, 0, v___x_4819_);
v___x_4824_ = v___x_4197_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4819_);
lean_ctor_set(v_reuseFailAlloc_4825_, 1, v_k_4812_);
lean_ctor_set(v_reuseFailAlloc_4825_, 2, v_v_4813_);
lean_ctor_set(v_reuseFailAlloc_4825_, 3, v_l_4809_);
lean_ctor_set(v_reuseFailAlloc_4825_, 4, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
else
{
lean_object* v_k_4830_; lean_object* v_v_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4843_; 
v_k_4830_ = lean_ctor_get(v_l_4194_, 1);
v_v_4831_ = lean_ctor_get(v_l_4194_, 2);
v_isSharedCheck_4843_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4843_ == 0)
{
lean_object* v_unused_4844_; lean_object* v_unused_4845_; lean_object* v_unused_4846_; 
v_unused_4844_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4844_);
v_unused_4845_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4845_);
v_unused_4846_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4846_);
v___x_4833_ = v_l_4194_;
v_isShared_4834_ = v_isSharedCheck_4843_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_v_4831_);
lean_inc(v_k_4830_);
lean_dec(v_l_4194_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4843_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
v___x_4835_ = lean_unsigned_to_nat(3u);
v___x_4836_ = lean_unsigned_to_nat(1u);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 3, v_r_4810_);
lean_ctor_set(v___x_4833_, 2, v_v_4193_);
lean_ctor_set(v___x_4833_, 1, v_k_4192_);
lean_ctor_set(v___x_4833_, 0, v___x_4836_);
v___x_4838_ = v___x_4833_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4836_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4842_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4842_, 3, v_r_4810_);
lean_ctor_set(v_reuseFailAlloc_4842_, 4, v_r_4810_);
v___x_4838_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
lean_object* v___x_4840_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v___x_4838_);
lean_ctor_set(v___x_4197_, 3, v_l_4809_);
lean_ctor_set(v___x_4197_, 2, v_v_4831_);
lean_ctor_set(v___x_4197_, 1, v_k_4830_);
lean_ctor_set(v___x_4197_, 0, v___x_4835_);
v___x_4840_ = v___x_4197_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_k_4830_);
lean_ctor_set(v_reuseFailAlloc_4841_, 2, v_v_4831_);
lean_ctor_set(v_reuseFailAlloc_4841_, 3, v_l_4809_);
lean_ctor_set(v_reuseFailAlloc_4841_, 4, v___x_4838_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
else
{
lean_object* v_r_4847_; 
v_r_4847_ = lean_ctor_get(v_l_4194_, 4);
lean_inc(v_r_4847_);
if (lean_obj_tag(v_r_4847_) == 0)
{
lean_object* v_k_4848_; lean_object* v_v_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4873_; 
lean_inc(v_l_4809_);
v_k_4848_ = lean_ctor_get(v_l_4194_, 1);
v_v_4849_ = lean_ctor_get(v_l_4194_, 2);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_l_4194_);
if (v_isSharedCheck_4873_ == 0)
{
lean_object* v_unused_4874_; lean_object* v_unused_4875_; lean_object* v_unused_4876_; 
v_unused_4874_ = lean_ctor_get(v_l_4194_, 4);
lean_dec(v_unused_4874_);
v_unused_4875_ = lean_ctor_get(v_l_4194_, 3);
lean_dec(v_unused_4875_);
v_unused_4876_ = lean_ctor_get(v_l_4194_, 0);
lean_dec(v_unused_4876_);
v___x_4851_ = v_l_4194_;
v_isShared_4852_ = v_isSharedCheck_4873_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_v_4849_);
lean_inc(v_k_4848_);
lean_dec(v_l_4194_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4873_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v_k_4853_; lean_object* v_v_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4869_; 
v_k_4853_ = lean_ctor_get(v_r_4847_, 1);
v_v_4854_ = lean_ctor_get(v_r_4847_, 2);
v_isSharedCheck_4869_ = !lean_is_exclusive(v_r_4847_);
if (v_isSharedCheck_4869_ == 0)
{
lean_object* v_unused_4870_; lean_object* v_unused_4871_; lean_object* v_unused_4872_; 
v_unused_4870_ = lean_ctor_get(v_r_4847_, 4);
lean_dec(v_unused_4870_);
v_unused_4871_ = lean_ctor_get(v_r_4847_, 3);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_r_4847_, 0);
lean_dec(v_unused_4872_);
v___x_4856_ = v_r_4847_;
v_isShared_4857_ = v_isSharedCheck_4869_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_v_4854_);
lean_inc(v_k_4853_);
lean_dec(v_r_4847_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4869_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4861_; 
v___x_4858_ = lean_unsigned_to_nat(3u);
v___x_4859_ = lean_unsigned_to_nat(1u);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 4, v_l_4809_);
lean_ctor_set(v___x_4856_, 3, v_l_4809_);
lean_ctor_set(v___x_4856_, 2, v_v_4849_);
lean_ctor_set(v___x_4856_, 1, v_k_4848_);
lean_ctor_set(v___x_4856_, 0, v___x_4859_);
v___x_4861_ = v___x_4856_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v_k_4848_);
lean_ctor_set(v_reuseFailAlloc_4868_, 2, v_v_4849_);
lean_ctor_set(v_reuseFailAlloc_4868_, 3, v_l_4809_);
lean_ctor_set(v_reuseFailAlloc_4868_, 4, v_l_4809_);
v___x_4861_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
lean_object* v___x_4863_; 
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 4, v_l_4809_);
lean_ctor_set(v___x_4851_, 2, v_v_4193_);
lean_ctor_set(v___x_4851_, 1, v_k_4192_);
lean_ctor_set(v___x_4851_, 0, v___x_4859_);
v___x_4863_ = v___x_4851_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4867_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4867_, 3, v_l_4809_);
lean_ctor_set(v_reuseFailAlloc_4867_, 4, v_l_4809_);
v___x_4863_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
lean_object* v___x_4865_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v___x_4863_);
lean_ctor_set(v___x_4197_, 3, v___x_4861_);
lean_ctor_set(v___x_4197_, 2, v_v_4854_);
lean_ctor_set(v___x_4197_, 1, v_k_4853_);
lean_ctor_set(v___x_4197_, 0, v___x_4858_);
v___x_4865_ = v___x_4197_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4858_);
lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_k_4853_);
lean_ctor_set(v_reuseFailAlloc_4866_, 2, v_v_4854_);
lean_ctor_set(v_reuseFailAlloc_4866_, 3, v___x_4861_);
lean_ctor_set(v_reuseFailAlloc_4866_, 4, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
}
}
else
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4877_ = lean_unsigned_to_nat(2u);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v_r_4847_);
lean_ctor_set(v___x_4197_, 0, v___x_4877_);
v___x_4879_ = v___x_4197_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4880_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4880_, 3, v_l_4194_);
lean_ctor_set(v_reuseFailAlloc_4880_, 4, v_r_4847_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4881_ = lean_unsigned_to_nat(1u);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 4, v_l_4194_);
lean_ctor_set(v___x_4197_, 0, v___x_4881_);
v___x_4883_ = v___x_4197_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_k_4192_);
lean_ctor_set(v_reuseFailAlloc_4884_, 2, v_v_4193_);
lean_ctor_set(v_reuseFailAlloc_4884_, 3, v_l_4194_);
lean_ctor_set(v_reuseFailAlloc_4884_, 4, v_l_4194_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
}
}
}
else
{
lean_dec(v_k_4190_);
lean_dec_ref(v_cmp_4189_);
return v_t_4191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(lean_object* v_cmp_4887_, lean_object* v_init_4888_, lean_object* v_x_4889_){
_start:
{
if (lean_obj_tag(v_x_4889_) == 0)
{
lean_object* v_k_4890_; lean_object* v_l_4891_; lean_object* v_r_4892_; lean_object* v___x_4893_; lean_object* v_a_4894_; lean_object* v_r_4895_; 
v_k_4890_ = lean_ctor_get(v_x_4889_, 1);
lean_inc(v_k_4890_);
v_l_4891_ = lean_ctor_get(v_x_4889_, 3);
lean_inc(v_l_4891_);
v_r_4892_ = lean_ctor_get(v_x_4889_, 4);
lean_inc(v_r_4892_);
lean_dec_ref_known(v_x_4889_, 5);
lean_inc_ref_n(v_cmp_4887_, 2);
v___x_4893_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4887_, v_init_4888_, v_l_4891_);
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref(v___x_4893_);
v_r_4895_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4887_, v_k_4890_, v_a_4894_);
v_init_4888_ = v_r_4895_;
v_x_4889_ = v_r_4892_;
goto _start;
}
else
{
lean_object* v___x_4897_; 
lean_dec_ref(v_cmp_4887_);
v___x_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4897_, 0, v_init_4888_);
return v___x_4897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(lean_object* v_cmp_4898_, lean_object* v_t_u2081_4899_, lean_object* v_t_u2082_4900_){
_start:
{
lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4909_; 
if (lean_obj_tag(v_t_u2081_4899_) == 0)
{
lean_object* v_size_4912_; 
v_size_4912_ = lean_ctor_get(v_t_u2081_4899_, 0);
lean_inc(v_size_4912_);
v___y_4909_ = v_size_4912_;
goto v___jp_4908_;
}
else
{
lean_object* v___x_4913_; 
v___x_4913_ = lean_unsigned_to_nat(0u);
v___y_4909_ = v___x_4913_;
goto v___jp_4908_;
}
v___jp_4901_:
{
uint8_t v___x_4904_; 
v___x_4904_ = lean_nat_dec_le(v___y_4902_, v___y_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; lean_object* v_a_4906_; 
lean_dec(v___y_4903_);
lean_dec(v___y_4902_);
v___x_4905_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4898_, v_t_u2081_4899_, v_t_u2082_4900_);
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc(v_a_4906_);
lean_dec_ref(v___x_4905_);
return v_a_4906_;
}
else
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4898_, v_t_u2082_4900_, v___y_4902_, v___y_4903_, v_t_u2081_4899_);
lean_dec(v___y_4903_);
lean_dec(v___y_4902_);
return v___x_4907_;
}
}
v___jp_4908_:
{
if (lean_obj_tag(v_t_u2082_4900_) == 0)
{
lean_object* v_size_4910_; 
v_size_4910_ = lean_ctor_get(v_t_u2082_4900_, 0);
lean_inc(v_size_4910_);
v___y_4902_ = v___y_4909_;
v___y_4903_ = v_size_4910_;
goto v___jp_4901_;
}
else
{
lean_object* v___x_4911_; 
v___x_4911_ = lean_unsigned_to_nat(0u);
v___y_4902_ = v___y_4909_;
v___y_4903_ = v___x_4911_;
goto v___jp_4901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff___redArg(lean_object* v_cmp_4914_, lean_object* v_t_u2081_4915_, lean_object* v_t_u2082_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4914_, v_t_u2081_4915_, v_t_u2082_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_diff(lean_object* v_00_u03b1_4918_, lean_object* v_00_u03b2_4919_, lean_object* v_cmp_4920_, lean_object* v_t_u2081_4921_, lean_object* v_t_u2082_4922_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4920_, v_t_u2081_4921_, v_t_u2082_4922_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0(lean_object* v_00_u03b1_4924_, lean_object* v_cmp_4925_, lean_object* v_00_u03b2_4926_, lean_object* v_t_u2081_4927_, lean_object* v_t_u2082_4928_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0___redArg(v_cmp_4925_, v_t_u2081_4927_, v_t_u2082_4928_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0(lean_object* v_00_u03b1_4930_, lean_object* v_cmp_4931_, lean_object* v_00_u03b2_4932_, lean_object* v_k_4933_, lean_object* v_t_4934_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__0___redArg(v_cmp_4931_, v_k_4933_, v_t_4934_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1(lean_object* v_00_u03b1_4936_, lean_object* v_00_u03b2_4937_, lean_object* v_cmp_4938_, lean_object* v_init_4939_, lean_object* v_x_4940_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__1___redArg(v_cmp_4938_, v_init_4939_, v_x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(lean_object* v_00_u03b1_4942_, lean_object* v_00_u03b2_4943_, lean_object* v_cmp_4944_, lean_object* v_t_u2082_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v_t_4948_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___redArg(v_cmp_4944_, v_t_u2082_4945_, v___y_4946_, v___y_4947_, v_t_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4950_, lean_object* v_00_u03b2_4951_, lean_object* v_cmp_4952_, lean_object* v_t_u2082_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v_t_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Std_DTreeMap_Internal_Impl_filter_x21___at___00Std_DTreeMap_Internal_Impl_diff_x21___at___00Std_DTreeMap_Raw_diff_spec__0_spec__2(v_00_u03b1_4950_, v_00_u03b2_4951_, v_cmp_4952_, v_t_u2082_4953_, v___y_4954_, v___y_4955_, v_t_4956_);
lean_dec(v___y_4955_);
lean_dec(v___y_4954_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff___redArg(lean_object* v_cmp_4958_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4959_, 0, lean_box(0));
lean_closure_set(v___x_4959_, 1, lean_box(0));
lean_closure_set(v___x_4959_, 2, v_cmp_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instSDiff(lean_object* v_00_u03b1_4960_, lean_object* v_00_u03b2_4961_, lean_object* v_cmp_4962_){
_start:
{
lean_object* v___x_4963_; 
v___x_4963_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_diff), 5, 3);
lean_closure_set(v___x_4963_, 0, lean_box(0));
lean_closure_set(v___x_4963_, 1, lean_box(0));
lean_closure_set(v___x_4963_, 2, v_cmp_4962_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0(lean_object* v_cmp_4964_, lean_object* v_a_4965_, lean_object* v_____s_4966_){
_start:
{
lean_object* v_r_4967_; lean_object* v___x_4968_; 
v_r_4967_ = l_Std_DTreeMap_Internal_Impl_erase_x21___redArg(v_cmp_4964_, v_a_4965_, v_____s_4966_);
v___x_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_r_4967_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany___redArg(lean_object* v_cmp_4969_, lean_object* v_inst_4970_, lean_object* v_t_4971_, lean_object* v_l_4972_){
_start:
{
lean_object* v___f_4973_; lean_object* v___x_4974_; 
v___f_4973_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4973_, 0, v_cmp_4969_);
v___x_4974_ = lean_apply_4(v_inst_4970_, lean_box(0), v_l_4972_, v_t_4971_, v___f_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_eraseMany(lean_object* v_00_u03b1_4975_, lean_object* v_00_u03b2_4976_, lean_object* v_cmp_4977_, lean_object* v_00_u03c1_4978_, lean_object* v_inst_4979_, lean_object* v_t_4980_, lean_object* v_l_4981_){
_start:
{
lean_object* v___f_4982_; lean_object* v___x_4983_; 
v___f_4982_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_eraseMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4982_, 0, v_cmp_4977_);
v___x_4983_ = lean_apply_4(v_inst_4979_, lean_box(0), v_l_4981_, v_t_4980_, v___f_4982_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0(lean_object* v_cmp_4984_, lean_object* v_x_4985_, lean_object* v_____s_4986_){
_start:
{
lean_object* v_fst_4987_; lean_object* v_snd_4988_; lean_object* v_r_4989_; lean_object* v___x_4990_; 
v_fst_4987_ = lean_ctor_get(v_x_4985_, 0);
lean_inc(v_fst_4987_);
v_snd_4988_ = lean_ctor_get(v_x_4985_, 1);
lean_inc(v_snd_4988_);
lean_dec_ref(v_x_4985_);
v_r_4989_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_4984_, v_fst_4987_, v_snd_4988_, v_____s_4986_);
v___x_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4990_, 0, v_r_4989_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany___redArg(lean_object* v_cmp_4991_, lean_object* v_inst_4992_, lean_object* v_t_4993_, lean_object* v_l_4994_){
_start:
{
lean_object* v___f_4995_; lean_object* v___x_4996_; 
v___f_4995_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4995_, 0, v_cmp_4991_);
v___x_4996_ = lean_apply_4(v_inst_4992_, lean_box(0), v_l_4994_, v_t_4993_, v___f_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertMany(lean_object* v_00_u03b1_4997_, lean_object* v_cmp_4998_, lean_object* v_00_u03b2_4999_, lean_object* v_00_u03c1_5000_, lean_object* v_inst_5001_, lean_object* v_t_5002_, lean_object* v_l_5003_){
_start:
{
lean_object* v___f_5004_; lean_object* v___x_5005_; 
v___f_5004_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertMany___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5004_, 0, v_cmp_4998_);
v___x_5005_ = lean_apply_4(v_inst_5001_, lean_box(0), v_l_5003_, v_t_5002_, v___f_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_cmp_5006_, lean_object* v_a_5007_, lean_object* v_____s_5008_){
_start:
{
uint8_t v___x_5009_; 
lean_inc(v_____s_5008_);
lean_inc(v_a_5007_);
lean_inc_ref(v_cmp_5006_);
v___x_5009_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_cmp_5006_, v_a_5007_, v_____s_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5010_ = lean_box(0);
v___x_5011_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v_cmp_5006_, v_a_5007_, v___x_5010_, v_____s_5008_);
v___x_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
return v___x_5012_;
}
else
{
lean_object* v___x_5013_; 
lean_dec(v_a_5007_);
lean_dec_ref(v_cmp_5006_);
v___x_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5013_, 0, v_____s_5008_);
return v___x_5013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_cmp_5014_, lean_object* v_inst_5015_, lean_object* v_t_5016_, lean_object* v_l_5017_){
_start:
{
lean_object* v___f_5018_; lean_object* v___x_5019_; 
v___f_5018_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5018_, 0, v_cmp_5014_);
v___x_5019_ = lean_apply_4(v_inst_5015_, lean_box(0), v_l_5017_, v_t_5016_, v___f_5018_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_5020_, lean_object* v_cmp_5021_, lean_object* v_00_u03c1_5022_, lean_object* v_inst_5023_, lean_object* v_t_5024_, lean_object* v_l_5025_){
_start:
{
lean_object* v___f_5026_; lean_object* v___x_5027_; 
v___f_5026_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_Const_insertManyIfNewUnit___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5026_, 0, v_cmp_5021_);
v___x_5027_ = lean_apply_4(v_inst_5023_, lean_box(0), v_l_5025_, v_t_5024_, v___f_5026_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_5031_, lean_object* v___x_5032_, lean_object* v_m_5033_, lean_object* v_prec_5034_){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5035_ = ((lean_object*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_5036_ = lean_box(0);
v___x_5037_ = ((lean_object*)(l_Std_DTreeMap_Raw_foldr___redArg___closed__9));
v___x_5038_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_5037_, v___f_5031_, v___x_5036_, v_m_5033_);
v___x_5039_ = l_List_repr___redArg(v___x_5032_, v___x_5038_);
v___x_5040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5035_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
v___x_5041_ = l_Repr_addAppParen(v___x_5040_, v_prec_5034_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_5042_, lean_object* v___x_5043_, lean_object* v_m_5044_, lean_object* v_prec_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Std_DTreeMap_Raw_instRepr___redArg___lam__1(v___f_5042_, v___x_5043_, v_m_5044_, v_prec_5045_);
lean_dec(v_prec_5045_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___redArg(lean_object* v_inst_5047_, lean_object* v_inst_5048_){
_start:
{
lean_object* v___f_5049_; lean_object* v___x_5050_; lean_object* v___f_5051_; 
v___f_5049_ = ((lean_object*)(l_Std_DTreeMap_Raw_toList___redArg___closed__0));
v___x_5050_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_5050_, 0, lean_box(0));
lean_closure_set(v___x_5050_, 1, lean_box(0));
lean_closure_set(v___x_5050_, 2, v_inst_5047_);
lean_closure_set(v___x_5050_, 3, v_inst_5048_);
v___f_5051_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5051_, 0, v___f_5049_);
lean_closure_set(v___f_5051_, 1, v___x_5050_);
return v___f_5051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr(lean_object* v_00_u03b1_5052_, lean_object* v_00_u03b2_5053_, lean_object* v_cmp_5054_, lean_object* v_inst_5055_, lean_object* v_inst_5056_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Std_DTreeMap_Raw_instRepr___redArg(v_inst_5055_, v_inst_5056_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Raw_instRepr___boxed(lean_object* v_00_u03b1_5058_, lean_object* v_00_u03b2_5059_, lean_object* v_cmp_5060_, lean_object* v_inst_5061_, lean_object* v_inst_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Std_DTreeMap_Raw_instRepr(v_00_u03b1_5058_, v_00_u03b2_5059_, v_cmp_5060_, v_inst_5061_, v_inst_5062_);
lean_dec_ref(v_cmp_5060_);
return v_res_5063_;
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
