// Lean compiler output
// Module: Lean.Data.Options
// Imports: public import Lean.ImportingFlag public import Lean.Data.KVMap public import Lean.Data.NameMap.Basic import Init.Data.ToString.Macro
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_data_value_to_string(lean_object*);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqDataValue_beq___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDataValue_default;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_ctor_object l_Lean_Options_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Options_empty___closed__0 = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_empty = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_Options_instInhabited = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Options_instToString___private__1___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__0 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__0_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__1 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__1_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_data_value_to_string, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__2 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__2_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringProd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Options_instToString___private__1___closed__1_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__2_value)} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__3 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__3_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__4 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__4_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__5 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__5_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__6 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__6_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__7 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__7_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__8 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__8_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__9 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__9_value;
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___private__1___closed__10 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__10_value;
static const lean_ctor_object l_Lean_Options_instToString___private__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Options_instToString___private__1___closed__4_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__5_value)}};
static const lean_object* l_Lean_Options_instToString___private__1___closed__11 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__11_value;
static const lean_ctor_object l_Lean_Options_instToString___private__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Options_instToString___private__1___closed__11_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__6_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__7_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__8_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__9_value)}};
static const lean_object* l_Lean_Options_instToString___private__1___closed__12 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__12_value;
static const lean_ctor_object l_Lean_Options_instToString___private__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Options_instToString___private__1___closed__12_value),((lean_object*)&l_Lean_Options_instToString___private__1___closed__10_value)}};
static const lean_object* l_Lean_Options_instToString___private__1___closed__13 = (const lean_object*)&l_Lean_Options_instToString___private__1___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instToString___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Options_instToString___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Options_instToString___private__1___closed__0_value)} };
static const lean_object* l_Lean_Options_instToString___closed__0 = (const lean_object*)&l_Lean_Options_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_instToString = (const lean_object*)&l_Lean_Options_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_instBEq___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqDataValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instBEq___private__1___closed__0 = (const lean_object*)&l_Lean_Options_instBEq___private__1___closed__0_value;
static const lean_closure_object l_Lean_Options_instBEq___private__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instBEq___private__1___closed__1 = (const lean_object*)&l_Lean_Options_instBEq___private__1___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Options_instBEq___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instBEq___closed__0 = (const lean_object*)&l_Lean_Options_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_instBEq = (const lean_object*)&l_Lean_Options_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_instEmptyCollection = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Options_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_getBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Options_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_insert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_insert___closed__0 = (const lean_object*)&l_Lean_Options_insert___closed__0_value;
static const lean_ctor_object l_Lean_Options_insert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_insert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_insert___closed__1 = (const lean_object*)&l_Lean_Options_insert___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Options_erase_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Options_erase_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedOptionDeprecation_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedOptionDeprecation_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedOptionDeprecation_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedOptionDeprecation_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedOptionDeprecation_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedOptionDeprecation_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedOptionDeprecation_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedOptionDeprecation_default = (const lean_object*)&l_Lean_instInhabitedOptionDeprecation_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedOptionDeprecation = (const lean_object*)&l_Lean_instInhabitedOptionDeprecation_default___closed__1_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__0 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__1 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__2 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__2_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__3 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__4 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value;
static const lean_array_object l_Lean_OptionDecl_declName___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__5 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__5_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__6 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__7 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__7_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__8 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__9 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__9_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__10 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__11 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__12;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__13;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__14 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__15 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__16 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__16_value;
static const lean_string_object l_Lean_OptionDecl_declName___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__17 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__18;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__19;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__20;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__21;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__22;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__23;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__24;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__25;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__26;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__27;
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_OptionDecl_declName___autoParam;
static const lean_string_object l_Lean_instInhabitedOptionDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "instInhabitedOptionDecl"};
static const lean_object* l_Lean_instInhabitedOptionDecl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__0_value;
static const lean_string_object l_Lean_instInhabitedOptionDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_instInhabitedOptionDecl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_0),((lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 8, 149, 203, 82, 241, 178)}};
static const lean_ctor_object l_Lean_instInhabitedOptionDecl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__2_value_aux_1),((lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 172, 126, 56, 195, 32, 77, 110)}};
static const lean_object* l_Lean_instInhabitedOptionDecl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedOptionDecl_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedOptionDecl_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptionDecl_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptionDecl;
static const lean_string_object l_Lean_OptionDecl_fullDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 218, .m_capacity = 218, .m_length = 217, .m_data = "This is a backwards compatibility option, intended to help migrating to new Lean releases. It may be removed without further notice 6 months after their introduction. Please report an issue if you rely on this option."};
static const lean_object* l_Lean_OptionDecl_fullDescr___closed__0 = (const lean_object*)&l_Lean_OptionDecl_fullDescr___closed__0_value;
static const lean_string_object l_Lean_OptionDecl_fullDescr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_OptionDecl_fullDescr___closed__1 = (const lean_object*)&l_Lean_OptionDecl_fullDescr___closed__1_value;
static const lean_ctor_object l_Lean_OptionDecl_fullDescr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_fullDescr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_object* l_Lean_OptionDecl_fullDescr___closed__2 = (const lean_object*)&l_Lean_OptionDecl_fullDescr___closed__2_value;
static const lean_string_object l_Lean_OptionDecl_fullDescr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_OptionDecl_fullDescr___closed__3 = (const lean_object*)&l_Lean_OptionDecl_fullDescr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptionDecls;
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
static const lean_string_object l_Lean_registerOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "Failed to register option: Options can only be registered during initialization"};
static const lean_object* l_Lean_registerOption___closed__0 = (const lean_object*)&l_Lean_registerOption___closed__0_value;
static lean_once_cell_t l_Lean_registerOption___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerOption___closed__1;
static const lean_string_object l_Lean_registerOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Invalid option declaration `"};
static const lean_object* l_Lean_registerOption___closed__2 = (const lean_object*)&l_Lean_registerOption___closed__2_value;
static const lean_string_object l_Lean_registerOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "`: Option already exists"};
static const lean_object* l_Lean_registerOption___closed__3 = (const lean_object*)&l_Lean_registerOption___closed__3_value;
LEAN_EXPORT lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDecls();
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_getOptionDeclsArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getOptionDeclsArray___closed__0 = (const lean_object*)&l_Lean_getOptionDeclsArray___closed__0_value;
LEAN_EXPORT lean_object* lean_get_option_decls_array();
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_getOptionDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Unknown option `"};
static const lean_object* l_Lean_getOptionDecl___closed__0 = (const lean_object*)&l_Lean_getOptionDecl___closed__0_value;
static const lean_string_object l_Lean_getOptionDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getOptionDecl___closed__1 = (const lean_object*)&l_Lean_getOptionDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_withInPattern___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_inPattern"};
static const lean_object* l_Lean_withInPattern___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_withInPattern___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_withInPattern___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_withInPattern___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 19, 88, 13, 241, 130, 160, 23)}};
static const lean_object* l_Lean_withInPattern___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_withInPattern___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withInPattern___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withInPattern___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___auto__1;
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__0 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "registerBuiltinOption"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__1 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__1_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__2_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__2_value_aux_1),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 128, 225, 170, 242, 224, 12, 82)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__2 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__2_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__3 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__3_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__4 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__5 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__5_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__6 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__6_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__7 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__7_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__7_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__8 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__8_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__8_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__9 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__9_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__6_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__9_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__10 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__10_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "visibility"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__11 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__11_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 205, 25, 140, 55, 50, 241, 254)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__12 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__12_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__12_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__13 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__13_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__6_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__13_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__14 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__14_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__10_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__14_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__15 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__15_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "register_builtin_option"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__16 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__16_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__16_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__17 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__17_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__15_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__17_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__18 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__18_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__19 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__19_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__19_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__20 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__20_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__20_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__21 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__21_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__18_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__21_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__22 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__22_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__23 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__23_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__23_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__24 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__24_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__22_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__24_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__25 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__25_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__26 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__26_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__26_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__27 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__27_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__28 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__28_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__25_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__28_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__29 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__29_value;
static const lean_string_object l_Lean_Option_registerBuiltinOption___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__30 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__30_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__30_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__31 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__31_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__29_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__31_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__32 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__32_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__32_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__28_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__33 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__33_value;
static const lean_ctor_object l_Lean_Option_registerBuiltinOption___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__33_value)}};
static const lean_object* l_Lean_Option_registerBuiltinOption___closed__34 = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__34_value;
LEAN_EXPORT const lean_object* l_Lean_Option_registerBuiltinOption = (const lean_object*)&l_Lean_Option_registerBuiltinOption___closed__34_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "initializeKeyword"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "builtin_initialize"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Option"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5_value;
static lean_once_cell_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7_value)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__8_value),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10_value)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "←"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Option.register"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16_value;
static lean_once_cell_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "register"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(127, 81, 22, 2, 70, 205, 7, 158)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28_value;
static lean_once_cell_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29;
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Option_registerOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "registerOption"};
static const lean_object* l_Lean_Option_registerOption___closed__0 = (const lean_object*)&l_Lean_Option_registerOption___closed__0_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option_registerOption___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__1_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l_Lean_Option_registerOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__1_value_aux_1),((lean_object*)&l_Lean_Option_registerOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 95, 60, 142, 241, 184, 36, 53)}};
static const lean_object* l_Lean_Option_registerOption___closed__1 = (const lean_object*)&l_Lean_Option_registerOption___closed__1_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(113, 135, 0, 93, 130, 217, 220, 132)}};
static const lean_object* l_Lean_Option_registerOption___closed__2 = (const lean_object*)&l_Lean_Option_registerOption___closed__2_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__2_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__3 = (const lean_object*)&l_Lean_Option_registerOption___closed__3_value;
static const lean_string_object l_Lean_Option_registerOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "register_option"};
static const lean_object* l_Lean_Option_registerOption___closed__4 = (const lean_object*)&l_Lean_Option_registerOption___closed__4_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__4_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__5 = (const lean_object*)&l_Lean_Option_registerOption___closed__5_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerOption___closed__3_value),((lean_object*)&l_Lean_Option_registerOption___closed__5_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__6 = (const lean_object*)&l_Lean_Option_registerOption___closed__6_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerOption___closed__6_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__21_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__7 = (const lean_object*)&l_Lean_Option_registerOption___closed__7_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerOption___closed__7_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__24_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__8 = (const lean_object*)&l_Lean_Option_registerOption___closed__8_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerOption___closed__8_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__28_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__9 = (const lean_object*)&l_Lean_Option_registerOption___closed__9_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerOption___closed__9_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__31_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__10 = (const lean_object*)&l_Lean_Option_registerOption___closed__10_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__4_value),((lean_object*)&l_Lean_Option_registerOption___closed__10_value),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__28_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__11 = (const lean_object*)&l_Lean_Option_registerOption___closed__11_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Option_registerOption___closed__11_value)}};
static const lean_object* l_Lean_Option_registerOption___closed__12 = (const lean_object*)&l_Lean_Option_registerOption___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean_Option_registerOption = (const lean_object*)&l_Lean_Option_registerOption___closed__12_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 140, 114, 135, 71, 133, 96, 5)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = ((lean_object*)(l_Lean_Options_empty));
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___lam__0(lean_object* v_x1_8_, lean_object* v_x2_9_, lean_object* v_x3_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_x1_8_);
lean_ctor_set(v___x_11_, 1, v_x2_9_);
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_x3_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object* v_o_38_){
_start:
{
lean_object* v_map_39_; lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_map_39_ = lean_ctor_get(v_o_38_, 0);
lean_inc(v_map_39_);
lean_dec_ref(v_o_38_);
v___f_40_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__0));
v___f_41_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__3));
v___x_42_ = lean_box(0);
v___x_43_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__13));
v___x_44_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_43_, v___f_40_, v___x_42_, v_map_39_);
v___x_45_ = l_List_toString___redArg(v___f_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___lam__1(lean_object* v___f_46_, lean_object* v_o_47_){
_start:
{
lean_object* v_map_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_map_48_ = lean_ctor_get(v_o_47_, 0);
lean_inc(v_map_48_);
lean_dec_ref(v_o_47_);
v___f_49_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__3));
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__13));
v___x_52_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_51_, v___f_46_, v___x_50_, v_map_48_);
v___x_53_ = l_List_toString___redArg(v___f_49_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object* v_f_57_, lean_object* v_a_58_, lean_object* v_b_59_, lean_object* v_c_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_a_58_);
lean_ctor_set(v___x_61_, 1, v_b_59_);
v___x_62_ = lean_apply_2(v_f_57_, v___x_61_, v_c_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object* v_toPure_63_, lean_object* v_____do__lift_64_){
_start:
{
lean_object* v_a_65_; lean_object* v___x_66_; 
v_a_65_ = lean_ctor_get(v_____do__lift_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref(v_____do__lift_64_);
v___x_66_ = lean_apply_2(v_toPure_63_, lean_box(0), v_a_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object* v_inst_67_, lean_object* v_o_68_, lean_object* v_init_69_, lean_object* v_f_70_){
_start:
{
lean_object* v_toApplicative_71_; lean_object* v_map_72_; lean_object* v_toBind_73_; lean_object* v_toPure_74_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v_toApplicative_71_ = lean_ctor_get(v_inst_67_, 0);
v_map_72_ = lean_ctor_get(v_o_68_, 0);
lean_inc(v_map_72_);
lean_dec_ref(v_o_68_);
v_toBind_73_ = lean_ctor_get(v_inst_67_, 1);
lean_inc(v_toBind_73_);
v_toPure_74_ = lean_ctor_get(v_toApplicative_71_, 1);
lean_inc(v_toPure_74_);
v___f_75_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_75_, 0, v_f_70_);
v___x_76_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_67_, v___f_75_, v_init_69_, v_map_72_);
v___f_77_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_77_, 0, v_toPure_74_);
v___x_78_ = lean_apply_4(v_toBind_73_, lean_box(0), lean_box(0), v___x_76_, v___f_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object* v_m_79_, lean_object* v_inst_80_, lean_object* v_00_u03b2_81_, lean_object* v_o_82_, lean_object* v_init_83_, lean_object* v_f_84_){
_start:
{
lean_object* v_toApplicative_85_; lean_object* v_map_86_; lean_object* v_toBind_87_; lean_object* v_toPure_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v_toApplicative_85_ = lean_ctor_get(v_inst_80_, 0);
v_map_86_ = lean_ctor_get(v_o_82_, 0);
lean_inc(v_map_86_);
lean_dec_ref(v_o_82_);
v_toBind_87_ = lean_ctor_get(v_inst_80_, 1);
lean_inc(v_toBind_87_);
v_toPure_88_ = lean_ctor_get(v_toApplicative_85_, 1);
lean_inc(v_toPure_88_);
v___f_89_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_89_, 0, v_f_84_);
v___x_90_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_80_, v___f_89_, v_init_83_, v_map_86_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_91_, 0, v_toPure_88_);
v___x_92_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_90_, v___f_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2(lean_object* v_inst_93_, lean_object* v_00_u03b2_94_, lean_object* v_o_95_, lean_object* v_init_96_, lean_object* v_f_97_){
_start:
{
lean_object* v_toApplicative_98_; lean_object* v_map_99_; lean_object* v_toBind_100_; lean_object* v_toPure_101_; lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___x_105_; 
v_toApplicative_98_ = lean_ctor_get(v_inst_93_, 0);
v_map_99_ = lean_ctor_get(v_o_95_, 0);
lean_inc(v_map_99_);
lean_dec_ref(v_o_95_);
v_toBind_100_ = lean_ctor_get(v_inst_93_, 1);
lean_inc(v_toBind_100_);
v_toPure_101_ = lean_ctor_get(v_toApplicative_98_, 1);
lean_inc(v_toPure_101_);
v___f_102_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_102_, 0, v_f_97_);
v___x_103_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_93_, v___f_102_, v_init_96_, v_map_99_);
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_104_, 0, v_toPure_101_);
v___x_105_ = lean_apply_4(v_toBind_100_, lean_box(0), lean_box(0), v___x_103_, v___f_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_106_){
_start:
{
lean_object* v___f_107_; 
v___f_107_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_107_, 0, v_inst_106_);
return v___f_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object* v_m_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v___f_110_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_110_, 0, v_inst_109_);
return v___f_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___private__1(lean_object* v_o1_113_, lean_object* v_o2_114_){
_start:
{
lean_object* v_map_115_; lean_object* v_map_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_map_115_ = lean_ctor_get(v_o1_113_, 0);
lean_inc(v_map_115_);
lean_dec_ref(v_o1_113_);
v_map_116_ = lean_ctor_get(v_o2_114_, 0);
lean_inc(v_map_116_);
lean_dec_ref(v_o2_114_);
v___x_117_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_118_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__1));
v___x_119_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v___x_118_, v___x_117_, v_map_115_, v_map_116_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object* v_o1_120_, lean_object* v_o2_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Lean_Options_instBEq___private__1(v_o1_120_, v_o2_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___lam__0(lean_object* v_o1_124_, lean_object* v_o2_125_){
_start:
{
lean_object* v_map_126_; lean_object* v_map_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_map_126_ = lean_ctor_get(v_o1_124_, 0);
lean_inc(v_map_126_);
lean_dec_ref(v_o1_124_);
v_map_127_ = lean_ctor_get(v_o2_125_, 0);
lean_inc(v_map_127_);
lean_dec_ref(v_o2_125_);
v___x_128_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_129_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__1));
v___x_130_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v___x_129_, v___x_128_, v_map_126_, v_map_127_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___lam__0___boxed(lean_object* v_o1_131_, lean_object* v_o2_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Options_instBEq___lam__0(v_o1_131_, v_o2_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f(lean_object* v_o_138_, lean_object* v_k_139_){
_start:
{
lean_object* v_map_140_; lean_object* v___x_141_; 
v_map_140_ = lean_ctor_get(v_o_138_, 0);
v___x_141_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_140_, v_k_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f___boxed(lean_object* v_o_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Options_find_x3f(v_o_142_, v_k_143_);
lean_dec(v_k_143_);
lean_dec_ref(v_o_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find(lean_object* v_o_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_map_147_; lean_object* v___x_148_; 
v_map_147_ = lean_ctor_get(v_o_145_, 0);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_147_, v_k_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find___boxed(lean_object* v_o_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Options_find(v_o_149_, v_k_150_);
lean_dec(v_k_150_);
lean_dec_ref(v_o_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg(lean_object* v_inst_152_, lean_object* v_o_153_, lean_object* v_k_154_){
_start:
{
lean_object* v_map_155_; lean_object* v_ofDataValue_x3f_156_; lean_object* v___x_157_; 
v_map_155_ = lean_ctor_get(v_o_153_, 0);
v_ofDataValue_x3f_156_ = lean_ctor_get(v_inst_152_, 1);
lean_inc_ref(v_ofDataValue_x3f_156_);
lean_dec_ref(v_inst_152_);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_155_, v_k_154_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v___x_158_; 
lean_dec_ref(v_ofDataValue_x3f_156_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_160_; 
v_val_159_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_val_159_);
lean_dec_ref(v___x_157_);
v___x_160_ = lean_apply_1(v_ofDataValue_x3f_156_, v_val_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg___boxed(lean_object* v_inst_161_, lean_object* v_o_162_, lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Options_get_x3f___redArg(v_inst_161_, v_o_162_, v_k_163_);
lean_dec(v_k_163_);
lean_dec_ref(v_o_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f(lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_o_167_, lean_object* v_k_168_){
_start:
{
lean_object* v_map_169_; lean_object* v_ofDataValue_x3f_170_; lean_object* v___x_171_; 
v_map_169_ = lean_ctor_get(v_o_167_, 0);
v_ofDataValue_x3f_170_ = lean_ctor_get(v_inst_166_, 1);
lean_inc_ref(v_ofDataValue_x3f_170_);
lean_dec_ref(v_inst_166_);
v___x_171_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_169_, v_k_168_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v___x_172_; 
lean_dec_ref(v_ofDataValue_x3f_170_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_174_; 
v_val_173_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_val_173_);
lean_dec_ref(v___x_171_);
v___x_174_ = lean_apply_1(v_ofDataValue_x3f_170_, v_val_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___boxed(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_o_177_, lean_object* v_k_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Options_get_x3f(v_00_u03b1_175_, v_inst_176_, v_o_177_, v_k_178_);
lean_dec(v_k_178_);
lean_dec_ref(v_o_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg(lean_object* v_inst_180_, lean_object* v_o_181_, lean_object* v_k_182_, lean_object* v_defVal_183_){
_start:
{
lean_object* v_map_184_; lean_object* v_ofDataValue_x3f_185_; lean_object* v___x_186_; 
v_map_184_ = lean_ctor_get(v_o_181_, 0);
v_ofDataValue_x3f_185_ = lean_ctor_get(v_inst_180_, 1);
lean_inc_ref(v_ofDataValue_x3f_185_);
lean_dec_ref(v_inst_180_);
v___x_186_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_184_, v_k_182_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_185_);
lean_inc(v_defVal_183_);
return v_defVal_183_;
}
else
{
lean_object* v_val_187_; lean_object* v___x_188_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v___x_186_);
v___x_188_ = lean_apply_1(v_ofDataValue_x3f_185_, v_val_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_inc(v_defVal_183_);
return v_defVal_183_;
}
else
{
lean_object* v_val_189_; 
v_val_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_val_189_);
lean_dec_ref(v___x_188_);
return v_val_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg___boxed(lean_object* v_inst_190_, lean_object* v_o_191_, lean_object* v_k_192_, lean_object* v_defVal_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Options_get___redArg(v_inst_190_, v_o_191_, v_k_192_, v_defVal_193_);
lean_dec(v_defVal_193_);
lean_dec(v_k_192_);
lean_dec_ref(v_o_191_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_o_197_, lean_object* v_k_198_, lean_object* v_defVal_199_){
_start:
{
lean_object* v_map_200_; lean_object* v_ofDataValue_x3f_201_; lean_object* v___x_202_; 
v_map_200_ = lean_ctor_get(v_o_197_, 0);
v_ofDataValue_x3f_201_ = lean_ctor_get(v_inst_196_, 1);
lean_inc_ref(v_ofDataValue_x3f_201_);
lean_dec_ref(v_inst_196_);
v___x_202_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_200_, v_k_198_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_201_);
lean_inc(v_defVal_199_);
return v_defVal_199_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_204_; 
v_val_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_val_203_);
lean_dec_ref(v___x_202_);
v___x_204_ = lean_apply_1(v_ofDataValue_x3f_201_, v_val_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_inc(v_defVal_199_);
return v_defVal_199_;
}
else
{
lean_object* v_val_205_; 
v_val_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v___x_204_);
return v_val_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___boxed(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_o_208_, lean_object* v_k_209_, lean_object* v_defVal_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Options_get(v_00_u03b1_206_, v_inst_207_, v_o_208_, v_k_209_, v_defVal_210_);
lean_dec(v_defVal_210_);
lean_dec(v_k_209_);
lean_dec_ref(v_o_208_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getBool(lean_object* v_o_212_, lean_object* v_k_213_, uint8_t v_defVal_214_){
_start:
{
lean_object* v_map_215_; lean_object* v___x_216_; 
v_map_215_ = lean_ctor_get(v_o_212_, 0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_215_, v_k_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
return v_defVal_214_;
}
else
{
lean_object* v_val_217_; 
v_val_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_217_);
lean_dec_ref(v___x_216_);
if (lean_obj_tag(v_val_217_) == 1)
{
uint8_t v_v_218_; 
v_v_218_ = lean_ctor_get_uint8(v_val_217_, 0);
lean_dec_ref(v_val_217_);
return v_v_218_;
}
else
{
lean_dec(v_val_217_);
return v_defVal_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getBool___boxed(lean_object* v_o_219_, lean_object* v_k_220_, lean_object* v_defVal_221_){
_start:
{
uint8_t v_defVal_boxed_222_; uint8_t v_res_223_; lean_object* v_r_224_; 
v_defVal_boxed_222_ = lean_unbox(v_defVal_221_);
v_res_223_ = l_Lean_Options_getBool(v_o_219_, v_k_220_, v_defVal_boxed_222_);
lean_dec(v_k_220_);
lean_dec_ref(v_o_219_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_contains(lean_object* v_o_225_, lean_object* v_k_226_){
_start:
{
lean_object* v_map_227_; uint8_t v___x_228_; 
v_map_227_ = lean_ctor_get(v_o_225_, 0);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_226_, v_map_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object* v_o_229_, lean_object* v_k_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Options_contains(v_o_229_, v_k_230_);
lean_dec(v_k_230_);
lean_dec_ref(v_o_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object* v_o_236_, lean_object* v_k_237_, lean_object* v_v_238_){
_start:
{
lean_object* v_map_239_; uint8_t v_hasTrace_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_253_; 
v_map_239_ = lean_ctor_get(v_o_236_, 0);
v_hasTrace_240_ = lean_ctor_get_uint8(v_o_236_, sizeof(void*)*1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_o_236_);
if (v_isSharedCheck_253_ == 0)
{
v___x_242_ = v_o_236_;
v_isShared_243_ = v_isSharedCheck_253_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_map_239_);
lean_dec(v_o_236_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_253_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; 
lean_inc(v_k_237_);
v___x_244_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_237_, v_v_238_, v_map_239_);
if (v_hasTrace_240_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_248_; 
v___x_245_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_246_ = l_Lean_Name_isPrefixOf(v___x_245_, v_k_237_);
lean_dec(v_k_237_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_244_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_ctor_set_uint8(v___x_248_, sizeof(void*)*1, v___x_246_);
return v___x_248_;
}
}
else
{
lean_object* v___x_251_; 
lean_dec(v_k_237_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_244_);
v___x_251_ = v___x_242_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_244_);
lean_ctor_set_uint8(v_reuseFailAlloc_252_, sizeof(void*)*1, v_hasTrace_240_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object* v_inst_254_, lean_object* v_o_255_, lean_object* v_k_256_, lean_object* v_v_257_){
_start:
{
lean_object* v_toDataValue_258_; lean_object* v_map_259_; uint8_t v_hasTrace_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_274_; 
v_toDataValue_258_ = lean_ctor_get(v_inst_254_, 0);
lean_inc_ref(v_toDataValue_258_);
lean_dec_ref(v_inst_254_);
v_map_259_ = lean_ctor_get(v_o_255_, 0);
v_hasTrace_260_ = lean_ctor_get_uint8(v_o_255_, sizeof(void*)*1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_o_255_);
if (v_isSharedCheck_274_ == 0)
{
v___x_262_ = v_o_255_;
v_isShared_263_ = v_isSharedCheck_274_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_map_259_);
lean_dec(v_o_255_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_274_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_apply_1(v_toDataValue_258_, v_v_257_);
lean_inc(v_k_256_);
v___x_265_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_256_, v___x_264_, v_map_259_);
if (v_hasTrace_260_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_269_; 
v___x_266_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_267_ = l_Lean_Name_isPrefixOf(v___x_266_, v_k_256_);
lean_dec(v_k_256_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_265_);
v___x_269_ = v___x_262_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_265_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*1, v___x_267_);
return v___x_269_;
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v_k_256_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_265_);
v___x_272_ = v___x_262_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*1, v_hasTrace_260_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_o_277_, lean_object* v_k_278_, lean_object* v_v_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Options_set___redArg(v_inst_276_, v_o_277_, v_k_278_, v_v_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool(lean_object* v_o_281_, lean_object* v_k_282_, uint8_t v_v_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = l_Lean_KVMap_instValueBool;
v___x_285_ = lean_box(v_v_283_);
v___x_286_ = l_Lean_Options_set___redArg(v___x_284_, v_o_281_, v_k_282_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object* v_o_287_, lean_object* v_k_288_, lean_object* v_v_289_){
_start:
{
uint8_t v_v_boxed_290_; lean_object* v_res_291_; 
v_v_boxed_290_ = lean_unbox(v_v_289_);
v_res_291_ = l_Lean_Options_setBool(v_o_287_, v_k_288_, v_v_boxed_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object* v_init_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v_k_294_; lean_object* v_l_295_; lean_object* v_r_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_k_294_ = lean_ctor_get(v_x_293_, 1);
v_l_295_ = lean_ctor_get(v_x_293_, 3);
v_r_296_ = lean_ctor_get(v_x_293_, 4);
v___x_297_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_292_, v_r_296_);
lean_inc(v_k_294_);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_k_294_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v_init_292_ = v___x_298_;
v_x_293_ = v_l_295_;
goto _start;
}
else
{
return v_init_292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object* v_init_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_300_, v_x_301_);
lean_dec(v_x_301_);
return v_res_302_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Options_erase_spec__2(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = 0;
return v___x_304_;
}
else
{
lean_object* v_head_305_; lean_object* v_tail_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_head_305_ = lean_ctor_get(v_x_303_, 0);
v_tail_306_ = lean_ctor_get(v_x_303_, 1);
v___x_307_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_308_ = l_Lean_Name_isPrefixOf(v___x_307_, v_head_305_);
if (v___x_308_ == 0)
{
v_x_303_ = v_tail_306_;
goto _start;
}
else
{
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Options_erase_spec__2___boxed(lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_List_any___at___00Lean_Options_erase_spec__2(v_x_310_);
lean_dec(v_x_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object* v_k_313_, lean_object* v_t_314_){
_start:
{
if (lean_obj_tag(v_t_314_) == 0)
{
lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v_l_317_; lean_object* v_r_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_972_; 
v_k_315_ = lean_ctor_get(v_t_314_, 1);
v_v_316_ = lean_ctor_get(v_t_314_, 2);
v_l_317_ = lean_ctor_get(v_t_314_, 3);
v_r_318_ = lean_ctor_get(v_t_314_, 4);
v_isSharedCheck_972_ = !lean_is_exclusive(v_t_314_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_t_314_, 0);
lean_dec(v_unused_973_);
v___x_320_ = v_t_314_;
v_isShared_321_ = v_isSharedCheck_972_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_r_318_);
lean_inc(v_l_317_);
lean_inc(v_v_316_);
lean_inc(v_k_315_);
lean_dec(v_t_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_972_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint8_t v___x_322_; 
v___x_322_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_313_, v_k_315_);
switch(v___x_322_)
{
case 0:
{
lean_object* v_impl_323_; lean_object* v___x_324_; 
v_impl_323_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_313_, v_l_317_);
v___x_324_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_323_) == 0)
{
if (lean_obj_tag(v_r_318_) == 0)
{
lean_object* v_size_325_; lean_object* v_size_326_; lean_object* v_k_327_; lean_object* v_v_328_; lean_object* v_l_329_; lean_object* v_r_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_size_325_ = lean_ctor_get(v_impl_323_, 0);
lean_inc(v_size_325_);
v_size_326_ = lean_ctor_get(v_r_318_, 0);
v_k_327_ = lean_ctor_get(v_r_318_, 1);
v_v_328_ = lean_ctor_get(v_r_318_, 2);
v_l_329_ = lean_ctor_get(v_r_318_, 3);
lean_inc(v_l_329_);
v_r_330_ = lean_ctor_get(v_r_318_, 4);
v___x_331_ = lean_unsigned_to_nat(3u);
v___x_332_ = lean_nat_mul(v___x_331_, v_size_325_);
v___x_333_ = lean_nat_dec_lt(v___x_332_, v_size_326_);
lean_dec(v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
lean_dec(v_l_329_);
v___x_334_ = lean_nat_add(v___x_324_, v_size_325_);
lean_dec(v_size_325_);
v___x_335_ = lean_nat_add(v___x_334_, v_size_326_);
lean_dec(v___x_334_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 3, v_impl_323_);
lean_ctor_set(v___x_320_, 0, v___x_335_);
v___x_337_ = v___x_320_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_impl_323_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_r_318_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_402_; 
lean_inc(v_r_330_);
lean_inc(v_v_328_);
lean_inc(v_k_327_);
lean_inc(v_size_326_);
v_isSharedCheck_402_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_403_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_r_318_, 2);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_r_318_, 1);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_407_);
v___x_340_ = v_r_318_;
v_isShared_341_ = v_isSharedCheck_402_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_r_318_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_402_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_size_342_; lean_object* v_k_343_; lean_object* v_v_344_; lean_object* v_l_345_; lean_object* v_r_346_; lean_object* v_size_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_size_342_ = lean_ctor_get(v_l_329_, 0);
v_k_343_ = lean_ctor_get(v_l_329_, 1);
v_v_344_ = lean_ctor_get(v_l_329_, 2);
v_l_345_ = lean_ctor_get(v_l_329_, 3);
v_r_346_ = lean_ctor_get(v_l_329_, 4);
v_size_347_ = lean_ctor_get(v_r_330_, 0);
v___x_348_ = lean_unsigned_to_nat(2u);
v___x_349_ = lean_nat_mul(v___x_348_, v_size_347_);
v___x_350_ = lean_nat_dec_lt(v_size_342_, v___x_349_);
lean_dec(v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_378_; 
lean_inc(v_r_346_);
lean_inc(v_l_345_);
lean_inc(v_v_344_);
lean_inc(v_k_343_);
v_isSharedCheck_378_ = !lean_is_exclusive(v_l_329_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_379_ = lean_ctor_get(v_l_329_, 4);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_l_329_, 3);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_l_329_, 2);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_l_329_, 1);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_l_329_, 0);
lean_dec(v_unused_383_);
v___x_352_ = v_l_329_;
v_isShared_353_ = v_isSharedCheck_378_;
goto v_resetjp_351_;
}
else
{
lean_dec(v_l_329_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_378_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_368_; 
v___x_354_ = lean_nat_add(v___x_324_, v_size_325_);
lean_dec(v_size_325_);
v___x_355_ = lean_nat_add(v___x_354_, v_size_326_);
lean_dec(v_size_326_);
if (lean_obj_tag(v_l_345_) == 0)
{
lean_object* v_size_376_; 
v_size_376_ = lean_ctor_get(v_l_345_, 0);
lean_inc(v_size_376_);
v___y_368_ = v_size_376_;
goto v___jp_367_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v___y_368_ = v___x_377_;
goto v___jp_367_;
}
v___jp_356_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_nat_add(v___y_357_, v___y_359_);
lean_dec(v___y_359_);
lean_dec(v___y_357_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 4, v_r_330_);
lean_ctor_set(v___x_352_, 3, v_r_346_);
lean_ctor_set(v___x_352_, 2, v_v_328_);
lean_ctor_set(v___x_352_, 1, v_k_327_);
lean_ctor_set(v___x_352_, 0, v___x_360_);
v___x_362_ = v___x_352_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_k_327_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_v_328_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_r_346_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v_r_330_);
v___x_362_ = v_reuseFailAlloc_366_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 4, v___x_362_);
lean_ctor_set(v___x_340_, 3, v___y_358_);
lean_ctor_set(v___x_340_, 2, v_v_344_);
lean_ctor_set(v___x_340_, 1, v_k_343_);
lean_ctor_set(v___x_340_, 0, v___x_355_);
v___x_364_ = v___x_340_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_343_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_344_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v___y_358_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
v___jp_367_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_nat_add(v___x_354_, v___y_368_);
lean_dec(v___y_368_);
lean_dec(v___x_354_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_l_345_);
lean_ctor_set(v___x_320_, 3, v_impl_323_);
lean_ctor_set(v___x_320_, 0, v___x_369_);
v___x_371_ = v___x_320_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_impl_323_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_l_345_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_nat_add(v___x_324_, v_size_347_);
if (lean_obj_tag(v_r_346_) == 0)
{
lean_object* v_size_373_; 
v_size_373_ = lean_ctor_get(v_r_346_, 0);
lean_inc(v_size_373_);
v___y_357_ = v___x_372_;
v___y_358_ = v___x_371_;
v___y_359_ = v_size_373_;
goto v___jp_356_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___y_357_ = v___x_372_;
v___y_358_ = v___x_371_;
v___y_359_ = v___x_374_;
goto v___jp_356_;
}
}
}
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_del_object(v___x_320_);
v___x_384_ = lean_nat_add(v___x_324_, v_size_325_);
lean_dec(v_size_325_);
v___x_385_ = lean_nat_add(v___x_384_, v_size_326_);
lean_dec(v_size_326_);
v___x_386_ = lean_nat_add(v___x_384_, v_size_342_);
lean_dec(v___x_384_);
lean_inc_ref(v_impl_323_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 4, v_l_329_);
lean_ctor_set(v___x_340_, 3, v_impl_323_);
lean_ctor_set(v___x_340_, 2, v_v_316_);
lean_ctor_set(v___x_340_, 1, v_k_315_);
lean_ctor_set(v___x_340_, 0, v___x_386_);
v___x_388_ = v___x_340_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_impl_323_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v_l_329_);
v___x_388_ = v_reuseFailAlloc_401_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v_isSharedCheck_395_ = !lean_is_exclusive(v_impl_323_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_396_ = lean_ctor_get(v_impl_323_, 4);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_impl_323_, 3);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_impl_323_, 2);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_impl_323_, 1);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_impl_323_, 0);
lean_dec(v_unused_400_);
v___x_390_ = v_impl_323_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_impl_323_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 4, v_r_330_);
lean_ctor_set(v___x_390_, 3, v___x_388_);
lean_ctor_set(v___x_390_, 2, v_v_328_);
lean_ctor_set(v___x_390_, 1, v_k_327_);
lean_ctor_set(v___x_390_, 0, v___x_385_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_k_327_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_v_328_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_r_330_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v_size_408_ = lean_ctor_get(v_impl_323_, 0);
lean_inc(v_size_408_);
v___x_409_ = lean_nat_add(v___x_324_, v_size_408_);
lean_dec(v_size_408_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 3, v_impl_323_);
lean_ctor_set(v___x_320_, 0, v___x_409_);
v___x_411_ = v___x_320_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_impl_323_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_r_318_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
if (lean_obj_tag(v_r_318_) == 0)
{
lean_object* v_l_413_; 
v_l_413_ = lean_ctor_get(v_r_318_, 3);
lean_inc(v_l_413_);
if (lean_obj_tag(v_l_413_) == 0)
{
lean_object* v_r_414_; 
v_r_414_ = lean_ctor_get(v_r_318_, 4);
lean_inc(v_r_414_);
if (lean_obj_tag(v_r_414_) == 0)
{
lean_object* v_size_415_; lean_object* v_k_416_; lean_object* v_v_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_430_; 
v_size_415_ = lean_ctor_get(v_r_318_, 0);
v_k_416_ = lean_ctor_get(v_r_318_, 1);
v_v_417_ = lean_ctor_get(v_r_318_, 2);
v_isSharedCheck_430_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; lean_object* v_unused_432_; 
v_unused_431_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_432_);
v___x_419_ = v_r_318_;
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_v_417_);
lean_inc(v_k_416_);
lean_inc(v_size_415_);
lean_dec(v_r_318_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_size_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v_size_421_ = lean_ctor_get(v_l_413_, 0);
v___x_422_ = lean_nat_add(v___x_324_, v_size_415_);
lean_dec(v_size_415_);
v___x_423_ = lean_nat_add(v___x_324_, v_size_421_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 4, v_l_413_);
lean_ctor_set(v___x_419_, 3, v_impl_323_);
lean_ctor_set(v___x_419_, 2, v_v_316_);
lean_ctor_set(v___x_419_, 1, v_k_315_);
lean_ctor_set(v___x_419_, 0, v___x_423_);
v___x_425_ = v___x_419_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_impl_323_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_l_413_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_r_414_);
lean_ctor_set(v___x_320_, 3, v___x_425_);
lean_ctor_set(v___x_320_, 2, v_v_417_);
lean_ctor_set(v___x_320_, 1, v_k_416_);
lean_ctor_set(v___x_320_, 0, v___x_422_);
v___x_427_ = v___x_320_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_416_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_r_414_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_k_433_; lean_object* v_v_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_457_; 
v_k_433_ = lean_ctor_get(v_r_318_, 1);
v_v_434_ = lean_ctor_get(v_r_318_, 2);
v_isSharedCheck_457_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_458_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_460_);
v___x_436_ = v_r_318_;
v_isShared_437_ = v_isSharedCheck_457_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_v_434_);
lean_inc(v_k_433_);
lean_dec(v_r_318_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_457_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_k_438_; lean_object* v_v_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_453_; 
v_k_438_ = lean_ctor_get(v_l_413_, 1);
v_v_439_ = lean_ctor_get(v_l_413_, 2);
v_isSharedCheck_453_ = !lean_is_exclusive(v_l_413_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; 
v_unused_454_ = lean_ctor_get(v_l_413_, 4);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_l_413_, 3);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_l_413_, 0);
lean_dec(v_unused_456_);
v___x_441_ = v_l_413_;
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_v_439_);
lean_inc(v_k_438_);
lean_dec(v_l_413_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(3u);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 4, v_r_414_);
lean_ctor_set(v___x_441_, 3, v_r_414_);
lean_ctor_set(v___x_441_, 2, v_v_316_);
lean_ctor_set(v___x_441_, 1, v_k_315_);
lean_ctor_set(v___x_441_, 0, v___x_324_);
v___x_445_ = v___x_441_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_r_414_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_r_414_);
v___x_445_ = v_reuseFailAlloc_452_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_447_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 3, v_r_414_);
lean_ctor_set(v___x_436_, 0, v___x_324_);
v___x_447_ = v___x_436_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_k_433_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_v_434_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_r_414_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_r_414_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_447_);
lean_ctor_set(v___x_320_, 3, v___x_445_);
lean_ctor_set(v___x_320_, 2, v_v_439_);
lean_ctor_set(v___x_320_, 1, v_k_438_);
lean_ctor_set(v___x_320_, 0, v___x_443_);
v___x_449_ = v___x_320_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_461_; 
v_r_461_ = lean_ctor_get(v_r_318_, 4);
lean_inc(v_r_461_);
if (lean_obj_tag(v_r_461_) == 0)
{
lean_object* v_k_462_; lean_object* v_v_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_474_; 
v_k_462_ = lean_ctor_get(v_r_318_, 1);
v_v_463_ = lean_ctor_get(v_r_318_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; 
v_unused_475_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_477_);
v___x_465_ = v_r_318_;
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_v_463_);
lean_inc(v_k_462_);
lean_dec(v_r_318_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_474_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_unsigned_to_nat(3u);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 4, v_l_413_);
lean_ctor_set(v___x_465_, 2, v_v_316_);
lean_ctor_set(v___x_465_, 1, v_k_315_);
lean_ctor_set(v___x_465_, 0, v___x_324_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_l_413_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_l_413_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_r_461_);
lean_ctor_set(v___x_320_, 3, v___x_469_);
lean_ctor_set(v___x_320_, 2, v_v_463_);
lean_ctor_set(v___x_320_, 1, v_k_462_);
lean_ctor_set(v___x_320_, 0, v___x_467_);
v___x_471_ = v___x_320_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_k_462_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_v_463_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v_r_461_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_object* v_size_478_; lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_491_; 
v_size_478_ = lean_ctor_get(v_r_318_, 0);
v_k_479_ = lean_ctor_get(v_r_318_, 1);
v_v_480_ = lean_ctor_get(v_r_318_, 2);
v_isSharedCheck_491_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_493_);
v___x_482_ = v_r_318_;
v_isShared_483_ = v_isSharedCheck_491_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_v_480_);
lean_inc(v_k_479_);
lean_inc(v_size_478_);
lean_dec(v_r_318_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_491_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 3, v_r_461_);
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_size_478_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_k_479_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_v_480_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_r_461_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v_r_461_);
v___x_485_ = v_reuseFailAlloc_490_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_unsigned_to_nat(2u);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_485_);
lean_ctor_set(v___x_320_, 3, v_r_461_);
lean_ctor_set(v___x_320_, 0, v___x_486_);
v___x_488_ = v___x_320_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_r_461_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v___x_485_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
else
{
lean_object* v___x_495_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 3, v_r_318_);
lean_ctor_set(v___x_320_, 0, v___x_324_);
v___x_495_ = v___x_320_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_r_318_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_r_318_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
case 1:
{
lean_del_object(v___x_320_);
lean_dec(v_v_316_);
lean_dec(v_k_315_);
if (lean_obj_tag(v_l_317_) == 0)
{
if (lean_obj_tag(v_r_318_) == 0)
{
lean_object* v_size_497_; lean_object* v_k_498_; lean_object* v_v_499_; lean_object* v_l_500_; lean_object* v_r_501_; lean_object* v_size_502_; lean_object* v_k_503_; lean_object* v_v_504_; lean_object* v_l_505_; lean_object* v_r_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_size_497_ = lean_ctor_get(v_l_317_, 0);
v_k_498_ = lean_ctor_get(v_l_317_, 1);
v_v_499_ = lean_ctor_get(v_l_317_, 2);
v_l_500_ = lean_ctor_get(v_l_317_, 3);
v_r_501_ = lean_ctor_get(v_l_317_, 4);
lean_inc(v_r_501_);
v_size_502_ = lean_ctor_get(v_r_318_, 0);
v_k_503_ = lean_ctor_get(v_r_318_, 1);
v_v_504_ = lean_ctor_get(v_r_318_, 2);
v_l_505_ = lean_ctor_get(v_r_318_, 3);
lean_inc(v_l_505_);
v_r_506_ = lean_ctor_get(v_r_318_, 4);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_dec_lt(v_size_497_, v_size_502_);
if (v___x_508_ == 0)
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_644_; 
lean_inc(v_l_500_);
lean_inc(v_v_499_);
lean_inc(v_k_498_);
v_isSharedCheck_644_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; 
v_unused_645_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_l_317_, 2);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v_l_317_, 1);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_649_);
v___x_510_ = v_l_317_;
v_isShared_511_ = v_isSharedCheck_644_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_l_317_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_644_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v_tree_513_; 
v___x_512_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_498_, v_v_499_, v_l_500_, v_r_501_);
v_tree_513_ = lean_ctor_get(v___x_512_, 2);
lean_inc(v_tree_513_);
if (lean_obj_tag(v_tree_513_) == 0)
{
lean_object* v_k_514_; lean_object* v_v_515_; lean_object* v_size_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_k_514_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_k_514_);
v_v_515_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_v_515_);
lean_dec_ref(v___x_512_);
v_size_516_ = lean_ctor_get(v_tree_513_, 0);
v___x_517_ = lean_unsigned_to_nat(3u);
v___x_518_ = lean_nat_mul(v___x_517_, v_size_516_);
v___x_519_ = lean_nat_dec_lt(v___x_518_, v_size_502_);
lean_dec(v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec(v_l_505_);
v___x_520_ = lean_nat_add(v___x_507_, v_size_516_);
v___x_521_ = lean_nat_add(v___x_520_, v_size_502_);
lean_dec(v___x_520_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_r_318_);
lean_ctor_set(v___x_510_, 3, v_tree_513_);
lean_ctor_set(v___x_510_, 2, v_v_515_);
lean_ctor_set(v___x_510_, 1, v_k_514_);
lean_ctor_set(v___x_510_, 0, v___x_521_);
v___x_523_ = v___x_510_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_tree_513_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_r_318_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_579_; 
lean_inc(v_r_506_);
lean_inc(v_v_504_);
lean_inc(v_k_503_);
lean_inc(v_size_502_);
v_isSharedCheck_579_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; 
v_unused_580_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_r_318_, 2);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_r_318_, 1);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_584_);
v___x_526_ = v_r_318_;
v_isShared_527_ = v_isSharedCheck_579_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_r_318_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_579_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_size_528_; lean_object* v_k_529_; lean_object* v_v_530_; lean_object* v_l_531_; lean_object* v_r_532_; lean_object* v_size_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_size_528_ = lean_ctor_get(v_l_505_, 0);
v_k_529_ = lean_ctor_get(v_l_505_, 1);
v_v_530_ = lean_ctor_get(v_l_505_, 2);
v_l_531_ = lean_ctor_get(v_l_505_, 3);
v_r_532_ = lean_ctor_get(v_l_505_, 4);
v_size_533_ = lean_ctor_get(v_r_506_, 0);
v___x_534_ = lean_unsigned_to_nat(2u);
v___x_535_ = lean_nat_mul(v___x_534_, v_size_533_);
v___x_536_ = lean_nat_dec_lt(v_size_528_, v___x_535_);
lean_dec(v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_564_; 
lean_inc(v_r_532_);
lean_inc(v_l_531_);
lean_inc(v_v_530_);
lean_inc(v_k_529_);
v_isSharedCheck_564_ = !lean_is_exclusive(v_l_505_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_565_ = lean_ctor_get(v_l_505_, 4);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_505_, 3);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_505_, 2);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_l_505_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_l_505_, 0);
lean_dec(v_unused_569_);
v___x_538_ = v_l_505_;
v_isShared_539_ = v_isSharedCheck_564_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_l_505_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_564_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_554_; 
v___x_540_ = lean_nat_add(v___x_507_, v_size_516_);
v___x_541_ = lean_nat_add(v___x_540_, v_size_502_);
lean_dec(v_size_502_);
if (lean_obj_tag(v_l_531_) == 0)
{
lean_object* v_size_562_; 
v_size_562_ = lean_ctor_get(v_l_531_, 0);
lean_inc(v_size_562_);
v___y_554_ = v_size_562_;
goto v___jp_553_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___y_554_ = v___x_563_;
goto v___jp_553_;
}
v___jp_542_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = lean_nat_add(v___y_543_, v___y_545_);
lean_dec(v___y_545_);
lean_dec(v___y_543_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_r_506_);
lean_ctor_set(v___x_538_, 3, v_r_532_);
lean_ctor_set(v___x_538_, 2, v_v_504_);
lean_ctor_set(v___x_538_, 1, v_k_503_);
lean_ctor_set(v___x_538_, 0, v___x_546_);
v___x_548_ = v___x_538_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_r_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_r_506_);
v___x_548_ = v_reuseFailAlloc_552_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v___x_548_);
lean_ctor_set(v___x_526_, 3, v___y_544_);
lean_ctor_set(v___x_526_, 2, v_v_530_);
lean_ctor_set(v___x_526_, 1, v_k_529_);
lean_ctor_set(v___x_526_, 0, v___x_541_);
v___x_550_ = v___x_526_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_k_529_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_v_530_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v___y_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_nat_add(v___x_540_, v___y_554_);
lean_dec(v___y_554_);
lean_dec(v___x_540_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_l_531_);
lean_ctor_set(v___x_510_, 3, v_tree_513_);
lean_ctor_set(v___x_510_, 2, v_v_515_);
lean_ctor_set(v___x_510_, 1, v_k_514_);
lean_ctor_set(v___x_510_, 0, v___x_555_);
v___x_557_ = v___x_510_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_tree_513_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_l_531_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = lean_nat_add(v___x_507_, v_size_533_);
if (lean_obj_tag(v_r_532_) == 0)
{
lean_object* v_size_559_; 
v_size_559_ = lean_ctor_get(v_r_532_, 0);
lean_inc(v_size_559_);
v___y_543_ = v___x_558_;
v___y_544_ = v___x_557_;
v___y_545_ = v_size_559_;
goto v___jp_542_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___y_543_ = v___x_558_;
v___y_544_ = v___x_557_;
v___y_545_ = v___x_560_;
goto v___jp_542_;
}
}
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_570_ = lean_nat_add(v___x_507_, v_size_516_);
v___x_571_ = lean_nat_add(v___x_570_, v_size_502_);
lean_dec(v_size_502_);
v___x_572_ = lean_nat_add(v___x_570_, v_size_528_);
lean_dec(v___x_570_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 4, v_l_505_);
lean_ctor_set(v___x_526_, 3, v_tree_513_);
lean_ctor_set(v___x_526_, 2, v_v_515_);
lean_ctor_set(v___x_526_, 1, v_k_514_);
lean_ctor_set(v___x_526_, 0, v___x_572_);
v___x_574_ = v___x_526_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_tree_513_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_l_505_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_r_506_);
lean_ctor_set(v___x_510_, 3, v___x_574_);
lean_ctor_set(v___x_510_, 2, v_v_504_);
lean_ctor_set(v___x_510_, 1, v_k_503_);
lean_ctor_set(v___x_510_, 0, v___x_571_);
v___x_576_ = v___x_510_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_r_506_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
else
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_638_; 
lean_inc(v_r_506_);
lean_inc(v_v_504_);
lean_inc(v_k_503_);
lean_inc(v_size_502_);
v_isSharedCheck_638_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_639_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_318_, 2);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_r_318_, 1);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_643_);
v___x_586_ = v_r_318_;
v_isShared_587_ = v_isSharedCheck_638_;
goto v_resetjp_585_;
}
else
{
lean_dec(v_r_318_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_638_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
if (lean_obj_tag(v_l_505_) == 0)
{
if (lean_obj_tag(v_r_506_) == 0)
{
lean_object* v_k_588_; lean_object* v_v_589_; lean_object* v_size_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_k_588_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_k_588_);
v_v_589_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_v_589_);
lean_dec_ref(v___x_512_);
v_size_590_ = lean_ctor_get(v_l_505_, 0);
v___x_591_ = lean_nat_add(v___x_507_, v_size_502_);
lean_dec(v_size_502_);
v___x_592_ = lean_nat_add(v___x_507_, v_size_590_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 4, v_l_505_);
lean_ctor_set(v___x_586_, 3, v_tree_513_);
lean_ctor_set(v___x_586_, 2, v_v_589_);
lean_ctor_set(v___x_586_, 1, v_k_588_);
lean_ctor_set(v___x_586_, 0, v___x_592_);
v___x_594_ = v___x_586_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_tree_513_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_l_505_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_r_506_);
lean_ctor_set(v___x_510_, 3, v___x_594_);
lean_ctor_set(v___x_510_, 2, v_v_504_);
lean_ctor_set(v___x_510_, 1, v_k_503_);
lean_ctor_set(v___x_510_, 0, v___x_591_);
v___x_596_ = v___x_510_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_r_506_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_size_502_);
v_k_599_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_k_599_);
v_v_600_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_v_600_);
lean_dec_ref(v___x_512_);
v_k_601_ = lean_ctor_get(v_l_505_, 1);
v_v_602_ = lean_ctor_get(v_l_505_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_l_505_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; 
v_unused_617_ = lean_ctor_get(v_l_505_, 4);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_l_505_, 3);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_l_505_, 0);
lean_dec(v_unused_619_);
v___x_604_ = v_l_505_;
v_isShared_605_ = v_isSharedCheck_616_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_v_602_);
lean_inc(v_k_601_);
lean_dec(v_l_505_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_616_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_unsigned_to_nat(3u);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 4, v_r_506_);
lean_ctor_set(v___x_604_, 3, v_r_506_);
lean_ctor_set(v___x_604_, 2, v_v_600_);
lean_ctor_set(v___x_604_, 1, v_k_599_);
lean_ctor_set(v___x_604_, 0, v___x_507_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_r_506_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_r_506_);
v___x_608_ = v_reuseFailAlloc_615_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 3, v_r_506_);
lean_ctor_set(v___x_586_, 0, v___x_507_);
v___x_610_ = v___x_586_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_r_506_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_r_506_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v___x_610_);
lean_ctor_set(v___x_510_, 3, v___x_608_);
lean_ctor_set(v___x_510_, 2, v_v_602_);
lean_ctor_set(v___x_510_, 1, v_k_601_);
lean_ctor_set(v___x_510_, 0, v___x_606_);
v___x_612_ = v___x_510_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_506_) == 0)
{
lean_object* v_k_620_; lean_object* v_v_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec(v_size_502_);
v_k_620_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_k_620_);
v_v_621_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_v_621_);
lean_dec_ref(v___x_512_);
v___x_622_ = lean_unsigned_to_nat(3u);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 4, v_l_505_);
lean_ctor_set(v___x_586_, 2, v_v_621_);
lean_ctor_set(v___x_586_, 1, v_k_620_);
lean_ctor_set(v___x_586_, 0, v___x_507_);
v___x_624_ = v___x_586_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_v_621_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v_l_505_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v_l_505_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_r_506_);
lean_ctor_set(v___x_510_, 3, v___x_624_);
lean_ctor_set(v___x_510_, 2, v_v_504_);
lean_ctor_set(v___x_510_, 1, v_k_503_);
lean_ctor_set(v___x_510_, 0, v___x_622_);
v___x_626_ = v___x_510_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_r_506_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_k_629_; lean_object* v_v_630_; lean_object* v___x_632_; 
v_k_629_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_k_629_);
v_v_630_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_v_630_);
lean_dec_ref(v___x_512_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 3, v_r_506_);
v___x_632_ = v___x_586_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_size_502_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_r_506_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_r_506_);
v___x_632_ = v_reuseFailAlloc_637_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_unsigned_to_nat(2u);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v___x_632_);
lean_ctor_set(v___x_510_, 3, v_r_506_);
lean_ctor_set(v___x_510_, 2, v_v_630_);
lean_ctor_set(v___x_510_, 1, v_k_629_);
lean_ctor_set(v___x_510_, 0, v___x_633_);
v___x_635_ = v___x_510_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_r_506_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v___x_632_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
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
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_802_; 
lean_inc(v_r_506_);
lean_inc(v_v_504_);
lean_inc(v_k_503_);
v_isSharedCheck_802_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; 
v_unused_803_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_r_318_, 2);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_r_318_, 1);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_807_);
v___x_651_ = v_r_318_;
v_isShared_652_ = v_isSharedCheck_802_;
goto v_resetjp_650_;
}
else
{
lean_dec(v_r_318_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_802_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v_tree_654_; 
v___x_653_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_503_, v_v_504_, v_l_505_, v_r_506_);
v_tree_654_ = lean_ctor_get(v___x_653_, 2);
lean_inc(v_tree_654_);
if (lean_obj_tag(v_tree_654_) == 0)
{
lean_object* v_k_655_; lean_object* v_v_656_; lean_object* v_size_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_k_655_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_k_655_);
v_v_656_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_v_656_);
lean_dec_ref(v___x_653_);
v_size_657_ = lean_ctor_get(v_tree_654_, 0);
v___x_658_ = lean_unsigned_to_nat(3u);
v___x_659_ = lean_nat_mul(v___x_658_, v_size_657_);
v___x_660_ = lean_nat_dec_lt(v___x_659_, v_size_497_);
lean_dec(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec(v_r_501_);
v___x_661_ = lean_nat_add(v___x_507_, v_size_497_);
v___x_662_ = lean_nat_add(v___x_661_, v_size_657_);
lean_dec(v___x_661_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_tree_654_);
lean_ctor_set(v___x_651_, 3, v_l_317_);
lean_ctor_set(v___x_651_, 2, v_v_656_);
lean_ctor_set(v___x_651_, 1, v_k_655_);
lean_ctor_set(v___x_651_, 0, v___x_662_);
v___x_664_ = v___x_651_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_k_655_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_v_656_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v_tree_654_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_731_; 
lean_inc(v_l_500_);
lean_inc(v_v_499_);
lean_inc(v_k_498_);
lean_inc(v_size_497_);
v_isSharedCheck_731_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_732_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_l_317_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_l_317_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_736_);
v___x_667_ = v_l_317_;
v_isShared_668_ = v_isSharedCheck_731_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_l_317_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_731_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_size_669_; lean_object* v_size_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v_l_673_; lean_object* v_r_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_size_669_ = lean_ctor_get(v_l_500_, 0);
v_size_670_ = lean_ctor_get(v_r_501_, 0);
v_k_671_ = lean_ctor_get(v_r_501_, 1);
v_v_672_ = lean_ctor_get(v_r_501_, 2);
v_l_673_ = lean_ctor_get(v_r_501_, 3);
v_r_674_ = lean_ctor_get(v_r_501_, 4);
v___x_675_ = lean_unsigned_to_nat(2u);
v___x_676_ = lean_nat_mul(v___x_675_, v_size_669_);
v___x_677_ = lean_nat_dec_lt(v_size_670_, v___x_676_);
lean_dec(v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_715_; 
lean_inc(v_r_674_);
lean_inc(v_l_673_);
lean_inc(v_v_672_);
lean_inc(v_k_671_);
lean_del_object(v___x_667_);
v_isSharedCheck_715_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; lean_object* v_unused_719_; lean_object* v_unused_720_; 
v_unused_716_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_r_501_, 2);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_r_501_, 1);
lean_dec(v_unused_719_);
v_unused_720_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_720_);
v___x_679_ = v_r_501_;
v_isShared_680_ = v_isSharedCheck_715_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_r_501_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_715_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___x_703_; lean_object* v___y_705_; 
v___x_681_ = lean_nat_add(v___x_507_, v_size_497_);
lean_dec(v_size_497_);
v___x_682_ = lean_nat_add(v___x_681_, v_size_657_);
lean_dec(v___x_681_);
v___x_703_ = lean_nat_add(v___x_507_, v_size_669_);
if (lean_obj_tag(v_l_673_) == 0)
{
lean_object* v_size_713_; 
v_size_713_ = lean_ctor_get(v_l_673_, 0);
lean_inc(v_size_713_);
v___y_705_ = v_size_713_;
goto v___jp_704_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_unsigned_to_nat(0u);
v___y_705_ = v___x_714_;
goto v___jp_704_;
}
v___jp_683_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_nat_add(v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec(v___y_685_);
lean_inc_ref(v_tree_654_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 4, v_tree_654_);
lean_ctor_set(v___x_679_, 3, v_r_674_);
lean_ctor_set(v___x_679_, 2, v_v_656_);
lean_ctor_set(v___x_679_, 1, v_k_655_);
lean_ctor_set(v___x_679_, 0, v___x_687_);
v___x_689_ = v___x_679_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_655_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_656_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_tree_654_);
v___x_689_ = v_reuseFailAlloc_702_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_isSharedCheck_696_ = !lean_is_exclusive(v_tree_654_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_697_ = lean_ctor_get(v_tree_654_, 4);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_tree_654_, 3);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_tree_654_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_tree_654_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_tree_654_, 0);
lean_dec(v_unused_701_);
v___x_691_ = v_tree_654_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_tree_654_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 4, v___x_689_);
lean_ctor_set(v___x_691_, 3, v___y_684_);
lean_ctor_set(v___x_691_, 2, v_v_672_);
lean_ctor_set(v___x_691_, 1, v_k_671_);
lean_ctor_set(v___x_691_, 0, v___x_682_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v___y_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_nat_add(v___x_703_, v___y_705_);
lean_dec(v___y_705_);
lean_dec(v___x_703_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_l_673_);
lean_ctor_set(v___x_651_, 3, v_l_500_);
lean_ctor_set(v___x_651_, 2, v_v_499_);
lean_ctor_set(v___x_651_, 1, v_k_498_);
lean_ctor_set(v___x_651_, 0, v___x_706_);
v___x_708_ = v___x_651_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_l_673_);
v___x_708_ = v_reuseFailAlloc_712_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; 
v___x_709_ = lean_nat_add(v___x_507_, v_size_657_);
if (lean_obj_tag(v_r_674_) == 0)
{
lean_object* v_size_710_; 
v_size_710_ = lean_ctor_get(v_r_674_, 0);
lean_inc(v_size_710_);
v___y_684_ = v___x_708_;
v___y_685_ = v___x_709_;
v___y_686_ = v_size_710_;
goto v___jp_683_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___y_684_ = v___x_708_;
v___y_685_ = v___x_709_;
v___y_686_ = v___x_711_;
goto v___jp_683_;
}
}
}
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_721_ = lean_nat_add(v___x_507_, v_size_497_);
lean_dec(v_size_497_);
v___x_722_ = lean_nat_add(v___x_721_, v_size_657_);
lean_dec(v___x_721_);
v___x_723_ = lean_nat_add(v___x_507_, v_size_657_);
v___x_724_ = lean_nat_add(v___x_723_, v_size_670_);
lean_dec(v___x_723_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_tree_654_);
lean_ctor_set(v___x_651_, 3, v_r_501_);
lean_ctor_set(v___x_651_, 2, v_v_656_);
lean_ctor_set(v___x_651_, 1, v_k_655_);
lean_ctor_set(v___x_651_, 0, v___x_724_);
v___x_726_ = v___x_651_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_655_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_656_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_r_501_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_tree_654_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 4, v___x_726_);
lean_ctor_set(v___x_667_, 0, v___x_722_);
v___x_728_ = v___x_667_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_500_) == 0)
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_760_; 
lean_inc_ref(v_l_500_);
lean_inc(v_v_499_);
lean_inc(v_k_498_);
lean_inc(v_size_497_);
v_isSharedCheck_760_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; 
v_unused_761_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_l_317_, 2);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_l_317_, 1);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_765_);
v___x_738_ = v_l_317_;
v_isShared_739_ = v_isSharedCheck_760_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_l_317_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_760_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
if (lean_obj_tag(v_r_501_) == 0)
{
lean_object* v_k_740_; lean_object* v_v_741_; lean_object* v_size_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v_k_740_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_k_740_);
v_v_741_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_v_741_);
lean_dec_ref(v___x_653_);
v_size_742_ = lean_ctor_get(v_r_501_, 0);
v___x_743_ = lean_nat_add(v___x_507_, v_size_497_);
lean_dec(v_size_497_);
v___x_744_ = lean_nat_add(v___x_507_, v_size_742_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_tree_654_);
lean_ctor_set(v___x_651_, 3, v_r_501_);
lean_ctor_set(v___x_651_, 2, v_v_741_);
lean_ctor_set(v___x_651_, 1, v_k_740_);
lean_ctor_set(v___x_651_, 0, v___x_744_);
v___x_746_ = v___x_651_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_k_740_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_v_741_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_r_501_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_tree_654_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_748_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_746_);
lean_ctor_set(v___x_738_, 0, v___x_743_);
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
else
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_size_497_);
v_k_751_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_k_751_);
v_v_752_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_v_752_);
lean_dec_ref(v___x_653_);
v___x_753_ = lean_unsigned_to_nat(3u);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_r_501_);
lean_ctor_set(v___x_651_, 3, v_r_501_);
lean_ctor_set(v___x_651_, 2, v_v_752_);
lean_ctor_set(v___x_651_, 1, v_k_751_);
lean_ctor_set(v___x_651_, 0, v___x_507_);
v___x_755_ = v___x_651_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_r_501_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_r_501_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_755_);
lean_ctor_set(v___x_738_, 0, v___x_753_);
v___x_757_ = v___x_738_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_501_) == 0)
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_790_; 
lean_inc(v_l_500_);
lean_inc(v_v_499_);
lean_inc(v_k_498_);
v_isSharedCheck_790_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; lean_object* v_unused_792_; lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_791_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_l_317_, 2);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_l_317_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_795_);
v___x_767_ = v_l_317_;
v_isShared_768_ = v_isSharedCheck_790_;
goto v_resetjp_766_;
}
else
{
lean_dec(v_l_317_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_790_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v_k_771_; lean_object* v_v_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_786_; 
v_k_769_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_k_769_);
v_v_770_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_v_770_);
lean_dec_ref(v___x_653_);
v_k_771_ = lean_ctor_get(v_r_501_, 1);
v_v_772_ = lean_ctor_get(v_r_501_, 2);
v_isSharedCheck_786_ = !lean_is_exclusive(v_r_501_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_787_ = lean_ctor_get(v_r_501_, 4);
lean_dec(v_unused_787_);
v_unused_788_ = lean_ctor_get(v_r_501_, 3);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_r_501_, 0);
lean_dec(v_unused_789_);
v___x_774_ = v_r_501_;
v_isShared_775_ = v_isSharedCheck_786_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_v_772_);
lean_inc(v_k_771_);
lean_dec(v_r_501_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_786_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(3u);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 4, v_l_500_);
lean_ctor_set(v___x_774_, 3, v_l_500_);
lean_ctor_set(v___x_774_, 2, v_v_499_);
lean_ctor_set(v___x_774_, 1, v_k_498_);
lean_ctor_set(v___x_774_, 0, v___x_507_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_k_498_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v_v_499_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v_l_500_);
v___x_778_ = v_reuseFailAlloc_785_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_l_500_);
lean_ctor_set(v___x_651_, 3, v_l_500_);
lean_ctor_set(v___x_651_, 2, v_v_770_);
lean_ctor_set(v___x_651_, 1, v_k_769_);
lean_ctor_set(v___x_651_, 0, v___x_507_);
v___x_780_ = v___x_651_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_l_500_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_l_500_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 4, v___x_780_);
lean_ctor_set(v___x_767_, 3, v___x_778_);
lean_ctor_set(v___x_767_, 2, v_v_772_);
lean_ctor_set(v___x_767_, 1, v_k_771_);
lean_ctor_set(v___x_767_, 0, v___x_776_);
v___x_782_ = v___x_767_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
}
else
{
lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v_k_796_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_k_796_);
v_v_797_ = lean_ctor_get(v___x_653_, 1);
lean_inc(v_v_797_);
lean_dec_ref(v___x_653_);
v___x_798_ = lean_unsigned_to_nat(2u);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v_r_501_);
lean_ctor_set(v___x_651_, 3, v_l_317_);
lean_ctor_set(v___x_651_, 2, v_v_797_);
lean_ctor_set(v___x_651_, 1, v_k_796_);
lean_ctor_set(v___x_651_, 0, v___x_798_);
v___x_800_ = v___x_651_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_r_501_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
}
else
{
return v_l_317_;
}
}
else
{
return v_r_318_;
}
}
default: 
{
lean_object* v_impl_808_; lean_object* v___x_809_; 
v_impl_808_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_313_, v_r_318_);
v___x_809_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_808_) == 0)
{
if (lean_obj_tag(v_l_317_) == 0)
{
lean_object* v_size_810_; lean_object* v_size_811_; lean_object* v_k_812_; lean_object* v_v_813_; lean_object* v_l_814_; lean_object* v_r_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_size_810_ = lean_ctor_get(v_impl_808_, 0);
lean_inc(v_size_810_);
v_size_811_ = lean_ctor_get(v_l_317_, 0);
v_k_812_ = lean_ctor_get(v_l_317_, 1);
v_v_813_ = lean_ctor_get(v_l_317_, 2);
v_l_814_ = lean_ctor_get(v_l_317_, 3);
v_r_815_ = lean_ctor_get(v_l_317_, 4);
lean_inc(v_r_815_);
v___x_816_ = lean_unsigned_to_nat(3u);
v___x_817_ = lean_nat_mul(v___x_816_, v_size_810_);
v___x_818_ = lean_nat_dec_lt(v___x_817_, v_size_811_);
lean_dec(v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_r_815_);
v___x_819_ = lean_nat_add(v___x_809_, v_size_811_);
v___x_820_ = lean_nat_add(v___x_819_, v_size_810_);
lean_dec(v_size_810_);
lean_dec(v___x_819_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_impl_808_);
lean_ctor_set(v___x_320_, 0, v___x_820_);
v___x_822_ = v___x_320_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_impl_808_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_889_; 
lean_inc(v_l_814_);
lean_inc(v_v_813_);
lean_inc(v_k_812_);
lean_inc(v_size_811_);
v_isSharedCheck_889_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_890_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_l_317_, 2);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_l_317_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_894_);
v___x_825_ = v_l_317_;
v_isShared_826_ = v_isSharedCheck_889_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_l_317_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_889_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_size_827_; lean_object* v_size_828_; lean_object* v_k_829_; lean_object* v_v_830_; lean_object* v_l_831_; lean_object* v_r_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_size_827_ = lean_ctor_get(v_l_814_, 0);
v_size_828_ = lean_ctor_get(v_r_815_, 0);
v_k_829_ = lean_ctor_get(v_r_815_, 1);
v_v_830_ = lean_ctor_get(v_r_815_, 2);
v_l_831_ = lean_ctor_get(v_r_815_, 3);
v_r_832_ = lean_ctor_get(v_r_815_, 4);
v___x_833_ = lean_unsigned_to_nat(2u);
v___x_834_ = lean_nat_mul(v___x_833_, v_size_827_);
v___x_835_ = lean_nat_dec_lt(v_size_828_, v___x_834_);
lean_dec(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_864_; 
lean_inc(v_r_832_);
lean_inc(v_l_831_);
lean_inc(v_v_830_);
lean_inc(v_k_829_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_r_815_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_865_ = lean_ctor_get(v_r_815_, 4);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_r_815_, 3);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_r_815_, 2);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_r_815_, 1);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_r_815_, 0);
lean_dec(v_unused_869_);
v___x_837_ = v_r_815_;
v_isShared_838_ = v_isSharedCheck_864_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_r_815_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_864_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___x_852_; lean_object* v___y_854_; 
v___x_839_ = lean_nat_add(v___x_809_, v_size_811_);
lean_dec(v_size_811_);
v___x_840_ = lean_nat_add(v___x_839_, v_size_810_);
lean_dec(v___x_839_);
v___x_852_ = lean_nat_add(v___x_809_, v_size_827_);
if (lean_obj_tag(v_l_831_) == 0)
{
lean_object* v_size_862_; 
v_size_862_ = lean_ctor_get(v_l_831_, 0);
lean_inc(v_size_862_);
v___y_854_ = v_size_862_;
goto v___jp_853_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___y_854_ = v___x_863_;
goto v___jp_853_;
}
v___jp_841_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_nat_add(v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 4, v_impl_808_);
lean_ctor_set(v___x_837_, 3, v_r_832_);
lean_ctor_set(v___x_837_, 2, v_v_316_);
lean_ctor_set(v___x_837_, 1, v_k_315_);
lean_ctor_set(v___x_837_, 0, v___x_845_);
v___x_847_ = v___x_837_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_r_832_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_impl_808_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 4, v___x_847_);
lean_ctor_set(v___x_825_, 3, v___y_842_);
lean_ctor_set(v___x_825_, 2, v_v_830_);
lean_ctor_set(v___x_825_, 1, v_k_829_);
lean_ctor_set(v___x_825_, 0, v___x_840_);
v___x_849_ = v___x_825_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_k_829_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_v_830_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v___y_842_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_nat_add(v___x_852_, v___y_854_);
lean_dec(v___y_854_);
lean_dec(v___x_852_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_l_831_);
lean_ctor_set(v___x_320_, 3, v_l_814_);
lean_ctor_set(v___x_320_, 2, v_v_813_);
lean_ctor_set(v___x_320_, 1, v_k_812_);
lean_ctor_set(v___x_320_, 0, v___x_855_);
v___x_857_ = v___x_320_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_l_814_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_l_831_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_nat_add(v___x_809_, v_size_810_);
lean_dec(v_size_810_);
if (lean_obj_tag(v_r_832_) == 0)
{
lean_object* v_size_859_; 
v_size_859_ = lean_ctor_get(v_r_832_, 0);
lean_inc(v_size_859_);
v___y_842_ = v___x_857_;
v___y_843_ = v___x_858_;
v___y_844_ = v_size_859_;
goto v___jp_841_;
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(0u);
v___y_842_ = v___x_857_;
v___y_843_ = v___x_858_;
v___y_844_ = v___x_860_;
goto v___jp_841_;
}
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_del_object(v___x_320_);
v___x_870_ = lean_nat_add(v___x_809_, v_size_811_);
lean_dec(v_size_811_);
v___x_871_ = lean_nat_add(v___x_870_, v_size_810_);
lean_dec(v___x_870_);
v___x_872_ = lean_nat_add(v___x_809_, v_size_810_);
lean_dec(v_size_810_);
v___x_873_ = lean_nat_add(v___x_872_, v_size_828_);
lean_dec(v___x_872_);
lean_inc_ref(v_impl_808_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 4, v_impl_808_);
lean_ctor_set(v___x_825_, 3, v_r_815_);
lean_ctor_set(v___x_825_, 2, v_v_316_);
lean_ctor_set(v___x_825_, 1, v_k_315_);
lean_ctor_set(v___x_825_, 0, v___x_873_);
v___x_875_ = v___x_825_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_r_815_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_impl_808_);
v___x_875_ = v_reuseFailAlloc_888_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_isSharedCheck_882_ = !lean_is_exclusive(v_impl_808_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_883_ = lean_ctor_get(v_impl_808_, 4);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_impl_808_, 3);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_impl_808_, 2);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_impl_808_, 1);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_impl_808_, 0);
lean_dec(v_unused_887_);
v___x_877_ = v_impl_808_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_dec(v_impl_808_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 4, v___x_875_);
lean_ctor_set(v___x_877_, 3, v_l_814_);
lean_ctor_set(v___x_877_, 2, v_v_813_);
lean_ctor_set(v___x_877_, 1, v_k_812_);
lean_ctor_set(v___x_877_, 0, v___x_871_);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_812_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_813_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_l_814_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v___x_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v_size_895_ = lean_ctor_get(v_impl_808_, 0);
lean_inc(v_size_895_);
v___x_896_ = lean_nat_add(v___x_809_, v_size_895_);
lean_dec(v_size_895_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_impl_808_);
lean_ctor_set(v___x_320_, 0, v___x_896_);
v___x_898_ = v___x_320_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_impl_808_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
else
{
if (lean_obj_tag(v_l_317_) == 0)
{
lean_object* v_l_900_; 
v_l_900_ = lean_ctor_get(v_l_317_, 3);
if (lean_obj_tag(v_l_900_) == 0)
{
lean_object* v_r_901_; 
lean_inc_ref(v_l_900_);
v_r_901_ = lean_ctor_get(v_l_317_, 4);
lean_inc(v_r_901_);
if (lean_obj_tag(v_r_901_) == 0)
{
lean_object* v_size_902_; lean_object* v_k_903_; lean_object* v_v_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_917_; 
v_size_902_ = lean_ctor_get(v_l_317_, 0);
v_k_903_ = lean_ctor_get(v_l_317_, 1);
v_v_904_ = lean_ctor_get(v_l_317_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; lean_object* v_unused_919_; 
v_unused_918_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_919_);
v___x_906_ = v_l_317_;
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_v_904_);
lean_inc(v_k_903_);
lean_inc(v_size_902_);
lean_dec(v_l_317_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_917_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_size_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v_size_908_ = lean_ctor_get(v_r_901_, 0);
v___x_909_ = lean_nat_add(v___x_809_, v_size_902_);
lean_dec(v_size_902_);
v___x_910_ = lean_nat_add(v___x_809_, v_size_908_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 4, v_impl_808_);
lean_ctor_set(v___x_906_, 3, v_r_901_);
lean_ctor_set(v___x_906_, 2, v_v_316_);
lean_ctor_set(v___x_906_, 1, v_k_315_);
lean_ctor_set(v___x_906_, 0, v___x_910_);
v___x_912_ = v___x_906_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_r_901_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_impl_808_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_912_);
lean_ctor_set(v___x_320_, 3, v_l_900_);
lean_ctor_set(v___x_320_, 2, v_v_904_);
lean_ctor_set(v___x_320_, 1, v_k_903_);
lean_ctor_set(v___x_320_, 0, v___x_909_);
v___x_914_ = v___x_320_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_k_903_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_v_904_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_l_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_k_920_; lean_object* v_v_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_932_; 
v_k_920_ = lean_ctor_get(v_l_317_, 1);
v_v_921_ = lean_ctor_get(v_l_317_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_933_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_935_);
v___x_923_ = v_l_317_;
v_isShared_924_ = v_isSharedCheck_932_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_v_921_);
lean_inc(v_k_920_);
lean_dec(v_l_317_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_932_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_unsigned_to_nat(3u);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 3, v_r_901_);
lean_ctor_set(v___x_923_, 2, v_v_316_);
lean_ctor_set(v___x_923_, 1, v_k_315_);
lean_ctor_set(v___x_923_, 0, v___x_809_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_r_901_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_r_901_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_927_);
lean_ctor_set(v___x_320_, 3, v_l_900_);
lean_ctor_set(v___x_320_, 2, v_v_921_);
lean_ctor_set(v___x_320_, 1, v_k_920_);
lean_ctor_set(v___x_320_, 0, v___x_925_);
v___x_929_ = v___x_320_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_k_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_v_921_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_l_900_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v_r_936_; 
v_r_936_ = lean_ctor_get(v_l_317_, 4);
lean_inc(v_r_936_);
if (lean_obj_tag(v_r_936_) == 0)
{
lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_961_; 
lean_inc(v_l_900_);
v_k_937_ = lean_ctor_get(v_l_317_, 1);
v_v_938_ = lean_ctor_get(v_l_317_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_l_317_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; 
v_unused_962_ = lean_ctor_get(v_l_317_, 4);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_317_, 3);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_317_, 0);
lean_dec(v_unused_964_);
v___x_940_ = v_l_317_;
v_isShared_941_ = v_isSharedCheck_961_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_v_938_);
lean_inc(v_k_937_);
lean_dec(v_l_317_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_961_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_k_942_; lean_object* v_v_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
v_k_942_ = lean_ctor_get(v_r_936_, 1);
v_v_943_ = lean_ctor_get(v_r_936_, 2);
v_isSharedCheck_957_ = !lean_is_exclusive(v_r_936_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; lean_object* v_unused_959_; lean_object* v_unused_960_; 
v_unused_958_ = lean_ctor_get(v_r_936_, 4);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_r_936_, 3);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_r_936_, 0);
lean_dec(v_unused_960_);
v___x_945_ = v_r_936_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_v_943_);
lean_inc(v_k_942_);
lean_dec(v_r_936_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_unsigned_to_nat(3u);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 4, v_l_900_);
lean_ctor_set(v___x_945_, 3, v_l_900_);
lean_ctor_set(v___x_945_, 2, v_v_938_);
lean_ctor_set(v___x_945_, 1, v_k_937_);
lean_ctor_set(v___x_945_, 0, v___x_809_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_k_937_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_v_938_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_l_900_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_l_900_);
v___x_949_ = v_reuseFailAlloc_956_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v_l_900_);
lean_ctor_set(v___x_940_, 2, v_v_316_);
lean_ctor_set(v___x_940_, 1, v_k_315_);
lean_ctor_set(v___x_940_, 0, v___x_809_);
v___x_951_ = v___x_940_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_l_900_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_l_900_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___x_951_);
lean_ctor_set(v___x_320_, 3, v___x_949_);
lean_ctor_set(v___x_320_, 2, v_v_943_);
lean_ctor_set(v___x_320_, 1, v_k_942_);
lean_ctor_set(v___x_320_, 0, v___x_947_);
v___x_953_ = v___x_320_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_k_942_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_v_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_unsigned_to_nat(2u);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_r_936_);
lean_ctor_set(v___x_320_, 0, v___x_965_);
v___x_967_ = v___x_320_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_r_936_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v___x_970_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_l_317_);
lean_ctor_set(v___x_320_, 0, v___x_809_);
v___x_970_ = v___x_320_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_l_317_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v_l_317_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
}
}
else
{
return v_t_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object* v_k_974_, lean_object* v_t_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_974_, v_t_975_);
lean_dec(v_k_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object* v_o_977_, lean_object* v_k_978_){
_start:
{
lean_object* v_map_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v_map_979_ = lean_ctor_get(v_o_977_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_o_977_);
if (v_isSharedCheck_990_ == 0)
{
v___x_981_ = v_o_977_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_map_979_);
lean_dec(v_o_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_988_; 
lean_inc(v_map_979_);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_978_, v_map_979_);
v___x_984_ = lean_box(0);
v___x_985_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v___x_984_, v_map_979_);
lean_dec(v_map_979_);
v___x_986_ = l_List_any___at___00Lean_Options_erase_spec__2(v___x_985_);
lean_dec(v___x_985_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_988_ = v___x_981_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*1, v___x_986_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object* v_o_991_, lean_object* v_k_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Options_erase(v_o_991_, v_k_992_);
lean_dec(v_k_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object* v_00_u03b2_994_, lean_object* v_k_995_, lean_object* v_t_996_, lean_object* v_h_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_995_, v_t_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object* v_00_u03b2_999_, lean_object* v_k_1000_, lean_object* v_t_1001_, lean_object* v_h_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(v_00_u03b2_999_, v_k_1000_, v_t_1001_, v_h_1002_);
lean_dec(v_k_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object* v_b_u2082_1004_, lean_object* v_f_1005_, lean_object* v_a_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_a_1006_);
lean_dec_ref(v_f_1005_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_b_u2082_1004_);
return v___x_1008_;
}
else
{
lean_object* v_val_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_val_1009_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v_x_1007_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_val_1009_);
lean_dec(v_x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_apply_3(v_f_1005_, v_a_1006_, v_val_1009_, v_b_u2082_1004_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object* v_b_u2082_1018_, lean_object* v_f_1019_, lean_object* v_a_1020_, lean_object* v_k_1021_, lean_object* v_t_1022_){
_start:
{
if (lean_obj_tag(v_t_1022_) == 0)
{
lean_object* v_size_1023_; lean_object* v_k_1024_; lean_object* v_v_1025_; lean_object* v_l_1026_; lean_object* v_r_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1042_; 
v_size_1023_ = lean_ctor_get(v_t_1022_, 0);
v_k_1024_ = lean_ctor_get(v_t_1022_, 1);
v_v_1025_ = lean_ctor_get(v_t_1022_, 2);
v_l_1026_ = lean_ctor_get(v_t_1022_, 3);
v_r_1027_ = lean_ctor_get(v_t_1022_, 4);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_t_1022_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1029_ = v_t_1022_;
v_isShared_1030_ = v_isSharedCheck_1042_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_r_1027_);
lean_inc(v_l_1026_);
lean_inc(v_v_1025_);
lean_inc(v_k_1024_);
lean_inc(v_size_1023_);
lean_dec(v_t_1022_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1042_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
uint8_t v___x_1031_; 
v___x_1031_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1021_, v_k_1024_);
switch(v___x_1031_)
{
case 0:
{
lean_object* v_impl_1032_; lean_object* v___x_1033_; 
lean_del_object(v___x_1029_);
lean_dec(v_size_1023_);
v_impl_1032_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1018_, v_f_1019_, v_a_1020_, v_k_1021_, v_l_1026_);
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1024_, v_v_1025_, v_impl_1032_, v_r_1027_);
return v___x_1033_;
}
case 1:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v_val_1036_; lean_object* v___x_1038_; 
lean_dec(v_k_1024_);
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_v_1025_);
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1018_, v_f_1019_, v_a_1020_, v___x_1034_);
v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1036_);
lean_dec(v___x_1035_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 2, v_val_1036_);
lean_ctor_set(v___x_1029_, 1, v_k_1021_);
v___x_1038_ = v___x_1029_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_size_1023_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_val_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_l_1026_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_r_1027_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
default: 
{
lean_object* v_impl_1040_; lean_object* v___x_1041_; 
lean_del_object(v___x_1029_);
lean_dec(v_size_1023_);
v_impl_1040_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1018_, v_f_1019_, v_a_1020_, v_k_1021_, v_r_1027_);
v___x_1041_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1024_, v_v_1025_, v_l_1026_, v_impl_1040_);
return v___x_1041_;
}
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_val_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1018_, v_f_1019_, v_a_1020_, v___x_1043_);
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1045_);
lean_dec(v___x_1044_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_k_1021_);
lean_ctor_set(v___x_1047_, 2, v_val_1045_);
lean_ctor_set(v___x_1047_, 3, v_t_1022_);
lean_ctor_set(v___x_1047_, 4, v_t_1022_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object* v_f_1048_, lean_object* v_init_1049_, lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 0)
{
lean_object* v_k_1051_; lean_object* v_v_1052_; lean_object* v_l_1053_; lean_object* v_r_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_k_1051_ = lean_ctor_get(v_x_1050_, 1);
lean_inc_n(v_k_1051_, 2);
v_v_1052_ = lean_ctor_get(v_x_1050_, 2);
lean_inc(v_v_1052_);
v_l_1053_ = lean_ctor_get(v_x_1050_, 3);
lean_inc(v_l_1053_);
v_r_1054_ = lean_ctor_get(v_x_1050_, 4);
lean_inc(v_r_1054_);
lean_dec_ref(v_x_1050_);
lean_inc_ref_n(v_f_1048_, 2);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1048_, v_init_1049_, v_l_1053_);
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_1052_, v_f_1048_, v_k_1051_, v_k_1051_, v___x_1055_);
v_init_1049_ = v___x_1056_;
v_x_1050_ = v_r_1054_;
goto _start;
}
else
{
lean_dec_ref(v_f_1048_);
return v_init_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object* v_f_1058_, lean_object* v_o1_1059_, lean_object* v_o2_1060_){
_start:
{
lean_object* v_map_1061_; uint8_t v_hasTrace_1062_; lean_object* v_map_1063_; uint8_t v_hasTrace_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1075_; 
v_map_1061_ = lean_ctor_get(v_o1_1059_, 0);
lean_inc(v_map_1061_);
v_hasTrace_1062_ = lean_ctor_get_uint8(v_o1_1059_, sizeof(void*)*1);
lean_dec_ref(v_o1_1059_);
v_map_1063_ = lean_ctor_get(v_o2_1060_, 0);
v_hasTrace_1064_ = lean_ctor_get_uint8(v_o2_1060_, sizeof(void*)*1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_o2_1060_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1066_ = v_o2_1060_;
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_map_1063_);
lean_dec(v_o2_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1075_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1058_, v_map_1061_, v_map_1063_);
if (v_hasTrace_1062_ == 0)
{
lean_object* v___x_1070_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1071_, sizeof(void*)*1, v_hasTrace_1064_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v___x_1073_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*1, v_hasTrace_1062_);
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object* v_b_u2082_1076_, lean_object* v_f_1077_, lean_object* v_a_1078_, lean_object* v_k_1079_, lean_object* v_t_1080_, lean_object* v_hl_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1076_, v_f_1077_, v_a_1078_, v_k_1079_, v_t_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object* v_f_1083_, lean_object* v_init_1084_, lean_object* v_t_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1083_, v_init_1084_, v_t_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
v___x_1120_ = l_Lean_mkAtom(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
v___x_1122_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1123_ = lean_array_push(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
v___x_1133_ = l_Lean_mkAtom(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
v___x_1135_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1136_ = lean_array_push(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
v___x_1138_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
v___x_1139_ = lean_box(2);
v___x_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
lean_ctor_set(v___x_1140_, 2, v___x_1137_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
v___x_1142_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
v___x_1143_ = lean_array_push(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
v___x_1145_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
v___x_1146_ = lean_box(2);
v___x_1147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
lean_ctor_set(v___x_1147_, 2, v___x_1144_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
v___x_1149_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1150_ = lean_array_push(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
v___x_1152_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1153_ = lean_box(2);
v___x_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
lean_ctor_set(v___x_1154_, 2, v___x_1151_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
v___x_1156_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
v___x_1159_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
v___x_1160_ = lean_box(2);
v___x_1161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v___x_1158_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
v___x_1163_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1164_ = lean_array_push(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
v___x_1166_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
v___x_1167_ = lean_box(2);
v___x_1168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___x_1166_);
lean_ctor_set(v___x_1168_, 2, v___x_1165_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__3(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = lean_box(0);
v___x_1177_ = ((lean_object*)(l_Lean_instInhabitedOptionDeprecation_default___closed__0));
v___x_1178_ = l_Lean_instInhabitedDataValue_default;
v___x_1179_ = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__2));
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
lean_ctor_set(v___x_1181_, 2, v___x_1178_);
lean_ctor_set(v___x_1181_, 3, v___x_1177_);
lean_ctor_set(v___x_1181_, 4, v___x_1176_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__3, &l_Lean_instInhabitedOptionDecl_default___closed__3_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__3);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_instInhabitedOptionDecl_default;
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* v_self_1189_){
_start:
{
lean_object* v_descr_1191_; lean_object* v_name_1194_; lean_object* v_descr_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_name_1194_ = lean_ctor_get(v_self_1189_, 0);
lean_inc(v_name_1194_);
v_descr_1195_ = lean_ctor_get(v_self_1189_, 3);
lean_inc_ref(v_descr_1195_);
lean_dec_ref(v_self_1189_);
v___x_1196_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
v___x_1197_ = l_Lean_Name_isPrefixOf(v___x_1196_, v_name_1194_);
lean_dec(v_name_1194_);
if (v___x_1197_ == 0)
{
return v_descr_1195_;
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = lean_string_utf8_byte_size(v_descr_1195_);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_nat_dec_eq(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v_descr_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
v_descr_1202_ = lean_string_append(v_descr_1195_, v___x_1201_);
v_descr_1191_ = v_descr_1202_;
goto v___jp_1190_;
}
else
{
v_descr_1191_ = v_descr_1195_;
goto v___jp_1190_;
}
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v_descr_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
v_descr_1193_ = lean_string_append(v_descr_1191_, v___x_1192_);
return v_descr_1193_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_box(1);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_box(1);
v___x_1206_ = lean_st_mk_ref(v___x_1205_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_registerOption___closed__0));
v___x_1212_ = lean_mk_io_user_error(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* v_name_1215_, lean_object* v_decl_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1245_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1245_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1245_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_unbox(v_a_1219_);
lean_dec(v_a_1219_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
lean_dec_ref(v_decl_1216_);
lean_dec(v_name_1215_);
v___x_1224_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1228_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1229_ = lean_st_ref_get(v___x_1228_);
v___x_1230_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1215_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1215_, v_decl_1216_, v___x_1229_);
v___x_1232_ = lean_st_ref_set(v___x_1228_, v___x_1231_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1232_);
v___x_1234_ = v___x_1221_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
lean_dec(v___x_1229_);
lean_dec_ref(v_decl_1216_);
v___x_1236_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1237_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1215_, v___x_1230_);
v___x_1238_ = lean_string_append(v___x_1236_, v___x_1237_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_mk_io_user_error(v___x_1240_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1241_);
v___x_1243_ = v___x_1221_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_decl_1216_);
lean_dec(v_name_1215_);
v_a_1246_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1218_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1218_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1254_, lean_object* v_decl_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = lean_register_option(v_name_1254_, v_decl_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1260_ = lean_st_ref_get(v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_getOptionDecls();
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* v_init_1264_, lean_object* v_x_1265_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 0)
{
lean_object* v_k_1266_; lean_object* v_v_1267_; lean_object* v_l_1268_; lean_object* v_r_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_k_1266_ = lean_ctor_get(v_x_1265_, 1);
v_v_1267_ = lean_ctor_get(v_x_1265_, 2);
v_l_1268_ = lean_ctor_get(v_x_1265_, 3);
v_r_1269_ = lean_ctor_get(v_x_1265_, 4);
v___x_1270_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1264_, v_l_1268_);
lean_inc(v_v_1267_);
lean_inc(v_k_1266_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_k_1266_);
lean_ctor_set(v___x_1271_, 1, v_v_1267_);
v___x_1272_ = lean_array_push(v___x_1270_, v___x_1271_);
v_init_1264_ = v___x_1272_;
v_x_1265_ = v_r_1269_;
goto _start;
}
else
{
return v_init_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* v_init_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1274_, v_x_1275_);
lean_dec(v_x_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(){
_start:
{
lean_object* v___x_1280_; lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1290_; 
v___x_1280_ = l_Lean_getOptionDecls();
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1290_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
v___x_1286_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_1285_, v_a_1281_);
lean_dec(v_a_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1286_);
v___x_1288_ = v___x_1283_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = lean_get_option_decls_array();
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* v_init_1293_, lean_object* v_t_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1293_, v_t_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* v_init_1296_, lean_object* v_t_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(v_init_1296_, v_t_1297_);
lean_dec(v_t_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* v_name_1301_){
_start:
{
lean_object* v___x_1303_; lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1323_; 
v___x_1303_ = l_Lean_getOptionDecls();
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1323_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1304_, v_name_1301_);
lean_dec(v_a_1304_);
if (lean_obj_tag(v___x_1308_) == 1)
{
lean_object* v_val_1309_; lean_object* v___x_1311_; 
lean_dec(v_name_1301_);
v_val_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1309_);
lean_dec_ref(v___x_1308_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_val_1309_);
v___x_1311_ = v___x_1306_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_val_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
lean_dec(v___x_1308_);
v___x_1313_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1314_ = 1;
v___x_1315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1301_, v___x_1314_);
v___x_1316_ = lean_string_append(v___x_1313_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_mk_io_user_error(v___x_1318_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 1);
lean_ctor_set(v___x_1306_, 0, v___x_1319_);
v___x_1321_ = v___x_1306_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_getOptionDecl(v_name_1324_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_getOptionDecl(v_name_1327_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1338_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_defValue_1334_; lean_object* v___x_1336_; 
v_defValue_1334_ = lean_ctor_get(v_a_1330_, 2);
lean_inc_ref(v_defValue_1334_);
lean_dec(v_a_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_defValue_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_defValue_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_a_1339_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1329_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1329_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_getOptionDefaultValue(v_name_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* v_name_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_getOptionDecl(v_name_1350_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_descr_1357_; lean_object* v___x_1359_; 
v_descr_1357_ = lean_ctor_get(v_a_1353_, 3);
lean_inc_ref(v_descr_1357_);
lean_dec(v_a_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_descr_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_descr_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1352_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1352_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_getOptionDescr(v_name_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1373_, lean_object* v_inst_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_apply_2(v_inst_1373_, lean_box(0), v_inst_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1376_, lean_object* v_n_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_apply_2(v_inst_1378_, lean_box(0), v_inst_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1381_, lean_object* v_toPure_1382_, uint8_t v_defValue_1383_, lean_object* v_opts_1384_){
_start:
{
lean_object* v_map_1385_; lean_object* v___x_1386_; 
v_map_1385_ = lean_ctor_get(v_opts_1384_, 0);
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1385_, v_k_1381_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_box(v_defValue_1383_);
v___x_1388_ = lean_apply_2(v_toPure_1382_, lean_box(0), v___x_1387_);
return v___x_1388_;
}
else
{
lean_object* v_val_1389_; 
v_val_1389_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_val_1389_);
lean_dec_ref(v___x_1386_);
if (lean_obj_tag(v_val_1389_) == 1)
{
uint8_t v_v_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_v_1390_ = lean_ctor_get_uint8(v_val_1389_, 0);
lean_dec_ref(v_val_1389_);
v___x_1391_ = lean_box(v_v_1390_);
v___x_1392_ = lean_apply_2(v_toPure_1382_, lean_box(0), v___x_1391_);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec(v_val_1389_);
v___x_1393_ = lean_box(v_defValue_1383_);
v___x_1394_ = lean_apply_2(v_toPure_1382_, lean_box(0), v___x_1393_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1395_, lean_object* v_toPure_1396_, lean_object* v_defValue_1397_, lean_object* v_opts_1398_){
_start:
{
uint8_t v_defValue_boxed_1399_; lean_object* v_res_1400_; 
v_defValue_boxed_1399_ = lean_unbox(v_defValue_1397_);
v_res_1400_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1395_, v_toPure_1396_, v_defValue_boxed_1399_, v_opts_1398_);
lean_dec_ref(v_opts_1398_);
lean_dec(v_k_1395_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_k_1403_, uint8_t v_defValue_1404_){
_start:
{
lean_object* v_toApplicative_1405_; lean_object* v_toBind_1406_; lean_object* v_toPure_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; lean_object* v___x_1410_; 
v_toApplicative_1405_ = lean_ctor_get(v_inst_1401_, 0);
lean_inc_ref(v_toApplicative_1405_);
v_toBind_1406_ = lean_ctor_get(v_inst_1401_, 1);
lean_inc(v_toBind_1406_);
lean_dec_ref(v_inst_1401_);
v_toPure_1407_ = lean_ctor_get(v_toApplicative_1405_, 1);
lean_inc(v_toPure_1407_);
lean_dec_ref(v_toApplicative_1405_);
v___x_1408_ = lean_box(v_defValue_1404_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1409_, 0, v_k_1403_);
lean_closure_set(v___f_1409_, 1, v_toPure_1407_);
lean_closure_set(v___f_1409_, 2, v___x_1408_);
v___x_1410_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v_inst_1402_, v___f_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_k_1413_, lean_object* v_defValue_1414_){
_start:
{
uint8_t v_defValue_boxed_1415_; lean_object* v_res_1416_; 
v_defValue_boxed_1415_ = lean_unbox(v_defValue_1414_);
v_res_1416_ = l_Lean_getBoolOption___redArg(v_inst_1411_, v_inst_1412_, v_k_1413_, v_defValue_boxed_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* v_m_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_k_1420_, uint8_t v_defValue_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_getBoolOption___redArg(v_inst_1418_, v_inst_1419_, v_k_1420_, v_defValue_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_k_1426_, lean_object* v_defValue_1427_){
_start:
{
uint8_t v_defValue_boxed_1428_; lean_object* v_res_1429_; 
v_defValue_boxed_1428_ = lean_unbox(v_defValue_1427_);
v_res_1429_ = l_Lean_getBoolOption(v_m_1423_, v_inst_1424_, v_inst_1425_, v_k_1426_, v_defValue_boxed_1428_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1430_, lean_object* v_toPure_1431_, lean_object* v_defValue_1432_, lean_object* v_opts_1433_){
_start:
{
lean_object* v_map_1434_; lean_object* v___x_1435_; 
v_map_1434_ = lean_ctor_get(v_opts_1433_, 0);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1434_, v_k_1430_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_defValue_1432_);
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; 
v_val_1437_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1437_);
lean_dec_ref(v___x_1435_);
if (lean_obj_tag(v_val_1437_) == 3)
{
lean_object* v_v_1438_; lean_object* v___x_1439_; 
lean_dec(v_defValue_1432_);
v_v_1438_ = lean_ctor_get(v_val_1437_, 0);
lean_inc(v_v_1438_);
lean_dec_ref(v_val_1437_);
v___x_1439_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_v_1438_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_val_1437_);
v___x_1440_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_defValue_1432_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1441_, lean_object* v_toPure_1442_, lean_object* v_defValue_1443_, lean_object* v_opts_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_getNatOption___redArg___lam__0(v_k_1441_, v_toPure_1442_, v_defValue_1443_, v_opts_1444_);
lean_dec_ref(v_opts_1444_);
lean_dec(v_k_1441_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_k_1448_, lean_object* v_defValue_1449_){
_start:
{
lean_object* v_toApplicative_1450_; lean_object* v_toBind_1451_; lean_object* v_toPure_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; 
v_toApplicative_1450_ = lean_ctor_get(v_inst_1446_, 0);
lean_inc_ref(v_toApplicative_1450_);
v_toBind_1451_ = lean_ctor_get(v_inst_1446_, 1);
lean_inc(v_toBind_1451_);
lean_dec_ref(v_inst_1446_);
v_toPure_1452_ = lean_ctor_get(v_toApplicative_1450_, 1);
lean_inc(v_toPure_1452_);
lean_dec_ref(v_toApplicative_1450_);
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1453_, 0, v_k_1448_);
lean_closure_set(v___f_1453_, 1, v_toPure_1452_);
lean_closure_set(v___f_1453_, 2, v_defValue_1449_);
v___x_1454_ = lean_apply_4(v_toBind_1451_, lean_box(0), lean_box(0), v_inst_1447_, v___f_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_, lean_object* v_k_1458_, lean_object* v_defValue_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_getNatOption___redArg(v_inst_1456_, v_inst_1457_, v_k_1458_, v_defValue_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1461_, lean_object* v_f_1462_, lean_object* v_00_u03b2_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_apply_3(v_inst_1461_, lean_box(0), v_f_1462_, v___y_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_00_u03b1_1468_, lean_object* v_f_1469_, lean_object* v_x_1470_){
_start:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; 
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1471_, 0, v_inst_1466_);
lean_closure_set(v___f_1471_, 1, v_f_1469_);
v___x_1472_ = lean_apply_3(v_inst_1467_, lean_box(0), v___f_1471_, v_x_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1473_, lean_object* v_inst_1474_){
_start:
{
lean_object* v___f_1475_; 
v___f_1475_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1475_, 0, v_inst_1474_);
lean_closure_set(v___f_1475_, 1, v_inst_1473_);
return v___f_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1476_, lean_object* v_n_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_){
_start:
{
lean_object* v___f_1480_; 
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1480_, 0, v_inst_1479_);
lean_closure_set(v___f_1480_, 1, v_inst_1478_);
return v___f_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1484_, lean_object* v_o_1485_){
_start:
{
lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1487_ = 1;
v___x_1488_ = lean_box(v___x_1487_);
v___x_1489_ = l_Lean_Options_set___redArg(v___x_1484_, v_o_1485_, v___x_1486_, v___x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___f_1491_; 
v___x_1490_ = l_Lean_KVMap_instValueBool;
v___f_1491_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1491_, 0, v___x_1490_);
return v___f_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1492_, lean_object* v_x_1493_){
_start:
{
lean_object* v___f_1494_; lean_object* v___x_1495_; 
v___f_1494_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1495_ = lean_apply_3(v_inst_1492_, lean_box(0), v___f_1494_, v_x_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1496_, lean_object* v_00_u03b1_1497_, lean_object* v_inst_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_withInPattern___redArg(v_inst_1498_, v_x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1501_){
_start:
{
lean_object* v_map_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v_map_1502_ = lean_ctor_get(v_o_1501_, 0);
v___x_1503_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1504_ = 0;
v___x_1505_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1502_, v___x_1503_);
if (lean_obj_tag(v___x_1505_) == 0)
{
return v___x_1504_;
}
else
{
lean_object* v_val_1506_; 
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref(v___x_1505_);
if (lean_obj_tag(v_val_1506_) == 1)
{
uint8_t v_v_1507_; 
v_v_1507_ = lean_ctor_get_uint8(v_val_1506_, 0);
lean_dec_ref(v_val_1506_);
return v_v_1507_;
}
else
{
lean_dec(v_val_1506_);
return v___x_1504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l_Lean_Options_getInPattern(v_o_1508_);
lean_dec_ref(v_o_1508_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v_inst_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_00_u03b1_1514_, lean_object* v_inst_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1519_, lean_object* v_inst_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1522_, lean_object* v_opts_1523_, lean_object* v_opt_1524_){
_start:
{
lean_object* v_name_1525_; lean_object* v_map_1526_; lean_object* v_ofDataValue_x3f_1527_; lean_object* v___x_1528_; 
v_name_1525_ = lean_ctor_get(v_opt_1524_, 0);
v_map_1526_ = lean_ctor_get(v_opts_1523_, 0);
v_ofDataValue_x3f_1527_ = lean_ctor_get(v_inst_1522_, 1);
lean_inc_ref(v_ofDataValue_x3f_1527_);
lean_dec_ref(v_inst_1522_);
v___x_1528_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1526_, v_name_1525_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v___x_1529_; 
lean_dec_ref(v_ofDataValue_x3f_1527_);
v___x_1529_ = lean_box(0);
return v___x_1529_;
}
else
{
lean_object* v_val_1530_; lean_object* v___x_1531_; 
v_val_1530_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1530_);
lean_dec_ref(v___x_1528_);
v___x_1531_ = lean_apply_1(v_ofDataValue_x3f_1527_, v_val_1530_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1532_, lean_object* v_opts_1533_, lean_object* v_opt_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Option_get_x3f___redArg(v_inst_1532_, v_opts_1533_, v_opt_1534_);
lean_dec_ref(v_opt_1534_);
lean_dec_ref(v_opts_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1536_, lean_object* v_inst_1537_, lean_object* v_opts_1538_, lean_object* v_opt_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_Option_get_x3f___redArg(v_inst_1537_, v_opts_1538_, v_opt_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1541_, lean_object* v_inst_1542_, lean_object* v_opts_1543_, lean_object* v_opt_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Option_get_x3f(v_00_u03b1_1541_, v_inst_1542_, v_opts_1543_, v_opt_1544_);
lean_dec_ref(v_opt_1544_);
lean_dec_ref(v_opts_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1546_, lean_object* v_opts_1547_, lean_object* v_opt_1548_){
_start:
{
lean_object* v_name_1549_; lean_object* v_defValue_1550_; lean_object* v_map_1551_; lean_object* v_ofDataValue_x3f_1552_; lean_object* v___x_1553_; 
v_name_1549_ = lean_ctor_get(v_opt_1548_, 0);
v_defValue_1550_ = lean_ctor_get(v_opt_1548_, 1);
v_map_1551_ = lean_ctor_get(v_opts_1547_, 0);
v_ofDataValue_x3f_1552_ = lean_ctor_get(v_inst_1546_, 1);
lean_inc_ref(v_ofDataValue_x3f_1552_);
lean_dec_ref(v_inst_1546_);
v___x_1553_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1551_, v_name_1549_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1552_);
lean_inc(v_defValue_1550_);
return v_defValue_1550_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1555_; 
v_val_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_val_1554_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = lean_apply_1(v_ofDataValue_x3f_1552_, v_val_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_inc(v_defValue_1550_);
return v_defValue_1550_;
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
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1557_, lean_object* v_opts_1558_, lean_object* v_opt_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_Option_get___redArg(v_inst_1557_, v_opts_1558_, v_opt_1559_);
lean_dec_ref(v_opt_1559_);
lean_dec_ref(v_opts_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1561_, lean_object* v_inst_1562_, lean_object* v_opts_1563_, lean_object* v_opt_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Option_get___redArg(v_inst_1562_, v_opts_1563_, v_opt_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1566_, lean_object* v_inst_1567_, lean_object* v_opts_1568_, lean_object* v_opt_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Option_get(v_00_u03b1_1566_, v_inst_1567_, v_opts_1568_, v_opt_1569_);
lean_dec_ref(v_opt_1569_);
lean_dec_ref(v_opts_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* v_opts_1571_, lean_object* v_name_1572_, uint8_t v_defValue_1573_){
_start:
{
lean_object* v_map_1574_; lean_object* v___x_1575_; 
v_map_1574_ = lean_ctor_get(v_opts_1571_, 0);
lean_inc(v_map_1574_);
lean_dec_ref(v_opts_1571_);
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1574_, v_name_1572_);
lean_dec(v_name_1572_);
lean_dec(v_map_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
return v_defValue_1573_;
}
else
{
lean_object* v_val_1576_; 
v_val_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_val_1576_);
lean_dec_ref(v___x_1575_);
if (lean_obj_tag(v_val_1576_) == 1)
{
uint8_t v_v_1577_; 
v_v_1577_ = lean_ctor_get_uint8(v_val_1576_, 0);
lean_dec_ref(v_val_1576_);
return v_v_1577_;
}
else
{
lean_dec(v_val_1576_);
return v_defValue_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* v_opts_1578_, lean_object* v_name_1579_, lean_object* v_defValue_1580_){
_start:
{
uint8_t v_defValue_boxed_1581_; uint8_t v_res_1582_; lean_object* v_r_1583_; 
v_defValue_boxed_1581_ = lean_unbox(v_defValue_1580_);
v_res_1582_ = lean_options_get_bool(v_opts_1578_, v_name_1579_, v_defValue_boxed_1581_);
v_r_1583_ = lean_box(v_res_1582_);
return v_r_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* v_inst_1584_, lean_object* v_opt_1585_, lean_object* v_toPure_1586_, lean_object* v_____do__lift_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = l_Lean_Option_get___redArg(v_inst_1584_, v_____do__lift_1587_, v_opt_1585_);
v___x_1589_ = lean_apply_2(v_toPure_1586_, lean_box(0), v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* v_inst_1590_, lean_object* v_opt_1591_, lean_object* v_toPure_1592_, lean_object* v_____do__lift_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Option_getM___redArg___lam__0(v_inst_1590_, v_opt_1591_, v_toPure_1592_, v_____do__lift_1593_);
lean_dec_ref(v_____do__lift_1593_);
lean_dec_ref(v_opt_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_opt_1598_){
_start:
{
lean_object* v_toApplicative_1599_; lean_object* v_toBind_1600_; lean_object* v_toPure_1601_; lean_object* v___f_1602_; lean_object* v___x_1603_; 
v_toApplicative_1599_ = lean_ctor_get(v_inst_1595_, 0);
lean_inc_ref(v_toApplicative_1599_);
v_toBind_1600_ = lean_ctor_get(v_inst_1595_, 1);
lean_inc(v_toBind_1600_);
lean_dec_ref(v_inst_1595_);
v_toPure_1601_ = lean_ctor_get(v_toApplicative_1599_, 1);
lean_inc(v_toPure_1601_);
lean_dec_ref(v_toApplicative_1599_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1602_, 0, v_inst_1597_);
lean_closure_set(v___f_1602_, 1, v_opt_1598_);
lean_closure_set(v___f_1602_, 2, v_toPure_1601_);
v___x_1603_ = lean_apply_4(v_toBind_1600_, lean_box(0), lean_box(0), v_inst_1596_, v___f_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* v_m_1604_, lean_object* v_00_u03b1_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_opt_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Option_getM___redArg(v_inst_1606_, v_inst_1607_, v_inst_1608_, v_opt_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* v_inst_1611_, lean_object* v_opts_1612_, lean_object* v_opt_1613_, lean_object* v_val_1614_){
_start:
{
lean_object* v_name_1615_; lean_object* v___x_1616_; 
v_name_1615_ = lean_ctor_get(v_opt_1613_, 0);
lean_inc(v_name_1615_);
lean_dec_ref(v_opt_1613_);
v___x_1616_ = l_Lean_Options_set___redArg(v_inst_1611_, v_opts_1612_, v_name_1615_, v_val_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* v_00_u03b1_1617_, lean_object* v_inst_1618_, lean_object* v_opts_1619_, lean_object* v_opt_1620_, lean_object* v_val_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Option_set___redArg(v_inst_1618_, v_opts_1619_, v_opt_1620_, v_val_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1623_, lean_object* v_k_1624_, uint8_t v_v_1625_){
_start:
{
lean_object* v_map_1626_; uint8_t v_hasTrace_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1641_; 
v_map_1626_ = lean_ctor_get(v_o_1623_, 0);
v_hasTrace_1627_ = lean_ctor_get_uint8(v_o_1623_, sizeof(void*)*1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_o_1623_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1629_ = v_o_1623_;
v_isShared_1630_ = v_isSharedCheck_1641_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_map_1626_);
lean_dec(v_o_1623_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1641_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1631_, 0, v_v_1625_);
lean_inc(v_k_1624_);
v___x_1632_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1624_, v___x_1631_, v_map_1626_);
if (v_hasTrace_1627_ == 0)
{
lean_object* v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1636_; 
v___x_1633_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_1634_ = l_Lean_Name_isPrefixOf(v___x_1633_, v_k_1624_);
lean_dec(v_k_1624_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1636_ = v___x_1629_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1632_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*1, v___x_1634_);
return v___x_1636_;
}
}
else
{
lean_object* v___x_1639_; 
lean_dec(v_k_1624_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1632_);
v___x_1639_ = v___x_1629_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1632_);
lean_ctor_set_uint8(v_reuseFailAlloc_1640_, sizeof(void*)*1, v_hasTrace_1627_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1642_, lean_object* v_k_1643_, lean_object* v_v_1644_){
_start:
{
uint8_t v_v_boxed_1645_; lean_object* v_res_1646_; 
v_v_boxed_1645_ = lean_unbox(v_v_1644_);
v_res_1646_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1642_, v_k_1643_, v_v_boxed_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* v_opts_1647_, lean_object* v_name_1648_, uint8_t v_val_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1647_, v_name_1648_, v_val_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1651_, lean_object* v_name_1652_, lean_object* v_val_1653_){
_start:
{
uint8_t v_val_boxed_1654_; lean_object* v_res_1655_; 
v_val_boxed_1654_ = lean_unbox(v_val_1653_);
v_res_1655_ = lean_options_update_bool(v_opts_1651_, v_name_1652_, v_val_boxed_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1656_, lean_object* v_opts_1657_, lean_object* v_opt_1658_, lean_object* v_val_1659_){
_start:
{
lean_object* v_name_1660_; lean_object* v_map_1661_; uint8_t v___x_1662_; 
v_name_1660_ = lean_ctor_get(v_opt_1658_, 0);
v_map_1661_ = lean_ctor_get(v_opts_1657_, 0);
v___x_1662_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1660_, v_map_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Option_set___redArg(v_inst_1656_, v_opts_1657_, v_opt_1658_, v_val_1659_);
return v___x_1663_;
}
else
{
lean_dec(v_val_1659_);
lean_dec_ref(v_opt_1658_);
lean_dec_ref(v_inst_1656_);
return v_opts_1657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1664_, lean_object* v_inst_1665_, lean_object* v_opts_1666_, lean_object* v_opt_1667_, lean_object* v_val_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1665_, v_opts_1666_, v_opt_1667_, v_val_1668_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1671_, lean_object* v_name_1672_, lean_object* v_decl_1673_, lean_object* v_ref_1674_){
_start:
{
lean_object* v_toDataValue_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1705_; 
v_toDataValue_1676_ = lean_ctor_get(v_inst_1671_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_inst_1671_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v_inst_1671_, 1);
lean_dec(v_unused_1706_);
v___x_1678_ = v_inst_1671_;
v_isShared_1679_ = v_isSharedCheck_1705_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_toDataValue_1676_);
lean_dec(v_inst_1671_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1705_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_defValue_1680_; lean_object* v_descr_1681_; lean_object* v_deprecation_x3f_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_defValue_1680_ = lean_ctor_get(v_decl_1673_, 0);
lean_inc_n(v_defValue_1680_, 2);
v_descr_1681_ = lean_ctor_get(v_decl_1673_, 1);
lean_inc_ref(v_descr_1681_);
v_deprecation_x3f_1682_ = lean_ctor_get(v_decl_1673_, 2);
lean_inc(v_deprecation_x3f_1682_);
lean_dec_ref(v_decl_1673_);
v___x_1683_ = lean_apply_1(v_toDataValue_1676_, v_defValue_1680_);
lean_inc_n(v_name_1672_, 2);
v___x_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1684_, 0, v_name_1672_);
lean_ctor_set(v___x_1684_, 1, v_ref_1674_);
lean_ctor_set(v___x_1684_, 2, v___x_1683_);
lean_ctor_set(v___x_1684_, 3, v_descr_1681_);
lean_ctor_set(v___x_1684_, 4, v_deprecation_x3f_1682_);
v___x_1685_ = lean_register_option(v_name_1672_, v___x_1684_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1695_; 
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1685_, 0);
lean_dec(v_unused_1696_);
v___x_1687_ = v___x_1685_;
v_isShared_1688_ = v_isSharedCheck_1695_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v___x_1685_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1695_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v_defValue_1680_);
lean_ctor_set(v___x_1678_, 0, v_name_1672_);
v___x_1690_ = v___x_1678_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_name_1672_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_defValue_1680_);
v___x_1690_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1692_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1690_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_defValue_1680_);
lean_del_object(v___x_1678_);
lean_dec(v_name_1672_);
v_a_1697_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1685_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1685_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1707_, lean_object* v_name_1708_, lean_object* v_decl_1709_, lean_object* v_ref_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Option_register___redArg(v_inst_1707_, v_name_1708_, v_decl_1709_, v_ref_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1713_, lean_object* v_inst_1714_, lean_object* v_name_1715_, lean_object* v_decl_1716_, lean_object* v_ref_1717_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Option_register___redArg(v_inst_1714_, v_name_1715_, v_decl_1716_, v_ref_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_inst_1721_, lean_object* v_name_1722_, lean_object* v_decl_1723_, lean_object* v_ref_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Option_register(v_00_u03b1_1720_, v_inst_1721_, v_name_1722_, v_decl_1723_, v_ref_1724_);
return v_res_1726_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
v___x_1815_ = l_String_toRawSubstring_x27(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
v___x_1836_ = l_String_toRawSubstring_x27(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29(void){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Array_mkArray0(lean_box(0));
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* v_x_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1867_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_1868_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(v_x_1864_);
v___x_1869_ = l_Lean_Syntax_isOfKind(v_x_1864_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
lean_dec(v_x_1864_);
v___x_1870_ = lean_box(1);
v___x_1871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v_a_1866_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_name_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_2006_; lean_object* v___x_2017_; 
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1872_);
v___x_1874_ = lean_unsigned_to_nat(1u);
v___x_1875_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(3u);
v_name_1877_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1876_);
v___x_1878_ = lean_unsigned_to_nat(5u);
v___x_1879_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1878_);
v___x_1880_ = lean_unsigned_to_nat(7u);
v___x_1881_ = l_Lean_Syntax_getArg(v_x_1864_, v___x_1880_);
lean_dec(v_x_1864_);
v___x_2017_ = l_Lean_Syntax_getOptional_x3f(v___x_1875_);
lean_dec(v___x_1875_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_box(0);
v___y_2006_ = v___x_2018_;
goto v___jp_2005_;
}
else
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_val_2019_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2017_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v___x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_val_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v___y_2006_ = v___x_2024_;
goto v___jp_2005_;
}
}
}
v___jp_1882_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_inc_n(v___y_1890_, 2);
lean_inc_n(v___y_1885_, 6);
v___x_1896_ = l_Lean_Syntax_node2(v___y_1885_, v___y_1890_, v___y_1895_, v___x_1881_);
v___x_1897_ = l_Lean_Syntax_node2(v___y_1885_, v___y_1884_, v___y_1893_, v___x_1896_);
v___x_1898_ = l_Lean_Syntax_node1(v___y_1885_, v___y_1883_, v___x_1897_);
v___x_1899_ = l_Lean_Syntax_node2(v___y_1885_, v___y_1889_, v___x_1898_, v___y_1891_);
v___x_1900_ = l_Lean_Syntax_node1(v___y_1885_, v___y_1890_, v___x_1899_);
v___x_1901_ = l_Lean_Syntax_node1(v___y_1885_, v___y_1886_, v___x_1900_);
lean_inc(v___y_1892_);
v___x_1902_ = l_Lean_Syntax_node4(v___y_1885_, v___y_1892_, v___y_1888_, v___y_1887_, v___y_1894_, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_a_1866_);
return v___x_1903_;
}
v___jp_1904_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_inc_ref(v___y_1909_);
v___x_1917_ = l_Array_append___redArg(v___y_1909_, v___y_1916_);
lean_dec_ref(v___y_1916_);
lean_inc_n(v___y_1908_, 3);
lean_inc_n(v___y_1906_, 12);
v___x_1918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1918_, 0, v___y_1906_);
lean_ctor_set(v___x_1918_, 1, v___y_1908_);
lean_ctor_set(v___x_1918_, 2, v___x_1917_);
lean_inc_n(v___y_1910_, 5);
lean_inc(v___y_1907_);
v___x_1919_ = l_Lean_Syntax_node7(v___y_1906_, v___y_1907_, v___y_1911_, v___y_1910_, v___x_1918_, v___y_1910_, v___y_1910_, v___y_1910_, v___y_1910_);
v___x_1920_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_1913_);
lean_inc_ref_n(v___y_1905_, 6);
v___x_1921_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___y_1913_, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
v___x_1923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___y_1906_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_Syntax_node1(v___y_1906_, v___x_1921_, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_1926_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_1927_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___x_1925_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___y_1906_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_1931_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___x_1925_, v___x_1930_);
v___x_1932_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_1933_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v___y_1915_, 2);
lean_inc_n(v___y_1912_, 2);
v___x_1934_ = l_Lean_addMacroScope(v___y_1912_, v___x_1933_, v___y_1915_);
v___x_1935_ = lean_box(0);
v___x_1936_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_1937_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1906_);
lean_ctor_set(v___x_1937_, 1, v___x_1932_);
lean_ctor_set(v___x_1937_, 2, v___x_1934_);
lean_ctor_set(v___x_1937_, 3, v___x_1936_);
v___x_1938_ = l_Lean_Syntax_node1(v___y_1906_, v___y_1908_, v___x_1879_);
lean_inc(v___x_1931_);
v___x_1939_ = l_Lean_Syntax_node2(v___y_1906_, v___x_1931_, v___x_1937_, v___x_1938_);
v___x_1940_ = l_Lean_Syntax_node2(v___y_1906_, v___x_1927_, v___x_1929_, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_1942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___y_1906_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
lean_inc(v_name_1877_);
v___x_1943_ = l_Lean_Syntax_node3(v___y_1906_, v___y_1908_, v_name_1877_, v___x_1940_, v___x_1942_);
v___x_1944_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_1945_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___x_1925_, v___x_1944_);
v___x_1946_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_1947_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___x_1925_, v___x_1946_);
v___x_1948_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_1949_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___x_1925_, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_1951_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_1952_ = l_Lean_addMacroScope(v___y_1912_, v___x_1951_, v___y_1915_);
v___x_1953_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_1954_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1954_, 0, v___y_1906_);
lean_ctor_set(v___x_1954_, 1, v___x_1950_);
lean_ctor_set(v___x_1954_, 2, v___x_1952_);
lean_ctor_set(v___x_1954_, 3, v___x_1953_);
v___x_1955_ = l_Lean_TSyntax_getId(v_name_1877_);
lean_dec(v_name_1877_);
lean_inc(v___x_1955_);
v___x_1956_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1935_, v___x_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_quoteNameMk(v___x_1955_);
v___y_1883_ = v___x_1949_;
v___y_1884_ = v___x_1931_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___x_1945_;
v___y_1887_ = v___x_1924_;
v___y_1888_ = v___x_1919_;
v___y_1889_ = v___x_1947_;
v___y_1890_ = v___y_1908_;
v___y_1891_ = v___y_1910_;
v___y_1892_ = v___y_1914_;
v___y_1893_ = v___x_1954_;
v___y_1894_ = v___x_1943_;
v___y_1895_ = v___x_1957_;
goto v___jp_1882_;
}
else
{
lean_object* v_val_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec(v___x_1955_);
v_val_1958_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_val_1958_);
lean_dec_ref(v___x_1956_);
v___x_1959_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
lean_inc_ref(v___y_1905_);
v___x_1960_ = l_Lean_Name_mkStr4(v___x_1867_, v___y_1905_, v___x_1925_, v___x_1959_);
v___x_1961_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1962_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_1963_ = lean_string_intercalate(v___x_1962_, v_val_1958_);
v___x_1964_ = lean_string_append(v___x_1961_, v___x_1963_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = lean_box(2);
v___x_1966_ = l_Lean_Syntax_mkNameLit(v___x_1964_, v___x_1965_);
v___x_1967_ = lean_mk_empty_array_with_capacity(v___x_1874_);
v___x_1968_ = lean_array_push(v___x_1967_, v___x_1966_);
v___x_1969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1965_);
lean_ctor_set(v___x_1969_, 1, v___x_1960_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
v___y_1883_ = v___x_1949_;
v___y_1884_ = v___x_1931_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___x_1945_;
v___y_1887_ = v___x_1924_;
v___y_1888_ = v___x_1919_;
v___y_1889_ = v___x_1947_;
v___y_1890_ = v___y_1908_;
v___y_1891_ = v___y_1910_;
v___y_1892_ = v___y_1914_;
v___y_1893_ = v___x_1954_;
v___y_1894_ = v___x_1943_;
v___y_1895_ = v___x_1969_;
goto v___jp_1882_;
}
}
v___jp_1970_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_inc_ref_n(v___y_1976_, 2);
v___x_1982_ = l_Array_append___redArg(v___y_1976_, v___y_1981_);
lean_dec_ref(v___y_1981_);
lean_inc_n(v___y_1975_, 2);
lean_inc_n(v___y_1972_, 2);
v___x_1983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1983_, 0, v___y_1972_);
lean_ctor_set(v___x_1983_, 1, v___y_1975_);
lean_ctor_set(v___x_1983_, 2, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1984_, 0, v___y_1972_);
lean_ctor_set(v___x_1984_, 1, v___y_1975_);
lean_ctor_set(v___x_1984_, 2, v___y_1976_);
if (lean_obj_tag(v___y_1973_) == 1)
{
lean_object* v_val_1985_; lean_object* v___x_1986_; 
v_val_1985_ = lean_ctor_get(v___y_1973_, 0);
lean_inc(v_val_1985_);
lean_dec_ref(v___y_1973_);
v___x_1986_ = l_Array_mkArray1___redArg(v_val_1985_);
v___y_1905_ = v___y_1971_;
v___y_1906_ = v___y_1972_;
v___y_1907_ = v___y_1974_;
v___y_1908_ = v___y_1975_;
v___y_1909_ = v___y_1976_;
v___y_1910_ = v___x_1984_;
v___y_1911_ = v___x_1983_;
v___y_1912_ = v___y_1977_;
v___y_1913_ = v___y_1978_;
v___y_1914_ = v___y_1979_;
v___y_1915_ = v___y_1980_;
v___y_1916_ = v___x_1986_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1987_; 
lean_dec(v___y_1973_);
v___x_1987_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1905_ = v___y_1971_;
v___y_1906_ = v___y_1972_;
v___y_1907_ = v___y_1974_;
v___y_1908_ = v___y_1975_;
v___y_1909_ = v___y_1976_;
v___y_1910_ = v___x_1984_;
v___y_1911_ = v___x_1983_;
v___y_1912_ = v___y_1977_;
v___y_1913_ = v___y_1978_;
v___y_1914_ = v___y_1979_;
v___y_1915_ = v___y_1980_;
v___y_1916_ = v___x_1987_;
goto v___jp_1904_;
}
}
v___jp_1988_:
{
lean_object* v_quotContext_1991_; lean_object* v_currMacroScope_1992_; lean_object* v_ref_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_quotContext_1991_ = lean_ctor_get(v_a_1865_, 1);
v_currMacroScope_1992_ = lean_ctor_get(v_a_1865_, 2);
v_ref_1993_ = lean_ctor_get(v_a_1865_, 5);
v___x_1994_ = 0;
v___x_1995_ = l_Lean_SourceInfo_fromRef(v_ref_1993_, v___x_1994_);
v___x_1996_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_1997_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_1998_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_1999_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28));
v___x_2000_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2001_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
if (lean_obj_tag(v___y_1990_) == 1)
{
lean_object* v_val_2002_; lean_object* v___x_2003_; 
v_val_2002_ = lean_ctor_get(v___y_1990_, 0);
lean_inc(v_val_2002_);
lean_dec_ref(v___y_1990_);
v___x_2003_ = l_Array_mkArray1___redArg(v_val_2002_);
v___y_1971_ = v___x_1996_;
v___y_1972_ = v___x_1995_;
v___y_1973_ = v___y_1989_;
v___y_1974_ = v___x_1999_;
v___y_1975_ = v___x_2000_;
v___y_1976_ = v___x_2001_;
v___y_1977_ = v_quotContext_1991_;
v___y_1978_ = v___x_1997_;
v___y_1979_ = v___x_1998_;
v___y_1980_ = v_currMacroScope_1992_;
v___y_1981_ = v___x_2003_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_2004_; 
lean_dec(v___y_1990_);
v___x_2004_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1971_ = v___x_1996_;
v___y_1972_ = v___x_1995_;
v___y_1973_ = v___y_1989_;
v___y_1974_ = v___x_1999_;
v___y_1975_ = v___x_2000_;
v___y_1976_ = v___x_2001_;
v___y_1977_ = v_quotContext_1991_;
v___y_1978_ = v___x_1997_;
v___y_1979_ = v___x_1998_;
v___y_1980_ = v_currMacroScope_1992_;
v___y_1981_ = v___x_2004_;
goto v___jp_1970_;
}
}
v___jp_2005_:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Syntax_getOptional_x3f(v___x_1873_);
lean_dec(v___x_1873_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_box(0);
v___y_1989_ = v___y_2006_;
v___y_1990_ = v___x_2008_;
goto v___jp_1988_;
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
v_val_2009_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2007_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v___x_2007_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_val_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
v___y_1989_ = v___y_2006_;
v___y_1990_ = v___x_2014_;
goto v___jp_1988_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(lean_object* v_x_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_2027_, v_a_2028_, v_a_2029_);
lean_dec_ref(v_a_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2107_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v_x_2107_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_x_2107_);
v___x_2112_ = lean_box(1);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_2109_);
return v___x_2113_;
}
else
{
lean_object* v_quotContext_2114_; lean_object* v_currMacroScope_2115_; lean_object* v_ref_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_name_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___y_2158_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_quotContext_2114_ = lean_ctor_get(v_a_2108_, 1);
v_currMacroScope_2115_ = lean_ctor_get(v_a_2108_, 2);
v_ref_2116_ = lean_ctor_get(v_a_2108_, 5);
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = l_Lean_Syntax_getArg(v_x_2107_, v___x_2117_);
v___x_2119_ = lean_unsigned_to_nat(2u);
v_name_2120_ = l_Lean_Syntax_getArg(v_x_2107_, v___x_2119_);
v___x_2121_ = lean_unsigned_to_nat(4u);
v___x_2122_ = l_Lean_Syntax_getArg(v_x_2107_, v___x_2121_);
v___x_2123_ = lean_unsigned_to_nat(6u);
v___x_2124_ = l_Lean_Syntax_getArg(v_x_2107_, v___x_2123_);
lean_dec(v_x_2107_);
v___x_2125_ = 0;
v___x_2126_ = l_Lean_SourceInfo_fromRef(v_ref_2116_, v___x_2125_);
v___x_2127_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25));
v___x_2128_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_2129_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
lean_inc_n(v___x_2126_, 10);
v___x_2130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2126_);
lean_ctor_set(v___x_2130_, 1, v___x_2127_);
v___x_2131_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2129_, v___x_2130_);
v___x_2132_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2133_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2134_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2135_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2126_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2137_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_2138_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v_currMacroScope_2115_, 2);
lean_inc_n(v_quotContext_2114_, 2);
v___x_2139_ = l_Lean_addMacroScope(v_quotContext_2114_, v___x_2138_, v_currMacroScope_2115_);
v___x_2140_ = lean_box(0);
v___x_2141_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_2142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2126_);
lean_ctor_set(v___x_2142_, 1, v___x_2137_);
lean_ctor_set(v___x_2142_, 2, v___x_2139_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
v___x_2143_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2132_, v___x_2122_);
v___x_2144_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2136_, v___x_2142_, v___x_2143_);
v___x_2145_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2133_, v___x_2135_, v___x_2144_);
v___x_2146_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_2147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2126_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
lean_inc(v_name_2120_);
v___x_2148_ = l_Lean_Syntax_node3(v___x_2126_, v___x_2132_, v_name_2120_, v___x_2145_, v___x_2147_);
v___x_2149_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2150_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4));
v___x_2151_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5));
v___x_2152_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2153_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_2154_ = l_Lean_addMacroScope(v_quotContext_2114_, v___x_2153_, v_currMacroScope_2115_);
v___x_2155_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_2156_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2126_);
lean_ctor_set(v___x_2156_, 1, v___x_2152_);
lean_ctor_set(v___x_2156_, 2, v___x_2154_);
lean_ctor_set(v___x_2156_, 3, v___x_2155_);
v___x_2169_ = l_Lean_TSyntax_getId(v_name_2120_);
lean_dec(v_name_2120_);
lean_inc(v___x_2169_);
v___x_2170_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2140_, v___x_2169_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_quoteNameMk(v___x_2169_);
v___y_2158_ = v___x_2171_;
goto v___jp_2157_;
}
else
{
lean_object* v_val_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v___x_2169_);
v_val_2172_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_val_2172_);
lean_dec_ref(v___x_2170_);
v___x_2173_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6));
v___x_2174_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_2175_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2176_ = lean_string_intercalate(v___x_2175_, v_val_2172_);
v___x_2177_ = lean_string_append(v___x_2174_, v___x_2176_);
lean_dec_ref(v___x_2176_);
v___x_2178_ = lean_box(2);
v___x_2179_ = l_Lean_Syntax_mkNameLit(v___x_2177_, v___x_2178_);
v___x_2180_ = lean_unsigned_to_nat(1u);
v___x_2181_ = lean_mk_empty_array_with_capacity(v___x_2180_);
v___x_2182_ = lean_array_push(v___x_2181_, v___x_2179_);
v___x_2183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2178_);
lean_ctor_set(v___x_2183_, 1, v___x_2173_);
lean_ctor_set(v___x_2183_, 2, v___x_2182_);
v___y_2158_ = v___x_2183_;
goto v___jp_2157_;
}
v___jp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_inc_n(v___x_2126_, 7);
v___x_2159_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2132_, v___y_2158_, v___x_2124_);
v___x_2160_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2136_, v___x_2156_, v___x_2159_);
v___x_2161_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2151_, v___x_2160_);
v___x_2162_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2126_);
lean_ctor_set(v___x_2163_, 1, v___x_2132_);
lean_ctor_set(v___x_2163_, 2, v___x_2162_);
v___x_2164_ = l_Lean_Syntax_node2(v___x_2126_, v___x_2150_, v___x_2161_, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2132_, v___x_2164_);
v___x_2166_ = l_Lean_Syntax_node1(v___x_2126_, v___x_2149_, v___x_2165_);
v___x_2167_ = l_Lean_Syntax_node4(v___x_2126_, v___x_2128_, v___x_2118_, v___x_2131_, v___x_2148_, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v_a_2109_);
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(lean_object* v_x_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(v_x_2184_, v_a_2185_, v_a_2186_);
lean_dec_ref(v_a_2185_);
return v_res_2187_;
}
}
lean_object* runtime_initialize_Lean_ImportingFlag(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_KVMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ImportingFlag(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_KVMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedOptionDecl_default = _init_l_Lean_instInhabitedOptionDecl_default();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl_default);
l_Lean_instInhabitedOptionDecl = _init_l_Lean_instInhabitedOptionDecl();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl);
l_Lean_instInhabitedOptionDecls = _init_l_Lean_instInhabitedOptionDecls();
lean_mark_persistent(l_Lean_instInhabitedOptionDecls);
res = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Data_Options_0__Lean_optionDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Data_Options_0__Lean_optionDeclsRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Options(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_OptionDecl_declName___autoParam = _init_l_Lean_OptionDecl_declName___autoParam();
lean_mark_persistent(l_Lean_OptionDecl_declName___autoParam);
l_Lean_Option_register___auto__1 = _init_l_Lean_Option_register___auto__1();
lean_mark_persistent(l_Lean_Option_register___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ImportingFlag(uint8_t builtin);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin);
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Options(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ImportingFlag(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Options(builtin);
}
#ifdef __cplusplus
}
#endif
