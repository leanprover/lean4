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
lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object*, lean_object*);
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
uint8_t l_List_any___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_isPrefixOf___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Options_insert___closed__1_value)} };
static const lean_object* l_Lean_Options_erase___closed__0 = (const lean_object*)&l_Lean_Options_erase___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object* v_k_303_, lean_object* v_t_304_){
_start:
{
if (lean_obj_tag(v_t_304_) == 0)
{
lean_object* v_k_305_; lean_object* v_v_306_; lean_object* v_l_307_; lean_object* v_r_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_962_; 
v_k_305_ = lean_ctor_get(v_t_304_, 1);
v_v_306_ = lean_ctor_get(v_t_304_, 2);
v_l_307_ = lean_ctor_get(v_t_304_, 3);
v_r_308_ = lean_ctor_get(v_t_304_, 4);
v_isSharedCheck_962_ = !lean_is_exclusive(v_t_304_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_t_304_, 0);
lean_dec(v_unused_963_);
v___x_310_ = v_t_304_;
v_isShared_311_ = v_isSharedCheck_962_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_r_308_);
lean_inc(v_l_307_);
lean_inc(v_v_306_);
lean_inc(v_k_305_);
lean_dec(v_t_304_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_962_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_303_, v_k_305_);
switch(v___x_312_)
{
case 0:
{
lean_object* v_impl_313_; lean_object* v___x_314_; 
v_impl_313_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_303_, v_l_307_);
v___x_314_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_313_) == 0)
{
if (lean_obj_tag(v_r_308_) == 0)
{
lean_object* v_size_315_; lean_object* v_size_316_; lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v_l_319_; lean_object* v_r_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_size_315_ = lean_ctor_get(v_impl_313_, 0);
lean_inc(v_size_315_);
v_size_316_ = lean_ctor_get(v_r_308_, 0);
v_k_317_ = lean_ctor_get(v_r_308_, 1);
v_v_318_ = lean_ctor_get(v_r_308_, 2);
v_l_319_ = lean_ctor_get(v_r_308_, 3);
lean_inc(v_l_319_);
v_r_320_ = lean_ctor_get(v_r_308_, 4);
v___x_321_ = lean_unsigned_to_nat(3u);
v___x_322_ = lean_nat_mul(v___x_321_, v_size_315_);
v___x_323_ = lean_nat_dec_lt(v___x_322_, v_size_316_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec(v_l_319_);
v___x_324_ = lean_nat_add(v___x_314_, v_size_315_);
lean_dec(v_size_315_);
v___x_325_ = lean_nat_add(v___x_324_, v_size_316_);
lean_dec(v___x_324_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_impl_313_);
lean_ctor_set(v___x_310_, 0, v___x_325_);
v___x_327_ = v___x_310_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_r_308_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_392_; 
lean_inc(v_r_320_);
lean_inc(v_v_318_);
lean_inc(v_k_317_);
lean_inc(v_size_316_);
v_isSharedCheck_392_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; lean_object* v_unused_394_; lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_393_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_397_);
v___x_330_ = v_r_308_;
v_isShared_331_ = v_isSharedCheck_392_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_r_308_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_392_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_size_332_; lean_object* v_k_333_; lean_object* v_v_334_; lean_object* v_l_335_; lean_object* v_r_336_; lean_object* v_size_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_size_332_ = lean_ctor_get(v_l_319_, 0);
v_k_333_ = lean_ctor_get(v_l_319_, 1);
v_v_334_ = lean_ctor_get(v_l_319_, 2);
v_l_335_ = lean_ctor_get(v_l_319_, 3);
v_r_336_ = lean_ctor_get(v_l_319_, 4);
v_size_337_ = lean_ctor_get(v_r_320_, 0);
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_nat_mul(v___x_338_, v_size_337_);
v___x_340_ = lean_nat_dec_lt(v_size_332_, v___x_339_);
lean_dec(v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_368_; 
lean_inc(v_r_336_);
lean_inc(v_l_335_);
lean_inc(v_v_334_);
lean_inc(v_k_333_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_l_319_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_369_ = lean_ctor_get(v_l_319_, 4);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_l_319_, 3);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_l_319_, 2);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_l_319_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_l_319_, 0);
lean_dec(v_unused_373_);
v___x_342_ = v_l_319_;
v_isShared_343_ = v_isSharedCheck_368_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_l_319_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_368_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_358_; 
v___x_344_ = lean_nat_add(v___x_314_, v_size_315_);
lean_dec(v_size_315_);
v___x_345_ = lean_nat_add(v___x_344_, v_size_316_);
lean_dec(v_size_316_);
if (lean_obj_tag(v_l_335_) == 0)
{
lean_object* v_size_366_; 
v_size_366_ = lean_ctor_get(v_l_335_, 0);
lean_inc(v_size_366_);
v___y_358_ = v_size_366_;
goto v___jp_357_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___y_358_ = v___x_367_;
goto v___jp_357_;
}
v___jp_346_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_nat_add(v___y_347_, v___y_349_);
lean_dec(v___y_349_);
lean_dec(v___y_347_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v_r_320_);
lean_ctor_set(v___x_342_, 3, v_r_336_);
lean_ctor_set(v___x_342_, 2, v_v_318_);
lean_ctor_set(v___x_342_, 1, v_k_317_);
lean_ctor_set(v___x_342_, 0, v___x_350_);
v___x_352_ = v___x_342_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_r_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_r_320_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v___x_352_);
lean_ctor_set(v___x_330_, 3, v___y_348_);
lean_ctor_set(v___x_330_, 2, v_v_334_);
lean_ctor_set(v___x_330_, 1, v_k_333_);
lean_ctor_set(v___x_330_, 0, v___x_345_);
v___x_354_ = v___x_330_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v___y_348_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_nat_add(v___x_344_, v___y_358_);
lean_dec(v___y_358_);
lean_dec(v___x_344_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_l_335_);
lean_ctor_set(v___x_310_, 3, v_impl_313_);
lean_ctor_set(v___x_310_, 0, v___x_359_);
v___x_361_ = v___x_310_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_l_335_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; 
v___x_362_ = lean_nat_add(v___x_314_, v_size_337_);
if (lean_obj_tag(v_r_336_) == 0)
{
lean_object* v_size_363_; 
v_size_363_ = lean_ctor_get(v_r_336_, 0);
lean_inc(v_size_363_);
v___y_347_ = v___x_362_;
v___y_348_ = v___x_361_;
v___y_349_ = v_size_363_;
goto v___jp_346_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___y_347_ = v___x_362_;
v___y_348_ = v___x_361_;
v___y_349_ = v___x_364_;
goto v___jp_346_;
}
}
}
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
lean_del_object(v___x_310_);
v___x_374_ = lean_nat_add(v___x_314_, v_size_315_);
lean_dec(v_size_315_);
v___x_375_ = lean_nat_add(v___x_374_, v_size_316_);
lean_dec(v_size_316_);
v___x_376_ = lean_nat_add(v___x_374_, v_size_332_);
lean_dec(v___x_374_);
lean_inc_ref(v_impl_313_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v_l_319_);
lean_ctor_set(v___x_330_, 3, v_impl_313_);
lean_ctor_set(v___x_330_, 2, v_v_306_);
lean_ctor_set(v___x_330_, 1, v_k_305_);
lean_ctor_set(v___x_330_, 0, v___x_376_);
v___x_378_ = v___x_330_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_l_319_);
v___x_378_ = v_reuseFailAlloc_391_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_isSharedCheck_385_ = !lean_is_exclusive(v_impl_313_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; lean_object* v_unused_388_; lean_object* v_unused_389_; lean_object* v_unused_390_; 
v_unused_386_ = lean_ctor_get(v_impl_313_, 4);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_impl_313_, 3);
lean_dec(v_unused_387_);
v_unused_388_ = lean_ctor_get(v_impl_313_, 2);
lean_dec(v_unused_388_);
v_unused_389_ = lean_ctor_get(v_impl_313_, 1);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_impl_313_, 0);
lean_dec(v_unused_390_);
v___x_380_ = v_impl_313_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_dec(v_impl_313_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 4, v_r_320_);
lean_ctor_set(v___x_380_, 3, v___x_378_);
lean_ctor_set(v___x_380_, 2, v_v_318_);
lean_ctor_set(v___x_380_, 1, v_k_317_);
lean_ctor_set(v___x_380_, 0, v___x_375_);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_r_320_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_size_398_ = lean_ctor_get(v_impl_313_, 0);
lean_inc(v_size_398_);
v___x_399_ = lean_nat_add(v___x_314_, v_size_398_);
lean_dec(v_size_398_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_impl_313_);
lean_ctor_set(v___x_310_, 0, v___x_399_);
v___x_401_ = v___x_310_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_r_308_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
if (lean_obj_tag(v_r_308_) == 0)
{
lean_object* v_l_403_; 
v_l_403_ = lean_ctor_get(v_r_308_, 3);
lean_inc(v_l_403_);
if (lean_obj_tag(v_l_403_) == 0)
{
lean_object* v_r_404_; 
v_r_404_ = lean_ctor_get(v_r_308_, 4);
lean_inc(v_r_404_);
if (lean_obj_tag(v_r_404_) == 0)
{
lean_object* v_size_405_; lean_object* v_k_406_; lean_object* v_v_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_420_; 
v_size_405_ = lean_ctor_get(v_r_308_, 0);
v_k_406_ = lean_ctor_get(v_r_308_, 1);
v_v_407_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_421_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_422_);
v___x_409_ = v_r_308_;
v_isShared_410_ = v_isSharedCheck_420_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_v_407_);
lean_inc(v_k_406_);
lean_inc(v_size_405_);
lean_dec(v_r_308_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_420_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_size_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_size_411_ = lean_ctor_get(v_l_403_, 0);
v___x_412_ = lean_nat_add(v___x_314_, v_size_405_);
lean_dec(v_size_405_);
v___x_413_ = lean_nat_add(v___x_314_, v_size_411_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 4, v_l_403_);
lean_ctor_set(v___x_409_, 3, v_impl_313_);
lean_ctor_set(v___x_409_, 2, v_v_306_);
lean_ctor_set(v___x_409_, 1, v_k_305_);
lean_ctor_set(v___x_409_, 0, v___x_413_);
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_impl_313_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_l_403_);
v___x_415_ = v_reuseFailAlloc_419_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_404_);
lean_ctor_set(v___x_310_, 3, v___x_415_);
lean_ctor_set(v___x_310_, 2, v_v_407_);
lean_ctor_set(v___x_310_, 1, v_k_406_);
lean_ctor_set(v___x_310_, 0, v___x_412_);
v___x_417_ = v___x_310_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_k_406_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_v_407_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_r_404_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_k_423_; lean_object* v_v_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_447_; 
v_k_423_ = lean_ctor_get(v_r_308_, 1);
v_v_424_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_448_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_450_);
v___x_426_ = v_r_308_;
v_isShared_427_ = v_isSharedCheck_447_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_v_424_);
lean_inc(v_k_423_);
lean_dec(v_r_308_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_447_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_k_428_; lean_object* v_v_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_443_; 
v_k_428_ = lean_ctor_get(v_l_403_, 1);
v_v_429_ = lean_ctor_get(v_l_403_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v_l_403_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_444_ = lean_ctor_get(v_l_403_, 4);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_l_403_, 3);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_l_403_, 0);
lean_dec(v_unused_446_);
v___x_431_ = v_l_403_;
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_v_429_);
lean_inc(v_k_428_);
lean_dec(v_l_403_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_443_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(3u);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 4, v_r_404_);
lean_ctor_set(v___x_431_, 3, v_r_404_);
lean_ctor_set(v___x_431_, 2, v_v_306_);
lean_ctor_set(v___x_431_, 1, v_k_305_);
lean_ctor_set(v___x_431_, 0, v___x_314_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_r_404_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_r_404_);
v___x_435_ = v_reuseFailAlloc_442_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 3, v_r_404_);
lean_ctor_set(v___x_426_, 0, v___x_314_);
v___x_437_ = v___x_426_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_k_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_v_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_r_404_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_r_404_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_437_);
lean_ctor_set(v___x_310_, 3, v___x_435_);
lean_ctor_set(v___x_310_, 2, v_v_429_);
lean_ctor_set(v___x_310_, 1, v_k_428_);
lean_ctor_set(v___x_310_, 0, v___x_433_);
v___x_439_ = v___x_310_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_k_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_v_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_451_; 
v_r_451_ = lean_ctor_get(v_r_308_, 4);
lean_inc(v_r_451_);
if (lean_obj_tag(v_r_451_) == 0)
{
lean_object* v_k_452_; lean_object* v_v_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_464_; 
v_k_452_ = lean_ctor_get(v_r_308_, 1);
v_v_453_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_464_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_465_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_467_);
v___x_455_ = v_r_308_;
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_v_453_);
lean_inc(v_k_452_);
lean_dec(v_r_308_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_464_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(3u);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v_l_403_);
lean_ctor_set(v___x_455_, 2, v_v_306_);
lean_ctor_set(v___x_455_, 1, v_k_305_);
lean_ctor_set(v___x_455_, 0, v___x_314_);
v___x_459_ = v___x_455_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_l_403_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_l_403_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_451_);
lean_ctor_set(v___x_310_, 3, v___x_459_);
lean_ctor_set(v___x_310_, 2, v_v_453_);
lean_ctor_set(v___x_310_, 1, v_k_452_);
lean_ctor_set(v___x_310_, 0, v___x_457_);
v___x_461_ = v___x_310_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_k_452_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_v_453_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_r_451_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_size_468_; lean_object* v_k_469_; lean_object* v_v_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_481_; 
v_size_468_ = lean_ctor_get(v_r_308_, 0);
v_k_469_ = lean_ctor_get(v_r_308_, 1);
v_v_470_ = lean_ctor_get(v_r_308_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_482_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_483_);
v___x_472_ = v_r_308_;
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_v_470_);
lean_inc(v_k_469_);
lean_inc(v_size_468_);
lean_dec(v_r_308_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_481_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 3, v_r_451_);
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_size_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_k_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_v_470_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_r_451_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_r_451_);
v___x_475_ = v_reuseFailAlloc_480_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(2u);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_475_);
lean_ctor_set(v___x_310_, 3, v_r_451_);
lean_ctor_set(v___x_310_, 0, v___x_476_);
v___x_478_ = v___x_310_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_r_451_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v___x_475_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
else
{
lean_object* v___x_485_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 3, v_r_308_);
lean_ctor_set(v___x_310_, 0, v___x_314_);
v___x_485_ = v___x_310_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_486_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_486_, 3, v_r_308_);
lean_ctor_set(v_reuseFailAlloc_486_, 4, v_r_308_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
case 1:
{
lean_del_object(v___x_310_);
lean_dec(v_v_306_);
lean_dec(v_k_305_);
if (lean_obj_tag(v_l_307_) == 0)
{
if (lean_obj_tag(v_r_308_) == 0)
{
lean_object* v_size_487_; lean_object* v_k_488_; lean_object* v_v_489_; lean_object* v_l_490_; lean_object* v_r_491_; lean_object* v_size_492_; lean_object* v_k_493_; lean_object* v_v_494_; lean_object* v_l_495_; lean_object* v_r_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_size_487_ = lean_ctor_get(v_l_307_, 0);
v_k_488_ = lean_ctor_get(v_l_307_, 1);
v_v_489_ = lean_ctor_get(v_l_307_, 2);
v_l_490_ = lean_ctor_get(v_l_307_, 3);
v_r_491_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_491_);
v_size_492_ = lean_ctor_get(v_r_308_, 0);
v_k_493_ = lean_ctor_get(v_r_308_, 1);
v_v_494_ = lean_ctor_get(v_r_308_, 2);
v_l_495_ = lean_ctor_get(v_r_308_, 3);
lean_inc(v_l_495_);
v_r_496_ = lean_ctor_get(v_r_308_, 4);
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_dec_lt(v_size_487_, v_size_492_);
if (v___x_498_ == 0)
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_634_; 
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
v_isSharedCheck_634_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; 
v_unused_635_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_639_);
v___x_500_ = v_l_307_;
v_isShared_501_ = v_isSharedCheck_634_;
goto v_resetjp_499_;
}
else
{
lean_dec(v_l_307_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_634_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v_tree_503_; 
v___x_502_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_488_, v_v_489_, v_l_490_, v_r_491_);
v_tree_503_ = lean_ctor_get(v___x_502_, 2);
lean_inc(v_tree_503_);
if (lean_obj_tag(v_tree_503_) == 0)
{
lean_object* v_k_504_; lean_object* v_v_505_; lean_object* v_size_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_k_504_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_504_);
v_v_505_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_505_);
lean_dec_ref(v___x_502_);
v_size_506_ = lean_ctor_get(v_tree_503_, 0);
v___x_507_ = lean_unsigned_to_nat(3u);
v___x_508_ = lean_nat_mul(v___x_507_, v_size_506_);
v___x_509_ = lean_nat_dec_lt(v___x_508_, v_size_492_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec(v_l_495_);
v___x_510_ = lean_nat_add(v___x_497_, v_size_506_);
v___x_511_ = lean_nat_add(v___x_510_, v_size_492_);
lean_dec(v___x_510_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_308_);
lean_ctor_set(v___x_500_, 3, v_tree_503_);
lean_ctor_set(v___x_500_, 2, v_v_505_);
lean_ctor_set(v___x_500_, 1, v_k_504_);
lean_ctor_set(v___x_500_, 0, v___x_511_);
v___x_513_ = v___x_500_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_505_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_r_308_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_569_; 
lean_inc(v_r_496_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
lean_inc(v_size_492_);
v_isSharedCheck_569_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_570_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_574_);
v___x_516_ = v_r_308_;
v_isShared_517_ = v_isSharedCheck_569_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_r_308_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_569_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_size_518_; lean_object* v_k_519_; lean_object* v_v_520_; lean_object* v_l_521_; lean_object* v_r_522_; lean_object* v_size_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_size_518_ = lean_ctor_get(v_l_495_, 0);
v_k_519_ = lean_ctor_get(v_l_495_, 1);
v_v_520_ = lean_ctor_get(v_l_495_, 2);
v_l_521_ = lean_ctor_get(v_l_495_, 3);
v_r_522_ = lean_ctor_get(v_l_495_, 4);
v_size_523_ = lean_ctor_get(v_r_496_, 0);
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = lean_nat_mul(v___x_524_, v_size_523_);
v___x_526_ = lean_nat_dec_lt(v_size_518_, v___x_525_);
lean_dec(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_554_; 
lean_inc(v_r_522_);
lean_inc(v_l_521_);
lean_inc(v_v_520_);
lean_inc(v_k_519_);
v_isSharedCheck_554_ = !lean_is_exclusive(v_l_495_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_555_ = lean_ctor_get(v_l_495_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_l_495_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_l_495_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_l_495_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_l_495_, 0);
lean_dec(v_unused_559_);
v___x_528_ = v_l_495_;
v_isShared_529_ = v_isSharedCheck_554_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_l_495_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_554_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_544_; 
v___x_530_ = lean_nat_add(v___x_497_, v_size_506_);
v___x_531_ = lean_nat_add(v___x_530_, v_size_492_);
lean_dec(v_size_492_);
if (lean_obj_tag(v_l_521_) == 0)
{
lean_object* v_size_552_; 
v_size_552_ = lean_ctor_get(v_l_521_, 0);
lean_inc(v_size_552_);
v___y_544_ = v_size_552_;
goto v___jp_543_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___y_544_ = v___x_553_;
goto v___jp_543_;
}
v___jp_532_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_nat_add(v___y_533_, v___y_535_);
lean_dec(v___y_535_);
lean_dec(v___y_533_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 4, v_r_496_);
lean_ctor_set(v___x_528_, 3, v_r_522_);
lean_ctor_set(v___x_528_, 2, v_v_494_);
lean_ctor_set(v___x_528_, 1, v_k_493_);
lean_ctor_set(v___x_528_, 0, v___x_536_);
v___x_538_ = v___x_528_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_542_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_542_, 3, v_r_522_);
lean_ctor_set(v_reuseFailAlloc_542_, 4, v_r_496_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v___x_538_);
lean_ctor_set(v___x_516_, 3, v___y_534_);
lean_ctor_set(v___x_516_, 2, v_v_520_);
lean_ctor_set(v___x_516_, 1, v_k_519_);
lean_ctor_set(v___x_516_, 0, v___x_531_);
v___x_540_ = v___x_516_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_k_519_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_v_520_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v___y_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_nat_add(v___x_530_, v___y_544_);
lean_dec(v___y_544_);
lean_dec(v___x_530_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_l_521_);
lean_ctor_set(v___x_500_, 3, v_tree_503_);
lean_ctor_set(v___x_500_, 2, v_v_505_);
lean_ctor_set(v___x_500_, 1, v_k_504_);
lean_ctor_set(v___x_500_, 0, v___x_545_);
v___x_547_ = v___x_500_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_k_504_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_v_505_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_l_521_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = lean_nat_add(v___x_497_, v_size_523_);
if (lean_obj_tag(v_r_522_) == 0)
{
lean_object* v_size_549_; 
v_size_549_ = lean_ctor_get(v_r_522_, 0);
lean_inc(v_size_549_);
v___y_533_ = v___x_548_;
v___y_534_ = v___x_547_;
v___y_535_ = v_size_549_;
goto v___jp_532_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___y_533_ = v___x_548_;
v___y_534_ = v___x_547_;
v___y_535_ = v___x_550_;
goto v___jp_532_;
}
}
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_nat_add(v___x_497_, v_size_506_);
v___x_561_ = lean_nat_add(v___x_560_, v_size_492_);
lean_dec(v_size_492_);
v___x_562_ = lean_nat_add(v___x_560_, v_size_518_);
lean_dec(v___x_560_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v_l_495_);
lean_ctor_set(v___x_516_, 3, v_tree_503_);
lean_ctor_set(v___x_516_, 2, v_v_505_);
lean_ctor_set(v___x_516_, 1, v_k_504_);
lean_ctor_set(v___x_516_, 0, v___x_562_);
v___x_564_ = v___x_516_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_k_504_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_v_505_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v_l_495_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_496_);
lean_ctor_set(v___x_500_, 3, v___x_564_);
lean_ctor_set(v___x_500_, 2, v_v_494_);
lean_ctor_set(v___x_500_, 1, v_k_493_);
lean_ctor_set(v___x_500_, 0, v___x_561_);
v___x_566_ = v___x_500_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_r_496_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_628_; 
lean_inc(v_r_496_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
lean_inc(v_size_492_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; 
v_unused_629_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_633_);
v___x_576_ = v_r_308_;
v_isShared_577_ = v_isSharedCheck_628_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_r_308_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_628_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
if (lean_obj_tag(v_l_495_) == 0)
{
if (lean_obj_tag(v_r_496_) == 0)
{
lean_object* v_k_578_; lean_object* v_v_579_; lean_object* v_size_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v_k_578_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_578_);
v_v_579_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_579_);
lean_dec_ref(v___x_502_);
v_size_580_ = lean_ctor_get(v_l_495_, 0);
v___x_581_ = lean_nat_add(v___x_497_, v_size_492_);
lean_dec(v_size_492_);
v___x_582_ = lean_nat_add(v___x_497_, v_size_580_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v_l_495_);
lean_ctor_set(v___x_576_, 3, v_tree_503_);
lean_ctor_set(v___x_576_, 2, v_v_579_);
lean_ctor_set(v___x_576_, 1, v_k_578_);
lean_ctor_set(v___x_576_, 0, v___x_582_);
v___x_584_ = v___x_576_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_578_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_579_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_tree_503_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_l_495_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_496_);
lean_ctor_set(v___x_500_, 3, v___x_584_);
lean_ctor_set(v___x_500_, 2, v_v_494_);
lean_ctor_set(v___x_500_, 1, v_k_493_);
lean_ctor_set(v___x_500_, 0, v___x_581_);
v___x_586_ = v___x_500_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_r_496_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_k_591_; lean_object* v_v_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_size_492_);
v_k_589_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_589_);
v_v_590_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_590_);
lean_dec_ref(v___x_502_);
v_k_591_ = lean_ctor_get(v_l_495_, 1);
v_v_592_ = lean_ctor_get(v_l_495_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_l_495_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; lean_object* v_unused_609_; 
v_unused_607_ = lean_ctor_get(v_l_495_, 4);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_l_495_, 3);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_l_495_, 0);
lean_dec(v_unused_609_);
v___x_594_ = v_l_495_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_v_592_);
lean_inc(v_k_591_);
lean_dec(v_l_495_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_unsigned_to_nat(3u);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v_r_496_);
lean_ctor_set(v___x_594_, 3, v_r_496_);
lean_ctor_set(v___x_594_, 2, v_v_590_);
lean_ctor_set(v___x_594_, 1, v_k_589_);
lean_ctor_set(v___x_594_, 0, v___x_497_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_k_589_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_v_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_r_496_);
v___x_598_ = v_reuseFailAlloc_605_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v_r_496_);
lean_ctor_set(v___x_576_, 0, v___x_497_);
v___x_600_ = v___x_576_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_r_496_);
v___x_600_ = v_reuseFailAlloc_604_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_602_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_600_);
lean_ctor_set(v___x_500_, 3, v___x_598_);
lean_ctor_set(v___x_500_, 2, v_v_592_);
lean_ctor_set(v___x_500_, 1, v_k_591_);
lean_ctor_set(v___x_500_, 0, v___x_596_);
v___x_602_ = v___x_500_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_k_591_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_v_592_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_496_) == 0)
{
lean_object* v_k_610_; lean_object* v_v_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
lean_dec(v_size_492_);
v_k_610_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_610_);
v_v_611_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_611_);
lean_dec_ref(v___x_502_);
v___x_612_ = lean_unsigned_to_nat(3u);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v_l_495_);
lean_ctor_set(v___x_576_, 2, v_v_611_);
lean_ctor_set(v___x_576_, 1, v_k_610_);
lean_ctor_set(v___x_576_, 0, v___x_497_);
v___x_614_ = v___x_576_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_k_610_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_v_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_l_495_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_l_495_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v_r_496_);
lean_ctor_set(v___x_500_, 3, v___x_614_);
lean_ctor_set(v___x_500_, 2, v_v_494_);
lean_ctor_set(v___x_500_, 1, v_k_493_);
lean_ctor_set(v___x_500_, 0, v___x_612_);
v___x_616_ = v___x_500_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_r_496_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v___x_622_; 
v_k_619_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_k_619_);
v_v_620_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_v_620_);
lean_dec_ref(v___x_502_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v_r_496_);
v___x_622_ = v___x_576_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_size_492_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_v_494_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_r_496_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(2u);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_622_);
lean_ctor_set(v___x_500_, 3, v_r_496_);
lean_ctor_set(v___x_500_, 2, v_v_620_);
lean_ctor_set(v___x_500_, 1, v_k_619_);
lean_ctor_set(v___x_500_, 0, v___x_623_);
v___x_625_ = v___x_500_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_k_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_v_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_r_496_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v___x_622_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
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
lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_792_; 
lean_inc(v_r_496_);
lean_inc(v_v_494_);
lean_inc(v_k_493_);
v_isSharedCheck_792_ = !lean_is_exclusive(v_r_308_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; lean_object* v_unused_797_; 
v_unused_793_ = lean_ctor_get(v_r_308_, 4);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_r_308_, 3);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_r_308_, 2);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_r_308_, 1);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_r_308_, 0);
lean_dec(v_unused_797_);
v___x_641_ = v_r_308_;
v_isShared_642_ = v_isSharedCheck_792_;
goto v_resetjp_640_;
}
else
{
lean_dec(v_r_308_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_792_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v_tree_644_; 
v___x_643_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_493_, v_v_494_, v_l_495_, v_r_496_);
v_tree_644_ = lean_ctor_get(v___x_643_, 2);
lean_inc(v_tree_644_);
if (lean_obj_tag(v_tree_644_) == 0)
{
lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v_size_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_k_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_645_);
v_v_646_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_646_);
lean_dec_ref(v___x_643_);
v_size_647_ = lean_ctor_get(v_tree_644_, 0);
v___x_648_ = lean_unsigned_to_nat(3u);
v___x_649_ = lean_nat_mul(v___x_648_, v_size_647_);
v___x_650_ = lean_nat_dec_lt(v___x_649_, v_size_487_);
lean_dec(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
lean_dec(v_r_491_);
v___x_651_ = lean_nat_add(v___x_497_, v_size_487_);
v___x_652_ = lean_nat_add(v___x_651_, v_size_647_);
lean_dec(v___x_651_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_tree_644_);
lean_ctor_set(v___x_641_, 3, v_l_307_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_652_);
v___x_654_ = v___x_641_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_tree_644_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_721_; 
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
lean_inc(v_size_487_);
v_isSharedCheck_721_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; 
v_unused_722_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_726_);
v___x_657_ = v_l_307_;
v_isShared_658_ = v_isSharedCheck_721_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_l_307_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_721_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_size_659_; lean_object* v_size_660_; lean_object* v_k_661_; lean_object* v_v_662_; lean_object* v_l_663_; lean_object* v_r_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_size_659_ = lean_ctor_get(v_l_490_, 0);
v_size_660_ = lean_ctor_get(v_r_491_, 0);
v_k_661_ = lean_ctor_get(v_r_491_, 1);
v_v_662_ = lean_ctor_get(v_r_491_, 2);
v_l_663_ = lean_ctor_get(v_r_491_, 3);
v_r_664_ = lean_ctor_get(v_r_491_, 4);
v___x_665_ = lean_unsigned_to_nat(2u);
v___x_666_ = lean_nat_mul(v___x_665_, v_size_659_);
v___x_667_ = lean_nat_dec_lt(v_size_660_, v___x_666_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_705_; 
lean_inc(v_r_664_);
lean_inc(v_l_663_);
lean_inc(v_v_662_);
lean_inc(v_k_661_);
lean_del_object(v___x_657_);
v_isSharedCheck_705_ = !lean_is_exclusive(v_r_491_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; lean_object* v_unused_707_; lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_706_ = lean_ctor_get(v_r_491_, 4);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_r_491_, 3);
lean_dec(v_unused_707_);
v_unused_708_ = lean_ctor_get(v_r_491_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_r_491_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_r_491_, 0);
lean_dec(v_unused_710_);
v___x_669_ = v_r_491_;
v_isShared_670_ = v_isSharedCheck_705_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_r_491_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_705_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___x_693_; lean_object* v___y_695_; 
v___x_671_ = lean_nat_add(v___x_497_, v_size_487_);
lean_dec(v_size_487_);
v___x_672_ = lean_nat_add(v___x_671_, v_size_647_);
lean_dec(v___x_671_);
v___x_693_ = lean_nat_add(v___x_497_, v_size_659_);
if (lean_obj_tag(v_l_663_) == 0)
{
lean_object* v_size_703_; 
v_size_703_ = lean_ctor_get(v_l_663_, 0);
lean_inc(v_size_703_);
v___y_695_ = v_size_703_;
goto v___jp_694_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___y_695_ = v___x_704_;
goto v___jp_694_;
}
v___jp_673_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_nat_add(v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec(v___y_675_);
lean_inc_ref(v_tree_644_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_tree_644_);
lean_ctor_set(v___x_669_, 3, v_r_664_);
lean_ctor_set(v___x_669_, 2, v_v_646_);
lean_ctor_set(v___x_669_, 1, v_k_645_);
lean_ctor_set(v___x_669_, 0, v___x_677_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_r_664_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_tree_644_);
v___x_679_ = v_reuseFailAlloc_692_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_isSharedCheck_686_ = !lean_is_exclusive(v_tree_644_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_687_ = lean_ctor_get(v_tree_644_, 4);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_tree_644_, 3);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_tree_644_, 2);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_tree_644_, 1);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_tree_644_, 0);
lean_dec(v_unused_691_);
v___x_681_ = v_tree_644_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_tree_644_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 4, v___x_679_);
lean_ctor_set(v___x_681_, 3, v___y_674_);
lean_ctor_set(v___x_681_, 2, v_v_662_);
lean_ctor_set(v___x_681_, 1, v_k_661_);
lean_ctor_set(v___x_681_, 0, v___x_672_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_k_661_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_v_662_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v___y_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v___x_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_nat_add(v___x_693_, v___y_695_);
lean_dec(v___y_695_);
lean_dec(v___x_693_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_l_663_);
lean_ctor_set(v___x_641_, 3, v_l_490_);
lean_ctor_set(v___x_641_, 2, v_v_489_);
lean_ctor_set(v___x_641_, 1, v_k_488_);
lean_ctor_set(v___x_641_, 0, v___x_696_);
v___x_698_ = v___x_641_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_l_663_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_nat_add(v___x_497_, v_size_647_);
if (lean_obj_tag(v_r_664_) == 0)
{
lean_object* v_size_700_; 
v_size_700_ = lean_ctor_get(v_r_664_, 0);
lean_inc(v_size_700_);
v___y_674_ = v___x_698_;
v___y_675_ = v___x_699_;
v___y_676_ = v_size_700_;
goto v___jp_673_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___y_674_ = v___x_698_;
v___y_675_ = v___x_699_;
v___y_676_ = v___x_701_;
goto v___jp_673_;
}
}
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_711_ = lean_nat_add(v___x_497_, v_size_487_);
lean_dec(v_size_487_);
v___x_712_ = lean_nat_add(v___x_711_, v_size_647_);
lean_dec(v___x_711_);
v___x_713_ = lean_nat_add(v___x_497_, v_size_647_);
v___x_714_ = lean_nat_add(v___x_713_, v_size_660_);
lean_dec(v___x_713_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_tree_644_);
lean_ctor_set(v___x_641_, 3, v_r_491_);
lean_ctor_set(v___x_641_, 2, v_v_646_);
lean_ctor_set(v___x_641_, 1, v_k_645_);
lean_ctor_set(v___x_641_, 0, v___x_714_);
v___x_716_ = v___x_641_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_tree_644_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___x_716_);
lean_ctor_set(v___x_657_, 0, v___x_712_);
v___x_718_ = v___x_657_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_490_) == 0)
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_750_; 
lean_inc_ref(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
lean_inc(v_size_487_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; 
v_unused_751_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_755_);
v___x_728_ = v_l_307_;
v_isShared_729_ = v_isSharedCheck_750_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_l_307_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_750_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
if (lean_obj_tag(v_r_491_) == 0)
{
lean_object* v_k_730_; lean_object* v_v_731_; lean_object* v_size_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_k_730_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_730_);
v_v_731_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_731_);
lean_dec_ref(v___x_643_);
v_size_732_ = lean_ctor_get(v_r_491_, 0);
v___x_733_ = lean_nat_add(v___x_497_, v_size_487_);
lean_dec(v_size_487_);
v___x_734_ = lean_nat_add(v___x_497_, v_size_732_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_tree_644_);
lean_ctor_set(v___x_641_, 3, v_r_491_);
lean_ctor_set(v___x_641_, 2, v_v_731_);
lean_ctor_set(v___x_641_, 1, v_k_730_);
lean_ctor_set(v___x_641_, 0, v___x_734_);
v___x_736_ = v___x_641_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_730_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_731_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_tree_644_);
v___x_736_ = v_reuseFailAlloc_740_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_736_);
lean_ctor_set(v___x_728_, 0, v___x_733_);
v___x_738_ = v___x_728_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v_k_741_; lean_object* v_v_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec(v_size_487_);
v_k_741_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_741_);
v_v_742_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_742_);
lean_dec_ref(v___x_643_);
v___x_743_ = lean_unsigned_to_nat(3u);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_491_);
lean_ctor_set(v___x_641_, 3, v_r_491_);
lean_ctor_set(v___x_641_, 2, v_v_742_);
lean_ctor_set(v___x_641_, 1, v_k_741_);
lean_ctor_set(v___x_641_, 0, v___x_497_);
v___x_745_ = v___x_641_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_741_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_742_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_r_491_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_r_491_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 4, v___x_745_);
lean_ctor_set(v___x_728_, 0, v___x_743_);
v___x_747_ = v___x_728_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_491_) == 0)
{
lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_780_; 
lean_inc(v_l_490_);
lean_inc(v_v_489_);
lean_inc(v_k_488_);
v_isSharedCheck_780_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_781_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_785_);
v___x_757_ = v_l_307_;
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
else
{
lean_dec(v_l_307_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_780_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_k_759_; lean_object* v_v_760_; lean_object* v_k_761_; lean_object* v_v_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_776_; 
v_k_759_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_759_);
v_v_760_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_760_);
lean_dec_ref(v___x_643_);
v_k_761_ = lean_ctor_get(v_r_491_, 1);
v_v_762_ = lean_ctor_get(v_r_491_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_r_491_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_777_ = lean_ctor_get(v_r_491_, 4);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_r_491_, 3);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_r_491_, 0);
lean_dec(v_unused_779_);
v___x_764_ = v_r_491_;
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_v_762_);
lean_inc(v_k_761_);
lean_dec(v_r_491_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(3u);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 4, v_l_490_);
lean_ctor_set(v___x_764_, 3, v_l_490_);
lean_ctor_set(v___x_764_, 2, v_v_489_);
lean_ctor_set(v___x_764_, 1, v_k_488_);
lean_ctor_set(v___x_764_, 0, v___x_497_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_488_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_489_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_l_490_);
v___x_768_ = v_reuseFailAlloc_775_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_l_490_);
lean_ctor_set(v___x_641_, 3, v_l_490_);
lean_ctor_set(v___x_641_, 2, v_v_760_);
lean_ctor_set(v___x_641_, 1, v_k_759_);
lean_ctor_set(v___x_641_, 0, v___x_497_);
v___x_770_ = v___x_641_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_l_490_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_l_490_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 4, v___x_770_);
lean_ctor_set(v___x_757_, 3, v___x_768_);
lean_ctor_set(v___x_757_, 2, v_v_762_);
lean_ctor_set(v___x_757_, 1, v_k_761_);
lean_ctor_set(v___x_757_, 0, v___x_766_);
v___x_772_ = v___x_757_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_761_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_object* v_k_786_; lean_object* v_v_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v_k_786_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_k_786_);
v_v_787_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_v_787_);
lean_dec_ref(v___x_643_);
v___x_788_ = lean_unsigned_to_nat(2u);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_491_);
lean_ctor_set(v___x_641_, 3, v_l_307_);
lean_ctor_set(v___x_641_, 2, v_v_787_);
lean_ctor_set(v___x_641_, 1, v_k_786_);
lean_ctor_set(v___x_641_, 0, v___x_788_);
v___x_790_ = v___x_641_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_r_491_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
}
else
{
return v_l_307_;
}
}
else
{
return v_r_308_;
}
}
default: 
{
lean_object* v_impl_798_; lean_object* v___x_799_; 
v_impl_798_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_303_, v_r_308_);
v___x_799_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_798_) == 0)
{
if (lean_obj_tag(v_l_307_) == 0)
{
lean_object* v_size_800_; lean_object* v_size_801_; lean_object* v_k_802_; lean_object* v_v_803_; lean_object* v_l_804_; lean_object* v_r_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_size_800_ = lean_ctor_get(v_impl_798_, 0);
lean_inc(v_size_800_);
v_size_801_ = lean_ctor_get(v_l_307_, 0);
v_k_802_ = lean_ctor_get(v_l_307_, 1);
v_v_803_ = lean_ctor_get(v_l_307_, 2);
v_l_804_ = lean_ctor_get(v_l_307_, 3);
v_r_805_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_805_);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_mul(v___x_806_, v_size_800_);
v___x_808_ = lean_nat_dec_lt(v___x_807_, v_size_801_);
lean_dec(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
lean_dec(v_r_805_);
v___x_809_ = lean_nat_add(v___x_799_, v_size_801_);
v___x_810_ = lean_nat_add(v___x_809_, v_size_800_);
lean_dec(v_size_800_);
lean_dec(v___x_809_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_impl_798_);
lean_ctor_set(v___x_310_, 0, v___x_810_);
v___x_812_ = v___x_310_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_impl_798_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_879_; 
lean_inc(v_l_804_);
lean_inc(v_v_803_);
lean_inc(v_k_802_);
lean_inc(v_size_801_);
v_isSharedCheck_879_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; lean_object* v_unused_884_; 
v_unused_880_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_880_);
v_unused_881_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_l_307_, 2);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_l_307_, 1);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_884_);
v___x_815_ = v_l_307_;
v_isShared_816_ = v_isSharedCheck_879_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_l_307_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_879_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_size_817_; lean_object* v_size_818_; lean_object* v_k_819_; lean_object* v_v_820_; lean_object* v_l_821_; lean_object* v_r_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_size_817_ = lean_ctor_get(v_l_804_, 0);
v_size_818_ = lean_ctor_get(v_r_805_, 0);
v_k_819_ = lean_ctor_get(v_r_805_, 1);
v_v_820_ = lean_ctor_get(v_r_805_, 2);
v_l_821_ = lean_ctor_get(v_r_805_, 3);
v_r_822_ = lean_ctor_get(v_r_805_, 4);
v___x_823_ = lean_unsigned_to_nat(2u);
v___x_824_ = lean_nat_mul(v___x_823_, v_size_817_);
v___x_825_ = lean_nat_dec_lt(v_size_818_, v___x_824_);
lean_dec(v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_854_; 
lean_inc(v_r_822_);
lean_inc(v_l_821_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_r_805_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_855_ = lean_ctor_get(v_r_805_, 4);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_r_805_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_r_805_, 2);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_r_805_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_r_805_, 0);
lean_dec(v_unused_859_);
v___x_827_ = v_r_805_;
v_isShared_828_ = v_isSharedCheck_854_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_r_805_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_854_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___x_842_; lean_object* v___y_844_; 
v___x_829_ = lean_nat_add(v___x_799_, v_size_801_);
lean_dec(v_size_801_);
v___x_830_ = lean_nat_add(v___x_829_, v_size_800_);
lean_dec(v___x_829_);
v___x_842_ = lean_nat_add(v___x_799_, v_size_817_);
if (lean_obj_tag(v_l_821_) == 0)
{
lean_object* v_size_852_; 
v_size_852_ = lean_ctor_get(v_l_821_, 0);
lean_inc(v_size_852_);
v___y_844_ = v_size_852_;
goto v___jp_843_;
}
else
{
lean_object* v___x_853_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___y_844_ = v___x_853_;
goto v___jp_843_;
}
v___jp_831_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = lean_nat_add(v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec(v___y_833_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 4, v_impl_798_);
lean_ctor_set(v___x_827_, 3, v_r_822_);
lean_ctor_set(v___x_827_, 2, v_v_306_);
lean_ctor_set(v___x_827_, 1, v_k_305_);
lean_ctor_set(v___x_827_, 0, v___x_835_);
v___x_837_ = v___x_827_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_r_822_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_impl_798_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v___x_837_);
lean_ctor_set(v___x_815_, 3, v___y_832_);
lean_ctor_set(v___x_815_, 2, v_v_820_);
lean_ctor_set(v___x_815_, 1, v_k_819_);
lean_ctor_set(v___x_815_, 0, v___x_830_);
v___x_839_ = v___x_815_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_k_819_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_v_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v___y_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_nat_add(v___x_842_, v___y_844_);
lean_dec(v___y_844_);
lean_dec(v___x_842_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_l_821_);
lean_ctor_set(v___x_310_, 3, v_l_804_);
lean_ctor_set(v___x_310_, 2, v_v_803_);
lean_ctor_set(v___x_310_, 1, v_k_802_);
lean_ctor_set(v___x_310_, 0, v___x_845_);
v___x_847_ = v___x_310_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_l_821_);
v___x_847_ = v_reuseFailAlloc_851_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_nat_add(v___x_799_, v_size_800_);
lean_dec(v_size_800_);
if (lean_obj_tag(v_r_822_) == 0)
{
lean_object* v_size_849_; 
v_size_849_ = lean_ctor_get(v_r_822_, 0);
lean_inc(v_size_849_);
v___y_832_ = v___x_847_;
v___y_833_ = v___x_848_;
v___y_834_ = v_size_849_;
goto v___jp_831_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___y_832_ = v___x_847_;
v___y_833_ = v___x_848_;
v___y_834_ = v___x_850_;
goto v___jp_831_;
}
}
}
}
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
lean_del_object(v___x_310_);
v___x_860_ = lean_nat_add(v___x_799_, v_size_801_);
lean_dec(v_size_801_);
v___x_861_ = lean_nat_add(v___x_860_, v_size_800_);
lean_dec(v___x_860_);
v___x_862_ = lean_nat_add(v___x_799_, v_size_800_);
lean_dec(v_size_800_);
v___x_863_ = lean_nat_add(v___x_862_, v_size_818_);
lean_dec(v___x_862_);
lean_inc_ref(v_impl_798_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 4, v_impl_798_);
lean_ctor_set(v___x_815_, 3, v_r_805_);
lean_ctor_set(v___x_815_, 2, v_v_306_);
lean_ctor_set(v___x_815_, 1, v_k_305_);
lean_ctor_set(v___x_815_, 0, v___x_863_);
v___x_865_ = v___x_815_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_r_805_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_impl_798_);
v___x_865_ = v_reuseFailAlloc_878_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_isSharedCheck_872_ = !lean_is_exclusive(v_impl_798_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_873_ = lean_ctor_get(v_impl_798_, 4);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_impl_798_, 3);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_impl_798_, 2);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_impl_798_, 1);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_impl_798_, 0);
lean_dec(v_unused_877_);
v___x_867_ = v_impl_798_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_impl_798_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_865_);
lean_ctor_set(v___x_867_, 3, v_l_804_);
lean_ctor_set(v___x_867_, 2, v_v_803_);
lean_ctor_set(v___x_867_, 1, v_k_802_);
lean_ctor_set(v___x_867_, 0, v___x_861_);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_k_802_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_v_803_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_l_804_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v___x_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v_size_885_ = lean_ctor_get(v_impl_798_, 0);
lean_inc(v_size_885_);
v___x_886_ = lean_nat_add(v___x_799_, v_size_885_);
lean_dec(v_size_885_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_impl_798_);
lean_ctor_set(v___x_310_, 0, v___x_886_);
v___x_888_ = v___x_310_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_impl_798_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
if (lean_obj_tag(v_l_307_) == 0)
{
lean_object* v_l_890_; 
v_l_890_ = lean_ctor_get(v_l_307_, 3);
if (lean_obj_tag(v_l_890_) == 0)
{
lean_object* v_r_891_; 
lean_inc_ref(v_l_890_);
v_r_891_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_891_);
if (lean_obj_tag(v_r_891_) == 0)
{
lean_object* v_size_892_; lean_object* v_k_893_; lean_object* v_v_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_907_; 
v_size_892_ = lean_ctor_get(v_l_307_, 0);
v_k_893_ = lean_ctor_get(v_l_307_, 1);
v_v_894_ = lean_ctor_get(v_l_307_, 2);
v_isSharedCheck_907_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_908_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_909_);
v___x_896_ = v_l_307_;
v_isShared_897_ = v_isSharedCheck_907_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_v_894_);
lean_inc(v_k_893_);
lean_inc(v_size_892_);
lean_dec(v_l_307_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_907_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_size_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v_size_898_ = lean_ctor_get(v_r_891_, 0);
v___x_899_ = lean_nat_add(v___x_799_, v_size_892_);
lean_dec(v_size_892_);
v___x_900_ = lean_nat_add(v___x_799_, v_size_898_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 4, v_impl_798_);
lean_ctor_set(v___x_896_, 3, v_r_891_);
lean_ctor_set(v___x_896_, 2, v_v_306_);
lean_ctor_set(v___x_896_, 1, v_k_305_);
lean_ctor_set(v___x_896_, 0, v___x_900_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_r_891_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_impl_798_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_902_);
lean_ctor_set(v___x_310_, 3, v_l_890_);
lean_ctor_set(v___x_310_, 2, v_v_894_);
lean_ctor_set(v___x_310_, 1, v_k_893_);
lean_ctor_set(v___x_310_, 0, v___x_899_);
v___x_904_ = v___x_310_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_894_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_922_; 
v_k_910_ = lean_ctor_get(v_l_307_, 1);
v_v_911_ = lean_ctor_get(v_l_307_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; 
v_unused_923_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_925_);
v___x_913_ = v_l_307_;
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_v_911_);
lean_inc(v_k_910_);
lean_dec(v_l_307_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_922_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_unsigned_to_nat(3u);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 3, v_r_891_);
lean_ctor_set(v___x_913_, 2, v_v_306_);
lean_ctor_set(v___x_913_, 1, v_k_305_);
lean_ctor_set(v___x_913_, 0, v___x_799_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_r_891_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_r_891_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_917_);
lean_ctor_set(v___x_310_, 3, v_l_890_);
lean_ctor_set(v___x_310_, 2, v_v_911_);
lean_ctor_set(v___x_310_, 1, v_k_910_);
lean_ctor_set(v___x_310_, 0, v___x_915_);
v___x_919_ = v___x_310_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
else
{
lean_object* v_r_926_; 
v_r_926_ = lean_ctor_get(v_l_307_, 4);
lean_inc(v_r_926_);
if (lean_obj_tag(v_r_926_) == 0)
{
lean_object* v_k_927_; lean_object* v_v_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_l_890_);
v_k_927_ = lean_ctor_get(v_l_307_, 1);
v_v_928_ = lean_ctor_get(v_l_307_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_l_307_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_952_ = lean_ctor_get(v_l_307_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_307_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_307_, 0);
lean_dec(v_unused_954_);
v___x_930_ = v_l_307_;
v_isShared_931_ = v_isSharedCheck_951_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_v_928_);
lean_inc(v_k_927_);
lean_dec(v_l_307_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_951_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_k_932_; lean_object* v_v_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_k_932_ = lean_ctor_get(v_r_926_, 1);
v_v_933_ = lean_ctor_get(v_r_926_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_r_926_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; 
v_unused_948_ = lean_ctor_get(v_r_926_, 4);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_r_926_, 3);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_r_926_, 0);
lean_dec(v_unused_950_);
v___x_935_ = v_r_926_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_v_933_);
lean_inc(v_k_932_);
lean_dec(v_r_926_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(3u);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v_l_890_);
lean_ctor_set(v___x_935_, 3, v_l_890_);
lean_ctor_set(v___x_935_, 2, v_v_928_);
lean_ctor_set(v___x_935_, 1, v_k_927_);
lean_ctor_set(v___x_935_, 0, v___x_799_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_k_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_v_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_l_890_);
v___x_939_ = v_reuseFailAlloc_946_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v_l_890_);
lean_ctor_set(v___x_930_, 2, v_v_306_);
lean_ctor_set(v___x_930_, 1, v_k_305_);
lean_ctor_set(v___x_930_, 0, v___x_799_);
v___x_941_ = v___x_930_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_l_890_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_l_890_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v___x_941_);
lean_ctor_set(v___x_310_, 3, v___x_939_);
lean_ctor_set(v___x_310_, 2, v_v_933_);
lean_ctor_set(v___x_310_, 1, v_k_932_);
lean_ctor_set(v___x_310_, 0, v___x_937_);
v___x_943_ = v___x_310_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_932_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_933_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
}
else
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_unsigned_to_nat(2u);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_926_);
lean_ctor_set(v___x_310_, 0, v___x_955_);
v___x_957_ = v___x_310_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_r_926_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_960_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_l_307_);
lean_ctor_set(v___x_310_, 0, v___x_799_);
v___x_960_ = v___x_310_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_k_305_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_v_306_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_l_307_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_l_307_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
}
else
{
return v_t_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object* v_k_964_, lean_object* v_t_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_964_, v_t_965_);
lean_dec(v_k_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object* v_o_969_, lean_object* v_k_970_){
_start:
{
lean_object* v_map_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_983_; 
v_map_971_ = lean_ctor_get(v_o_969_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_o_969_);
if (v_isSharedCheck_983_ == 0)
{
v___x_973_ = v_o_969_;
v_isShared_974_ = v_isSharedCheck_983_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_map_971_);
lean_dec(v_o_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_983_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_981_; 
lean_inc(v_map_971_);
v___x_975_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_970_, v_map_971_);
v___x_976_ = lean_box(0);
v___x_977_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v___x_976_, v_map_971_);
lean_dec(v_map_971_);
v___x_978_ = ((lean_object*)(l_Lean_Options_erase___closed__0));
v___x_979_ = l_List_any___redArg(v___x_977_, v___x_978_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_981_ = v___x_973_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_975_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*1, v___x_979_);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object* v_o_984_, lean_object* v_k_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Options_erase(v_o_984_, v_k_985_);
lean_dec(v_k_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object* v_00_u03b2_987_, lean_object* v_k_988_, lean_object* v_t_989_, lean_object* v_h_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_988_, v_t_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object* v_00_u03b2_992_, lean_object* v_k_993_, lean_object* v_t_994_, lean_object* v_h_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(v_00_u03b2_992_, v_k_993_, v_t_994_, v_h_995_);
lean_dec(v_k_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object* v_b_u2082_997_, lean_object* v_f_998_, lean_object* v_a_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_a_999_);
lean_dec_ref(v_f_998_);
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_b_u2082_997_);
return v___x_1001_;
}
else
{
lean_object* v_val_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
v_val_1002_ = lean_ctor_get(v_x_1000_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v_x_1000_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_val_1002_);
lean_dec(v_x_1000_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = lean_apply_3(v_f_998_, v_a_999_, v_val_1002_, v_b_u2082_997_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1006_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object* v_b_u2082_1011_, lean_object* v_f_1012_, lean_object* v_a_1013_, lean_object* v_k_1014_, lean_object* v_t_1015_){
_start:
{
if (lean_obj_tag(v_t_1015_) == 0)
{
lean_object* v_size_1016_; lean_object* v_k_1017_; lean_object* v_v_1018_; lean_object* v_l_1019_; lean_object* v_r_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1035_; 
v_size_1016_ = lean_ctor_get(v_t_1015_, 0);
v_k_1017_ = lean_ctor_get(v_t_1015_, 1);
v_v_1018_ = lean_ctor_get(v_t_1015_, 2);
v_l_1019_ = lean_ctor_get(v_t_1015_, 3);
v_r_1020_ = lean_ctor_get(v_t_1015_, 4);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_t_1015_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1022_ = v_t_1015_;
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_r_1020_);
lean_inc(v_l_1019_);
lean_inc(v_v_1018_);
lean_inc(v_k_1017_);
lean_inc(v_size_1016_);
lean_dec(v_t_1015_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v___x_1024_; 
v___x_1024_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1014_, v_k_1017_);
switch(v___x_1024_)
{
case 0:
{
lean_object* v_impl_1025_; lean_object* v___x_1026_; 
lean_del_object(v___x_1022_);
lean_dec(v_size_1016_);
v_impl_1025_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1011_, v_f_1012_, v_a_1013_, v_k_1014_, v_l_1019_);
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1017_, v_v_1018_, v_impl_1025_, v_r_1020_);
return v___x_1026_;
}
case 1:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_val_1029_; lean_object* v___x_1031_; 
lean_dec(v_k_1017_);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_v_1018_);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1011_, v_f_1012_, v_a_1013_, v___x_1027_);
v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1029_);
lean_dec(v___x_1028_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 2, v_val_1029_);
lean_ctor_set(v___x_1022_, 1, v_k_1014_);
v___x_1031_ = v___x_1022_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_size_1016_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_val_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_l_1019_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_r_1020_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
default: 
{
lean_object* v_impl_1033_; lean_object* v___x_1034_; 
lean_del_object(v___x_1022_);
lean_dec(v_size_1016_);
v_impl_1033_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1011_, v_f_1012_, v_a_1013_, v_k_1014_, v_r_1020_);
v___x_1034_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1017_, v_v_1018_, v_l_1019_, v_impl_1033_);
return v___x_1034_;
}
}
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_val_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1011_, v_f_1012_, v_a_1013_, v___x_1036_);
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec(v___x_1037_);
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_k_1014_);
lean_ctor_set(v___x_1040_, 2, v_val_1038_);
lean_ctor_set(v___x_1040_, 3, v_t_1015_);
lean_ctor_set(v___x_1040_, 4, v_t_1015_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object* v_f_1041_, lean_object* v_init_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_object* v_k_1044_; lean_object* v_v_1045_; lean_object* v_l_1046_; lean_object* v_r_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_k_1044_ = lean_ctor_get(v_x_1043_, 1);
lean_inc_n(v_k_1044_, 2);
v_v_1045_ = lean_ctor_get(v_x_1043_, 2);
lean_inc(v_v_1045_);
v_l_1046_ = lean_ctor_get(v_x_1043_, 3);
lean_inc(v_l_1046_);
v_r_1047_ = lean_ctor_get(v_x_1043_, 4);
lean_inc(v_r_1047_);
lean_dec_ref(v_x_1043_);
lean_inc_ref_n(v_f_1041_, 2);
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1041_, v_init_1042_, v_l_1046_);
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_1045_, v_f_1041_, v_k_1044_, v_k_1044_, v___x_1048_);
v_init_1042_ = v___x_1049_;
v_x_1043_ = v_r_1047_;
goto _start;
}
else
{
lean_dec_ref(v_f_1041_);
return v_init_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object* v_f_1051_, lean_object* v_o1_1052_, lean_object* v_o2_1053_){
_start:
{
lean_object* v_map_1054_; uint8_t v_hasTrace_1055_; lean_object* v_map_1056_; uint8_t v_hasTrace_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1068_; 
v_map_1054_ = lean_ctor_get(v_o1_1052_, 0);
lean_inc(v_map_1054_);
v_hasTrace_1055_ = lean_ctor_get_uint8(v_o1_1052_, sizeof(void*)*1);
lean_dec_ref(v_o1_1052_);
v_map_1056_ = lean_ctor_get(v_o2_1053_, 0);
v_hasTrace_1057_ = lean_ctor_get_uint8(v_o2_1053_, sizeof(void*)*1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_o2_1053_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1059_ = v_o2_1053_;
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_map_1056_);
lean_dec(v_o2_1053_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1068_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1051_, v_map_1054_, v_map_1056_);
if (v_hasTrace_1055_ == 0)
{
lean_object* v___x_1063_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
lean_ctor_set_uint8(v_reuseFailAlloc_1064_, sizeof(void*)*1, v_hasTrace_1057_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v___x_1066_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1061_);
v___x_1066_ = v___x_1059_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*1, v_hasTrace_1055_);
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object* v_b_u2082_1069_, lean_object* v_f_1070_, lean_object* v_a_1071_, lean_object* v_k_1072_, lean_object* v_t_1073_, lean_object* v_hl_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1069_, v_f_1070_, v_a_1071_, v_k_1072_, v_t_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object* v_f_1076_, lean_object* v_init_1077_, lean_object* v_t_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1076_, v_init_1077_, v_t_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
v___x_1113_ = l_Lean_mkAtom(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
v___x_1115_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1116_ = lean_array_push(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
v___x_1126_ = l_Lean_mkAtom(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
v___x_1128_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1129_ = lean_array_push(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
v___x_1131_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
v___x_1132_ = lean_box(2);
v___x_1133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1131_);
lean_ctor_set(v___x_1133_, 2, v___x_1130_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
v___x_1135_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
v___x_1136_ = lean_array_push(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1137_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
v___x_1138_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
v___x_1139_ = lean_box(2);
v___x_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1138_);
lean_ctor_set(v___x_1140_, 2, v___x_1137_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
v___x_1142_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1143_ = lean_array_push(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
v___x_1145_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1146_ = lean_box(2);
v___x_1147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
lean_ctor_set(v___x_1147_, 2, v___x_1144_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
v___x_1149_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1150_ = lean_array_push(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
v___x_1152_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
v___x_1153_ = lean_box(2);
v___x_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
lean_ctor_set(v___x_1154_, 2, v___x_1151_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
v___x_1156_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1157_ = lean_array_push(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
v___x_1159_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
v___x_1160_ = lean_box(2);
v___x_1161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1159_);
lean_ctor_set(v___x_1161_, 2, v___x_1158_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__3(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1169_ = lean_box(0);
v___x_1170_ = ((lean_object*)(l_Lean_instInhabitedOptionDeprecation_default___closed__0));
v___x_1171_ = l_Lean_instInhabitedDataValue_default;
v___x_1172_ = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__2));
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___x_1172_);
lean_ctor_set(v___x_1174_, 2, v___x_1171_);
lean_ctor_set(v___x_1174_, 3, v___x_1170_);
lean_ctor_set(v___x_1174_, 4, v___x_1169_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__3, &l_Lean_instInhabitedOptionDecl_default___closed__3_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__3);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_instInhabitedOptionDecl_default;
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* v_self_1182_){
_start:
{
lean_object* v_descr_1184_; lean_object* v_name_1187_; lean_object* v_descr_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v_name_1187_ = lean_ctor_get(v_self_1182_, 0);
lean_inc(v_name_1187_);
v_descr_1188_ = lean_ctor_get(v_self_1182_, 3);
lean_inc_ref(v_descr_1188_);
lean_dec_ref(v_self_1182_);
v___x_1189_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
v___x_1190_ = l_Lean_Name_isPrefixOf(v___x_1189_, v_name_1187_);
lean_dec(v_name_1187_);
if (v___x_1190_ == 0)
{
return v_descr_1188_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_string_utf8_byte_size(v_descr_1188_);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_nat_dec_eq(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v_descr_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
v_descr_1195_ = lean_string_append(v_descr_1188_, v___x_1194_);
v_descr_1184_ = v_descr_1195_;
goto v___jp_1183_;
}
else
{
v_descr_1184_ = v_descr_1188_;
goto v___jp_1183_;
}
}
v___jp_1183_:
{
lean_object* v___x_1185_; lean_object* v_descr_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
v_descr_1186_ = lean_string_append(v_descr_1184_, v___x_1185_);
return v_descr_1186_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_box(1);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_box(1);
v___x_1199_ = lean_st_mk_ref(v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_registerOption___closed__0));
v___x_1205_ = lean_mk_io_user_error(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* v_name_1208_, lean_object* v_decl_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1238_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1238_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1238_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_unbox(v_a_1212_);
lean_dec(v_a_1212_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
lean_dec_ref(v_decl_1209_);
lean_dec(v_name_1208_);
v___x_1217_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 1);
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1221_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1222_ = lean_st_ref_get(v___x_1221_);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1208_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1208_, v_decl_1209_, v___x_1222_);
v___x_1225_ = lean_st_ref_set(v___x_1221_, v___x_1224_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1225_);
v___x_1227_ = v___x_1214_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec(v___x_1222_);
lean_dec_ref(v_decl_1209_);
v___x_1229_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1230_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1208_, v___x_1223_);
v___x_1231_ = lean_string_append(v___x_1229_, v___x_1230_);
lean_dec_ref(v___x_1230_);
v___x_1232_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1233_ = lean_string_append(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_mk_io_user_error(v___x_1233_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set_tag(v___x_1214_, 1);
lean_ctor_set(v___x_1214_, 0, v___x_1234_);
v___x_1236_ = v___x_1214_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_decl_1209_);
lean_dec(v_name_1208_);
v_a_1239_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1211_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1211_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1247_, lean_object* v_decl_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = lean_register_option(v_name_1247_, v_decl_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1253_ = lean_st_ref_get(v___x_1252_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_getOptionDecls();
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* v_init_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v_k_1259_; lean_object* v_v_1260_; lean_object* v_l_1261_; lean_object* v_r_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_k_1259_ = lean_ctor_get(v_x_1258_, 1);
v_v_1260_ = lean_ctor_get(v_x_1258_, 2);
v_l_1261_ = lean_ctor_get(v_x_1258_, 3);
v_r_1262_ = lean_ctor_get(v_x_1258_, 4);
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1257_, v_l_1261_);
lean_inc(v_v_1260_);
lean_inc(v_k_1259_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_k_1259_);
lean_ctor_set(v___x_1264_, 1, v_v_1260_);
v___x_1265_ = lean_array_push(v___x_1263_, v___x_1264_);
v_init_1257_ = v___x_1265_;
v_x_1258_ = v_r_1262_;
goto _start;
}
else
{
return v_init_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* v_init_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1267_, v_x_1268_);
lean_dec(v_x_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(){
_start:
{
lean_object* v___x_1273_; lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1283_; 
v___x_1273_ = l_Lean_getOptionDecls();
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1283_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_1278_, v_a_1274_);
lean_dec(v_a_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1279_);
v___x_1281_ = v___x_1276_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = lean_get_option_decls_array();
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* v_init_1286_, lean_object* v_t_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1286_, v_t_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* v_init_1289_, lean_object* v_t_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(v_init_1289_, v_t_1290_);
lean_dec(v_t_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* v_name_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1316_; 
v___x_1296_ = l_Lean_getOptionDecls();
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1316_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1316_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1297_, v_name_1294_);
lean_dec(v_a_1297_);
if (lean_obj_tag(v___x_1301_) == 1)
{
lean_object* v_val_1302_; lean_object* v___x_1304_; 
lean_dec(v_name_1294_);
v_val_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1302_);
lean_dec_ref(v___x_1301_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_val_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_val_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec(v___x_1301_);
v___x_1306_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1307_ = 1;
v___x_1308_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1294_, v___x_1307_);
v___x_1309_ = lean_string_append(v___x_1306_, v___x_1308_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1311_ = lean_string_append(v___x_1309_, v___x_1310_);
v___x_1312_ = lean_mk_io_user_error(v___x_1311_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 1);
lean_ctor_set(v___x_1299_, 0, v___x_1312_);
v___x_1314_ = v___x_1299_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_getOptionDecl(v_name_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_getOptionDecl(v_name_1320_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_defValue_1327_; lean_object* v___x_1329_; 
v_defValue_1327_ = lean_ctor_get(v_a_1323_, 2);
lean_inc_ref(v_defValue_1327_);
lean_dec(v_a_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v_defValue_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_defValue_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1322_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_getOptionDefaultValue(v_name_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* v_name_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_getOptionDecl(v_name_1343_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v_descr_1350_; lean_object* v___x_1352_; 
v_descr_1350_ = lean_ctor_get(v_a_1346_, 3);
lean_inc_ref(v_descr_1350_);
lean_dec(v_a_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v_descr_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_descr_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1345_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1345_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_getOptionDescr(v_name_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_apply_2(v_inst_1366_, lean_box(0), v_inst_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1369_, lean_object* v_n_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_apply_2(v_inst_1371_, lean_box(0), v_inst_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1374_, lean_object* v_toPure_1375_, uint8_t v_defValue_1376_, lean_object* v_opts_1377_){
_start:
{
lean_object* v_map_1378_; lean_object* v___x_1379_; 
v_map_1378_ = lean_ctor_get(v_opts_1377_, 0);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1378_, v_k_1374_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(v_defValue_1376_);
v___x_1381_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1380_);
return v___x_1381_;
}
else
{
lean_object* v_val_1382_; 
v_val_1382_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1382_);
lean_dec_ref(v___x_1379_);
if (lean_obj_tag(v_val_1382_) == 1)
{
uint8_t v_v_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_v_1383_ = lean_ctor_get_uint8(v_val_1382_, 0);
lean_dec_ref(v_val_1382_);
v___x_1384_ = lean_box(v_v_1383_);
v___x_1385_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec(v_val_1382_);
v___x_1386_ = lean_box(v_defValue_1376_);
v___x_1387_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1386_);
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1388_, lean_object* v_toPure_1389_, lean_object* v_defValue_1390_, lean_object* v_opts_1391_){
_start:
{
uint8_t v_defValue_boxed_1392_; lean_object* v_res_1393_; 
v_defValue_boxed_1392_ = lean_unbox(v_defValue_1390_);
v_res_1393_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1388_, v_toPure_1389_, v_defValue_boxed_1392_, v_opts_1391_);
lean_dec_ref(v_opts_1391_);
lean_dec(v_k_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_k_1396_, uint8_t v_defValue_1397_){
_start:
{
lean_object* v_toApplicative_1398_; lean_object* v_toBind_1399_; lean_object* v_toPure_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; 
v_toApplicative_1398_ = lean_ctor_get(v_inst_1394_, 0);
lean_inc_ref(v_toApplicative_1398_);
v_toBind_1399_ = lean_ctor_get(v_inst_1394_, 1);
lean_inc(v_toBind_1399_);
lean_dec_ref(v_inst_1394_);
v_toPure_1400_ = lean_ctor_get(v_toApplicative_1398_, 1);
lean_inc(v_toPure_1400_);
lean_dec_ref(v_toApplicative_1398_);
v___x_1401_ = lean_box(v_defValue_1397_);
v___f_1402_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1402_, 0, v_k_1396_);
lean_closure_set(v___f_1402_, 1, v_toPure_1400_);
lean_closure_set(v___f_1402_, 2, v___x_1401_);
v___x_1403_ = lean_apply_4(v_toBind_1399_, lean_box(0), lean_box(0), v_inst_1395_, v___f_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_k_1406_, lean_object* v_defValue_1407_){
_start:
{
uint8_t v_defValue_boxed_1408_; lean_object* v_res_1409_; 
v_defValue_boxed_1408_ = lean_unbox(v_defValue_1407_);
v_res_1409_ = l_Lean_getBoolOption___redArg(v_inst_1404_, v_inst_1405_, v_k_1406_, v_defValue_boxed_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* v_m_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_k_1413_, uint8_t v_defValue_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_getBoolOption___redArg(v_inst_1411_, v_inst_1412_, v_k_1413_, v_defValue_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_k_1419_, lean_object* v_defValue_1420_){
_start:
{
uint8_t v_defValue_boxed_1421_; lean_object* v_res_1422_; 
v_defValue_boxed_1421_ = lean_unbox(v_defValue_1420_);
v_res_1422_ = l_Lean_getBoolOption(v_m_1416_, v_inst_1417_, v_inst_1418_, v_k_1419_, v_defValue_boxed_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1423_, lean_object* v_toPure_1424_, lean_object* v_defValue_1425_, lean_object* v_opts_1426_){
_start:
{
lean_object* v_map_1427_; lean_object* v___x_1428_; 
v_map_1427_ = lean_ctor_get(v_opts_1426_, 0);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1427_, v_k_1423_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_apply_2(v_toPure_1424_, lean_box(0), v_defValue_1425_);
return v___x_1429_;
}
else
{
lean_object* v_val_1430_; 
v_val_1430_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1430_);
lean_dec_ref(v___x_1428_);
if (lean_obj_tag(v_val_1430_) == 3)
{
lean_object* v_v_1431_; lean_object* v___x_1432_; 
lean_dec(v_defValue_1425_);
v_v_1431_ = lean_ctor_get(v_val_1430_, 0);
lean_inc(v_v_1431_);
lean_dec_ref(v_val_1430_);
v___x_1432_ = lean_apply_2(v_toPure_1424_, lean_box(0), v_v_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_val_1430_);
v___x_1433_ = lean_apply_2(v_toPure_1424_, lean_box(0), v_defValue_1425_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1434_, lean_object* v_toPure_1435_, lean_object* v_defValue_1436_, lean_object* v_opts_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_getNatOption___redArg___lam__0(v_k_1434_, v_toPure_1435_, v_defValue_1436_, v_opts_1437_);
lean_dec_ref(v_opts_1437_);
lean_dec(v_k_1434_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_k_1441_, lean_object* v_defValue_1442_){
_start:
{
lean_object* v_toApplicative_1443_; lean_object* v_toBind_1444_; lean_object* v_toPure_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; 
v_toApplicative_1443_ = lean_ctor_get(v_inst_1439_, 0);
lean_inc_ref(v_toApplicative_1443_);
v_toBind_1444_ = lean_ctor_get(v_inst_1439_, 1);
lean_inc(v_toBind_1444_);
lean_dec_ref(v_inst_1439_);
v_toPure_1445_ = lean_ctor_get(v_toApplicative_1443_, 1);
lean_inc(v_toPure_1445_);
lean_dec_ref(v_toApplicative_1443_);
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1446_, 0, v_k_1441_);
lean_closure_set(v___f_1446_, 1, v_toPure_1445_);
lean_closure_set(v___f_1446_, 2, v_defValue_1442_);
v___x_1447_ = lean_apply_4(v_toBind_1444_, lean_box(0), lean_box(0), v_inst_1440_, v___f_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_k_1451_, lean_object* v_defValue_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_getNatOption___redArg(v_inst_1449_, v_inst_1450_, v_k_1451_, v_defValue_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1454_, lean_object* v_f_1455_, lean_object* v_00_u03b2_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_apply_3(v_inst_1454_, lean_box(0), v_f_1455_, v___y_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_00_u03b1_1461_, lean_object* v_f_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1464_, 0, v_inst_1459_);
lean_closure_set(v___f_1464_, 1, v_f_1462_);
v___x_1465_ = lean_apply_3(v_inst_1460_, lean_box(0), v___f_1464_, v_x_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1466_, lean_object* v_inst_1467_){
_start:
{
lean_object* v___f_1468_; 
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1468_, 0, v_inst_1467_);
lean_closure_set(v___f_1468_, 1, v_inst_1466_);
return v___f_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1469_, lean_object* v_n_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_){
_start:
{
lean_object* v___f_1473_; 
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1473_, 0, v_inst_1472_);
lean_closure_set(v___f_1473_, 1, v_inst_1471_);
return v___f_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1477_, lean_object* v_o_1478_){
_start:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1479_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1480_ = 1;
v___x_1481_ = lean_box(v___x_1480_);
v___x_1482_ = l_Lean_Options_set___redArg(v___x_1477_, v_o_1478_, v___x_1479_, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___f_1484_; 
v___x_1483_ = l_Lean_KVMap_instValueBool;
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1484_, 0, v___x_1483_);
return v___f_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1485_, lean_object* v_x_1486_){
_start:
{
lean_object* v___f_1487_; lean_object* v___x_1488_; 
v___f_1487_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1488_ = lean_apply_3(v_inst_1485_, lean_box(0), v___f_1487_, v_x_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1489_, lean_object* v_00_u03b1_1490_, lean_object* v_inst_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_withInPattern___redArg(v_inst_1491_, v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1494_){
_start:
{
lean_object* v_map_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; 
v_map_1495_ = lean_ctor_get(v_o_1494_, 0);
v___x_1496_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1497_ = 0;
v___x_1498_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1495_, v___x_1496_);
if (lean_obj_tag(v___x_1498_) == 0)
{
return v___x_1497_;
}
else
{
lean_object* v_val_1499_; 
v_val_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1499_);
lean_dec_ref(v___x_1498_);
if (lean_obj_tag(v_val_1499_) == 1)
{
uint8_t v_v_1500_; 
v_v_1500_ = lean_ctor_get_uint8(v_val_1499_, 0);
lean_dec_ref(v_val_1499_);
return v_v_1500_;
}
else
{
lean_dec(v_val_1499_);
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1501_){
_start:
{
uint8_t v_res_1502_; lean_object* v_r_1503_; 
v_res_1502_ = l_Lean_Options_getInPattern(v_o_1501_);
lean_dec_ref(v_o_1501_);
v_r_1503_ = lean_box(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_inst_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_00_u03b1_1507_, lean_object* v_inst_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1512_, lean_object* v_inst_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1515_, lean_object* v_opts_1516_, lean_object* v_opt_1517_){
_start:
{
lean_object* v_name_1518_; lean_object* v_map_1519_; lean_object* v_ofDataValue_x3f_1520_; lean_object* v___x_1521_; 
v_name_1518_ = lean_ctor_get(v_opt_1517_, 0);
v_map_1519_ = lean_ctor_get(v_opts_1516_, 0);
v_ofDataValue_x3f_1520_ = lean_ctor_get(v_inst_1515_, 1);
lean_inc_ref(v_ofDataValue_x3f_1520_);
lean_dec_ref(v_inst_1515_);
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1519_, v_name_1518_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v_ofDataValue_x3f_1520_);
v___x_1522_ = lean_box(0);
return v___x_1522_;
}
else
{
lean_object* v_val_1523_; lean_object* v___x_1524_; 
v_val_1523_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___x_1521_);
v___x_1524_ = lean_apply_1(v_ofDataValue_x3f_1520_, v_val_1523_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1525_, lean_object* v_opts_1526_, lean_object* v_opt_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Option_get_x3f___redArg(v_inst_1525_, v_opts_1526_, v_opt_1527_);
lean_dec_ref(v_opt_1527_);
lean_dec_ref(v_opts_1526_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1529_, lean_object* v_inst_1530_, lean_object* v_opts_1531_, lean_object* v_opt_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Option_get_x3f___redArg(v_inst_1530_, v_opts_1531_, v_opt_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_inst_1535_, lean_object* v_opts_1536_, lean_object* v_opt_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Option_get_x3f(v_00_u03b1_1534_, v_inst_1535_, v_opts_1536_, v_opt_1537_);
lean_dec_ref(v_opt_1537_);
lean_dec_ref(v_opts_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1539_, lean_object* v_opts_1540_, lean_object* v_opt_1541_){
_start:
{
lean_object* v_name_1542_; lean_object* v_defValue_1543_; lean_object* v_map_1544_; lean_object* v_ofDataValue_x3f_1545_; lean_object* v___x_1546_; 
v_name_1542_ = lean_ctor_get(v_opt_1541_, 0);
v_defValue_1543_ = lean_ctor_get(v_opt_1541_, 1);
v_map_1544_ = lean_ctor_get(v_opts_1540_, 0);
v_ofDataValue_x3f_1545_ = lean_ctor_get(v_inst_1539_, 1);
lean_inc_ref(v_ofDataValue_x3f_1545_);
lean_dec_ref(v_inst_1539_);
v___x_1546_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1544_, v_name_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1545_);
lean_inc(v_defValue_1543_);
return v_defValue_1543_;
}
else
{
lean_object* v_val_1547_; lean_object* v___x_1548_; 
v_val_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_val_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_apply_1(v_ofDataValue_x3f_1545_, v_val_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_inc(v_defValue_1543_);
return v_defValue_1543_;
}
else
{
lean_object* v_val_1549_; 
v_val_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref(v___x_1548_);
return v_val_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1550_, lean_object* v_opts_1551_, lean_object* v_opt_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Option_get___redArg(v_inst_1550_, v_opts_1551_, v_opt_1552_);
lean_dec_ref(v_opt_1552_);
lean_dec_ref(v_opts_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1554_, lean_object* v_inst_1555_, lean_object* v_opts_1556_, lean_object* v_opt_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Option_get___redArg(v_inst_1555_, v_opts_1556_, v_opt_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_inst_1560_, lean_object* v_opts_1561_, lean_object* v_opt_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Option_get(v_00_u03b1_1559_, v_inst_1560_, v_opts_1561_, v_opt_1562_);
lean_dec_ref(v_opt_1562_);
lean_dec_ref(v_opts_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* v_opts_1564_, lean_object* v_name_1565_, uint8_t v_defValue_1566_){
_start:
{
lean_object* v_map_1567_; lean_object* v___x_1568_; 
v_map_1567_ = lean_ctor_get(v_opts_1564_, 0);
lean_inc(v_map_1567_);
lean_dec_ref(v_opts_1564_);
v___x_1568_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1567_, v_name_1565_);
lean_dec(v_name_1565_);
lean_dec(v_map_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
return v_defValue_1566_;
}
else
{
lean_object* v_val_1569_; 
v_val_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v___x_1568_);
if (lean_obj_tag(v_val_1569_) == 1)
{
uint8_t v_v_1570_; 
v_v_1570_ = lean_ctor_get_uint8(v_val_1569_, 0);
lean_dec_ref(v_val_1569_);
return v_v_1570_;
}
else
{
lean_dec(v_val_1569_);
return v_defValue_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* v_opts_1571_, lean_object* v_name_1572_, lean_object* v_defValue_1573_){
_start:
{
uint8_t v_defValue_boxed_1574_; uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_defValue_boxed_1574_ = lean_unbox(v_defValue_1573_);
v_res_1575_ = lean_options_get_bool(v_opts_1571_, v_name_1572_, v_defValue_boxed_1574_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* v_inst_1577_, lean_object* v_opt_1578_, lean_object* v_toPure_1579_, lean_object* v_____do__lift_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = l_Lean_Option_get___redArg(v_inst_1577_, v_____do__lift_1580_, v_opt_1578_);
v___x_1582_ = lean_apply_2(v_toPure_1579_, lean_box(0), v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* v_inst_1583_, lean_object* v_opt_1584_, lean_object* v_toPure_1585_, lean_object* v_____do__lift_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Option_getM___redArg___lam__0(v_inst_1583_, v_opt_1584_, v_toPure_1585_, v_____do__lift_1586_);
lean_dec_ref(v_____do__lift_1586_);
lean_dec_ref(v_opt_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_opt_1591_){
_start:
{
lean_object* v_toApplicative_1592_; lean_object* v_toBind_1593_; lean_object* v_toPure_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; 
v_toApplicative_1592_ = lean_ctor_get(v_inst_1588_, 0);
lean_inc_ref(v_toApplicative_1592_);
v_toBind_1593_ = lean_ctor_get(v_inst_1588_, 1);
lean_inc(v_toBind_1593_);
lean_dec_ref(v_inst_1588_);
v_toPure_1594_ = lean_ctor_get(v_toApplicative_1592_, 1);
lean_inc(v_toPure_1594_);
lean_dec_ref(v_toApplicative_1592_);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1595_, 0, v_inst_1590_);
lean_closure_set(v___f_1595_, 1, v_opt_1591_);
lean_closure_set(v___f_1595_, 2, v_toPure_1594_);
v___x_1596_ = lean_apply_4(v_toBind_1593_, lean_box(0), lean_box(0), v_inst_1589_, v___f_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* v_m_1597_, lean_object* v_00_u03b1_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_opt_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Option_getM___redArg(v_inst_1599_, v_inst_1600_, v_inst_1601_, v_opt_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* v_inst_1604_, lean_object* v_opts_1605_, lean_object* v_opt_1606_, lean_object* v_val_1607_){
_start:
{
lean_object* v_name_1608_; lean_object* v___x_1609_; 
v_name_1608_ = lean_ctor_get(v_opt_1606_, 0);
lean_inc(v_name_1608_);
lean_dec_ref(v_opt_1606_);
v___x_1609_ = l_Lean_Options_set___redArg(v_inst_1604_, v_opts_1605_, v_name_1608_, v_val_1607_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* v_00_u03b1_1610_, lean_object* v_inst_1611_, lean_object* v_opts_1612_, lean_object* v_opt_1613_, lean_object* v_val_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Option_set___redArg(v_inst_1611_, v_opts_1612_, v_opt_1613_, v_val_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1616_, lean_object* v_k_1617_, uint8_t v_v_1618_){
_start:
{
lean_object* v_map_1619_; uint8_t v_hasTrace_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1634_; 
v_map_1619_ = lean_ctor_get(v_o_1616_, 0);
v_hasTrace_1620_ = lean_ctor_get_uint8(v_o_1616_, sizeof(void*)*1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_o_1616_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1622_ = v_o_1616_;
v_isShared_1623_ = v_isSharedCheck_1634_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_map_1619_);
lean_dec(v_o_1616_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1634_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1624_, 0, v_v_1618_);
lean_inc(v_k_1617_);
v___x_1625_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1617_, v___x_1624_, v_map_1619_);
if (v_hasTrace_1620_ == 0)
{
lean_object* v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_1627_ = l_Lean_Name_isPrefixOf(v___x_1626_, v_k_1617_);
lean_dec(v_k_1617_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1625_);
v___x_1629_ = v___x_1622_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1625_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*1, v___x_1627_);
return v___x_1629_;
}
}
else
{
lean_object* v___x_1632_; 
lean_dec(v_k_1617_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1625_);
v___x_1632_ = v___x_1622_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1633_, sizeof(void*)*1, v_hasTrace_1620_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1635_, lean_object* v_k_1636_, lean_object* v_v_1637_){
_start:
{
uint8_t v_v_boxed_1638_; lean_object* v_res_1639_; 
v_v_boxed_1638_ = lean_unbox(v_v_1637_);
v_res_1639_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1635_, v_k_1636_, v_v_boxed_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* v_opts_1640_, lean_object* v_name_1641_, uint8_t v_val_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1640_, v_name_1641_, v_val_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1644_, lean_object* v_name_1645_, lean_object* v_val_1646_){
_start:
{
uint8_t v_val_boxed_1647_; lean_object* v_res_1648_; 
v_val_boxed_1647_ = lean_unbox(v_val_1646_);
v_res_1648_ = lean_options_update_bool(v_opts_1644_, v_name_1645_, v_val_boxed_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1649_, lean_object* v_opts_1650_, lean_object* v_opt_1651_, lean_object* v_val_1652_){
_start:
{
lean_object* v_name_1653_; lean_object* v_map_1654_; uint8_t v___x_1655_; 
v_name_1653_ = lean_ctor_get(v_opt_1651_, 0);
v_map_1654_ = lean_ctor_get(v_opts_1650_, 0);
v___x_1655_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1653_, v_map_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Option_set___redArg(v_inst_1649_, v_opts_1650_, v_opt_1651_, v_val_1652_);
return v___x_1656_;
}
else
{
lean_dec(v_val_1652_);
lean_dec_ref(v_opt_1651_);
lean_dec_ref(v_inst_1649_);
return v_opts_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1657_, lean_object* v_inst_1658_, lean_object* v_opts_1659_, lean_object* v_opt_1660_, lean_object* v_val_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1658_, v_opts_1659_, v_opt_1660_, v_val_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1664_, lean_object* v_name_1665_, lean_object* v_decl_1666_, lean_object* v_ref_1667_){
_start:
{
lean_object* v_toDataValue_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1698_; 
v_toDataValue_1669_ = lean_ctor_get(v_inst_1664_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_inst_1664_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v_inst_1664_, 1);
lean_dec(v_unused_1699_);
v___x_1671_ = v_inst_1664_;
v_isShared_1672_ = v_isSharedCheck_1698_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_toDataValue_1669_);
lean_dec(v_inst_1664_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1698_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_defValue_1673_; lean_object* v_descr_1674_; lean_object* v_deprecation_x3f_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_defValue_1673_ = lean_ctor_get(v_decl_1666_, 0);
lean_inc_n(v_defValue_1673_, 2);
v_descr_1674_ = lean_ctor_get(v_decl_1666_, 1);
lean_inc_ref(v_descr_1674_);
v_deprecation_x3f_1675_ = lean_ctor_get(v_decl_1666_, 2);
lean_inc(v_deprecation_x3f_1675_);
lean_dec_ref(v_decl_1666_);
v___x_1676_ = lean_apply_1(v_toDataValue_1669_, v_defValue_1673_);
lean_inc_n(v_name_1665_, 2);
v___x_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1677_, 0, v_name_1665_);
lean_ctor_set(v___x_1677_, 1, v_ref_1667_);
lean_ctor_set(v___x_1677_, 2, v___x_1676_);
lean_ctor_set(v___x_1677_, 3, v_descr_1674_);
lean_ctor_set(v___x_1677_, 4, v_deprecation_x3f_1675_);
v___x_1678_ = lean_register_option(v_name_1665_, v___x_1677_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1688_; 
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1678_, 0);
lean_dec(v_unused_1689_);
v___x_1680_ = v___x_1678_;
v_isShared_1681_ = v_isSharedCheck_1688_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v___x_1678_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1688_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v_defValue_1673_);
lean_ctor_set(v___x_1671_, 0, v_name_1665_);
v___x_1683_ = v___x_1671_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_name_1665_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_defValue_1673_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1683_);
v___x_1685_ = v___x_1680_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_defValue_1673_);
lean_del_object(v___x_1671_);
lean_dec(v_name_1665_);
v_a_1690_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1678_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1678_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1700_, lean_object* v_name_1701_, lean_object* v_decl_1702_, lean_object* v_ref_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Option_register___redArg(v_inst_1700_, v_name_1701_, v_decl_1702_, v_ref_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1706_, lean_object* v_inst_1707_, lean_object* v_name_1708_, lean_object* v_decl_1709_, lean_object* v_ref_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Option_register___redArg(v_inst_1707_, v_name_1708_, v_decl_1709_, v_ref_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_inst_1714_, lean_object* v_name_1715_, lean_object* v_decl_1716_, lean_object* v_ref_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Option_register(v_00_u03b1_1713_, v_inst_1714_, v_name_1715_, v_decl_1716_, v_ref_1717_);
return v_res_1719_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
v___x_1808_ = l_String_toRawSubstring_x27(v___x_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
v___x_1829_ = l_String_toRawSubstring_x27(v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29(void){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Array_mkArray0(lean_box(0));
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* v_x_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_1861_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(v_x_1857_);
v___x_1862_ = l_Lean_Syntax_isOfKind(v_x_1857_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec(v_x_1857_);
v___x_1863_ = lean_box(1);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_a_1859_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_name_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1999_; lean_object* v___x_2010_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1865_);
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1867_);
v___x_1869_ = lean_unsigned_to_nat(3u);
v_name_1870_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1869_);
v___x_1871_ = lean_unsigned_to_nat(5u);
v___x_1872_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1871_);
v___x_1873_ = lean_unsigned_to_nat(7u);
v___x_1874_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1873_);
lean_dec(v_x_1857_);
v___x_2010_ = l_Lean_Syntax_getOptional_x3f(v___x_1868_);
lean_dec(v___x_1868_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(0);
v___y_1999_ = v___x_2011_;
goto v___jp_1998_;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_val_2012_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2010_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v___x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v___y_1999_ = v___x_2017_;
goto v___jp_1998_;
}
}
}
v___jp_1875_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_inc_n(v___y_1877_, 2);
lean_inc_n(v___y_1886_, 6);
v___x_1889_ = l_Lean_Syntax_node2(v___y_1886_, v___y_1877_, v___y_1888_, v___x_1874_);
v___x_1890_ = l_Lean_Syntax_node2(v___y_1886_, v___y_1882_, v___y_1881_, v___x_1889_);
v___x_1891_ = l_Lean_Syntax_node1(v___y_1886_, v___y_1883_, v___x_1890_);
v___x_1892_ = l_Lean_Syntax_node2(v___y_1886_, v___y_1878_, v___x_1891_, v___y_1879_);
v___x_1893_ = l_Lean_Syntax_node1(v___y_1886_, v___y_1877_, v___x_1892_);
v___x_1894_ = l_Lean_Syntax_node1(v___y_1886_, v___y_1887_, v___x_1893_);
lean_inc(v___y_1885_);
v___x_1895_ = l_Lean_Syntax_node4(v___y_1886_, v___y_1885_, v___y_1880_, v___y_1876_, v___y_1884_, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v_a_1859_);
return v___x_1896_;
}
v___jp_1897_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_inc_ref(v___y_1900_);
v___x_1910_ = l_Array_append___redArg(v___y_1900_, v___y_1909_);
lean_dec_ref(v___y_1909_);
lean_inc_n(v___y_1899_, 3);
lean_inc_n(v___y_1908_, 12);
v___x_1911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1911_, 0, v___y_1908_);
lean_ctor_set(v___x_1911_, 1, v___y_1899_);
lean_ctor_set(v___x_1911_, 2, v___x_1910_);
lean_inc_n(v___y_1901_, 5);
lean_inc(v___y_1907_);
v___x_1912_ = l_Lean_Syntax_node7(v___y_1908_, v___y_1907_, v___y_1903_, v___y_1901_, v___x_1911_, v___y_1901_, v___y_1901_, v___y_1901_, v___y_1901_);
v___x_1913_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_1906_);
lean_inc_ref_n(v___y_1898_, 6);
v___x_1914_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___y_1906_, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
v___x_1916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___y_1908_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_Syntax_node1(v___y_1908_, v___x_1914_, v___x_1916_);
v___x_1918_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_1919_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_1920_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___x_1918_, v___x_1919_);
v___x_1921_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_1922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1908_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_1924_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___x_1918_, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_1926_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v___y_1902_, 2);
lean_inc_n(v___y_1904_, 2);
v___x_1927_ = l_Lean_addMacroScope(v___y_1904_, v___x_1926_, v___y_1902_);
v___x_1928_ = lean_box(0);
v___x_1929_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_1930_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1930_, 0, v___y_1908_);
lean_ctor_set(v___x_1930_, 1, v___x_1925_);
lean_ctor_set(v___x_1930_, 2, v___x_1927_);
lean_ctor_set(v___x_1930_, 3, v___x_1929_);
v___x_1931_ = l_Lean_Syntax_node1(v___y_1908_, v___y_1899_, v___x_1872_);
lean_inc(v___x_1924_);
v___x_1932_ = l_Lean_Syntax_node2(v___y_1908_, v___x_1924_, v___x_1930_, v___x_1931_);
v___x_1933_ = l_Lean_Syntax_node2(v___y_1908_, v___x_1920_, v___x_1922_, v___x_1932_);
v___x_1934_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_1935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___y_1908_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
lean_inc(v_name_1870_);
v___x_1936_ = l_Lean_Syntax_node3(v___y_1908_, v___y_1899_, v_name_1870_, v___x_1933_, v___x_1935_);
v___x_1937_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_1938_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___x_1918_, v___x_1937_);
v___x_1939_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_1940_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___x_1918_, v___x_1939_);
v___x_1941_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_1942_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___x_1918_, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_1944_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_1945_ = l_Lean_addMacroScope(v___y_1904_, v___x_1944_, v___y_1902_);
v___x_1946_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_1947_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1947_, 0, v___y_1908_);
lean_ctor_set(v___x_1947_, 1, v___x_1943_);
lean_ctor_set(v___x_1947_, 2, v___x_1945_);
lean_ctor_set(v___x_1947_, 3, v___x_1946_);
v___x_1948_ = l_Lean_TSyntax_getId(v_name_1870_);
lean_dec(v_name_1870_);
lean_inc(v___x_1948_);
v___x_1949_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1928_, v___x_1948_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_quoteNameMk(v___x_1948_);
v___y_1876_ = v___x_1917_;
v___y_1877_ = v___y_1899_;
v___y_1878_ = v___x_1940_;
v___y_1879_ = v___y_1901_;
v___y_1880_ = v___x_1912_;
v___y_1881_ = v___x_1947_;
v___y_1882_ = v___x_1924_;
v___y_1883_ = v___x_1942_;
v___y_1884_ = v___x_1936_;
v___y_1885_ = v___y_1905_;
v___y_1886_ = v___y_1908_;
v___y_1887_ = v___x_1938_;
v___y_1888_ = v___x_1950_;
goto v___jp_1875_;
}
else
{
lean_object* v_val_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec(v___x_1948_);
v_val_1951_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_val_1951_);
lean_dec_ref(v___x_1949_);
v___x_1952_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
lean_inc_ref(v___y_1898_);
v___x_1953_ = l_Lean_Name_mkStr4(v___x_1860_, v___y_1898_, v___x_1918_, v___x_1952_);
v___x_1954_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1955_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_1956_ = lean_string_intercalate(v___x_1955_, v_val_1951_);
v___x_1957_ = lean_string_append(v___x_1954_, v___x_1956_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = lean_box(2);
v___x_1959_ = l_Lean_Syntax_mkNameLit(v___x_1957_, v___x_1958_);
v___x_1960_ = lean_mk_empty_array_with_capacity(v___x_1867_);
v___x_1961_ = lean_array_push(v___x_1960_, v___x_1959_);
v___x_1962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1958_);
lean_ctor_set(v___x_1962_, 1, v___x_1953_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
v___y_1876_ = v___x_1917_;
v___y_1877_ = v___y_1899_;
v___y_1878_ = v___x_1940_;
v___y_1879_ = v___y_1901_;
v___y_1880_ = v___x_1912_;
v___y_1881_ = v___x_1947_;
v___y_1882_ = v___x_1924_;
v___y_1883_ = v___x_1942_;
v___y_1884_ = v___x_1936_;
v___y_1885_ = v___y_1905_;
v___y_1886_ = v___y_1908_;
v___y_1887_ = v___x_1938_;
v___y_1888_ = v___x_1962_;
goto v___jp_1875_;
}
}
v___jp_1963_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_inc_ref_n(v___y_1966_, 2);
v___x_1975_ = l_Array_append___redArg(v___y_1966_, v___y_1974_);
lean_dec_ref(v___y_1974_);
lean_inc_n(v___y_1965_, 2);
lean_inc_n(v___y_1973_, 2);
v___x_1976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1976_, 0, v___y_1973_);
lean_ctor_set(v___x_1976_, 1, v___y_1965_);
lean_ctor_set(v___x_1976_, 2, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1977_, 0, v___y_1973_);
lean_ctor_set(v___x_1977_, 1, v___y_1965_);
lean_ctor_set(v___x_1977_, 2, v___y_1966_);
if (lean_obj_tag(v___y_1967_) == 1)
{
lean_object* v_val_1978_; lean_object* v___x_1979_; 
v_val_1978_ = lean_ctor_get(v___y_1967_, 0);
lean_inc(v_val_1978_);
lean_dec_ref(v___y_1967_);
v___x_1979_ = l_Array_mkArray1___redArg(v_val_1978_);
v___y_1898_ = v___y_1964_;
v___y_1899_ = v___y_1965_;
v___y_1900_ = v___y_1966_;
v___y_1901_ = v___x_1977_;
v___y_1902_ = v___y_1968_;
v___y_1903_ = v___x_1976_;
v___y_1904_ = v___y_1969_;
v___y_1905_ = v___y_1971_;
v___y_1906_ = v___y_1970_;
v___y_1907_ = v___y_1972_;
v___y_1908_ = v___y_1973_;
v___y_1909_ = v___x_1979_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1980_; 
lean_dec(v___y_1967_);
v___x_1980_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1898_ = v___y_1964_;
v___y_1899_ = v___y_1965_;
v___y_1900_ = v___y_1966_;
v___y_1901_ = v___x_1977_;
v___y_1902_ = v___y_1968_;
v___y_1903_ = v___x_1976_;
v___y_1904_ = v___y_1969_;
v___y_1905_ = v___y_1971_;
v___y_1906_ = v___y_1970_;
v___y_1907_ = v___y_1972_;
v___y_1908_ = v___y_1973_;
v___y_1909_ = v___x_1980_;
goto v___jp_1897_;
}
}
v___jp_1981_:
{
lean_object* v_quotContext_1984_; lean_object* v_currMacroScope_1985_; lean_object* v_ref_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_quotContext_1984_ = lean_ctor_get(v_a_1858_, 1);
v_currMacroScope_1985_ = lean_ctor_get(v_a_1858_, 2);
v_ref_1986_ = lean_ctor_get(v_a_1858_, 5);
v___x_1987_ = 0;
v___x_1988_ = l_Lean_SourceInfo_fromRef(v_ref_1986_, v___x_1987_);
v___x_1989_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_1990_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_1991_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_1992_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28));
v___x_1993_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1994_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
if (lean_obj_tag(v___y_1983_) == 1)
{
lean_object* v_val_1995_; lean_object* v___x_1996_; 
v_val_1995_ = lean_ctor_get(v___y_1983_, 0);
lean_inc(v_val_1995_);
lean_dec_ref(v___y_1983_);
v___x_1996_ = l_Array_mkArray1___redArg(v_val_1995_);
v___y_1964_ = v___x_1989_;
v___y_1965_ = v___x_1993_;
v___y_1966_ = v___x_1994_;
v___y_1967_ = v___y_1982_;
v___y_1968_ = v_currMacroScope_1985_;
v___y_1969_ = v_quotContext_1984_;
v___y_1970_ = v___x_1990_;
v___y_1971_ = v___x_1991_;
v___y_1972_ = v___x_1992_;
v___y_1973_ = v___x_1988_;
v___y_1974_ = v___x_1996_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_1997_; 
lean_dec(v___y_1983_);
v___x_1997_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1964_ = v___x_1989_;
v___y_1965_ = v___x_1993_;
v___y_1966_ = v___x_1994_;
v___y_1967_ = v___y_1982_;
v___y_1968_ = v_currMacroScope_1985_;
v___y_1969_ = v_quotContext_1984_;
v___y_1970_ = v___x_1990_;
v___y_1971_ = v___x_1991_;
v___y_1972_ = v___x_1992_;
v___y_1973_ = v___x_1988_;
v___y_1974_ = v___x_1997_;
goto v___jp_1963_;
}
}
v___jp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Syntax_getOptional_x3f(v___x_1866_);
lean_dec(v___x_1866_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_box(0);
v___y_1982_ = v___y_1999_;
v___y_1983_ = v___x_2001_;
goto v___jp_1981_;
}
else
{
lean_object* v_val_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_val_2002_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_val_2002_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_val_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v___y_1982_ = v___y_1999_;
v___y_1983_ = v___x_2007_;
goto v___jp_1981_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(lean_object* v_x_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_2020_, v_a_2021_, v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2100_);
v___x_2104_ = l_Lean_Syntax_isOfKind(v_x_2100_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_dec(v_x_2100_);
v___x_2105_ = lean_box(1);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_a_2102_);
return v___x_2106_;
}
else
{
lean_object* v_quotContext_2107_; lean_object* v_currMacroScope_2108_; lean_object* v_ref_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_name_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___y_2151_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_quotContext_2107_ = lean_ctor_get(v_a_2101_, 1);
v_currMacroScope_2108_ = lean_ctor_get(v_a_2101_, 2);
v_ref_2109_ = lean_ctor_get(v_a_2101_, 5);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = l_Lean_Syntax_getArg(v_x_2100_, v___x_2110_);
v___x_2112_ = lean_unsigned_to_nat(2u);
v_name_2113_ = l_Lean_Syntax_getArg(v_x_2100_, v___x_2112_);
v___x_2114_ = lean_unsigned_to_nat(4u);
v___x_2115_ = l_Lean_Syntax_getArg(v_x_2100_, v___x_2114_);
v___x_2116_ = lean_unsigned_to_nat(6u);
v___x_2117_ = l_Lean_Syntax_getArg(v_x_2100_, v___x_2116_);
lean_dec(v_x_2100_);
v___x_2118_ = 0;
v___x_2119_ = l_Lean_SourceInfo_fromRef(v_ref_2109_, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25));
v___x_2121_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_2122_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
lean_inc_n(v___x_2119_, 10);
v___x_2123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2119_);
lean_ctor_set(v___x_2123_, 1, v___x_2120_);
v___x_2124_ = l_Lean_Syntax_node1(v___x_2119_, v___x_2122_, v___x_2123_);
v___x_2125_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2126_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2127_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2119_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2130_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_2131_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v_currMacroScope_2108_, 2);
lean_inc_n(v_quotContext_2107_, 2);
v___x_2132_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2131_, v_currMacroScope_2108_);
v___x_2133_ = lean_box(0);
v___x_2134_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_2135_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2119_);
lean_ctor_set(v___x_2135_, 1, v___x_2130_);
lean_ctor_set(v___x_2135_, 2, v___x_2132_);
lean_ctor_set(v___x_2135_, 3, v___x_2134_);
v___x_2136_ = l_Lean_Syntax_node1(v___x_2119_, v___x_2125_, v___x_2115_);
v___x_2137_ = l_Lean_Syntax_node2(v___x_2119_, v___x_2129_, v___x_2135_, v___x_2136_);
v___x_2138_ = l_Lean_Syntax_node2(v___x_2119_, v___x_2126_, v___x_2128_, v___x_2137_);
v___x_2139_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2119_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
lean_inc(v_name_2113_);
v___x_2141_ = l_Lean_Syntax_node3(v___x_2119_, v___x_2125_, v_name_2113_, v___x_2138_, v___x_2140_);
v___x_2142_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2143_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4));
v___x_2144_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5));
v___x_2145_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2146_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_2147_ = l_Lean_addMacroScope(v_quotContext_2107_, v___x_2146_, v_currMacroScope_2108_);
v___x_2148_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_2149_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2119_);
lean_ctor_set(v___x_2149_, 1, v___x_2145_);
lean_ctor_set(v___x_2149_, 2, v___x_2147_);
lean_ctor_set(v___x_2149_, 3, v___x_2148_);
v___x_2162_ = l_Lean_TSyntax_getId(v_name_2113_);
lean_dec(v_name_2113_);
lean_inc(v___x_2162_);
v___x_2163_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2133_, v___x_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_quoteNameMk(v___x_2162_);
v___y_2151_ = v___x_2164_;
goto v___jp_2150_;
}
else
{
lean_object* v_val_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec(v___x_2162_);
v_val_2165_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_val_2165_);
lean_dec_ref(v___x_2163_);
v___x_2166_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6));
v___x_2167_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_2168_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2169_ = lean_string_intercalate(v___x_2168_, v_val_2165_);
v___x_2170_ = lean_string_append(v___x_2167_, v___x_2169_);
lean_dec_ref(v___x_2169_);
v___x_2171_ = lean_box(2);
v___x_2172_ = l_Lean_Syntax_mkNameLit(v___x_2170_, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
v___x_2175_ = lean_array_push(v___x_2174_, v___x_2172_);
v___x_2176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2171_);
lean_ctor_set(v___x_2176_, 1, v___x_2166_);
lean_ctor_set(v___x_2176_, 2, v___x_2175_);
v___y_2151_ = v___x_2176_;
goto v___jp_2150_;
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_inc_n(v___x_2119_, 7);
v___x_2152_ = l_Lean_Syntax_node2(v___x_2119_, v___x_2125_, v___y_2151_, v___x_2117_);
v___x_2153_ = l_Lean_Syntax_node2(v___x_2119_, v___x_2129_, v___x_2149_, v___x_2152_);
v___x_2154_ = l_Lean_Syntax_node1(v___x_2119_, v___x_2144_, v___x_2153_);
v___x_2155_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2119_);
lean_ctor_set(v___x_2156_, 1, v___x_2125_);
lean_ctor_set(v___x_2156_, 2, v___x_2155_);
v___x_2157_ = l_Lean_Syntax_node2(v___x_2119_, v___x_2143_, v___x_2154_, v___x_2156_);
v___x_2158_ = l_Lean_Syntax_node1(v___x_2119_, v___x_2125_, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node1(v___x_2119_, v___x_2142_, v___x_2158_);
v___x_2160_ = l_Lean_Syntax_node4(v___x_2119_, v___x_2121_, v___x_2111_, v___x_2124_, v___x_2141_, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_a_2102_);
return v___x_2161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(lean_object* v_x_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(v_x_2177_, v_a_2178_, v_a_2179_);
lean_dec_ref(v_a_2178_);
return v_res_2180_;
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
