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
static const lean_string_object l_Lean_instInhabitedOptionDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedOptionDecl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedOptionDecl_default___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedOptionDecl_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedOptionDecl_default___closed__1;
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
v___x_350_ = lean_nat_add(v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec(v___y_348_);
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
lean_ctor_set(v___x_330_, 3, v___y_347_);
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
lean_ctor_set(v_reuseFailAlloc_355_, 3, v___y_347_);
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
v___y_347_ = v___x_361_;
v___y_348_ = v___x_362_;
v___y_349_ = v_size_363_;
goto v___jp_346_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(0u);
v___y_347_ = v___x_361_;
v___y_348_ = v___x_362_;
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
v___x_536_ = lean_nat_add(v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec(v___y_534_);
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
lean_ctor_set(v___x_516_, 3, v___y_533_);
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
lean_ctor_set(v_reuseFailAlloc_541_, 3, v___y_533_);
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
v___y_533_ = v___x_547_;
v___y_534_ = v___x_548_;
v___y_535_ = v_size_549_;
goto v___jp_532_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___y_533_ = v___x_547_;
v___y_534_ = v___x_548_;
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
v___x_677_ = lean_nat_add(v___y_674_, v___y_676_);
lean_dec(v___y_676_);
lean_dec(v___y_674_);
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
lean_ctor_set(v___x_681_, 3, v___y_675_);
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
lean_ctor_set(v_reuseFailAlloc_685_, 3, v___y_675_);
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
v___y_674_ = v___x_699_;
v___y_675_ = v___x_698_;
v___y_676_ = v_size_700_;
goto v___jp_673_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_unsigned_to_nat(0u);
v___y_674_ = v___x_699_;
v___y_675_ = v___x_698_;
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
lean_inc(v_k_1044_);
v_v_1045_ = lean_ctor_get(v_x_1043_, 2);
lean_inc(v_v_1045_);
v_l_1046_ = lean_ctor_get(v_x_1043_, 3);
lean_inc(v_l_1046_);
v_r_1047_ = lean_ctor_get(v_x_1043_, 4);
lean_inc(v_r_1047_);
lean_dec_ref(v_x_1043_);
lean_inc_ref(v_f_1041_);
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1041_, v_init_1042_, v_l_1046_);
lean_inc(v_k_1044_);
lean_inc_ref(v_f_1041_);
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
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
v___x_1107_ = l_Lean_mkAtom(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
v___x_1109_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1110_ = lean_array_push(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
v___x_1120_ = l_Lean_mkAtom(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
v___x_1122_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1123_ = lean_array_push(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1124_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
v___x_1125_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
v___x_1126_ = lean_box(2);
v___x_1127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v___x_1125_);
lean_ctor_set(v___x_1127_, 2, v___x_1124_);
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
v___x_1129_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
v___x_1130_ = lean_array_push(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1131_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
v___x_1132_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
v___x_1133_ = lean_box(2);
v___x_1134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
lean_ctor_set(v___x_1134_, 2, v___x_1131_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
v___x_1136_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1137_ = lean_array_push(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
v___x_1139_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1140_ = lean_box(2);
v___x_1141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1139_);
lean_ctor_set(v___x_1141_, 2, v___x_1138_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
v___x_1143_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1144_ = lean_array_push(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
v___x_1146_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
v___x_1147_ = lean_box(2);
v___x_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___x_1146_);
lean_ctor_set(v___x_1148_, 2, v___x_1145_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
v___x_1150_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1151_ = lean_array_push(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
v___x_1153_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
v___x_1154_ = lean_box(2);
v___x_1155_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
lean_ctor_set(v___x_1155_, 2, v___x_1152_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__0));
v___x_1159_ = l_Lean_instInhabitedDataValue_default;
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
lean_ctor_set(v___x_1161_, 2, v___x_1159_);
lean_ctor_set(v___x_1161_, 3, v___x_1158_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__1, &l_Lean_instInhabitedOptionDecl_default___closed__1_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__1);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_instInhabitedOptionDecl_default;
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* v_self_1169_){
_start:
{
lean_object* v_descr_1171_; lean_object* v_name_1174_; lean_object* v_descr_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_name_1174_ = lean_ctor_get(v_self_1169_, 0);
lean_inc(v_name_1174_);
v_descr_1175_ = lean_ctor_get(v_self_1169_, 3);
lean_inc_ref(v_descr_1175_);
lean_dec_ref(v_self_1169_);
v___x_1176_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
v___x_1177_ = l_Lean_Name_isPrefixOf(v___x_1176_, v_name_1174_);
lean_dec(v_name_1174_);
if (v___x_1177_ == 0)
{
return v_descr_1175_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = lean_string_utf8_byte_size(v_descr_1175_);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_nat_dec_eq(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v_descr_1182_; 
v___x_1181_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
v_descr_1182_ = lean_string_append(v_descr_1175_, v___x_1181_);
v_descr_1171_ = v_descr_1182_;
goto v___jp_1170_;
}
else
{
v_descr_1171_ = v_descr_1175_;
goto v___jp_1170_;
}
}
v___jp_1170_:
{
lean_object* v___x_1172_; lean_object* v_descr_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
v_descr_1173_ = lean_string_append(v_descr_1171_, v___x_1172_);
return v_descr_1173_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_box(1);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_box(1);
v___x_1186_ = lean_st_mk_ref(v___x_1185_);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return v_res_1189_;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l_Lean_registerOption___closed__0));
v___x_1192_ = lean_mk_io_user_error(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* v_name_1195_, lean_object* v_decl_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1225_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1225_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1225_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_unbox(v_a_1199_);
lean_dec(v_a_1199_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec_ref(v_decl_1196_);
lean_dec(v_name_1195_);
v___x_1204_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1209_ = lean_st_ref_get(v___x_1208_);
v___x_1210_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1195_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1195_, v_decl_1196_, v___x_1209_);
v___x_1212_ = lean_st_ref_set(v___x_1208_, v___x_1211_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1212_);
v___x_1214_ = v___x_1201_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
lean_dec(v___x_1209_);
lean_dec_ref(v_decl_1196_);
v___x_1216_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1195_, v___x_1210_);
v___x_1218_ = lean_string_append(v___x_1216_, v___x_1217_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1220_ = lean_string_append(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_mk_io_user_error(v___x_1220_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1221_);
v___x_1223_ = v___x_1201_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_decl_1196_);
lean_dec(v_name_1195_);
v_a_1226_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1198_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1198_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1234_, lean_object* v_decl_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = lean_register_option(v_name_1234_, v_decl_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1240_ = lean_st_ref_get(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_getOptionDecls();
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* v_init_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_object* v_k_1246_; lean_object* v_v_1247_; lean_object* v_l_1248_; lean_object* v_r_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_k_1246_ = lean_ctor_get(v_x_1245_, 1);
v_v_1247_ = lean_ctor_get(v_x_1245_, 2);
v_l_1248_ = lean_ctor_get(v_x_1245_, 3);
v_r_1249_ = lean_ctor_get(v_x_1245_, 4);
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1244_, v_l_1248_);
lean_inc(v_v_1247_);
lean_inc(v_k_1246_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_k_1246_);
lean_ctor_set(v___x_1251_, 1, v_v_1247_);
v___x_1252_ = lean_array_push(v___x_1250_, v___x_1251_);
v_init_1244_ = v___x_1252_;
v_x_1245_ = v_r_1249_;
goto _start;
}
else
{
return v_init_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* v_init_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1254_, v_x_1255_);
lean_dec(v_x_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(){
_start:
{
lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1270_; 
v___x_1260_ = l_Lean_getOptionDecls();
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1270_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1270_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1265_ = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
v___x_1266_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_1265_, v_a_1261_);
lean_dec(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = lean_get_option_decls_array();
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* v_init_1273_, lean_object* v_t_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1273_, v_t_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* v_init_1276_, lean_object* v_t_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(v_init_1276_, v_t_1277_);
lean_dec(v_t_1277_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* v_name_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1303_; 
v___x_1283_ = l_Lean_getOptionDecls();
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1284_, v_name_1281_);
lean_dec(v_a_1284_);
if (lean_obj_tag(v___x_1288_) == 1)
{
lean_object* v_val_1289_; lean_object* v___x_1291_; 
lean_dec(v_name_1281_);
v_val_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1289_);
lean_dec_ref(v___x_1288_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v_val_1289_);
v___x_1291_ = v___x_1286_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_val_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
else
{
lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec(v___x_1288_);
v___x_1293_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1294_ = 1;
v___x_1295_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1281_, v___x_1294_);
v___x_1296_ = lean_string_append(v___x_1293_, v___x_1295_);
lean_dec_ref(v___x_1295_);
v___x_1297_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1298_ = lean_string_append(v___x_1296_, v___x_1297_);
v___x_1299_ = lean_mk_io_user_error(v___x_1298_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1299_);
v___x_1301_ = v___x_1286_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_getOptionDecl(v_name_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_getOptionDecl(v_name_1307_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_defValue_1314_; lean_object* v___x_1316_; 
v_defValue_1314_ = lean_ctor_get(v_a_1310_, 2);
lean_inc_ref(v_defValue_1314_);
lean_dec(v_a_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_defValue_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_defValue_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1319_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1309_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1309_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_getOptionDefaultValue(v_name_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* v_name_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_getOptionDecl(v_name_1330_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_descr_1337_; lean_object* v___x_1339_; 
v_descr_1337_ = lean_ctor_get(v_a_1333_, 3);
lean_inc_ref(v_descr_1337_);
lean_dec(v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_descr_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_descr_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1332_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1332_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_getOptionDescr(v_name_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1353_, lean_object* v_inst_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_apply_2(v_inst_1353_, lean_box(0), v_inst_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1356_, lean_object* v_n_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_apply_2(v_inst_1358_, lean_box(0), v_inst_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1361_, lean_object* v_toPure_1362_, uint8_t v_defValue_1363_, lean_object* v_opts_1364_){
_start:
{
lean_object* v_map_1365_; lean_object* v___x_1366_; 
v_map_1365_ = lean_ctor_get(v_opts_1364_, 0);
v___x_1366_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1365_, v_k_1361_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_box(v_defValue_1363_);
v___x_1368_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v_val_1369_; 
v_val_1369_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1369_);
lean_dec_ref(v___x_1366_);
if (lean_obj_tag(v_val_1369_) == 1)
{
uint8_t v_v_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_v_1370_ = lean_ctor_get_uint8(v_val_1369_, 0);
lean_dec_ref(v_val_1369_);
v___x_1371_ = lean_box(v_v_1370_);
v___x_1372_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1371_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v_val_1369_);
v___x_1373_ = lean_box(v_defValue_1363_);
v___x_1374_ = lean_apply_2(v_toPure_1362_, lean_box(0), v___x_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1375_, lean_object* v_toPure_1376_, lean_object* v_defValue_1377_, lean_object* v_opts_1378_){
_start:
{
uint8_t v_defValue_boxed_1379_; lean_object* v_res_1380_; 
v_defValue_boxed_1379_ = lean_unbox(v_defValue_1377_);
v_res_1380_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1375_, v_toPure_1376_, v_defValue_boxed_1379_, v_opts_1378_);
lean_dec_ref(v_opts_1378_);
lean_dec(v_k_1375_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_k_1383_, uint8_t v_defValue_1384_){
_start:
{
lean_object* v_toApplicative_1385_; lean_object* v_toBind_1386_; lean_object* v_toPure_1387_; lean_object* v___x_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; 
v_toApplicative_1385_ = lean_ctor_get(v_inst_1381_, 0);
lean_inc_ref(v_toApplicative_1385_);
v_toBind_1386_ = lean_ctor_get(v_inst_1381_, 1);
lean_inc(v_toBind_1386_);
lean_dec_ref(v_inst_1381_);
v_toPure_1387_ = lean_ctor_get(v_toApplicative_1385_, 1);
lean_inc(v_toPure_1387_);
lean_dec_ref(v_toApplicative_1385_);
v___x_1388_ = lean_box(v_defValue_1384_);
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1389_, 0, v_k_1383_);
lean_closure_set(v___f_1389_, 1, v_toPure_1387_);
lean_closure_set(v___f_1389_, 2, v___x_1388_);
v___x_1390_ = lean_apply_4(v_toBind_1386_, lean_box(0), lean_box(0), v_inst_1382_, v___f_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_k_1393_, lean_object* v_defValue_1394_){
_start:
{
uint8_t v_defValue_boxed_1395_; lean_object* v_res_1396_; 
v_defValue_boxed_1395_ = lean_unbox(v_defValue_1394_);
v_res_1396_ = l_Lean_getBoolOption___redArg(v_inst_1391_, v_inst_1392_, v_k_1393_, v_defValue_boxed_1395_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* v_m_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_k_1400_, uint8_t v_defValue_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_getBoolOption___redArg(v_inst_1398_, v_inst_1399_, v_k_1400_, v_defValue_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_k_1406_, lean_object* v_defValue_1407_){
_start:
{
uint8_t v_defValue_boxed_1408_; lean_object* v_res_1409_; 
v_defValue_boxed_1408_ = lean_unbox(v_defValue_1407_);
v_res_1409_ = l_Lean_getBoolOption(v_m_1403_, v_inst_1404_, v_inst_1405_, v_k_1406_, v_defValue_boxed_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1410_, lean_object* v_toPure_1411_, lean_object* v_defValue_1412_, lean_object* v_opts_1413_){
_start:
{
lean_object* v_map_1414_; lean_object* v___x_1415_; 
v_map_1414_ = lean_ctor_get(v_opts_1413_, 0);
v___x_1415_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1414_, v_k_1410_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_apply_2(v_toPure_1411_, lean_box(0), v_defValue_1412_);
return v___x_1416_;
}
else
{
lean_object* v_val_1417_; 
v_val_1417_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1417_);
lean_dec_ref(v___x_1415_);
if (lean_obj_tag(v_val_1417_) == 3)
{
lean_object* v_v_1418_; lean_object* v___x_1419_; 
lean_dec(v_defValue_1412_);
v_v_1418_ = lean_ctor_get(v_val_1417_, 0);
lean_inc(v_v_1418_);
lean_dec_ref(v_val_1417_);
v___x_1419_ = lean_apply_2(v_toPure_1411_, lean_box(0), v_v_1418_);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; 
lean_dec(v_val_1417_);
v___x_1420_ = lean_apply_2(v_toPure_1411_, lean_box(0), v_defValue_1412_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1421_, lean_object* v_toPure_1422_, lean_object* v_defValue_1423_, lean_object* v_opts_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_getNatOption___redArg___lam__0(v_k_1421_, v_toPure_1422_, v_defValue_1423_, v_opts_1424_);
lean_dec_ref(v_opts_1424_);
lean_dec(v_k_1421_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_k_1428_, lean_object* v_defValue_1429_){
_start:
{
lean_object* v_toApplicative_1430_; lean_object* v_toBind_1431_; lean_object* v_toPure_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; 
v_toApplicative_1430_ = lean_ctor_get(v_inst_1426_, 0);
lean_inc_ref(v_toApplicative_1430_);
v_toBind_1431_ = lean_ctor_get(v_inst_1426_, 1);
lean_inc(v_toBind_1431_);
lean_dec_ref(v_inst_1426_);
v_toPure_1432_ = lean_ctor_get(v_toApplicative_1430_, 1);
lean_inc(v_toPure_1432_);
lean_dec_ref(v_toApplicative_1430_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1433_, 0, v_k_1428_);
lean_closure_set(v___f_1433_, 1, v_toPure_1432_);
lean_closure_set(v___f_1433_, 2, v_defValue_1429_);
v___x_1434_ = lean_apply_4(v_toBind_1431_, lean_box(0), lean_box(0), v_inst_1427_, v___f_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_k_1438_, lean_object* v_defValue_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_getNatOption___redArg(v_inst_1436_, v_inst_1437_, v_k_1438_, v_defValue_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1441_, lean_object* v_f_1442_, lean_object* v_00_u03b2_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_apply_3(v_inst_1441_, lean_box(0), v_f_1442_, v___y_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_00_u03b1_1448_, lean_object* v_f_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v___f_1451_; lean_object* v___x_1452_; 
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1451_, 0, v_inst_1446_);
lean_closure_set(v___f_1451_, 1, v_f_1449_);
v___x_1452_ = lean_apply_3(v_inst_1447_, lean_box(0), v___f_1451_, v_x_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1453_, lean_object* v_inst_1454_){
_start:
{
lean_object* v___f_1455_; 
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1455_, 0, v_inst_1454_);
lean_closure_set(v___f_1455_, 1, v_inst_1453_);
return v___f_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1456_, lean_object* v_n_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_){
_start:
{
lean_object* v___f_1460_; 
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1460_, 0, v_inst_1459_);
lean_closure_set(v___f_1460_, 1, v_inst_1458_);
return v___f_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1464_, lean_object* v_o_1465_){
_start:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1467_ = 1;
v___x_1468_ = lean_box(v___x_1467_);
v___x_1469_ = l_Lean_Options_set___redArg(v___x_1464_, v_o_1465_, v___x_1466_, v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___f_1471_; 
v___x_1470_ = l_Lean_KVMap_instValueBool;
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1471_, 0, v___x_1470_);
return v___f_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v___f_1474_; lean_object* v___x_1475_; 
v___f_1474_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1475_ = lean_apply_3(v_inst_1472_, lean_box(0), v___f_1474_, v_x_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1476_, lean_object* v_00_u03b1_1477_, lean_object* v_inst_1478_, lean_object* v_x_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_withInPattern___redArg(v_inst_1478_, v_x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1481_){
_start:
{
lean_object* v_map_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
v_map_1482_ = lean_ctor_get(v_o_1481_, 0);
v___x_1483_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1484_ = 0;
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1482_, v___x_1483_);
if (lean_obj_tag(v___x_1485_) == 0)
{
return v___x_1484_;
}
else
{
lean_object* v_val_1486_; 
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref(v___x_1485_);
if (lean_obj_tag(v_val_1486_) == 1)
{
uint8_t v_v_1487_; 
v_v_1487_ = lean_ctor_get_uint8(v_val_1486_, 0);
lean_dec_ref(v_val_1486_);
return v_v_1487_;
}
else
{
lean_dec(v_val_1486_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1488_){
_start:
{
uint8_t v_res_1489_; lean_object* v_r_1490_; 
v_res_1489_ = l_Lean_Options_getInPattern(v_o_1488_);
lean_dec_ref(v_o_1488_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
lean_ctor_set(v___x_1493_, 1, v_inst_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_a_1494_, lean_object* v_inst_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1502_, lean_object* v_opts_1503_, lean_object* v_opt_1504_){
_start:
{
lean_object* v_name_1505_; lean_object* v_map_1506_; lean_object* v_ofDataValue_x3f_1507_; lean_object* v___x_1508_; 
v_name_1505_ = lean_ctor_get(v_opt_1504_, 0);
v_map_1506_ = lean_ctor_get(v_opts_1503_, 0);
v_ofDataValue_x3f_1507_ = lean_ctor_get(v_inst_1502_, 1);
lean_inc_ref(v_ofDataValue_x3f_1507_);
lean_dec_ref(v_inst_1502_);
v___x_1508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1506_, v_name_1505_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1509_; 
lean_dec_ref(v_ofDataValue_x3f_1507_);
v___x_1509_ = lean_box(0);
return v___x_1509_;
}
else
{
lean_object* v_val_1510_; lean_object* v___x_1511_; 
v_val_1510_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1510_);
lean_dec_ref(v___x_1508_);
v___x_1511_ = lean_apply_1(v_ofDataValue_x3f_1507_, v_val_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1512_, lean_object* v_opts_1513_, lean_object* v_opt_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Option_get_x3f___redArg(v_inst_1512_, v_opts_1513_, v_opt_1514_);
lean_dec_ref(v_opt_1514_);
lean_dec_ref(v_opts_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1516_, lean_object* v_inst_1517_, lean_object* v_opts_1518_, lean_object* v_opt_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Option_get_x3f___redArg(v_inst_1517_, v_opts_1518_, v_opt_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_inst_1522_, lean_object* v_opts_1523_, lean_object* v_opt_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Option_get_x3f(v_00_u03b1_1521_, v_inst_1522_, v_opts_1523_, v_opt_1524_);
lean_dec_ref(v_opt_1524_);
lean_dec_ref(v_opts_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1526_, lean_object* v_opts_1527_, lean_object* v_opt_1528_){
_start:
{
lean_object* v_name_1529_; lean_object* v_defValue_1530_; lean_object* v_map_1531_; lean_object* v_ofDataValue_x3f_1532_; lean_object* v___x_1533_; 
v_name_1529_ = lean_ctor_get(v_opt_1528_, 0);
v_defValue_1530_ = lean_ctor_get(v_opt_1528_, 1);
v_map_1531_ = lean_ctor_get(v_opts_1527_, 0);
v_ofDataValue_x3f_1532_ = lean_ctor_get(v_inst_1526_, 1);
lean_inc_ref(v_ofDataValue_x3f_1532_);
lean_dec_ref(v_inst_1526_);
v___x_1533_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1531_, v_name_1529_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1532_);
lean_inc(v_defValue_1530_);
return v_defValue_1530_;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1535_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = lean_apply_1(v_ofDataValue_x3f_1532_, v_val_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_inc(v_defValue_1530_);
return v_defValue_1530_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref(v___x_1535_);
return v_val_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1537_, lean_object* v_opts_1538_, lean_object* v_opt_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Option_get___redArg(v_inst_1537_, v_opts_1538_, v_opt_1539_);
lean_dec_ref(v_opt_1539_);
lean_dec_ref(v_opts_1538_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1541_, lean_object* v_inst_1542_, lean_object* v_opts_1543_, lean_object* v_opt_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Option_get___redArg(v_inst_1542_, v_opts_1543_, v_opt_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1546_, lean_object* v_inst_1547_, lean_object* v_opts_1548_, lean_object* v_opt_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Option_get(v_00_u03b1_1546_, v_inst_1547_, v_opts_1548_, v_opt_1549_);
lean_dec_ref(v_opt_1549_);
lean_dec_ref(v_opts_1548_);
return v_res_1550_;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* v_opts_1551_, lean_object* v_name_1552_, uint8_t v_defValue_1553_){
_start:
{
lean_object* v_map_1554_; lean_object* v___x_1555_; 
v_map_1554_ = lean_ctor_get(v_opts_1551_, 0);
lean_inc(v_map_1554_);
lean_dec_ref(v_opts_1551_);
v___x_1555_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1554_, v_name_1552_);
lean_dec(v_name_1552_);
lean_dec(v_map_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
return v_defValue_1553_;
}
else
{
lean_object* v_val_1556_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref(v___x_1555_);
if (lean_obj_tag(v_val_1556_) == 1)
{
uint8_t v_v_1557_; 
v_v_1557_ = lean_ctor_get_uint8(v_val_1556_, 0);
lean_dec_ref(v_val_1556_);
return v_v_1557_;
}
else
{
lean_dec(v_val_1556_);
return v_defValue_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* v_opts_1558_, lean_object* v_name_1559_, lean_object* v_defValue_1560_){
_start:
{
uint8_t v_defValue_boxed_1561_; uint8_t v_res_1562_; lean_object* v_r_1563_; 
v_defValue_boxed_1561_ = lean_unbox(v_defValue_1560_);
v_res_1562_ = lean_options_get_bool(v_opts_1558_, v_name_1559_, v_defValue_boxed_1561_);
v_r_1563_ = lean_box(v_res_1562_);
return v_r_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* v_inst_1564_, lean_object* v_opt_1565_, lean_object* v_toPure_1566_, lean_object* v_____do__lift_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = l_Lean_Option_get___redArg(v_inst_1564_, v_____do__lift_1567_, v_opt_1565_);
v___x_1569_ = lean_apply_2(v_toPure_1566_, lean_box(0), v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* v_inst_1570_, lean_object* v_opt_1571_, lean_object* v_toPure_1572_, lean_object* v_____do__lift_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Option_getM___redArg___lam__0(v_inst_1570_, v_opt_1571_, v_toPure_1572_, v_____do__lift_1573_);
lean_dec_ref(v_____do__lift_1573_);
lean_dec_ref(v_opt_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_opt_1578_){
_start:
{
lean_object* v_toApplicative_1579_; lean_object* v_toBind_1580_; lean_object* v_toPure_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; 
v_toApplicative_1579_ = lean_ctor_get(v_inst_1575_, 0);
lean_inc_ref(v_toApplicative_1579_);
v_toBind_1580_ = lean_ctor_get(v_inst_1575_, 1);
lean_inc(v_toBind_1580_);
lean_dec_ref(v_inst_1575_);
v_toPure_1581_ = lean_ctor_get(v_toApplicative_1579_, 1);
lean_inc(v_toPure_1581_);
lean_dec_ref(v_toApplicative_1579_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1582_, 0, v_inst_1577_);
lean_closure_set(v___f_1582_, 1, v_opt_1578_);
lean_closure_set(v___f_1582_, 2, v_toPure_1581_);
v___x_1583_ = lean_apply_4(v_toBind_1580_, lean_box(0), lean_box(0), v_inst_1576_, v___f_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* v_m_1584_, lean_object* v_00_u03b1_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_opt_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Option_getM___redArg(v_inst_1586_, v_inst_1587_, v_inst_1588_, v_opt_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* v_inst_1591_, lean_object* v_opts_1592_, lean_object* v_opt_1593_, lean_object* v_val_1594_){
_start:
{
lean_object* v_name_1595_; lean_object* v___x_1596_; 
v_name_1595_ = lean_ctor_get(v_opt_1593_, 0);
lean_inc(v_name_1595_);
lean_dec_ref(v_opt_1593_);
v___x_1596_ = l_Lean_Options_set___redArg(v_inst_1591_, v_opts_1592_, v_name_1595_, v_val_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* v_00_u03b1_1597_, lean_object* v_inst_1598_, lean_object* v_opts_1599_, lean_object* v_opt_1600_, lean_object* v_val_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Option_set___redArg(v_inst_1598_, v_opts_1599_, v_opt_1600_, v_val_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1603_, lean_object* v_k_1604_, uint8_t v_v_1605_){
_start:
{
lean_object* v_map_1606_; uint8_t v_hasTrace_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1621_; 
v_map_1606_ = lean_ctor_get(v_o_1603_, 0);
v_hasTrace_1607_ = lean_ctor_get_uint8(v_o_1603_, sizeof(void*)*1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_o_1603_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1609_ = v_o_1603_;
v_isShared_1610_ = v_isSharedCheck_1621_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_map_1606_);
lean_dec(v_o_1603_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1621_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1611_, 0, v_v_1605_);
lean_inc(v_k_1604_);
v___x_1612_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1604_, v___x_1611_, v_map_1606_);
if (v_hasTrace_1607_ == 0)
{
lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1616_; 
v___x_1613_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_1614_ = l_Lean_Name_isPrefixOf(v___x_1613_, v_k_1604_);
lean_dec(v_k_1604_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1612_);
v___x_1616_ = v___x_1609_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1612_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_ctor_set_uint8(v___x_1616_, sizeof(void*)*1, v___x_1614_);
return v___x_1616_;
}
}
else
{
lean_object* v___x_1619_; 
lean_dec(v_k_1604_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1612_);
v___x_1619_ = v___x_1609_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1612_);
lean_ctor_set_uint8(v_reuseFailAlloc_1620_, sizeof(void*)*1, v_hasTrace_1607_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1622_, lean_object* v_k_1623_, lean_object* v_v_1624_){
_start:
{
uint8_t v_v_boxed_1625_; lean_object* v_res_1626_; 
v_v_boxed_1625_ = lean_unbox(v_v_1624_);
v_res_1626_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1622_, v_k_1623_, v_v_boxed_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* v_opts_1627_, lean_object* v_name_1628_, uint8_t v_val_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1627_, v_name_1628_, v_val_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1631_, lean_object* v_name_1632_, lean_object* v_val_1633_){
_start:
{
uint8_t v_val_boxed_1634_; lean_object* v_res_1635_; 
v_val_boxed_1634_ = lean_unbox(v_val_1633_);
v_res_1635_ = lean_options_update_bool(v_opts_1631_, v_name_1632_, v_val_boxed_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1636_, lean_object* v_opts_1637_, lean_object* v_opt_1638_, lean_object* v_val_1639_){
_start:
{
lean_object* v_name_1640_; lean_object* v_map_1641_; uint8_t v___x_1642_; 
v_name_1640_ = lean_ctor_get(v_opt_1638_, 0);
v_map_1641_ = lean_ctor_get(v_opts_1637_, 0);
v___x_1642_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1640_, v_map_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Option_set___redArg(v_inst_1636_, v_opts_1637_, v_opt_1638_, v_val_1639_);
return v___x_1643_;
}
else
{
lean_dec(v_val_1639_);
lean_dec_ref(v_opt_1638_);
lean_dec_ref(v_inst_1636_);
return v_opts_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1644_, lean_object* v_inst_1645_, lean_object* v_opts_1646_, lean_object* v_opt_1647_, lean_object* v_val_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1645_, v_opts_1646_, v_opt_1647_, v_val_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1651_, lean_object* v_name_1652_, lean_object* v_decl_1653_, lean_object* v_ref_1654_){
_start:
{
lean_object* v_toDataValue_1656_; lean_object* v_defValue_1657_; lean_object* v_descr_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1684_; 
v_toDataValue_1656_ = lean_ctor_get(v_inst_1651_, 0);
lean_inc_ref(v_toDataValue_1656_);
lean_dec_ref(v_inst_1651_);
v_defValue_1657_ = lean_ctor_get(v_decl_1653_, 0);
v_descr_1658_ = lean_ctor_get(v_decl_1653_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_decl_1653_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1660_ = v_decl_1653_;
v_isShared_1661_ = v_isSharedCheck_1684_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_descr_1658_);
lean_inc(v_defValue_1657_);
lean_dec(v_decl_1653_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1684_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_inc(v_defValue_1657_);
v___x_1662_ = lean_apply_1(v_toDataValue_1656_, v_defValue_1657_);
lean_inc(v_name_1652_);
v___x_1663_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1663_, 0, v_name_1652_);
lean_ctor_set(v___x_1663_, 1, v_ref_1654_);
lean_ctor_set(v___x_1663_, 2, v___x_1662_);
lean_ctor_set(v___x_1663_, 3, v_descr_1658_);
lean_inc(v_name_1652_);
v___x_1664_ = lean_register_option(v_name_1652_, v___x_1663_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v___x_1664_, 0);
lean_dec(v_unused_1675_);
v___x_1666_ = v___x_1664_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v___x_1664_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_defValue_1657_);
lean_ctor_set(v___x_1660_, 0, v_name_1652_);
v___x_1669_ = v___x_1660_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_name_1652_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_defValue_1657_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1669_);
v___x_1671_ = v___x_1666_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1660_);
lean_dec(v_defValue_1657_);
lean_dec(v_name_1652_);
v_a_1676_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1664_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1664_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1685_, lean_object* v_name_1686_, lean_object* v_decl_1687_, lean_object* v_ref_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Option_register___redArg(v_inst_1685_, v_name_1686_, v_decl_1687_, v_ref_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1691_, lean_object* v_inst_1692_, lean_object* v_name_1693_, lean_object* v_decl_1694_, lean_object* v_ref_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Option_register___redArg(v_inst_1692_, v_name_1693_, v_decl_1694_, v_ref_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* v_00_u03b1_1698_, lean_object* v_inst_1699_, lean_object* v_name_1700_, lean_object* v_decl_1701_, lean_object* v_ref_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Option_register(v_00_u03b1_1698_, v_inst_1699_, v_name_1700_, v_decl_1701_, v_ref_1702_);
return v_res_1704_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
v___x_1793_ = l_String_toRawSubstring_x27(v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
v___x_1814_ = l_String_toRawSubstring_x27(v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29(void){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Array_mkArray0(lean_box(0));
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* v_x_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_1846_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(v_x_1842_);
v___x_1847_ = l_Lean_Syntax_isOfKind(v_x_1842_, v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v_x_1842_);
v___x_1848_ = lean_box(1);
v___x_1849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1844_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v_name_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1984_; lean_object* v___x_1995_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = l_Lean_Syntax_getArg(v_x_1842_, v___x_1850_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = l_Lean_Syntax_getArg(v_x_1842_, v___x_1852_);
v___x_1854_ = lean_unsigned_to_nat(3u);
v_name_1855_ = l_Lean_Syntax_getArg(v_x_1842_, v___x_1854_);
v___x_1856_ = lean_unsigned_to_nat(5u);
v___x_1857_ = l_Lean_Syntax_getArg(v_x_1842_, v___x_1856_);
v___x_1858_ = lean_unsigned_to_nat(7u);
v___x_1859_ = l_Lean_Syntax_getArg(v_x_1842_, v___x_1858_);
lean_dec(v_x_1842_);
v___x_1995_ = l_Lean_Syntax_getOptional_x3f(v___x_1853_);
lean_dec(v___x_1853_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_box(0);
v___y_1984_ = v___x_1996_;
goto v___jp_1983_;
}
else
{
lean_object* v_val_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_val_1997_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1995_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_val_1997_);
lean_dec(v___x_1995_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_val_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
v___y_1984_ = v___x_2002_;
goto v___jp_1983_;
}
}
}
v___jp_1860_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_inc(v___y_1862_);
lean_inc(v___y_1863_);
v___x_1874_ = l_Lean_Syntax_node2(v___y_1863_, v___y_1862_, v___y_1873_, v___x_1859_);
lean_inc(v___y_1863_);
v___x_1875_ = l_Lean_Syntax_node2(v___y_1863_, v___y_1861_, v___y_1868_, v___x_1874_);
lean_inc(v___y_1863_);
v___x_1876_ = l_Lean_Syntax_node1(v___y_1863_, v___y_1872_, v___x_1875_);
lean_inc(v___y_1863_);
v___x_1877_ = l_Lean_Syntax_node2(v___y_1863_, v___y_1867_, v___x_1876_, v___y_1864_);
lean_inc(v___y_1863_);
v___x_1878_ = l_Lean_Syntax_node1(v___y_1863_, v___y_1862_, v___x_1877_);
lean_inc(v___y_1863_);
v___x_1879_ = l_Lean_Syntax_node1(v___y_1863_, v___y_1866_, v___x_1878_);
v___x_1880_ = l_Lean_Syntax_node4(v___y_1863_, v___y_1871_, v___y_1865_, v___y_1869_, v___y_1870_, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v_a_1844_);
return v___x_1881_;
}
v___jp_1882_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1895_ = l_Array_append___redArg(v___y_1889_, v___y_1894_);
lean_dec_ref(v___y_1894_);
lean_inc(v___y_1884_);
lean_inc(v___y_1886_);
v___x_1896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1896_, 0, v___y_1886_);
lean_ctor_set(v___x_1896_, 1, v___y_1884_);
lean_ctor_set(v___x_1896_, 2, v___x_1895_);
lean_inc_n(v___y_1887_, 5);
lean_inc(v___y_1886_);
v___x_1897_ = l_Lean_Syntax_node7(v___y_1886_, v___y_1885_, v___y_1893_, v___y_1887_, v___x_1896_, v___y_1887_, v___y_1887_, v___y_1887_, v___y_1887_);
v___x_1898_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_1883_);
v___x_1899_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___y_1888_, v___x_1898_);
v___x_1900_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
lean_inc(v___y_1886_);
v___x_1901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___y_1886_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
lean_inc(v___y_1886_);
v___x_1902_ = l_Lean_Syntax_node1(v___y_1886_, v___x_1899_, v___x_1901_);
v___x_1903_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_1904_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
lean_inc_ref(v___y_1883_);
v___x_1905_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___x_1903_, v___x_1904_);
v___x_1906_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
lean_inc(v___y_1886_);
v___x_1907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___y_1886_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
lean_inc_ref(v___y_1883_);
v___x_1909_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___x_1903_, v___x_1908_);
v___x_1910_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_1911_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc(v___y_1890_);
lean_inc(v___y_1892_);
v___x_1912_ = l_Lean_addMacroScope(v___y_1892_, v___x_1911_, v___y_1890_);
v___x_1913_ = lean_box(0);
v___x_1914_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
lean_inc(v___y_1886_);
v___x_1915_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1915_, 0, v___y_1886_);
lean_ctor_set(v___x_1915_, 1, v___x_1910_);
lean_ctor_set(v___x_1915_, 2, v___x_1912_);
lean_ctor_set(v___x_1915_, 3, v___x_1914_);
lean_inc(v___y_1884_);
lean_inc(v___y_1886_);
v___x_1916_ = l_Lean_Syntax_node1(v___y_1886_, v___y_1884_, v___x_1857_);
lean_inc(v___x_1909_);
lean_inc(v___y_1886_);
v___x_1917_ = l_Lean_Syntax_node2(v___y_1886_, v___x_1909_, v___x_1915_, v___x_1916_);
lean_inc(v___y_1886_);
v___x_1918_ = l_Lean_Syntax_node2(v___y_1886_, v___x_1905_, v___x_1907_, v___x_1917_);
v___x_1919_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
lean_inc(v___y_1886_);
v___x_1920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___y_1886_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
lean_inc(v_name_1855_);
lean_inc(v___y_1884_);
lean_inc(v___y_1886_);
v___x_1921_ = l_Lean_Syntax_node3(v___y_1886_, v___y_1884_, v_name_1855_, v___x_1918_, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
lean_inc_ref(v___y_1883_);
v___x_1923_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___x_1903_, v___x_1922_);
v___x_1924_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
lean_inc_ref(v___y_1883_);
v___x_1925_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___x_1903_, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
lean_inc_ref(v___y_1883_);
v___x_1927_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___x_1903_, v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_1929_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
lean_inc(v___y_1890_);
lean_inc(v___y_1892_);
v___x_1930_ = l_Lean_addMacroScope(v___y_1892_, v___x_1929_, v___y_1890_);
v___x_1931_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
lean_inc(v___y_1886_);
v___x_1932_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1932_, 0, v___y_1886_);
lean_ctor_set(v___x_1932_, 1, v___x_1928_);
lean_ctor_set(v___x_1932_, 2, v___x_1930_);
lean_ctor_set(v___x_1932_, 3, v___x_1931_);
v___x_1933_ = l_Lean_TSyntax_getId(v_name_1855_);
lean_dec(v_name_1855_);
lean_inc(v___x_1933_);
v___x_1934_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1913_, v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v___y_1883_);
v___x_1935_ = l_Lean_quoteNameMk(v___x_1933_);
v___y_1861_ = v___x_1909_;
v___y_1862_ = v___y_1884_;
v___y_1863_ = v___y_1886_;
v___y_1864_ = v___y_1887_;
v___y_1865_ = v___x_1897_;
v___y_1866_ = v___x_1923_;
v___y_1867_ = v___x_1925_;
v___y_1868_ = v___x_1932_;
v___y_1869_ = v___x_1902_;
v___y_1870_ = v___x_1921_;
v___y_1871_ = v___y_1891_;
v___y_1872_ = v___x_1927_;
v___y_1873_ = v___x_1935_;
goto v___jp_1860_;
}
else
{
lean_object* v_val_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v___x_1933_);
v_val_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_val_1936_);
lean_dec_ref(v___x_1934_);
v___x_1937_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
v___x_1938_ = l_Lean_Name_mkStr4(v___x_1845_, v___y_1883_, v___x_1903_, v___x_1937_);
v___x_1939_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1940_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_1941_ = lean_string_intercalate(v___x_1940_, v_val_1936_);
v___x_1942_ = lean_string_append(v___x_1939_, v___x_1941_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = lean_box(2);
v___x_1944_ = l_Lean_Syntax_mkNameLit(v___x_1942_, v___x_1943_);
v___x_1945_ = lean_mk_empty_array_with_capacity(v___x_1852_);
v___x_1946_ = lean_array_push(v___x_1945_, v___x_1944_);
v___x_1947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1943_);
lean_ctor_set(v___x_1947_, 1, v___x_1938_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
v___y_1861_ = v___x_1909_;
v___y_1862_ = v___y_1884_;
v___y_1863_ = v___y_1886_;
v___y_1864_ = v___y_1887_;
v___y_1865_ = v___x_1897_;
v___y_1866_ = v___x_1923_;
v___y_1867_ = v___x_1925_;
v___y_1868_ = v___x_1932_;
v___y_1869_ = v___x_1902_;
v___y_1870_ = v___x_1921_;
v___y_1871_ = v___y_1891_;
v___y_1872_ = v___x_1927_;
v___y_1873_ = v___x_1947_;
goto v___jp_1860_;
}
}
v___jp_1948_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_inc_ref(v___y_1954_);
v___x_1960_ = l_Array_append___redArg(v___y_1954_, v___y_1959_);
lean_dec_ref(v___y_1959_);
lean_inc(v___y_1950_);
lean_inc(v___y_1952_);
v___x_1961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1961_, 0, v___y_1952_);
lean_ctor_set(v___x_1961_, 1, v___y_1950_);
lean_ctor_set(v___x_1961_, 2, v___x_1960_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1950_);
lean_inc(v___y_1952_);
v___x_1962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1962_, 0, v___y_1952_);
lean_ctor_set(v___x_1962_, 1, v___y_1950_);
lean_ctor_set(v___x_1962_, 2, v___y_1954_);
if (lean_obj_tag(v___y_1956_) == 1)
{
lean_object* v_val_1963_; lean_object* v___x_1964_; 
v_val_1963_ = lean_ctor_get(v___y_1956_, 0);
lean_inc(v_val_1963_);
lean_dec_ref(v___y_1956_);
v___x_1964_ = l_Array_mkArray1___redArg(v_val_1963_);
v___y_1883_ = v___y_1949_;
v___y_1884_ = v___y_1950_;
v___y_1885_ = v___y_1951_;
v___y_1886_ = v___y_1952_;
v___y_1887_ = v___x_1962_;
v___y_1888_ = v___y_1953_;
v___y_1889_ = v___y_1954_;
v___y_1890_ = v___y_1955_;
v___y_1891_ = v___y_1957_;
v___y_1892_ = v___y_1958_;
v___y_1893_ = v___x_1961_;
v___y_1894_ = v___x_1964_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1965_; 
lean_dec(v___y_1956_);
v___x_1965_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1883_ = v___y_1949_;
v___y_1884_ = v___y_1950_;
v___y_1885_ = v___y_1951_;
v___y_1886_ = v___y_1952_;
v___y_1887_ = v___x_1962_;
v___y_1888_ = v___y_1953_;
v___y_1889_ = v___y_1954_;
v___y_1890_ = v___y_1955_;
v___y_1891_ = v___y_1957_;
v___y_1892_ = v___y_1958_;
v___y_1893_ = v___x_1961_;
v___y_1894_ = v___x_1965_;
goto v___jp_1882_;
}
}
v___jp_1966_:
{
lean_object* v_quotContext_1969_; lean_object* v_currMacroScope_1970_; lean_object* v_ref_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_quotContext_1969_ = lean_ctor_get(v_a_1843_, 1);
v_currMacroScope_1970_ = lean_ctor_get(v_a_1843_, 2);
v_ref_1971_ = lean_ctor_get(v_a_1843_, 5);
v___x_1972_ = 0;
v___x_1973_ = l_Lean_SourceInfo_fromRef(v_ref_1971_, v___x_1972_);
v___x_1974_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_1975_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_1976_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_1977_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28));
v___x_1978_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1979_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
if (lean_obj_tag(v___y_1968_) == 1)
{
lean_object* v_val_1980_; lean_object* v___x_1981_; 
v_val_1980_ = lean_ctor_get(v___y_1968_, 0);
lean_inc(v_val_1980_);
lean_dec_ref(v___y_1968_);
v___x_1981_ = l_Array_mkArray1___redArg(v_val_1980_);
v___y_1949_ = v___x_1974_;
v___y_1950_ = v___x_1978_;
v___y_1951_ = v___x_1977_;
v___y_1952_ = v___x_1973_;
v___y_1953_ = v___x_1975_;
v___y_1954_ = v___x_1979_;
v___y_1955_ = v_currMacroScope_1970_;
v___y_1956_ = v___y_1967_;
v___y_1957_ = v___x_1976_;
v___y_1958_ = v_quotContext_1969_;
v___y_1959_ = v___x_1981_;
goto v___jp_1948_;
}
else
{
lean_object* v___x_1982_; 
lean_dec(v___y_1968_);
v___x_1982_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1949_ = v___x_1974_;
v___y_1950_ = v___x_1978_;
v___y_1951_ = v___x_1977_;
v___y_1952_ = v___x_1973_;
v___y_1953_ = v___x_1975_;
v___y_1954_ = v___x_1979_;
v___y_1955_ = v_currMacroScope_1970_;
v___y_1956_ = v___y_1967_;
v___y_1957_ = v___x_1976_;
v___y_1958_ = v_quotContext_1969_;
v___y_1959_ = v___x_1982_;
goto v___jp_1948_;
}
}
v___jp_1983_:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_Syntax_getOptional_x3f(v___x_1851_);
lean_dec(v___x_1851_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_box(0);
v___y_1967_ = v___y_1984_;
v___y_1968_ = v___x_1986_;
goto v___jp_1966_;
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_val_1987_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1985_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_val_1987_);
lean_dec(v___x_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_val_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v___y_1967_ = v___y_1984_;
v___y_1968_ = v___x_1992_;
goto v___jp_1966_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(lean_object* v_x_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_2005_, v_a_2006_, v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2085_);
v___x_2089_ = l_Lean_Syntax_isOfKind(v_x_2085_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec_ref(v_a_2086_);
lean_dec(v_x_2085_);
v___x_2090_ = lean_box(1);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v_a_2087_);
return v___x_2091_;
}
else
{
lean_object* v_quotContext_2092_; lean_object* v_currMacroScope_2093_; lean_object* v_ref_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_name_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___y_2136_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_quotContext_2092_ = lean_ctor_get(v_a_2086_, 1);
lean_inc(v_quotContext_2092_);
v_currMacroScope_2093_ = lean_ctor_get(v_a_2086_, 2);
lean_inc(v_currMacroScope_2093_);
v_ref_2094_ = lean_ctor_get(v_a_2086_, 5);
lean_inc(v_ref_2094_);
lean_dec_ref(v_a_2086_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = l_Lean_Syntax_getArg(v_x_2085_, v___x_2095_);
v___x_2097_ = lean_unsigned_to_nat(2u);
v_name_2098_ = l_Lean_Syntax_getArg(v_x_2085_, v___x_2097_);
v___x_2099_ = lean_unsigned_to_nat(4u);
v___x_2100_ = l_Lean_Syntax_getArg(v_x_2085_, v___x_2099_);
v___x_2101_ = lean_unsigned_to_nat(6u);
v___x_2102_ = l_Lean_Syntax_getArg(v_x_2085_, v___x_2101_);
lean_dec(v_x_2085_);
v___x_2103_ = 0;
v___x_2104_ = l_Lean_SourceInfo_fromRef(v_ref_2094_, v___x_2103_);
lean_dec(v_ref_2094_);
v___x_2105_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25));
v___x_2106_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_2107_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
lean_inc(v___x_2104_);
v___x_2108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2104_);
lean_ctor_set(v___x_2108_, 1, v___x_2105_);
lean_inc(v___x_2104_);
v___x_2109_ = l_Lean_Syntax_node1(v___x_2104_, v___x_2107_, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2111_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2112_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
lean_inc(v___x_2104_);
v___x_2113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2104_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2115_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_2116_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc(v_currMacroScope_2093_);
lean_inc(v_quotContext_2092_);
v___x_2117_ = l_Lean_addMacroScope(v_quotContext_2092_, v___x_2116_, v_currMacroScope_2093_);
v___x_2118_ = lean_box(0);
v___x_2119_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
lean_inc(v___x_2104_);
v___x_2120_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2104_);
lean_ctor_set(v___x_2120_, 1, v___x_2115_);
lean_ctor_set(v___x_2120_, 2, v___x_2117_);
lean_ctor_set(v___x_2120_, 3, v___x_2119_);
lean_inc(v___x_2104_);
v___x_2121_ = l_Lean_Syntax_node1(v___x_2104_, v___x_2110_, v___x_2100_);
lean_inc(v___x_2104_);
v___x_2122_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2114_, v___x_2120_, v___x_2121_);
lean_inc(v___x_2104_);
v___x_2123_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2111_, v___x_2113_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
lean_inc(v___x_2104_);
v___x_2125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2104_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
lean_inc(v_name_2098_);
lean_inc(v___x_2104_);
v___x_2126_ = l_Lean_Syntax_node3(v___x_2104_, v___x_2110_, v_name_2098_, v___x_2123_, v___x_2125_);
v___x_2127_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2128_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4));
v___x_2129_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5));
v___x_2130_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2131_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_2132_ = l_Lean_addMacroScope(v_quotContext_2092_, v___x_2131_, v_currMacroScope_2093_);
v___x_2133_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
lean_inc(v___x_2104_);
v___x_2134_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2104_);
lean_ctor_set(v___x_2134_, 1, v___x_2130_);
lean_ctor_set(v___x_2134_, 2, v___x_2132_);
lean_ctor_set(v___x_2134_, 3, v___x_2133_);
v___x_2147_ = l_Lean_TSyntax_getId(v_name_2098_);
lean_dec(v_name_2098_);
lean_inc(v___x_2147_);
v___x_2148_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2118_, v___x_2147_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_quoteNameMk(v___x_2147_);
v___y_2136_ = v___x_2149_;
goto v___jp_2135_;
}
else
{
lean_object* v_val_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec(v___x_2147_);
v_val_2150_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_val_2150_);
lean_dec_ref(v___x_2148_);
v___x_2151_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__6));
v___x_2152_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_2153_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2154_ = lean_string_intercalate(v___x_2153_, v_val_2150_);
v___x_2155_ = lean_string_append(v___x_2152_, v___x_2154_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = lean_box(2);
v___x_2157_ = l_Lean_Syntax_mkNameLit(v___x_2155_, v___x_2156_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = lean_mk_empty_array_with_capacity(v___x_2158_);
v___x_2160_ = lean_array_push(v___x_2159_, v___x_2157_);
v___x_2161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2156_);
lean_ctor_set(v___x_2161_, 1, v___x_2151_);
lean_ctor_set(v___x_2161_, 2, v___x_2160_);
v___y_2136_ = v___x_2161_;
goto v___jp_2135_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_inc(v___x_2104_);
v___x_2137_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2110_, v___y_2136_, v___x_2102_);
lean_inc(v___x_2104_);
v___x_2138_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2114_, v___x_2134_, v___x_2137_);
lean_inc(v___x_2104_);
v___x_2139_ = l_Lean_Syntax_node1(v___x_2104_, v___x_2129_, v___x_2138_);
v___x_2140_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
lean_inc(v___x_2104_);
v___x_2141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2104_);
lean_ctor_set(v___x_2141_, 1, v___x_2110_);
lean_ctor_set(v___x_2141_, 2, v___x_2140_);
lean_inc(v___x_2104_);
v___x_2142_ = l_Lean_Syntax_node2(v___x_2104_, v___x_2128_, v___x_2139_, v___x_2141_);
lean_inc(v___x_2104_);
v___x_2143_ = l_Lean_Syntax_node1(v___x_2104_, v___x_2110_, v___x_2142_);
lean_inc(v___x_2104_);
v___x_2144_ = l_Lean_Syntax_node1(v___x_2104_, v___x_2127_, v___x_2143_);
v___x_2145_ = l_Lean_Syntax_node4(v___x_2104_, v___x_2106_, v___x_2096_, v___x_2109_, v___x_2126_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v_a_2087_);
return v___x_2146_;
}
}
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
