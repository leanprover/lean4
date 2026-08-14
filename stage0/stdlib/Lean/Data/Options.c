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
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqDataValue_beq___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDataValue_default;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_instInhabitedOptionDeprecation_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedOptionDeprecation_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__0 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__2 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__2_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__3 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__3_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__5 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__5_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__5_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__8 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__8_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__11 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__11_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Option.Decl"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__13 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__13_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Decl"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__15 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__15_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__15_value),LEAN_SCALAR_PTR_LITERAL(16, 81, 68, 143, 61, 155, 11, 11)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__17 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__17_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16_value)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__18 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__18_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__19 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__19_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__17_value),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__19_value)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__20 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__20_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__22 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__22_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__23 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__23_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__23_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__25 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__25_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__25_value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "structInstLVal"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__27 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__27_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__27_value),LEAN_SCALAR_PTR_LITERAL(185, 133, 6, 147, 6, 183, 100, 198)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "deprecation\?"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__29 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__29_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__29_value),LEAN_SCALAR_PTR_LITERAL(163, 80, 239, 206, 134, 73, 163, 23)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structInstFieldDef"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__32 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__32_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__32_value),LEAN_SCALAR_PTR_LITERAL(81, 102, 39, 227, 176, 252, 65, 103)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__34 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__34_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38_value_aux_0),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__39 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__39_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__40 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__40_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "since"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__41 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__41_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__41_value),LEAN_SCALAR_PTR_LITERAL(227, 79, 129, 16, 148, 113, 14, 88)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__43 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__43_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__44 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__44_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "text\?"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__45 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__45_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__45_value),LEAN_SCALAR_PTR_LITERAL(119, 11, 87, 192, 206, 66, 232, 28)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__47 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__47_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "newName\?"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__48 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__48_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__48_value),LEAN_SCALAR_PTR_LITERAL(77, 105, 171, 104, 123, 82, 208, 222)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__50 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__50_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optEllipsis"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__51 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__51_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__51_value),LEAN_SCALAR_PTR_LITERAL(13, 1, 242, 203, 207, 188, 181, 160)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__53 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__53_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__57 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__57_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__58 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__58_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__58_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__60 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__60_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__62 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__62_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__62_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__64 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__64_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value_aux_2),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__64_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66_value;
static lean_once_cell_t l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__68 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__68_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value_aux_1),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66_value),LEAN_SCALAR_PTR_LITERAL(189, 181, 26, 9, 96, 98, 157, 222)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__70 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__70_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__70_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__71 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__71_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__72 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__72_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__72_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__73 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__73_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\"\""};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__74 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__74_value;
static const lean_string_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75_value;
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76_value_aux_0),((lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75_value),LEAN_SCALAR_PTR_LITERAL(71, 123, 37, 172, 84, 157, 83, 143)}};
static const lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76 = (const lean_object*)&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value;
static const lean_closure_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value)} };
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 172, .m_capacity = 172, .m_length = 171, .m_data = "do not set the `deprecation\?` field directly; it is an internal implementation detail. Deprecate the option with a `@[deprecated \"...\" (since := \"...\")]` attribute instead"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 107, .m_capacity = 107, .m_length = 106, .m_data = "remove the `deprecation\?` field: it is populated automatically from the option's `@[deprecated]` attribute"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3_value;
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
lean_dec_ref_known(v___x_157_, 1);
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
lean_dec_ref_known(v___x_171_, 1);
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
lean_dec_ref_known(v___x_186_, 1);
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
lean_dec_ref_known(v___x_188_, 1);
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
lean_dec_ref_known(v___x_202_, 1);
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
lean_dec_ref_known(v___x_204_, 1);
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
lean_dec_ref_known(v___x_216_, 1);
if (lean_obj_tag(v_val_217_) == 1)
{
uint8_t v_v_218_; 
v_v_218_ = lean_ctor_get_uint8(v_val_217_, 0);
lean_dec_ref_known(v_val_217_, 0);
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
v___x_360_ = lean_nat_add(v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec(v___y_358_);
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
lean_ctor_set(v___x_340_, 3, v___y_357_);
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
lean_ctor_set(v_reuseFailAlloc_365_, 3, v___y_357_);
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
v___y_357_ = v___x_371_;
v___y_358_ = v___x_372_;
v___y_359_ = v_size_373_;
goto v___jp_356_;
}
else
{
lean_object* v___x_374_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___y_357_ = v___x_371_;
v___y_358_ = v___x_372_;
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
v___x_687_ = lean_nat_add(v___y_684_, v___y_686_);
lean_dec(v___y_686_);
lean_dec(v___y_684_);
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
lean_ctor_set(v___x_691_, 3, v___y_685_);
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
lean_ctor_set(v_reuseFailAlloc_695_, 3, v___y_685_);
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
v___y_684_ = v___x_709_;
v___y_685_ = v___x_708_;
v___y_686_ = v_size_710_;
goto v___jp_683_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_unsigned_to_nat(0u);
v___y_684_ = v___x_709_;
v___y_685_ = v___x_708_;
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
lean_dec_ref_known(v_x_1050_, 5);
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
uint8_t v___x_1218_; 
v___x_1218_ = l_Lean_initializing();
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v_decl_1216_);
lean_dec(v_name_1215_);
v___x_1219_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1221_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1222_ = lean_st_ref_get(v___x_1221_);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1215_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1215_, v_decl_1216_, v___x_1222_);
v___x_1225_ = lean_st_ref_swap(v___x_1221_, v___x_1224_);
lean_dec(v___x_1225_);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v___x_1222_);
lean_dec_ref(v_decl_1216_);
v___x_1228_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1215_, v___x_1223_);
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_mk_io_user_error(v___x_1232_);
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1235_, lean_object* v_decl_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = lean_register_option(v_name_1235_, v_decl_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1241_ = lean_st_ref_get(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_getOptionDecls();
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* v_init_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v_k_1247_; lean_object* v_v_1248_; lean_object* v_l_1249_; lean_object* v_r_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_k_1247_ = lean_ctor_get(v_x_1246_, 1);
v_v_1248_ = lean_ctor_get(v_x_1246_, 2);
v_l_1249_ = lean_ctor_get(v_x_1246_, 3);
v_r_1250_ = lean_ctor_get(v_x_1246_, 4);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1245_, v_l_1249_);
lean_inc(v_v_1248_);
lean_inc(v_k_1247_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_k_1247_);
lean_ctor_set(v___x_1252_, 1, v_v_1248_);
v___x_1253_ = lean_array_push(v___x_1251_, v___x_1252_);
v_init_1245_ = v___x_1253_;
v_x_1246_ = v_r_1250_;
goto _start;
}
else
{
return v_init_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* v_init_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1255_, v_x_1256_);
lean_dec(v_x_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(){
_start:
{
lean_object* v___x_1261_; lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1271_; 
v___x_1261_ = l_Lean_getOptionDecls();
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1271_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1266_ = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_1266_, v_a_1262_);
lean_dec(v_a_1262_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = lean_get_option_decls_array();
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* v_init_1274_, lean_object* v_t_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1274_, v_t_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* v_init_1277_, lean_object* v_t_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(v_init_1277_, v_t_1278_);
lean_dec(v_t_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* v_name_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1304_; 
v___x_1284_ = l_Lean_getOptionDecls();
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1285_, v_name_1282_);
lean_dec(v_a_1285_);
if (lean_obj_tag(v___x_1289_) == 1)
{
lean_object* v_val_1290_; lean_object* v___x_1292_; 
lean_dec(v_name_1282_);
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1289_, 1);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_val_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_val_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec(v___x_1289_);
v___x_1294_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1295_ = 1;
v___x_1296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1282_, v___x_1295_);
v___x_1297_ = lean_string_append(v___x_1294_, v___x_1296_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1299_ = lean_string_append(v___x_1297_, v___x_1298_);
v___x_1300_ = lean_mk_io_user_error(v___x_1299_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 1);
lean_ctor_set(v___x_1287_, 0, v___x_1300_);
v___x_1302_ = v___x_1287_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_getOptionDecl(v_name_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_getOptionDecl(v_name_1308_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_defValue_1315_; lean_object* v___x_1317_; 
v_defValue_1315_ = lean_ctor_get(v_a_1311_, 2);
lean_inc_ref(v_defValue_1315_);
lean_dec(v_a_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_defValue_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_defValue_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_a_1320_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1310_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1310_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_getOptionDefaultValue(v_name_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* v_name_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_getOptionDecl(v_name_1331_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1342_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_descr_1338_; lean_object* v___x_1340_; 
v_descr_1338_ = lean_ctor_get(v_a_1334_, 3);
lean_inc_ref(v_descr_1338_);
lean_dec(v_a_1334_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_descr_1338_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_descr_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1333_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1333_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_getOptionDescr(v_name_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1354_, lean_object* v_inst_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_apply_2(v_inst_1354_, lean_box(0), v_inst_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1357_, lean_object* v_n_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_apply_2(v_inst_1359_, lean_box(0), v_inst_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1362_, lean_object* v_toPure_1363_, uint8_t v_defValue_1364_, lean_object* v_opts_1365_){
_start:
{
lean_object* v_map_1366_; lean_object* v___x_1367_; 
v_map_1366_ = lean_ctor_get(v_opts_1365_, 0);
v___x_1367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1366_, v_k_1362_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(v_defValue_1364_);
v___x_1369_ = lean_apply_2(v_toPure_1363_, lean_box(0), v___x_1368_);
return v___x_1369_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1367_, 1);
if (lean_obj_tag(v_val_1370_) == 1)
{
uint8_t v_v_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_v_1371_ = lean_ctor_get_uint8(v_val_1370_, 0);
lean_dec_ref_known(v_val_1370_, 0);
v___x_1372_ = lean_box(v_v_1371_);
v___x_1373_ = lean_apply_2(v_toPure_1363_, lean_box(0), v___x_1372_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec(v_val_1370_);
v___x_1374_ = lean_box(v_defValue_1364_);
v___x_1375_ = lean_apply_2(v_toPure_1363_, lean_box(0), v___x_1374_);
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1376_, lean_object* v_toPure_1377_, lean_object* v_defValue_1378_, lean_object* v_opts_1379_){
_start:
{
uint8_t v_defValue_boxed_1380_; lean_object* v_res_1381_; 
v_defValue_boxed_1380_ = lean_unbox(v_defValue_1378_);
v_res_1381_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1376_, v_toPure_1377_, v_defValue_boxed_1380_, v_opts_1379_);
lean_dec_ref(v_opts_1379_);
lean_dec(v_k_1376_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_k_1384_, uint8_t v_defValue_1385_){
_start:
{
lean_object* v_toApplicative_1386_; lean_object* v_toBind_1387_; lean_object* v_toPure_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
v_toApplicative_1386_ = lean_ctor_get(v_inst_1382_, 0);
lean_inc_ref(v_toApplicative_1386_);
v_toBind_1387_ = lean_ctor_get(v_inst_1382_, 1);
lean_inc(v_toBind_1387_);
lean_dec_ref(v_inst_1382_);
v_toPure_1388_ = lean_ctor_get(v_toApplicative_1386_, 1);
lean_inc(v_toPure_1388_);
lean_dec_ref(v_toApplicative_1386_);
v___x_1389_ = lean_box(v_defValue_1385_);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1390_, 0, v_k_1384_);
lean_closure_set(v___f_1390_, 1, v_toPure_1388_);
lean_closure_set(v___f_1390_, 2, v___x_1389_);
v___x_1391_ = lean_apply_4(v_toBind_1387_, lean_box(0), lean_box(0), v_inst_1383_, v___f_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_k_1394_, lean_object* v_defValue_1395_){
_start:
{
uint8_t v_defValue_boxed_1396_; lean_object* v_res_1397_; 
v_defValue_boxed_1396_ = lean_unbox(v_defValue_1395_);
v_res_1397_ = l_Lean_getBoolOption___redArg(v_inst_1392_, v_inst_1393_, v_k_1394_, v_defValue_boxed_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* v_m_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_k_1401_, uint8_t v_defValue_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_getBoolOption___redArg(v_inst_1399_, v_inst_1400_, v_k_1401_, v_defValue_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_k_1407_, lean_object* v_defValue_1408_){
_start:
{
uint8_t v_defValue_boxed_1409_; lean_object* v_res_1410_; 
v_defValue_boxed_1409_ = lean_unbox(v_defValue_1408_);
v_res_1410_ = l_Lean_getBoolOption(v_m_1404_, v_inst_1405_, v_inst_1406_, v_k_1407_, v_defValue_boxed_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1411_, lean_object* v_toPure_1412_, lean_object* v_defValue_1413_, lean_object* v_opts_1414_){
_start:
{
lean_object* v_map_1415_; lean_object* v___x_1416_; 
v_map_1415_ = lean_ctor_get(v_opts_1414_, 0);
v___x_1416_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1415_, v_k_1411_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_apply_2(v_toPure_1412_, lean_box(0), v_defValue_1413_);
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; 
v_val_1418_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v___x_1416_, 1);
if (lean_obj_tag(v_val_1418_) == 3)
{
lean_object* v_v_1419_; lean_object* v___x_1420_; 
lean_dec(v_defValue_1413_);
v_v_1419_ = lean_ctor_get(v_val_1418_, 0);
lean_inc(v_v_1419_);
lean_dec_ref_known(v_val_1418_, 1);
v___x_1420_ = lean_apply_2(v_toPure_1412_, lean_box(0), v_v_1419_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; 
lean_dec(v_val_1418_);
v___x_1421_ = lean_apply_2(v_toPure_1412_, lean_box(0), v_defValue_1413_);
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1422_, lean_object* v_toPure_1423_, lean_object* v_defValue_1424_, lean_object* v_opts_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_getNatOption___redArg___lam__0(v_k_1422_, v_toPure_1423_, v_defValue_1424_, v_opts_1425_);
lean_dec_ref(v_opts_1425_);
lean_dec(v_k_1422_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_k_1429_, lean_object* v_defValue_1430_){
_start:
{
lean_object* v_toApplicative_1431_; lean_object* v_toBind_1432_; lean_object* v_toPure_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; 
v_toApplicative_1431_ = lean_ctor_get(v_inst_1427_, 0);
lean_inc_ref(v_toApplicative_1431_);
v_toBind_1432_ = lean_ctor_get(v_inst_1427_, 1);
lean_inc(v_toBind_1432_);
lean_dec_ref(v_inst_1427_);
v_toPure_1433_ = lean_ctor_get(v_toApplicative_1431_, 1);
lean_inc(v_toPure_1433_);
lean_dec_ref(v_toApplicative_1431_);
v___f_1434_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1434_, 0, v_k_1429_);
lean_closure_set(v___f_1434_, 1, v_toPure_1433_);
lean_closure_set(v___f_1434_, 2, v_defValue_1430_);
v___x_1435_ = lean_apply_4(v_toBind_1432_, lean_box(0), lean_box(0), v_inst_1428_, v___f_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_k_1439_, lean_object* v_defValue_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_getNatOption___redArg(v_inst_1437_, v_inst_1438_, v_k_1439_, v_defValue_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1442_, lean_object* v_f_1443_, lean_object* v_00_u03b2_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_apply_3(v_inst_1442_, lean_box(0), v_f_1443_, v___y_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v_00_u03b1_1449_, lean_object* v_f_1450_, lean_object* v_x_1451_){
_start:
{
lean_object* v___f_1452_; lean_object* v___x_1453_; 
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1452_, 0, v_inst_1447_);
lean_closure_set(v___f_1452_, 1, v_f_1450_);
v___x_1453_ = lean_apply_3(v_inst_1448_, lean_box(0), v___f_1452_, v_x_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1454_, lean_object* v_inst_1455_){
_start:
{
lean_object* v___f_1456_; 
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1456_, 0, v_inst_1455_);
lean_closure_set(v___f_1456_, 1, v_inst_1454_);
return v___f_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1457_, lean_object* v_n_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_){
_start:
{
lean_object* v___f_1461_; 
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1461_, 0, v_inst_1460_);
lean_closure_set(v___f_1461_, 1, v_inst_1459_);
return v___f_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1465_, lean_object* v_o_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1468_ = 1;
v___x_1469_ = lean_box(v___x_1468_);
v___x_1470_ = l_Lean_Options_set___redArg(v___x_1465_, v_o_1466_, v___x_1467_, v___x_1469_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___f_1472_; 
v___x_1471_ = l_Lean_KVMap_instValueBool;
v___f_1472_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1472_, 0, v___x_1471_);
return v___f_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1473_, lean_object* v_x_1474_){
_start:
{
lean_object* v___f_1475_; lean_object* v___x_1476_; 
v___f_1475_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1476_ = lean_apply_3(v_inst_1473_, lean_box(0), v___f_1475_, v_x_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1477_, lean_object* v_00_u03b1_1478_, lean_object* v_inst_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_withInPattern___redArg(v_inst_1479_, v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1482_){
_start:
{
lean_object* v_map_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; 
v_map_1483_ = lean_ctor_get(v_o_1482_, 0);
v___x_1484_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1485_ = 0;
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1483_, v___x_1484_);
if (lean_obj_tag(v___x_1486_) == 0)
{
return v___x_1485_;
}
else
{
lean_object* v_val_1487_; 
v_val_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v___x_1486_, 1);
if (lean_obj_tag(v_val_1487_) == 1)
{
uint8_t v_v_1488_; 
v_v_1488_ = lean_ctor_get_uint8(v_val_1487_, 0);
lean_dec_ref_known(v_val_1487_, 0);
return v_v_1488_;
}
else
{
lean_dec(v_val_1487_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Lean_Options_getInPattern(v_o_1489_);
lean_dec_ref(v_o_1489_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v_inst_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1500_, lean_object* v_inst_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1503_, lean_object* v_opts_1504_, lean_object* v_opt_1505_){
_start:
{
lean_object* v_name_1506_; lean_object* v_map_1507_; lean_object* v_ofDataValue_x3f_1508_; lean_object* v___x_1509_; 
v_name_1506_ = lean_ctor_get(v_opt_1505_, 0);
v_map_1507_ = lean_ctor_get(v_opts_1504_, 0);
v_ofDataValue_x3f_1508_ = lean_ctor_get(v_inst_1503_, 1);
lean_inc_ref(v_ofDataValue_x3f_1508_);
lean_dec_ref(v_inst_1503_);
v___x_1509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1507_, v_name_1506_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v_ofDataValue_x3f_1508_);
v___x_1510_ = lean_box(0);
return v___x_1510_;
}
else
{
lean_object* v_val_1511_; lean_object* v___x_1512_; 
v_val_1511_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1512_ = lean_apply_1(v_ofDataValue_x3f_1508_, v_val_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1513_, lean_object* v_opts_1514_, lean_object* v_opt_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Option_get_x3f___redArg(v_inst_1513_, v_opts_1514_, v_opt_1515_);
lean_dec_ref(v_opt_1515_);
lean_dec_ref(v_opts_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1517_, lean_object* v_inst_1518_, lean_object* v_opts_1519_, lean_object* v_opt_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Option_get_x3f___redArg(v_inst_1518_, v_opts_1519_, v_opt_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1522_, lean_object* v_inst_1523_, lean_object* v_opts_1524_, lean_object* v_opt_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Option_get_x3f(v_00_u03b1_1522_, v_inst_1523_, v_opts_1524_, v_opt_1525_);
lean_dec_ref(v_opt_1525_);
lean_dec_ref(v_opts_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1527_, lean_object* v_opts_1528_, lean_object* v_opt_1529_){
_start:
{
lean_object* v_name_1530_; lean_object* v_defValue_1531_; lean_object* v_map_1532_; lean_object* v_ofDataValue_x3f_1533_; lean_object* v___x_1534_; 
v_name_1530_ = lean_ctor_get(v_opt_1529_, 0);
v_defValue_1531_ = lean_ctor_get(v_opt_1529_, 1);
v_map_1532_ = lean_ctor_get(v_opts_1528_, 0);
v_ofDataValue_x3f_1533_ = lean_ctor_get(v_inst_1527_, 1);
lean_inc_ref(v_ofDataValue_x3f_1533_);
lean_dec_ref(v_inst_1527_);
v___x_1534_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1532_, v_name_1530_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1533_);
lean_inc(v_defValue_1531_);
return v_defValue_1531_;
}
else
{
lean_object* v_val_1535_; lean_object* v___x_1536_; 
v_val_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = lean_apply_1(v_ofDataValue_x3f_1533_, v_val_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_inc(v_defValue_1531_);
return v_defValue_1531_;
}
else
{
lean_object* v_val_1537_; 
v_val_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v___x_1536_, 1);
return v_val_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1538_, lean_object* v_opts_1539_, lean_object* v_opt_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Option_get___redArg(v_inst_1538_, v_opts_1539_, v_opt_1540_);
lean_dec_ref(v_opt_1540_);
lean_dec_ref(v_opts_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1542_, lean_object* v_inst_1543_, lean_object* v_opts_1544_, lean_object* v_opt_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Option_get___redArg(v_inst_1543_, v_opts_1544_, v_opt_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_inst_1548_, lean_object* v_opts_1549_, lean_object* v_opt_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Option_get(v_00_u03b1_1547_, v_inst_1548_, v_opts_1549_, v_opt_1550_);
lean_dec_ref(v_opt_1550_);
lean_dec_ref(v_opts_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* v_opts_1552_, lean_object* v_name_1553_, uint8_t v_defValue_1554_){
_start:
{
lean_object* v_map_1555_; lean_object* v___x_1556_; 
v_map_1555_ = lean_ctor_get(v_opts_1552_, 0);
lean_inc(v_map_1555_);
lean_dec_ref(v_opts_1552_);
v___x_1556_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1555_, v_name_1553_);
lean_dec(v_name_1553_);
lean_dec(v_map_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
return v_defValue_1554_;
}
else
{
lean_object* v_val_1557_; 
v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_val_1557_);
lean_dec_ref_known(v___x_1556_, 1);
if (lean_obj_tag(v_val_1557_) == 1)
{
uint8_t v_v_1558_; 
v_v_1558_ = lean_ctor_get_uint8(v_val_1557_, 0);
lean_dec_ref_known(v_val_1557_, 0);
return v_v_1558_;
}
else
{
lean_dec(v_val_1557_);
return v_defValue_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* v_opts_1559_, lean_object* v_name_1560_, lean_object* v_defValue_1561_){
_start:
{
uint8_t v_defValue_boxed_1562_; uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_defValue_boxed_1562_ = lean_unbox(v_defValue_1561_);
v_res_1563_ = lean_options_get_bool(v_opts_1559_, v_name_1560_, v_defValue_boxed_1562_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* v_inst_1565_, lean_object* v_opt_1566_, lean_object* v_toPure_1567_, lean_object* v_____do__lift_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = l_Lean_Option_get___redArg(v_inst_1565_, v_____do__lift_1568_, v_opt_1566_);
v___x_1570_ = lean_apply_2(v_toPure_1567_, lean_box(0), v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* v_inst_1571_, lean_object* v_opt_1572_, lean_object* v_toPure_1573_, lean_object* v_____do__lift_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Option_getM___redArg___lam__0(v_inst_1571_, v_opt_1572_, v_toPure_1573_, v_____do__lift_1574_);
lean_dec_ref(v_____do__lift_1574_);
lean_dec_ref(v_opt_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_opt_1579_){
_start:
{
lean_object* v_toApplicative_1580_; lean_object* v_toBind_1581_; lean_object* v_toPure_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; 
v_toApplicative_1580_ = lean_ctor_get(v_inst_1576_, 0);
lean_inc_ref(v_toApplicative_1580_);
v_toBind_1581_ = lean_ctor_get(v_inst_1576_, 1);
lean_inc(v_toBind_1581_);
lean_dec_ref(v_inst_1576_);
v_toPure_1582_ = lean_ctor_get(v_toApplicative_1580_, 1);
lean_inc(v_toPure_1582_);
lean_dec_ref(v_toApplicative_1580_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1583_, 0, v_inst_1578_);
lean_closure_set(v___f_1583_, 1, v_opt_1579_);
lean_closure_set(v___f_1583_, 2, v_toPure_1582_);
v___x_1584_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v_inst_1577_, v___f_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* v_m_1585_, lean_object* v_00_u03b1_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_opt_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Option_getM___redArg(v_inst_1587_, v_inst_1588_, v_inst_1589_, v_opt_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* v_inst_1592_, lean_object* v_opts_1593_, lean_object* v_opt_1594_, lean_object* v_val_1595_){
_start:
{
lean_object* v_name_1596_; lean_object* v___x_1597_; 
v_name_1596_ = lean_ctor_get(v_opt_1594_, 0);
lean_inc(v_name_1596_);
lean_dec_ref(v_opt_1594_);
v___x_1597_ = l_Lean_Options_set___redArg(v_inst_1592_, v_opts_1593_, v_name_1596_, v_val_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* v_00_u03b1_1598_, lean_object* v_inst_1599_, lean_object* v_opts_1600_, lean_object* v_opt_1601_, lean_object* v_val_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Option_set___redArg(v_inst_1599_, v_opts_1600_, v_opt_1601_, v_val_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1604_, lean_object* v_k_1605_, uint8_t v_v_1606_){
_start:
{
lean_object* v_map_1607_; uint8_t v_hasTrace_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1622_; 
v_map_1607_ = lean_ctor_get(v_o_1604_, 0);
v_hasTrace_1608_ = lean_ctor_get_uint8(v_o_1604_, sizeof(void*)*1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_o_1604_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1610_ = v_o_1604_;
v_isShared_1611_ = v_isSharedCheck_1622_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_map_1607_);
lean_dec(v_o_1604_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1622_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1612_, 0, v_v_1606_);
lean_inc(v_k_1605_);
v___x_1613_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1605_, v___x_1612_, v_map_1607_);
if (v_hasTrace_1608_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1617_; 
v___x_1614_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_1615_ = l_Lean_Name_isPrefixOf(v___x_1614_, v_k_1605_);
lean_dec(v_k_1605_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1617_ = v___x_1610_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1613_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*1, v___x_1615_);
return v___x_1617_;
}
}
else
{
lean_object* v___x_1620_; 
lean_dec(v_k_1605_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1620_ = v___x_1610_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*1, v_hasTrace_1608_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1623_, lean_object* v_k_1624_, lean_object* v_v_1625_){
_start:
{
uint8_t v_v_boxed_1626_; lean_object* v_res_1627_; 
v_v_boxed_1626_ = lean_unbox(v_v_1625_);
v_res_1627_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1623_, v_k_1624_, v_v_boxed_1626_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* v_opts_1628_, lean_object* v_name_1629_, uint8_t v_val_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1628_, v_name_1629_, v_val_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1632_, lean_object* v_name_1633_, lean_object* v_val_1634_){
_start:
{
uint8_t v_val_boxed_1635_; lean_object* v_res_1636_; 
v_val_boxed_1635_ = lean_unbox(v_val_1634_);
v_res_1636_ = lean_options_update_bool(v_opts_1632_, v_name_1633_, v_val_boxed_1635_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1637_, lean_object* v_opts_1638_, lean_object* v_opt_1639_, lean_object* v_val_1640_){
_start:
{
lean_object* v_name_1641_; lean_object* v_map_1642_; uint8_t v___x_1643_; 
v_name_1641_ = lean_ctor_get(v_opt_1639_, 0);
v_map_1642_ = lean_ctor_get(v_opts_1638_, 0);
v___x_1643_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1641_, v_map_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Option_set___redArg(v_inst_1637_, v_opts_1638_, v_opt_1639_, v_val_1640_);
return v___x_1644_;
}
else
{
lean_dec(v_val_1640_);
lean_dec_ref(v_opt_1639_);
lean_dec_ref(v_inst_1637_);
return v_opts_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1645_, lean_object* v_inst_1646_, lean_object* v_opts_1647_, lean_object* v_opt_1648_, lean_object* v_val_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1646_, v_opts_1647_, v_opt_1648_, v_val_1649_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1652_, lean_object* v_name_1653_, lean_object* v_decl_1654_, lean_object* v_ref_1655_){
_start:
{
lean_object* v_toDataValue_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1686_; 
v_toDataValue_1657_ = lean_ctor_get(v_inst_1652_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_inst_1652_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_inst_1652_, 1);
lean_dec(v_unused_1687_);
v___x_1659_ = v_inst_1652_;
v_isShared_1660_ = v_isSharedCheck_1686_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_toDataValue_1657_);
lean_dec(v_inst_1652_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1686_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_defValue_1661_; lean_object* v_descr_1662_; lean_object* v_deprecation_x3f_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_defValue_1661_ = lean_ctor_get(v_decl_1654_, 0);
lean_inc_n(v_defValue_1661_, 2);
v_descr_1662_ = lean_ctor_get(v_decl_1654_, 1);
lean_inc_ref(v_descr_1662_);
v_deprecation_x3f_1663_ = lean_ctor_get(v_decl_1654_, 2);
lean_inc(v_deprecation_x3f_1663_);
lean_dec_ref(v_decl_1654_);
v___x_1664_ = lean_apply_1(v_toDataValue_1657_, v_defValue_1661_);
lean_inc_n(v_name_1653_, 2);
v___x_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1665_, 0, v_name_1653_);
lean_ctor_set(v___x_1665_, 1, v_ref_1655_);
lean_ctor_set(v___x_1665_, 2, v___x_1664_);
lean_ctor_set(v___x_1665_, 3, v_descr_1662_);
lean_ctor_set(v___x_1665_, 4, v_deprecation_x3f_1663_);
v___x_1666_ = lean_register_option(v_name_1653_, v___x_1665_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1676_; 
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1666_, 0);
lean_dec(v_unused_1677_);
v___x_1668_ = v___x_1666_;
v_isShared_1669_ = v_isSharedCheck_1676_;
goto v_resetjp_1667_;
}
else
{
lean_dec(v___x_1666_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1676_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_defValue_1661_);
lean_ctor_set(v___x_1659_, 0, v_name_1653_);
v___x_1671_ = v___x_1659_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_name_1653_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_defValue_1661_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1671_);
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_defValue_1661_);
lean_del_object(v___x_1659_);
lean_dec(v_name_1653_);
v_a_1678_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1666_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1666_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1688_, lean_object* v_name_1689_, lean_object* v_decl_1690_, lean_object* v_ref_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Option_register___redArg(v_inst_1688_, v_name_1689_, v_decl_1690_, v_ref_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1694_, lean_object* v_inst_1695_, lean_object* v_name_1696_, lean_object* v_decl_1697_, lean_object* v_ref_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Option_register___redArg(v_inst_1695_, v_name_1696_, v_decl_1697_, v_ref_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_inst_1702_, lean_object* v_name_1703_, lean_object* v_decl_1704_, lean_object* v_ref_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Option_register(v_00_u03b1_1701_, v_inst_1702_, v_name_1703_, v_decl_1704_, v_ref_1705_);
return v_res_1707_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
v___x_1796_ = l_String_toRawSubstring_x27(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
v___x_1817_ = l_String_toRawSubstring_x27(v___x_1816_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29(void){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Array_mkArray0(lean_box(0));
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* v_x_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_1849_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(v_x_1845_);
v___x_1850_ = l_Lean_Syntax_isOfKind(v_x_1845_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v_x_1845_);
v___x_1851_ = lean_box(1);
v___x_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v_a_1847_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_name_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1987_; lean_object* v___x_1998_; 
v___x_1853_ = lean_unsigned_to_nat(0u);
v___x_1854_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1853_);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1855_);
v___x_1857_ = lean_unsigned_to_nat(3u);
v_name_1858_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1857_);
v___x_1859_ = lean_unsigned_to_nat(5u);
v___x_1860_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1859_);
v___x_1861_ = lean_unsigned_to_nat(7u);
v___x_1862_ = l_Lean_Syntax_getArg(v_x_1845_, v___x_1861_);
lean_dec(v_x_1845_);
v___x_1998_ = l_Lean_Syntax_getOptional_x3f(v___x_1856_);
lean_dec(v___x_1856_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_box(0);
v___y_1987_ = v___x_1999_;
goto v___jp_1986_;
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_val_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_val_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_val_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v___y_1987_ = v___x_2005_;
goto v___jp_1986_;
}
}
}
v___jp_1863_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_inc_n(v___y_1874_, 2);
lean_inc_n(v___y_1872_, 6);
v___x_1877_ = l_Lean_Syntax_node2(v___y_1872_, v___y_1874_, v___y_1876_, v___x_1862_);
v___x_1878_ = l_Lean_Syntax_node2(v___y_1872_, v___y_1871_, v___y_1865_, v___x_1877_);
v___x_1879_ = l_Lean_Syntax_node1(v___y_1872_, v___y_1870_, v___x_1878_);
v___x_1880_ = l_Lean_Syntax_node2(v___y_1872_, v___y_1873_, v___x_1879_, v___y_1869_);
v___x_1881_ = l_Lean_Syntax_node1(v___y_1872_, v___y_1874_, v___x_1880_);
v___x_1882_ = l_Lean_Syntax_node1(v___y_1872_, v___y_1875_, v___x_1881_);
lean_inc(v___y_1867_);
v___x_1883_ = l_Lean_Syntax_node4(v___y_1872_, v___y_1867_, v___y_1868_, v___y_1864_, v___y_1866_, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v_a_1847_);
return v___x_1884_;
}
v___jp_1885_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_inc_ref(v___y_1891_);
v___x_1898_ = l_Array_append___redArg(v___y_1891_, v___y_1897_);
lean_dec_ref(v___y_1897_);
lean_inc_n(v___y_1893_, 3);
lean_inc_n(v___y_1892_, 12);
v___x_1899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1899_, 0, v___y_1892_);
lean_ctor_set(v___x_1899_, 1, v___y_1893_);
lean_ctor_set(v___x_1899_, 2, v___x_1898_);
lean_inc_n(v___y_1889_, 5);
lean_inc(v___y_1886_);
v___x_1900_ = l_Lean_Syntax_node7(v___y_1892_, v___y_1886_, v___y_1890_, v___y_1889_, v___x_1899_, v___y_1889_, v___y_1889_, v___y_1889_, v___y_1889_);
v___x_1901_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_1895_);
lean_inc_ref_n(v___y_1896_, 6);
v___x_1902_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___y_1895_, v___x_1901_);
v___x_1903_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
v___x_1904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___y_1892_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_Syntax_node1(v___y_1892_, v___x_1902_, v___x_1904_);
v___x_1906_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_1907_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_1908_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___x_1906_, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___y_1892_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_1912_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___x_1906_, v___x_1911_);
v___x_1913_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_1914_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v___y_1894_, 2);
lean_inc_n(v___y_1888_, 2);
v___x_1915_ = l_Lean_addMacroScope(v___y_1888_, v___x_1914_, v___y_1894_);
v___x_1916_ = lean_box(0);
v___x_1917_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_1918_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1918_, 0, v___y_1892_);
lean_ctor_set(v___x_1918_, 1, v___x_1913_);
lean_ctor_set(v___x_1918_, 2, v___x_1915_);
lean_ctor_set(v___x_1918_, 3, v___x_1917_);
v___x_1919_ = l_Lean_Syntax_node1(v___y_1892_, v___y_1893_, v___x_1860_);
lean_inc(v___x_1912_);
v___x_1920_ = l_Lean_Syntax_node2(v___y_1892_, v___x_1912_, v___x_1918_, v___x_1919_);
v___x_1921_ = l_Lean_Syntax_node2(v___y_1892_, v___x_1908_, v___x_1910_, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_1923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___y_1892_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_inc(v_name_1858_);
v___x_1924_ = l_Lean_Syntax_node3(v___y_1892_, v___y_1893_, v_name_1858_, v___x_1921_, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_1926_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___x_1906_, v___x_1925_);
v___x_1927_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_1928_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___x_1906_, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_1930_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___x_1906_, v___x_1929_);
v___x_1931_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_1932_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_1933_ = l_Lean_addMacroScope(v___y_1888_, v___x_1932_, v___y_1894_);
v___x_1934_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_1935_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1935_, 0, v___y_1892_);
lean_ctor_set(v___x_1935_, 1, v___x_1931_);
lean_ctor_set(v___x_1935_, 2, v___x_1933_);
lean_ctor_set(v___x_1935_, 3, v___x_1934_);
v___x_1936_ = l_Lean_TSyntax_getId(v_name_1858_);
lean_dec(v_name_1858_);
lean_inc(v___x_1936_);
v___x_1937_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1916_, v___x_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_quoteNameMk(v___x_1936_);
v___y_1864_ = v___x_1905_;
v___y_1865_ = v___x_1935_;
v___y_1866_ = v___x_1924_;
v___y_1867_ = v___y_1887_;
v___y_1868_ = v___x_1900_;
v___y_1869_ = v___y_1889_;
v___y_1870_ = v___x_1930_;
v___y_1871_ = v___x_1912_;
v___y_1872_ = v___y_1892_;
v___y_1873_ = v___x_1928_;
v___y_1874_ = v___y_1893_;
v___y_1875_ = v___x_1926_;
v___y_1876_ = v___x_1938_;
goto v___jp_1863_;
}
else
{
lean_object* v_val_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec(v___x_1936_);
v_val_1939_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1940_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
lean_inc_ref(v___y_1896_);
v___x_1941_ = l_Lean_Name_mkStr4(v___x_1848_, v___y_1896_, v___x_1906_, v___x_1940_);
v___x_1942_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1943_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_1944_ = lean_string_intercalate(v___x_1943_, v_val_1939_);
v___x_1945_ = lean_string_append(v___x_1942_, v___x_1944_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = lean_box(2);
v___x_1947_ = l_Lean_Syntax_mkNameLit(v___x_1945_, v___x_1946_);
v___x_1948_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1949_ = lean_array_push(v___x_1948_, v___x_1947_);
v___x_1950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1946_);
lean_ctor_set(v___x_1950_, 1, v___x_1941_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
v___y_1864_ = v___x_1905_;
v___y_1865_ = v___x_1935_;
v___y_1866_ = v___x_1924_;
v___y_1867_ = v___y_1887_;
v___y_1868_ = v___x_1900_;
v___y_1869_ = v___y_1889_;
v___y_1870_ = v___x_1930_;
v___y_1871_ = v___x_1912_;
v___y_1872_ = v___y_1892_;
v___y_1873_ = v___x_1928_;
v___y_1874_ = v___y_1893_;
v___y_1875_ = v___x_1926_;
v___y_1876_ = v___x_1950_;
goto v___jp_1863_;
}
}
v___jp_1951_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_ref_n(v___y_1956_, 2);
v___x_1963_ = l_Array_append___redArg(v___y_1956_, v___y_1962_);
lean_dec_ref(v___y_1962_);
lean_inc_n(v___y_1958_, 2);
lean_inc_n(v___y_1957_, 2);
v___x_1964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1964_, 0, v___y_1957_);
lean_ctor_set(v___x_1964_, 1, v___y_1958_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1965_, 0, v___y_1957_);
lean_ctor_set(v___x_1965_, 1, v___y_1958_);
lean_ctor_set(v___x_1965_, 2, v___y_1956_);
if (lean_obj_tag(v___y_1953_) == 1)
{
lean_object* v_val_1966_; lean_object* v___x_1967_; 
v_val_1966_ = lean_ctor_get(v___y_1953_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v___y_1953_, 1);
v___x_1967_ = l_Array_mkArray1___redArg(v_val_1966_);
v___y_1886_ = v___y_1952_;
v___y_1887_ = v___y_1954_;
v___y_1888_ = v___y_1955_;
v___y_1889_ = v___x_1965_;
v___y_1890_ = v___x_1964_;
v___y_1891_ = v___y_1956_;
v___y_1892_ = v___y_1957_;
v___y_1893_ = v___y_1958_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v___y_1961_;
v___y_1896_ = v___y_1960_;
v___y_1897_ = v___x_1967_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_1968_; 
lean_dec(v___y_1953_);
v___x_1968_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1886_ = v___y_1952_;
v___y_1887_ = v___y_1954_;
v___y_1888_ = v___y_1955_;
v___y_1889_ = v___x_1965_;
v___y_1890_ = v___x_1964_;
v___y_1891_ = v___y_1956_;
v___y_1892_ = v___y_1957_;
v___y_1893_ = v___y_1958_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v___y_1961_;
v___y_1896_ = v___y_1960_;
v___y_1897_ = v___x_1968_;
goto v___jp_1885_;
}
}
v___jp_1969_:
{
lean_object* v_quotContext_1972_; lean_object* v_currMacroScope_1973_; lean_object* v_ref_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_quotContext_1972_ = lean_ctor_get(v_a_1846_, 1);
v_currMacroScope_1973_ = lean_ctor_get(v_a_1846_, 2);
v_ref_1974_ = lean_ctor_get(v_a_1846_, 5);
v___x_1975_ = 0;
v___x_1976_ = l_Lean_SourceInfo_fromRef(v_ref_1974_, v___x_1975_);
v___x_1977_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_1978_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_1979_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_1980_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28));
v___x_1981_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1982_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
if (lean_obj_tag(v___y_1971_) == 1)
{
lean_object* v_val_1983_; lean_object* v___x_1984_; 
v_val_1983_ = lean_ctor_get(v___y_1971_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v___y_1971_, 1);
v___x_1984_ = l_Array_mkArray1___redArg(v_val_1983_);
v___y_1952_ = v___x_1980_;
v___y_1953_ = v___y_1970_;
v___y_1954_ = v___x_1979_;
v___y_1955_ = v_quotContext_1972_;
v___y_1956_ = v___x_1982_;
v___y_1957_ = v___x_1976_;
v___y_1958_ = v___x_1981_;
v___y_1959_ = v_currMacroScope_1973_;
v___y_1960_ = v___x_1977_;
v___y_1961_ = v___x_1978_;
v___y_1962_ = v___x_1984_;
goto v___jp_1951_;
}
else
{
lean_object* v___x_1985_; 
lean_dec(v___y_1971_);
v___x_1985_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1952_ = v___x_1980_;
v___y_1953_ = v___y_1970_;
v___y_1954_ = v___x_1979_;
v___y_1955_ = v_quotContext_1972_;
v___y_1956_ = v___x_1982_;
v___y_1957_ = v___x_1976_;
v___y_1958_ = v___x_1981_;
v___y_1959_ = v_currMacroScope_1973_;
v___y_1960_ = v___x_1977_;
v___y_1961_ = v___x_1978_;
v___y_1962_ = v___x_1985_;
goto v___jp_1951_;
}
}
v___jp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Syntax_getOptional_x3f(v___x_1854_);
lean_dec(v___x_1854_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_box(0);
v___y_1970_ = v___y_1987_;
v___y_1971_ = v___x_1989_;
goto v___jp_1969_;
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_val_1990_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1988_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_val_1990_);
lean_dec(v___x_1988_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_val_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
v___y_1970_ = v___y_1987_;
v___y_1971_ = v___x_1995_;
goto v___jp_1969_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(lean_object* v_x_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2011_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_instInhabitedOptionDeprecation_default___closed__0));
v___x_2036_ = l_String_toRawSubstring_x27(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__13));
v___x_2047_ = l_String_toRawSubstring_x27(v___x_2046_);
return v___x_2047_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__29));
v___x_2086_ = l_String_toRawSubstring_x27(v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35));
v___x_2098_ = l_String_toRawSubstring_x27(v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__41));
v___x_2112_ = l_String_toRawSubstring_x27(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__45));
v___x_2118_ = l_String_toRawSubstring_x27(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__48));
v___x_2123_ = l_String_toRawSubstring_x27(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54));
v___x_2135_ = l_String_toRawSubstring_x27(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66));
v___x_2167_ = l_String_toRawSubstring_x27(v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(lean_object* v_attr_2188_, lean_object* v_type_2189_, lean_object* v_decl_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v_newName_2196_; lean_object* v_quotContext_2197_; lean_object* v_currMacroScope_2198_; lean_object* v_ref_2199_; lean_object* v___y_2200_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v_text_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v_since_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76));
lean_inc(v_attr_2188_);
v___x_2405_ = l_Lean_Syntax_isOfKind(v_attr_2188_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
lean_dec(v_type_2189_);
lean_dec(v_attr_2188_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_decl_2190_);
lean_ctor_set(v___x_2406_, 1, v_a_2192_);
return v___x_2406_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___y_2410_; lean_object* v_text_x3f_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v_id_x3f_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2407_ = lean_unsigned_to_nat(0u);
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2431_ = l_Lean_Syntax_getArg(v_attr_2188_, v___x_2408_);
v___x_2432_ = l_Lean_Syntax_isNone(v___x_2431_);
if (v___x_2432_ == 0)
{
uint8_t v___x_2433_; 
lean_inc(v___x_2431_);
v___x_2433_ = l_Lean_Syntax_matchesNull(v___x_2431_, v___x_2408_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; 
lean_dec(v___x_2431_);
lean_dec(v_type_2189_);
lean_dec(v_attr_2188_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_decl_2190_);
lean_ctor_set(v___x_2434_, 1, v_a_2192_);
return v___x_2434_;
}
else
{
lean_object* v_id_x3f_2435_; lean_object* v___x_2436_; 
v_id_x3f_2435_ = l_Lean_Syntax_getArg(v___x_2431_, v___x_2407_);
lean_dec(v___x_2431_);
v___x_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_id_x3f_2435_);
v_id_x3f_2420_ = v___x_2436_;
v___y_2421_ = v_a_2191_;
v___y_2422_ = v_a_2192_;
goto v___jp_2419_;
}
}
else
{
lean_object* v___x_2437_; 
lean_dec(v___x_2431_);
v___x_2437_ = lean_box(0);
v_id_x3f_2420_ = v___x_2437_;
v___y_2421_ = v_a_2191_;
v___y_2422_ = v_a_2192_;
goto v___jp_2419_;
}
v___jp_2409_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2414_ = lean_unsigned_to_nat(3u);
v___x_2415_ = l_Lean_Syntax_getArg(v_attr_2188_, v___x_2414_);
v___x_2416_ = l_Lean_Syntax_isNone(v___x_2415_);
if (v___x_2416_ == 0)
{
uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_Syntax_matchesNull(v___x_2415_, v___x_2408_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
lean_dec(v_text_x3f_2411_);
lean_dec(v___y_2410_);
lean_dec(v_type_2189_);
lean_dec(v_attr_2188_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_decl_2190_);
lean_ctor_set(v___x_2418_, 1, v___y_2413_);
return v___x_2418_;
}
else
{
v___y_2385_ = v___y_2410_;
v___y_2386_ = v_text_x3f_2411_;
v___y_2387_ = v___x_2414_;
v___y_2388_ = v___y_2412_;
v___y_2389_ = v___y_2413_;
goto v___jp_2384_;
}
}
else
{
lean_dec(v___x_2415_);
v___y_2385_ = v___y_2410_;
v___y_2386_ = v_text_x3f_2411_;
v___y_2387_ = v___x_2414_;
v___y_2388_ = v___y_2412_;
v___y_2389_ = v___y_2413_;
goto v___jp_2384_;
}
}
v___jp_2419_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2423_ = lean_unsigned_to_nat(2u);
v___x_2424_ = l_Lean_Syntax_getArg(v_attr_2188_, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_isNone(v___x_2424_);
if (v___x_2425_ == 0)
{
uint8_t v___x_2426_; 
lean_inc(v___x_2424_);
v___x_2426_ = l_Lean_Syntax_matchesNull(v___x_2424_, v___x_2408_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_dec(v___x_2424_);
lean_dec(v_id_x3f_2420_);
lean_dec(v_type_2189_);
lean_dec(v_attr_2188_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_decl_2190_);
lean_ctor_set(v___x_2427_, 1, v___y_2422_);
return v___x_2427_;
}
else
{
lean_object* v_text_x3f_2428_; lean_object* v___x_2429_; 
v_text_x3f_2428_ = l_Lean_Syntax_getArg(v___x_2424_, v___x_2407_);
lean_dec(v___x_2424_);
v___x_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_text_x3f_2428_);
v___y_2410_ = v_id_x3f_2420_;
v_text_x3f_2411_ = v___x_2429_;
v___y_2412_ = v___y_2421_;
v___y_2413_ = v___y_2422_;
goto v___jp_2409_;
}
}
else
{
lean_object* v___x_2430_; 
lean_dec(v___x_2424_);
v___x_2430_ = lean_box(0);
v___y_2410_ = v_id_x3f_2420_;
v_text_x3f_2411_ = v___x_2430_;
v___y_2412_ = v___y_2421_;
v___y_2413_ = v___y_2422_;
goto v___jp_2409_;
}
}
}
v___jp_2193_:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2201_ = 0;
v___x_2202_ = l_Lean_SourceInfo_fromRef(v_ref_2199_, v___x_2201_);
v___x_2203_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1));
v___x_2204_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__2));
lean_inc_n(v___x_2202_, 48);
v___x_2205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2202_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2207_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4));
v___x_2208_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6));
v___x_2209_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7));
v___x_2210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2202_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9));
v___x_2212_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10);
v___x_2213_ = lean_box(0);
lean_inc_n(v_currMacroScope_2198_, 6);
lean_inc_n(v_quotContext_2197_, 6);
v___x_2214_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2213_, v_currMacroScope_2198_);
v___x_2215_ = lean_box(0);
v___x_2216_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__11));
v___x_2217_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2202_);
lean_ctor_set(v___x_2217_, 1, v___x_2212_);
lean_ctor_set(v___x_2217_, 2, v___x_2214_);
lean_ctor_set(v___x_2217_, 3, v___x_2216_);
v___x_2218_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2211_, v___x_2217_);
v___x_2219_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2208_, v___x_2210_, v___x_2218_);
v___x_2220_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2202_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12));
v___x_2223_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14);
v___x_2224_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16));
v___x_2225_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2224_, v_currMacroScope_2198_);
v___x_2226_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__20));
v___x_2227_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2202_);
lean_ctor_set(v___x_2227_, 1, v___x_2223_);
lean_ctor_set(v___x_2227_, 2, v___x_2225_);
lean_ctor_set(v___x_2227_, 3, v___x_2226_);
v___x_2228_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2206_, v_type_2189_);
v___x_2229_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2222_, v___x_2227_, v___x_2228_);
v___x_2230_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2206_, v___x_2229_);
v___x_2231_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21));
v___x_2232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2202_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_Syntax_node5(v___x_2202_, v___x_2207_, v___x_2219_, v_decl_2190_, v___x_2221_, v___x_2230_, v___x_2232_);
v___x_2234_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2206_, v___x_2233_);
v___x_2235_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__22));
v___x_2236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2202_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2206_, v___x_2234_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24));
v___x_2239_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26));
v___x_2240_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28));
v___x_2241_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30);
v___x_2242_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31));
v___x_2243_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2242_, v_currMacroScope_2198_);
v___x_2244_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2202_);
lean_ctor_set(v___x_2244_, 1, v___x_2241_);
lean_ctor_set(v___x_2244_, 2, v___x_2243_);
lean_ctor_set(v___x_2244_, 3, v___x_2215_);
v___x_2245_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2202_);
lean_ctor_set(v___x_2246_, 1, v___x_2206_);
lean_ctor_set(v___x_2246_, 2, v___x_2245_);
lean_inc_ref_n(v___x_2246_, 19);
v___x_2247_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2240_, v___x_2244_, v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33));
v___x_2249_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__34));
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2202_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36);
v___x_2252_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37));
v___x_2253_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2252_, v_currMacroScope_2198_);
v___x_2254_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__40));
v___x_2255_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2202_);
lean_ctor_set(v___x_2255_, 1, v___x_2251_);
lean_ctor_set(v___x_2255_, 2, v___x_2253_);
lean_ctor_set(v___x_2255_, 3, v___x_2254_);
v___x_2256_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42);
v___x_2257_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__43));
v___x_2258_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2257_, v_currMacroScope_2198_);
v___x_2259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2202_);
lean_ctor_set(v___x_2259_, 1, v___x_2256_);
lean_ctor_set(v___x_2259_, 2, v___x_2258_);
lean_ctor_set(v___x_2259_, 3, v___x_2215_);
v___x_2260_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2240_, v___x_2259_, v___x_2246_);
lean_inc_ref_n(v___x_2250_, 3);
v___x_2261_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2248_, v___x_2250_, v___x_2246_, v___y_2195_);
v___x_2262_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2206_, v___x_2246_, v___x_2246_, v___x_2261_);
v___x_2263_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2239_, v___x_2260_, v___x_2262_);
v___x_2264_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__44));
v___x_2265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2202_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46);
v___x_2267_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__47));
v___x_2268_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2267_, v_currMacroScope_2198_);
v___x_2269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2202_);
lean_ctor_set(v___x_2269_, 1, v___x_2266_);
lean_ctor_set(v___x_2269_, 2, v___x_2268_);
lean_ctor_set(v___x_2269_, 3, v___x_2215_);
v___x_2270_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2240_, v___x_2269_, v___x_2246_);
v___x_2271_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2248_, v___x_2250_, v___x_2246_, v___y_2194_);
v___x_2272_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2206_, v___x_2246_, v___x_2246_, v___x_2271_);
v___x_2273_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2239_, v___x_2270_, v___x_2272_);
v___x_2274_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49);
v___x_2275_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__50));
v___x_2276_ = l_Lean_addMacroScope(v_quotContext_2197_, v___x_2275_, v_currMacroScope_2198_);
v___x_2277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2202_);
lean_ctor_set(v___x_2277_, 1, v___x_2274_);
lean_ctor_set(v___x_2277_, 2, v___x_2276_);
lean_ctor_set(v___x_2277_, 3, v___x_2215_);
v___x_2278_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2240_, v___x_2277_, v___x_2246_);
v___x_2279_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2248_, v___x_2250_, v___x_2246_, v_newName_2196_);
v___x_2280_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2206_, v___x_2246_, v___x_2246_, v___x_2279_);
v___x_2281_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2239_, v___x_2278_, v___x_2280_);
lean_inc_ref(v___x_2265_);
v___x_2282_ = l_Lean_Syntax_node5(v___x_2202_, v___x_2206_, v___x_2263_, v___x_2265_, v___x_2273_, v___x_2265_, v___x_2281_);
v___x_2283_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2238_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52));
v___x_2285_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2284_, v___x_2246_);
v___x_2286_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__53));
v___x_2287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2202_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
lean_inc_ref(v___x_2287_);
lean_inc(v___x_2285_);
lean_inc_ref(v___x_2205_);
v___x_2288_ = l_Lean_Syntax_node6(v___x_2202_, v___x_2203_, v___x_2205_, v___x_2246_, v___x_2283_, v___x_2285_, v___x_2246_, v___x_2287_);
v___x_2289_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2206_, v___x_2288_);
v___x_2290_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2222_, v___x_2255_, v___x_2289_);
v___x_2291_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2248_, v___x_2250_, v___x_2246_, v___x_2290_);
v___x_2292_ = l_Lean_Syntax_node3(v___x_2202_, v___x_2206_, v___x_2246_, v___x_2246_, v___x_2291_);
v___x_2293_ = l_Lean_Syntax_node2(v___x_2202_, v___x_2239_, v___x_2247_, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2206_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_node1(v___x_2202_, v___x_2238_, v___x_2294_);
v___x_2296_ = l_Lean_Syntax_node6(v___x_2202_, v___x_2203_, v___x_2205_, v___x_2237_, v___x_2295_, v___x_2285_, v___x_2246_, v___x_2287_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v___y_2200_);
return v___x_2297_;
}
v___jp_2298_:
{
if (lean_obj_tag(v___y_2299_) == 0)
{
lean_object* v_quotContext_2304_; lean_object* v_currMacroScope_2305_; lean_object* v_ref_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_quotContext_2304_ = lean_ctor_get(v___y_2302_, 1);
v_currMacroScope_2305_ = lean_ctor_get(v___y_2302_, 2);
v_ref_2306_ = lean_ctor_get(v___y_2302_, 5);
v___x_2307_ = 0;
v___x_2308_ = l_Lean_SourceInfo_fromRef(v_ref_2306_, v___x_2307_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55);
v___x_2310_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56));
lean_inc_n(v_currMacroScope_2305_, 2);
lean_inc_n(v_quotContext_2304_, 2);
v___x_2311_ = l_Lean_addMacroScope(v_quotContext_2304_, v___x_2310_, v_currMacroScope_2305_);
v___x_2312_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59));
v___x_2313_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2308_);
lean_ctor_set(v___x_2313_, 1, v___x_2309_);
lean_ctor_set(v___x_2313_, 2, v___x_2311_);
lean_ctor_set(v___x_2313_, 3, v___x_2312_);
v___y_2194_ = v_text_2301_;
v___y_2195_ = v___y_2300_;
v_newName_2196_ = v___x_2313_;
v_quotContext_2197_ = v_quotContext_2304_;
v_currMacroScope_2198_ = v_currMacroScope_2305_;
v_ref_2199_ = v_ref_2306_;
v___y_2200_ = v___y_2303_;
goto v___jp_2193_;
}
else
{
lean_object* v_val_2314_; lean_object* v_quotContext_2315_; lean_object* v_currMacroScope_2316_; lean_object* v_ref_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_val_2314_ = lean_ctor_get(v___y_2299_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v___y_2299_, 1);
v_quotContext_2315_ = lean_ctor_get(v___y_2302_, 1);
v_currMacroScope_2316_ = lean_ctor_get(v___y_2302_, 2);
v_ref_2317_ = lean_ctor_get(v___y_2302_, 5);
v___x_2318_ = 0;
v___x_2319_ = l_Lean_SourceInfo_fromRef(v_ref_2317_, v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12));
v___x_2321_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36);
v___x_2322_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37));
lean_inc_n(v_currMacroScope_2316_, 4);
lean_inc_n(v_quotContext_2315_, 4);
v___x_2323_ = l_Lean_addMacroScope(v_quotContext_2315_, v___x_2322_, v_currMacroScope_2316_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61));
lean_inc_n(v___x_2319_, 11);
v___x_2325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2319_);
lean_ctor_set(v___x_2325_, 1, v___x_2321_);
lean_ctor_set(v___x_2325_, 2, v___x_2323_);
lean_ctor_set(v___x_2325_, 3, v___x_2324_);
v___x_2326_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2327_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63));
v___x_2328_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65));
v___x_2329_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6));
v___x_2330_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7));
v___x_2331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2319_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9));
v___x_2333_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10);
v___x_2334_ = lean_box(0);
v___x_2335_ = l_Lean_addMacroScope(v_quotContext_2315_, v___x_2334_, v_currMacroScope_2316_);
v___x_2336_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10));
v___x_2337_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2319_);
lean_ctor_set(v___x_2337_, 1, v___x_2333_);
lean_ctor_set(v___x_2337_, 2, v___x_2335_);
lean_ctor_set(v___x_2337_, 3, v___x_2336_);
v___x_2338_ = l_Lean_Syntax_node1(v___x_2319_, v___x_2332_, v___x_2337_);
v___x_2339_ = l_Lean_Syntax_node2(v___x_2319_, v___x_2329_, v___x_2331_, v___x_2338_);
v___x_2340_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21));
v___x_2341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2319_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = l_Lean_Syntax_node3(v___x_2319_, v___x_2328_, v___x_2339_, v_val_2314_, v___x_2341_);
v___x_2343_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2319_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67);
v___x_2346_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__68));
v___x_2347_ = l_Lean_addMacroScope(v_quotContext_2315_, v___x_2346_, v_currMacroScope_2316_);
v___x_2348_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__71));
v___x_2349_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2319_);
lean_ctor_set(v___x_2349_, 1, v___x_2345_);
lean_ctor_set(v___x_2349_, 2, v___x_2347_);
lean_ctor_set(v___x_2349_, 3, v___x_2348_);
v___x_2350_ = l_Lean_Syntax_node3(v___x_2319_, v___x_2327_, v___x_2342_, v___x_2344_, v___x_2349_);
v___x_2351_ = l_Lean_Syntax_node1(v___x_2319_, v___x_2326_, v___x_2350_);
v___x_2352_ = l_Lean_Syntax_node2(v___x_2319_, v___x_2320_, v___x_2325_, v___x_2351_);
v___y_2194_ = v_text_2301_;
v___y_2195_ = v___y_2300_;
v_newName_2196_ = v___x_2352_;
v_quotContext_2197_ = v_quotContext_2315_;
v_currMacroScope_2198_ = v_currMacroScope_2316_;
v_ref_2199_ = v_ref_2317_;
v___y_2200_ = v___y_2303_;
goto v___jp_2193_;
}
}
v___jp_2353_:
{
if (lean_obj_tag(v___y_2354_) == 0)
{
lean_object* v_quotContext_2359_; lean_object* v_currMacroScope_2360_; lean_object* v_ref_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_quotContext_2359_ = lean_ctor_get(v___y_2357_, 1);
v_currMacroScope_2360_ = lean_ctor_get(v___y_2357_, 2);
v_ref_2361_ = lean_ctor_get(v___y_2357_, 5);
v___x_2362_ = 0;
v___x_2363_ = l_Lean_SourceInfo_fromRef(v_ref_2361_, v___x_2362_);
v___x_2364_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55);
v___x_2365_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56));
lean_inc(v_currMacroScope_2360_);
lean_inc(v_quotContext_2359_);
v___x_2366_ = l_Lean_addMacroScope(v_quotContext_2359_, v___x_2365_, v_currMacroScope_2360_);
v___x_2367_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59));
v___x_2368_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2363_);
lean_ctor_set(v___x_2368_, 1, v___x_2364_);
lean_ctor_set(v___x_2368_, 2, v___x_2366_);
lean_ctor_set(v___x_2368_, 3, v___x_2367_);
v___y_2299_ = v___y_2355_;
v___y_2300_ = v_since_2356_;
v_text_2301_ = v___x_2368_;
v___y_2302_ = v___y_2357_;
v___y_2303_ = v___y_2358_;
goto v___jp_2298_;
}
else
{
lean_object* v_val_2369_; lean_object* v_quotContext_2370_; lean_object* v_currMacroScope_2371_; lean_object* v_ref_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_val_2369_ = lean_ctor_get(v___y_2354_, 0);
lean_inc(v_val_2369_);
lean_dec_ref_known(v___y_2354_, 1);
v_quotContext_2370_ = lean_ctor_get(v___y_2357_, 1);
v_currMacroScope_2371_ = lean_ctor_get(v___y_2357_, 2);
v_ref_2372_ = lean_ctor_get(v___y_2357_, 5);
v___x_2373_ = 0;
v___x_2374_ = l_Lean_SourceInfo_fromRef(v_ref_2372_, v___x_2373_);
v___x_2375_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12));
v___x_2376_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36);
v___x_2377_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37));
lean_inc(v_currMacroScope_2371_);
lean_inc(v_quotContext_2370_);
v___x_2378_ = l_Lean_addMacroScope(v_quotContext_2370_, v___x_2377_, v_currMacroScope_2371_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61));
lean_inc_n(v___x_2374_, 2);
v___x_2380_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2374_);
lean_ctor_set(v___x_2380_, 1, v___x_2376_);
lean_ctor_set(v___x_2380_, 2, v___x_2378_);
lean_ctor_set(v___x_2380_, 3, v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2382_ = l_Lean_Syntax_node1(v___x_2374_, v___x_2381_, v_val_2369_);
v___x_2383_ = l_Lean_Syntax_node2(v___x_2374_, v___x_2375_, v___x_2380_, v___x_2382_);
v___y_2299_ = v___y_2355_;
v___y_2300_ = v_since_2356_;
v_text_2301_ = v___x_2383_;
v___y_2302_ = v___y_2357_;
v___y_2303_ = v___y_2358_;
goto v___jp_2298_;
}
}
v___jp_2384_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(4u);
v___x_2391_ = l_Lean_Syntax_getArg(v_attr_2188_, v___x_2390_);
lean_dec(v_attr_2188_);
v___x_2392_ = l_Lean_Syntax_isNone(v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2391_);
v___x_2394_ = l_Lean_Syntax_matchesNull(v___x_2391_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_dec(v___x_2391_);
lean_dec(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec(v_type_2189_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v_decl_2190_);
lean_ctor_set(v___x_2395_, 1, v___y_2389_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Syntax_getArg(v___x_2391_, v___y_2387_);
lean_dec(v___x_2391_);
v___y_2354_ = v___y_2386_;
v___y_2355_ = v___y_2385_;
v_since_2356_ = v___x_2396_;
v___y_2357_ = v___y_2388_;
v___y_2358_ = v___y_2389_;
goto v___jp_2353_;
}
}
else
{
lean_object* v_ref_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec(v___x_2391_);
v_ref_2397_ = lean_ctor_get(v___y_2388_, 5);
v___x_2398_ = 0;
v___x_2399_ = l_Lean_SourceInfo_fromRef(v_ref_2397_, v___x_2398_);
v___x_2400_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__73));
v___x_2401_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__74));
lean_inc(v___x_2399_);
v___x_2402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2399_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_Lean_Syntax_node1(v___x_2399_, v___x_2400_, v___x_2402_);
v___y_2354_ = v___y_2386_;
v___y_2355_ = v___y_2385_;
v_since_2356_ = v___x_2403_;
v___y_2357_ = v___y_2388_;
v___y_2358_ = v___y_2389_;
goto v___jp_2353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___boxed(lean_object* v_attr_2438_, lean_object* v_type_2439_, lean_object* v_decl_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(v_attr_2438_, v_type_2439_, v_decl_2440_, v_a_2441_, v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(lean_object* v_x_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2486_ = l_Lean_Syntax_getId(v_x_2485_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31));
v___x_2488_ = lean_name_eq(v___x_2486_, v___x_2487_);
lean_dec(v___x_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0___boxed(lean_object* v_x_2489_){
_start:
{
uint8_t v_res_2490_; lean_object* v_r_2491_; 
v_res_2490_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(v_x_2489_);
lean_dec(v_x_2489_);
v_r_2491_ = lean_box(v_res_2490_);
return v_r_2491_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(lean_object* v___x_2492_, lean_object* v_x_2493_){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2494_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75));
v___x_2495_ = l_Lean_Name_mkStr2(v___x_2492_, v___x_2494_);
v___x_2496_ = l_Lean_Syntax_isOfKind(v_x_2493_, v___x_2495_);
lean_dec(v___x_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1___boxed(lean_object* v___x_2497_, lean_object* v_x_2498_){
_start:
{
uint8_t v_res_2499_; lean_object* v_r_2500_; 
v_res_2499_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(v___x_2497_, v_x_2498_);
v_r_2500_ = lean_box(v_res_2499_);
return v_r_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v___x_2503_, lean_object* v___x_2504_, lean_object* v_type_2505_, lean_object* v_name_2506_, lean_object* v___x_2507_, lean_object* v_decl_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_quotContext_2511_; lean_object* v_currMacroScope_2512_; lean_object* v_ref_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___y_2559_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_quotContext_2511_ = lean_ctor_get(v___y_2509_, 1);
v_currMacroScope_2512_ = lean_ctor_get(v___y_2509_, 2);
v_ref_2513_ = lean_ctor_get(v___y_2509_, 5);
v___x_2514_ = 0;
v___x_2515_ = l_Lean_SourceInfo_fromRef(v_ref_2513_, v___x_2514_);
v___x_2516_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25));
lean_inc_ref(v___x_2503_);
lean_inc_ref_n(v___x_2502_, 7);
lean_inc_ref_n(v___x_2501_, 9);
v___x_2517_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2503_, v___x_2516_);
v___x_2518_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
v___x_2519_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2503_, v___x_2518_);
lean_inc_n(v___x_2515_, 10);
v___x_2520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2515_);
lean_ctor_set(v___x_2520_, 1, v___x_2516_);
v___x_2521_ = l_Lean_Syntax_node1(v___x_2515_, v___x_2519_, v___x_2520_);
v___x_2522_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2523_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_2524_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_2525_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2523_, v___x_2524_);
v___x_2526_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2515_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_2529_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2523_, v___x_2528_);
v___x_2530_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
lean_inc_ref(v___x_2504_);
v___x_2531_ = l_Lean_Name_mkStr2(v___x_2501_, v___x_2504_);
lean_inc_n(v_currMacroScope_2512_, 2);
lean_inc_n(v___x_2531_, 2);
lean_inc_n(v_quotContext_2511_, 2);
v___x_2532_ = l_Lean_addMacroScope(v_quotContext_2511_, v___x_2531_, v_currMacroScope_2512_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2531_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2531_);
v___x_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2533_);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2534_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2515_);
lean_ctor_set(v___x_2538_, 1, v___x_2530_);
lean_ctor_set(v___x_2538_, 2, v___x_2532_);
lean_ctor_set(v___x_2538_, 3, v___x_2537_);
v___x_2539_ = l_Lean_Syntax_node1(v___x_2515_, v___x_2522_, v_type_2505_);
lean_inc(v___x_2529_);
v___x_2540_ = l_Lean_Syntax_node2(v___x_2515_, v___x_2529_, v___x_2538_, v___x_2539_);
v___x_2541_ = l_Lean_Syntax_node2(v___x_2515_, v___x_2525_, v___x_2527_, v___x_2540_);
v___x_2542_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_2543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2515_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
lean_inc(v_name_2506_);
v___x_2544_ = l_Lean_Syntax_node3(v___x_2515_, v___x_2522_, v_name_2506_, v___x_2541_, v___x_2543_);
v___x_2545_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_2546_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2523_, v___x_2545_);
v___x_2547_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_2548_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2523_, v___x_2547_);
v___x_2549_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_2550_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2523_, v___x_2549_);
v___x_2551_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2552_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18));
v___x_2553_ = l_Lean_Name_mkStr3(v___x_2501_, v___x_2504_, v___x_2552_);
lean_inc(v___x_2553_);
v___x_2554_ = l_Lean_addMacroScope(v_quotContext_2511_, v___x_2553_, v_currMacroScope_2512_);
v___x_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2533_);
v___x_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v___x_2533_);
v___x_2557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2515_);
lean_ctor_set(v___x_2557_, 1, v___x_2551_);
lean_ctor_set(v___x_2557_, 2, v___x_2554_);
lean_ctor_set(v___x_2557_, 3, v___x_2556_);
v___x_2570_ = l_Lean_TSyntax_getId(v_name_2506_);
lean_dec(v_name_2506_);
lean_inc(v___x_2570_);
v___x_2571_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2533_, v___x_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref(v___x_2502_);
lean_dec_ref(v___x_2501_);
v___x_2572_ = l_Lean_quoteNameMk(v___x_2570_);
v___y_2559_ = v___x_2572_;
goto v___jp_2558_;
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec(v___x_2570_);
v_val_2573_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2574_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
v___x_2575_ = l_Lean_Name_mkStr4(v___x_2501_, v___x_2502_, v___x_2523_, v___x_2574_);
v___x_2576_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_2577_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2578_ = lean_string_intercalate(v___x_2577_, v_val_2573_);
v___x_2579_ = lean_string_append(v___x_2576_, v___x_2578_);
lean_dec_ref(v___x_2578_);
v___x_2580_ = lean_box(2);
v___x_2581_ = l_Lean_Syntax_mkNameLit(v___x_2579_, v___x_2580_);
v___x_2582_ = lean_unsigned_to_nat(1u);
v___x_2583_ = lean_mk_empty_array_with_capacity(v___x_2582_);
v___x_2584_ = lean_array_push(v___x_2583_, v___x_2581_);
v___x_2585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2580_);
lean_ctor_set(v___x_2585_, 1, v___x_2575_);
lean_ctor_set(v___x_2585_, 2, v___x_2584_);
v___y_2559_ = v___x_2585_;
goto v___jp_2558_;
}
v___jp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_inc_n(v___x_2515_, 7);
v___x_2560_ = l_Lean_Syntax_node2(v___x_2515_, v___x_2522_, v___y_2559_, v_decl_2508_);
v___x_2561_ = l_Lean_Syntax_node2(v___x_2515_, v___x_2529_, v___x_2557_, v___x_2560_);
v___x_2562_ = l_Lean_Syntax_node1(v___x_2515_, v___x_2550_, v___x_2561_);
v___x_2563_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2515_);
lean_ctor_set(v___x_2564_, 1, v___x_2522_);
lean_ctor_set(v___x_2564_, 2, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node2(v___x_2515_, v___x_2548_, v___x_2562_, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node1(v___x_2515_, v___x_2522_, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node1(v___x_2515_, v___x_2546_, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node4(v___x_2515_, v___x_2517_, v___x_2507_, v___x_2521_, v___x_2544_, v___x_2567_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
lean_ctor_set(v___x_2569_, 1, v___y_2510_);
return v___x_2569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2___boxed(lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v___x_2589_, lean_object* v_type_2590_, lean_object* v_name_2591_, lean_object* v___x_2592_, lean_object* v_decl_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2586_, v___x_2587_, v___x_2588_, v___x_2589_, v_type_2590_, v_name_2591_, v___x_2592_, v_decl_2593_, v___y_2594_, v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___y_2606_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2625_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_2626_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__0));
v___x_2627_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2602_);
v___x_2628_ = l_Lean_Syntax_isOfKind(v_x_2602_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v_x_2602_);
v___x_2629_ = lean_box(1);
v___x_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
lean_ctor_set(v___x_2630_, 1, v_a_2604_);
return v___x_2630_;
}
else
{
lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_name_2636_; lean_object* v___x_2637_; lean_object* v_type_2638_; lean_object* v___x_2639_; lean_object* v_decl_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v_attr_x3f_2643_; lean_object* v_field_x3f_2644_; 
v___f_2631_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
v___f_2632_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = l_Lean_Syntax_getArg(v_x_2602_, v___x_2633_);
v___x_2635_ = lean_unsigned_to_nat(2u);
v_name_2636_ = l_Lean_Syntax_getArg(v_x_2602_, v___x_2635_);
v___x_2637_ = lean_unsigned_to_nat(4u);
v_type_2638_ = l_Lean_Syntax_getArg(v_x_2602_, v___x_2637_);
v___x_2639_ = lean_unsigned_to_nat(6u);
v_decl_2640_ = l_Lean_Syntax_getArg(v_x_2602_, v___x_2639_);
lean_dec(v_x_2602_);
v___x_2641_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_2642_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
lean_inc(v___x_2634_);
v_attr_x3f_2643_ = l_Lean_Syntax_find_x3f(v___x_2634_, v___f_2632_);
lean_inc(v_decl_2640_);
v_field_x3f_2644_ = l_Lean_Syntax_find_x3f(v_decl_2640_, v___f_2631_);
if (lean_obj_tag(v_attr_x3f_2643_) == 0)
{
if (lean_obj_tag(v_field_x3f_2644_) == 0)
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2625_, v___x_2641_, v___x_2642_, v___x_2626_, v_type_2638_, v_name_2636_, v___x_2634_, v_decl_2640_, v_a_2603_, v_a_2604_);
v___y_2606_ = v___x_2645_;
goto v___jp_2605_;
}
else
{
lean_object* v_val_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec(v_decl_2640_);
v_val_2646_ = lean_ctor_get(v_field_x3f_2644_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v_field_x3f_2644_, 1);
v___x_2647_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2648_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2646_, v___x_2647_, v_a_2603_, v_a_2604_);
lean_dec(v_val_2646_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
v_a_2650_ = lean_ctor_get(v___x_2648_, 1);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2648_, 2);
v___x_2651_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2625_, v___x_2641_, v___x_2642_, v___x_2626_, v_type_2638_, v_name_2636_, v___x_2634_, v_a_2649_, v_a_2603_, v_a_2650_);
v___y_2606_ = v___x_2651_;
goto v___jp_2605_;
}
else
{
lean_dec(v_type_2638_);
lean_dec(v_name_2636_);
lean_dec(v___x_2634_);
v___y_2606_ = v___x_2648_;
goto v___jp_2605_;
}
}
}
else
{
if (lean_obj_tag(v_field_x3f_2644_) == 0)
{
lean_object* v_val_2652_; lean_object* v___x_2653_; lean_object* v_a_2654_; lean_object* v_a_2655_; lean_object* v___x_2656_; 
v_val_2652_ = lean_ctor_get(v_attr_x3f_2643_, 0);
lean_inc(v_val_2652_);
lean_dec_ref_known(v_attr_x3f_2643_, 1);
lean_inc(v_type_2638_);
v___x_2653_ = l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(v_val_2652_, v_type_2638_, v_decl_2640_, v_a_2603_, v_a_2604_);
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
v_a_2655_ = lean_ctor_get(v___x_2653_, 1);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2653_);
v___x_2656_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2625_, v___x_2641_, v___x_2642_, v___x_2626_, v_type_2638_, v_name_2636_, v___x_2634_, v_a_2654_, v_a_2603_, v_a_2655_);
v___y_2606_ = v___x_2656_;
goto v___jp_2605_;
}
else
{
lean_object* v_val_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref_known(v_attr_x3f_2643_, 1);
lean_dec(v_decl_2640_);
v_val_2657_ = lean_ctor_get(v_field_x3f_2644_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v_field_x3f_2644_, 1);
v___x_2658_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2659_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2657_, v___x_2658_, v_a_2603_, v_a_2604_);
lean_dec(v_val_2657_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
v_a_2661_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2659_, 2);
v___x_2662_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2625_, v___x_2641_, v___x_2642_, v___x_2626_, v_type_2638_, v_name_2636_, v___x_2634_, v_a_2660_, v_a_2603_, v_a_2661_);
v___y_2606_ = v___x_2662_;
goto v___jp_2605_;
}
else
{
lean_dec(v_type_2638_);
lean_dec(v_name_2636_);
lean_dec(v___x_2634_);
v___y_2606_ = v___x_2659_;
goto v___jp_2605_;
}
}
}
}
v___jp_2605_:
{
if (lean_obj_tag(v___y_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2607_ = lean_ctor_get(v___y_2606_, 0);
v_a_2608_ = lean_ctor_get(v___y_2606_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___y_2606_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___y_2606_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_inc(v_a_2607_);
lean_dec(v___y_2606_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2607_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_a_2616_ = lean_ctor_get(v___y_2606_, 0);
v_a_2617_ = lean_ctor_get(v___y_2606_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___y_2606_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___y_2606_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_inc(v_a_2616_);
lean_dec(v___y_2606_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2616_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(lean_object* v_x_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(v_x_2663_, v_a_2664_, v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2666_;
}
}
lean_object* runtime_initialize_Lean_ImportingFlag(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_KVMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
