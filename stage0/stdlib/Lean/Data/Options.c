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
lean_object* l_Array_mkArray0___redArg();
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg(){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = ((lean_object*)(l_Lean_Options_empty));
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg___boxed(lean_object* v___dummy_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = ((lean_object*)(l_Lean_Options_empty));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___lam__0(lean_object* v_x1_12_, lean_object* v_x2_13_, lean_object* v_x3_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_x1_12_);
lean_ctor_set(v___x_15_, 1, v_x2_13_);
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_x3_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object* v_o_42_){
_start:
{
lean_object* v_map_43_; lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_map_43_ = lean_ctor_get(v_o_42_, 0);
lean_inc(v_map_43_);
lean_dec_ref(v_o_42_);
v___f_44_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__0));
v___f_45_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__3));
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__13));
v___x_48_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_47_, v___f_44_, v___x_46_, v_map_43_);
v___x_49_ = l_List_toString___redArg(v___f_45_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___lam__1(lean_object* v___f_50_, lean_object* v_o_51_){
_start:
{
lean_object* v_map_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_map_52_ = lean_ctor_get(v_o_51_, 0);
lean_inc(v_map_52_);
lean_dec_ref(v_o_51_);
v___f_53_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__3));
v___x_54_ = lean_box(0);
v___x_55_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__13));
v___x_56_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_55_, v___f_50_, v___x_54_, v_map_52_);
v___x_57_ = l_List_toString___redArg(v___f_53_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object* v_f_61_, lean_object* v_a_62_, lean_object* v_b_63_, lean_object* v_c_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v_a_62_);
lean_ctor_set(v___x_65_, 1, v_b_63_);
v___x_66_ = lean_apply_2(v_f_61_, v___x_65_, v_c_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object* v_toPure_67_, lean_object* v_____do__lift_68_){
_start:
{
lean_object* v_a_69_; lean_object* v___x_70_; 
v_a_69_ = lean_ctor_get(v_____do__lift_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref(v_____do__lift_68_);
v___x_70_ = lean_apply_2(v_toPure_67_, lean_box(0), v_a_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object* v_inst_71_, lean_object* v_o_72_, lean_object* v_init_73_, lean_object* v_f_74_){
_start:
{
lean_object* v_toApplicative_75_; lean_object* v_map_76_; lean_object* v_toBind_77_; lean_object* v_toPure_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___x_82_; 
v_toApplicative_75_ = lean_ctor_get(v_inst_71_, 0);
v_map_76_ = lean_ctor_get(v_o_72_, 0);
lean_inc(v_map_76_);
lean_dec_ref(v_o_72_);
v_toBind_77_ = lean_ctor_get(v_inst_71_, 1);
lean_inc(v_toBind_77_);
v_toPure_78_ = lean_ctor_get(v_toApplicative_75_, 1);
lean_inc(v_toPure_78_);
v___f_79_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_79_, 0, v_f_74_);
v___x_80_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_71_, v___f_79_, v_init_73_, v_map_76_);
v___f_81_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_81_, 0, v_toPure_78_);
v___x_82_ = lean_apply_4(v_toBind_77_, lean_box(0), lean_box(0), v___x_80_, v___f_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object* v_m_83_, lean_object* v_inst_84_, lean_object* v_00_u03b2_85_, lean_object* v_o_86_, lean_object* v_init_87_, lean_object* v_f_88_){
_start:
{
lean_object* v_toApplicative_89_; lean_object* v_map_90_; lean_object* v_toBind_91_; lean_object* v_toPure_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___f_95_; lean_object* v___x_96_; 
v_toApplicative_89_ = lean_ctor_get(v_inst_84_, 0);
v_map_90_ = lean_ctor_get(v_o_86_, 0);
lean_inc(v_map_90_);
lean_dec_ref(v_o_86_);
v_toBind_91_ = lean_ctor_get(v_inst_84_, 1);
lean_inc(v_toBind_91_);
v_toPure_92_ = lean_ctor_get(v_toApplicative_89_, 1);
lean_inc(v_toPure_92_);
v___f_93_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_93_, 0, v_f_88_);
v___x_94_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_84_, v___f_93_, v_init_87_, v_map_90_);
v___f_95_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_95_, 0, v_toPure_92_);
v___x_96_ = lean_apply_4(v_toBind_91_, lean_box(0), lean_box(0), v___x_94_, v___f_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2(lean_object* v_inst_97_, lean_object* v_00_u03b2_98_, lean_object* v_o_99_, lean_object* v_init_100_, lean_object* v_f_101_){
_start:
{
lean_object* v_toApplicative_102_; lean_object* v_map_103_; lean_object* v_toBind_104_; lean_object* v_toPure_105_; lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___x_109_; 
v_toApplicative_102_ = lean_ctor_get(v_inst_97_, 0);
v_map_103_ = lean_ctor_get(v_o_99_, 0);
lean_inc(v_map_103_);
lean_dec_ref(v_o_99_);
v_toBind_104_ = lean_ctor_get(v_inst_97_, 1);
lean_inc(v_toBind_104_);
v_toPure_105_ = lean_ctor_get(v_toApplicative_102_, 1);
lean_inc(v_toPure_105_);
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_106_, 0, v_f_101_);
v___x_107_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_97_, v___f_106_, v_init_100_, v_map_103_);
v___f_108_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_108_, 0, v_toPure_105_);
v___x_109_ = lean_apply_4(v_toBind_104_, lean_box(0), lean_box(0), v___x_107_, v___f_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_110_){
_start:
{
lean_object* v___f_111_; 
v___f_111_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_111_, 0, v_inst_110_);
return v___f_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object* v_m_112_, lean_object* v_inst_113_){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_114_, 0, v_inst_113_);
return v___f_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___private__1(lean_object* v_o1_117_, lean_object* v_o2_118_){
_start:
{
lean_object* v_map_119_; lean_object* v_map_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_map_119_ = lean_ctor_get(v_o1_117_, 0);
lean_inc(v_map_119_);
lean_dec_ref(v_o1_117_);
v_map_120_ = lean_ctor_get(v_o2_118_, 0);
lean_inc(v_map_120_);
lean_dec_ref(v_o2_118_);
v___x_121_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_122_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__1));
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v___x_122_, v___x_121_, v_map_119_, v_map_120_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object* v_o1_124_, lean_object* v_o2_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lean_Options_instBEq___private__1(v_o1_124_, v_o2_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___lam__0(lean_object* v_o1_128_, lean_object* v_o2_129_){
_start:
{
lean_object* v_map_130_; lean_object* v_map_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v_map_130_ = lean_ctor_get(v_o1_128_, 0);
lean_inc(v_map_130_);
lean_dec_ref(v_o1_128_);
v_map_131_ = lean_ctor_get(v_o2_129_, 0);
lean_inc(v_map_131_);
lean_dec_ref(v_o2_129_);
v___x_132_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_133_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__1));
v___x_134_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v___x_133_, v___x_132_, v_map_130_, v_map_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___lam__0___boxed(lean_object* v_o1_135_, lean_object* v_o2_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Lean_Options_instBEq___lam__0(v_o1_135_, v_o2_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f(lean_object* v_o_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_map_144_; lean_object* v___x_145_; 
v_map_144_ = lean_ctor_get(v_o_142_, 0);
v___x_145_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_144_, v_k_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f___boxed(lean_object* v_o_146_, lean_object* v_k_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Options_find_x3f(v_o_146_, v_k_147_);
lean_dec(v_k_147_);
lean_dec_ref(v_o_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find(lean_object* v_o_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_map_151_; lean_object* v___x_152_; 
v_map_151_ = lean_ctor_get(v_o_149_, 0);
v___x_152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_151_, v_k_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find___boxed(lean_object* v_o_153_, lean_object* v_k_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Options_find(v_o_153_, v_k_154_);
lean_dec(v_k_154_);
lean_dec_ref(v_o_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg(lean_object* v_inst_156_, lean_object* v_o_157_, lean_object* v_k_158_){
_start:
{
lean_object* v_map_159_; lean_object* v_ofDataValue_x3f_160_; lean_object* v___x_161_; 
v_map_159_ = lean_ctor_get(v_o_157_, 0);
v_ofDataValue_x3f_160_ = lean_ctor_get(v_inst_156_, 1);
lean_inc_ref(v_ofDataValue_x3f_160_);
lean_dec_ref(v_inst_156_);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_159_, v_k_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; 
lean_dec_ref(v_ofDataValue_x3f_160_);
v___x_162_ = lean_box(0);
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v___x_164_; 
v_val_163_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v___x_161_, 1);
v___x_164_ = lean_apply_1(v_ofDataValue_x3f_160_, v_val_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg___boxed(lean_object* v_inst_165_, lean_object* v_o_166_, lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Options_get_x3f___redArg(v_inst_165_, v_o_166_, v_k_167_);
lean_dec(v_k_167_);
lean_dec_ref(v_o_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_o_171_, lean_object* v_k_172_){
_start:
{
lean_object* v_map_173_; lean_object* v_ofDataValue_x3f_174_; lean_object* v___x_175_; 
v_map_173_ = lean_ctor_get(v_o_171_, 0);
v_ofDataValue_x3f_174_ = lean_ctor_get(v_inst_170_, 1);
lean_inc_ref(v_ofDataValue_x3f_174_);
lean_dec_ref(v_inst_170_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_173_, v_k_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; 
lean_dec_ref(v_ofDataValue_x3f_174_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_175_, 1);
v___x_178_ = lean_apply_1(v_ofDataValue_x3f_174_, v_val_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___boxed(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_o_181_, lean_object* v_k_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Options_get_x3f(v_00_u03b1_179_, v_inst_180_, v_o_181_, v_k_182_);
lean_dec(v_k_182_);
lean_dec_ref(v_o_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg(lean_object* v_inst_184_, lean_object* v_o_185_, lean_object* v_k_186_, lean_object* v_defVal_187_){
_start:
{
lean_object* v_map_188_; lean_object* v_ofDataValue_x3f_189_; lean_object* v___x_190_; 
v_map_188_ = lean_ctor_get(v_o_185_, 0);
v_ofDataValue_x3f_189_ = lean_ctor_get(v_inst_184_, 1);
lean_inc_ref(v_ofDataValue_x3f_189_);
lean_dec_ref(v_inst_184_);
v___x_190_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_188_, v_k_186_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_189_);
lean_inc(v_defVal_187_);
return v_defVal_187_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_192_; 
v_val_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v___x_190_, 1);
v___x_192_ = lean_apply_1(v_ofDataValue_x3f_189_, v_val_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_inc(v_defVal_187_);
return v_defVal_187_;
}
else
{
lean_object* v_val_193_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_192_, 1);
return v_val_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg___boxed(lean_object* v_inst_194_, lean_object* v_o_195_, lean_object* v_k_196_, lean_object* v_defVal_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Options_get___redArg(v_inst_194_, v_o_195_, v_k_196_, v_defVal_197_);
lean_dec(v_defVal_197_);
lean_dec(v_k_196_);
lean_dec_ref(v_o_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_o_201_, lean_object* v_k_202_, lean_object* v_defVal_203_){
_start:
{
lean_object* v_map_204_; lean_object* v_ofDataValue_x3f_205_; lean_object* v___x_206_; 
v_map_204_ = lean_ctor_get(v_o_201_, 0);
v_ofDataValue_x3f_205_ = lean_ctor_get(v_inst_200_, 1);
lean_inc_ref(v_ofDataValue_x3f_205_);
lean_dec_ref(v_inst_200_);
v___x_206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_204_, v_k_202_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_205_);
lean_inc(v_defVal_203_);
return v_defVal_203_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_208_; 
v_val_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = lean_apply_1(v_ofDataValue_x3f_205_, v_val_207_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_inc(v_defVal_203_);
return v_defVal_203_;
}
else
{
lean_object* v_val_209_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v___x_208_, 1);
return v_val_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___boxed(lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_o_212_, lean_object* v_k_213_, lean_object* v_defVal_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Options_get(v_00_u03b1_210_, v_inst_211_, v_o_212_, v_k_213_, v_defVal_214_);
lean_dec(v_defVal_214_);
lean_dec(v_k_213_);
lean_dec_ref(v_o_212_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getBool(lean_object* v_o_216_, lean_object* v_k_217_, uint8_t v_defVal_218_){
_start:
{
lean_object* v_map_219_; lean_object* v___x_220_; 
v_map_219_ = lean_ctor_get(v_o_216_, 0);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_219_, v_k_217_);
if (lean_obj_tag(v___x_220_) == 0)
{
return v_defVal_218_;
}
else
{
lean_object* v_val_221_; 
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
if (lean_obj_tag(v_val_221_) == 1)
{
uint8_t v_v_222_; 
v_v_222_ = lean_ctor_get_uint8(v_val_221_, 0);
lean_dec_ref_known(v_val_221_, 0);
return v_v_222_;
}
else
{
lean_dec(v_val_221_);
return v_defVal_218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getBool___boxed(lean_object* v_o_223_, lean_object* v_k_224_, lean_object* v_defVal_225_){
_start:
{
uint8_t v_defVal_boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v_defVal_boxed_226_ = lean_unbox(v_defVal_225_);
v_res_227_ = l_Lean_Options_getBool(v_o_223_, v_k_224_, v_defVal_boxed_226_);
lean_dec(v_k_224_);
lean_dec_ref(v_o_223_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_contains(lean_object* v_o_229_, lean_object* v_k_230_){
_start:
{
lean_object* v_map_231_; uint8_t v___x_232_; 
v_map_231_ = lean_ctor_get(v_o_229_, 0);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_230_, v_map_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object* v_o_233_, lean_object* v_k_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Lean_Options_contains(v_o_233_, v_k_234_);
lean_dec(v_k_234_);
lean_dec_ref(v_o_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object* v_o_240_, lean_object* v_k_241_, lean_object* v_v_242_){
_start:
{
lean_object* v_map_243_; uint8_t v_hasTrace_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_257_; 
v_map_243_ = lean_ctor_get(v_o_240_, 0);
v_hasTrace_244_ = lean_ctor_get_uint8(v_o_240_, sizeof(void*)*1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_o_240_);
if (v_isSharedCheck_257_ == 0)
{
v___x_246_ = v_o_240_;
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_map_243_);
lean_dec(v_o_240_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; 
lean_inc(v_k_241_);
v___x_248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_241_, v_v_242_, v_map_243_);
if (v_hasTrace_244_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_252_; 
v___x_249_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_250_ = l_Lean_Name_isPrefixOf(v___x_249_, v_k_241_);
lean_dec(v_k_241_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_252_ = v___x_246_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_248_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v___x_250_);
return v___x_252_;
}
}
else
{
lean_object* v___x_255_; 
lean_dec(v_k_241_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_255_ = v___x_246_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_256_, sizeof(void*)*1, v_hasTrace_244_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object* v_inst_258_, lean_object* v_o_259_, lean_object* v_k_260_, lean_object* v_v_261_){
_start:
{
lean_object* v_toDataValue_262_; lean_object* v_map_263_; uint8_t v_hasTrace_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_278_; 
v_toDataValue_262_ = lean_ctor_get(v_inst_258_, 0);
lean_inc_ref(v_toDataValue_262_);
lean_dec_ref(v_inst_258_);
v_map_263_ = lean_ctor_get(v_o_259_, 0);
v_hasTrace_264_ = lean_ctor_get_uint8(v_o_259_, sizeof(void*)*1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_o_259_);
if (v_isSharedCheck_278_ == 0)
{
v___x_266_ = v_o_259_;
v_isShared_267_ = v_isSharedCheck_278_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_map_263_);
lean_dec(v_o_259_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_278_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_apply_1(v_toDataValue_262_, v_v_261_);
lean_inc(v_k_260_);
v___x_269_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_260_, v___x_268_, v_map_263_);
if (v_hasTrace_264_ == 0)
{
lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_273_; 
v___x_270_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_271_ = l_Lean_Name_isPrefixOf(v___x_270_, v_k_260_);
lean_dec(v_k_260_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_273_ = v___x_266_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_269_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_271_);
return v___x_273_;
}
}
else
{
lean_object* v___x_276_; 
lean_dec(v_k_260_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_276_ = v___x_266_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*1, v_hasTrace_264_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_o_281_, lean_object* v_k_282_, lean_object* v_v_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Options_set___redArg(v_inst_280_, v_o_281_, v_k_282_, v_v_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool(lean_object* v_o_285_, lean_object* v_k_286_, uint8_t v_v_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = l_Lean_KVMap_instValueBool;
v___x_289_ = lean_box(v_v_287_);
v___x_290_ = l_Lean_Options_set___redArg(v___x_288_, v_o_285_, v_k_286_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object* v_o_291_, lean_object* v_k_292_, lean_object* v_v_293_){
_start:
{
uint8_t v_v_boxed_294_; lean_object* v_res_295_; 
v_v_boxed_294_ = lean_unbox(v_v_293_);
v_res_295_ = l_Lean_Options_setBool(v_o_291_, v_k_292_, v_v_boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object* v_init_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v_k_298_; lean_object* v_l_299_; lean_object* v_r_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_k_298_ = lean_ctor_get(v_x_297_, 1);
v_l_299_ = lean_ctor_get(v_x_297_, 3);
v_r_300_ = lean_ctor_get(v_x_297_, 4);
v___x_301_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_296_, v_r_300_);
lean_inc(v_k_298_);
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v_k_298_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v_init_296_ = v___x_302_;
v_x_297_ = v_l_299_;
goto _start;
}
else
{
return v_init_296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object* v_init_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_304_, v_x_305_);
lean_dec(v_x_305_);
return v_res_306_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Options_erase_spec__2(lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
else
{
lean_object* v_head_309_; lean_object* v_tail_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_head_309_ = lean_ctor_get(v_x_307_, 0);
v_tail_310_ = lean_ctor_get(v_x_307_, 1);
v___x_311_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_312_ = l_Lean_Name_isPrefixOf(v___x_311_, v_head_309_);
if (v___x_312_ == 0)
{
v_x_307_ = v_tail_310_;
goto _start;
}
else
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Options_erase_spec__2___boxed(lean_object* v_x_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_List_any___at___00Lean_Options_erase_spec__2(v_x_314_);
lean_dec(v_x_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object* v_k_317_, lean_object* v_t_318_){
_start:
{
if (lean_obj_tag(v_t_318_) == 0)
{
lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v_l_321_; lean_object* v_r_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_976_; 
v_k_319_ = lean_ctor_get(v_t_318_, 1);
v_v_320_ = lean_ctor_get(v_t_318_, 2);
v_l_321_ = lean_ctor_get(v_t_318_, 3);
v_r_322_ = lean_ctor_get(v_t_318_, 4);
v_isSharedCheck_976_ = !lean_is_exclusive(v_t_318_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_t_318_, 0);
lean_dec(v_unused_977_);
v___x_324_ = v_t_318_;
v_isShared_325_ = v_isSharedCheck_976_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_r_322_);
lean_inc(v_l_321_);
lean_inc(v_v_320_);
lean_inc(v_k_319_);
lean_dec(v_t_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_976_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint8_t v___x_326_; 
v___x_326_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_317_, v_k_319_);
switch(v___x_326_)
{
case 0:
{
lean_object* v_impl_327_; lean_object* v___x_328_; 
v_impl_327_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_317_, v_l_321_);
v___x_328_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_327_) == 0)
{
if (lean_obj_tag(v_r_322_) == 0)
{
lean_object* v_size_329_; lean_object* v_size_330_; lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v_l_333_; lean_object* v_r_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_size_329_ = lean_ctor_get(v_impl_327_, 0);
lean_inc(v_size_329_);
v_size_330_ = lean_ctor_get(v_r_322_, 0);
v_k_331_ = lean_ctor_get(v_r_322_, 1);
v_v_332_ = lean_ctor_get(v_r_322_, 2);
v_l_333_ = lean_ctor_get(v_r_322_, 3);
lean_inc(v_l_333_);
v_r_334_ = lean_ctor_get(v_r_322_, 4);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_mul(v___x_335_, v_size_329_);
v___x_337_ = lean_nat_dec_lt(v___x_336_, v_size_330_);
lean_dec(v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v_l_333_);
v___x_338_ = lean_nat_add(v___x_328_, v_size_329_);
lean_dec(v_size_329_);
v___x_339_ = lean_nat_add(v___x_338_, v_size_330_);
lean_dec(v___x_338_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v_impl_327_);
lean_ctor_set(v___x_324_, 0, v___x_339_);
v___x_341_ = v___x_324_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_impl_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v_r_322_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_406_; 
lean_inc(v_r_334_);
lean_inc(v_v_332_);
lean_inc(v_k_331_);
lean_inc(v_size_330_);
v_isSharedCheck_406_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_407_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_r_322_, 2);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_r_322_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_r_322_, 0);
lean_dec(v_unused_411_);
v___x_344_ = v_r_322_;
v_isShared_345_ = v_isSharedCheck_406_;
goto v_resetjp_343_;
}
else
{
lean_dec(v_r_322_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_406_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_size_346_; lean_object* v_k_347_; lean_object* v_v_348_; lean_object* v_l_349_; lean_object* v_r_350_; lean_object* v_size_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_size_346_ = lean_ctor_get(v_l_333_, 0);
v_k_347_ = lean_ctor_get(v_l_333_, 1);
v_v_348_ = lean_ctor_get(v_l_333_, 2);
v_l_349_ = lean_ctor_get(v_l_333_, 3);
v_r_350_ = lean_ctor_get(v_l_333_, 4);
v_size_351_ = lean_ctor_get(v_r_334_, 0);
v___x_352_ = lean_unsigned_to_nat(2u);
v___x_353_ = lean_nat_mul(v___x_352_, v_size_351_);
v___x_354_ = lean_nat_dec_lt(v_size_346_, v___x_353_);
lean_dec(v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_382_; 
lean_inc(v_r_350_);
lean_inc(v_l_349_);
lean_inc(v_v_348_);
lean_inc(v_k_347_);
v_isSharedCheck_382_ = !lean_is_exclusive(v_l_333_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_383_ = lean_ctor_get(v_l_333_, 4);
lean_dec(v_unused_383_);
v_unused_384_ = lean_ctor_get(v_l_333_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_l_333_, 2);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_l_333_, 1);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_l_333_, 0);
lean_dec(v_unused_387_);
v___x_356_ = v_l_333_;
v_isShared_357_ = v_isSharedCheck_382_;
goto v_resetjp_355_;
}
else
{
lean_dec(v_l_333_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_382_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_372_; 
v___x_358_ = lean_nat_add(v___x_328_, v_size_329_);
lean_dec(v_size_329_);
v___x_359_ = lean_nat_add(v___x_358_, v_size_330_);
lean_dec(v_size_330_);
if (lean_obj_tag(v_l_349_) == 0)
{
lean_object* v_size_380_; 
v_size_380_ = lean_ctor_get(v_l_349_, 0);
lean_inc(v_size_380_);
v___y_372_ = v_size_380_;
goto v___jp_371_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___y_372_ = v___x_381_;
goto v___jp_371_;
}
v___jp_360_:
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_nat_add(v___y_361_, v___y_363_);
lean_dec(v___y_363_);
lean_dec(v___y_361_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 4, v_r_334_);
lean_ctor_set(v___x_356_, 3, v_r_350_);
lean_ctor_set(v___x_356_, 2, v_v_332_);
lean_ctor_set(v___x_356_, 1, v_k_331_);
lean_ctor_set(v___x_356_, 0, v___x_364_);
v___x_366_ = v___x_356_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_k_331_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_v_332_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_r_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_r_334_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 4, v___x_366_);
lean_ctor_set(v___x_344_, 3, v___y_362_);
lean_ctor_set(v___x_344_, 2, v_v_348_);
lean_ctor_set(v___x_344_, 1, v_k_347_);
lean_ctor_set(v___x_344_, 0, v___x_359_);
v___x_368_ = v___x_344_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_347_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_348_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v___y_362_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
v___jp_371_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_nat_add(v___x_358_, v___y_372_);
lean_dec(v___y_372_);
lean_dec(v___x_358_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_l_349_);
lean_ctor_set(v___x_324_, 3, v_impl_327_);
lean_ctor_set(v___x_324_, 0, v___x_373_);
v___x_375_ = v___x_324_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_impl_327_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_l_349_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_nat_add(v___x_328_, v_size_351_);
if (lean_obj_tag(v_r_350_) == 0)
{
lean_object* v_size_377_; 
v_size_377_ = lean_ctor_get(v_r_350_, 0);
lean_inc(v_size_377_);
v___y_361_ = v___x_376_;
v___y_362_ = v___x_375_;
v___y_363_ = v_size_377_;
goto v___jp_360_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___y_361_ = v___x_376_;
v___y_362_ = v___x_375_;
v___y_363_ = v___x_378_;
goto v___jp_360_;
}
}
}
}
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
lean_del_object(v___x_324_);
v___x_388_ = lean_nat_add(v___x_328_, v_size_329_);
lean_dec(v_size_329_);
v___x_389_ = lean_nat_add(v___x_388_, v_size_330_);
lean_dec(v_size_330_);
v___x_390_ = lean_nat_add(v___x_388_, v_size_346_);
lean_dec(v___x_388_);
lean_inc_ref(v_impl_327_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 4, v_l_333_);
lean_ctor_set(v___x_344_, 3, v_impl_327_);
lean_ctor_set(v___x_344_, 2, v_v_320_);
lean_ctor_set(v___x_344_, 1, v_k_319_);
lean_ctor_set(v___x_344_, 0, v___x_390_);
v___x_392_ = v___x_344_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_impl_327_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_l_333_);
v___x_392_ = v_reuseFailAlloc_405_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_isSharedCheck_399_ = !lean_is_exclusive(v_impl_327_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; lean_object* v_unused_401_; lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; 
v_unused_400_ = lean_ctor_get(v_impl_327_, 4);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_impl_327_, 3);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_impl_327_, 2);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_impl_327_, 1);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_impl_327_, 0);
lean_dec(v_unused_404_);
v___x_394_ = v_impl_327_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_dec(v_impl_327_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 4, v_r_334_);
lean_ctor_set(v___x_394_, 3, v___x_392_);
lean_ctor_set(v___x_394_, 2, v_v_332_);
lean_ctor_set(v___x_394_, 1, v_k_331_);
lean_ctor_set(v___x_394_, 0, v___x_389_);
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_331_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_332_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_r_334_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_size_412_ = lean_ctor_get(v_impl_327_, 0);
lean_inc(v_size_412_);
v___x_413_ = lean_nat_add(v___x_328_, v_size_412_);
lean_dec(v_size_412_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v_impl_327_);
lean_ctor_set(v___x_324_, 0, v___x_413_);
v___x_415_ = v___x_324_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_impl_327_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v_r_322_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
if (lean_obj_tag(v_r_322_) == 0)
{
lean_object* v_l_417_; 
v_l_417_ = lean_ctor_get(v_r_322_, 3);
lean_inc(v_l_417_);
if (lean_obj_tag(v_l_417_) == 0)
{
lean_object* v_r_418_; 
v_r_418_ = lean_ctor_get(v_r_322_, 4);
lean_inc(v_r_418_);
if (lean_obj_tag(v_r_418_) == 0)
{
lean_object* v_size_419_; lean_object* v_k_420_; lean_object* v_v_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_434_; 
v_size_419_ = lean_ctor_get(v_r_322_, 0);
v_k_420_ = lean_ctor_get(v_r_322_, 1);
v_v_421_ = lean_ctor_get(v_r_322_, 2);
v_isSharedCheck_434_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_435_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_436_);
v___x_423_ = v_r_322_;
v_isShared_424_ = v_isSharedCheck_434_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_v_421_);
lean_inc(v_k_420_);
lean_inc(v_size_419_);
lean_dec(v_r_322_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_434_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_size_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v_size_425_ = lean_ctor_get(v_l_417_, 0);
v___x_426_ = lean_nat_add(v___x_328_, v_size_419_);
lean_dec(v_size_419_);
v___x_427_ = lean_nat_add(v___x_328_, v_size_425_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_l_417_);
lean_ctor_set(v___x_423_, 3, v_impl_327_);
lean_ctor_set(v___x_423_, 2, v_v_320_);
lean_ctor_set(v___x_423_, 1, v_k_319_);
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_impl_327_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_l_417_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_r_418_);
lean_ctor_set(v___x_324_, 3, v___x_429_);
lean_ctor_set(v___x_324_, 2, v_v_421_);
lean_ctor_set(v___x_324_, 1, v_k_420_);
lean_ctor_set(v___x_324_, 0, v___x_426_);
v___x_431_ = v___x_324_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_k_420_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_v_421_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_r_418_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_object* v_k_437_; lean_object* v_v_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_461_; 
v_k_437_ = lean_ctor_get(v_r_322_, 1);
v_v_438_ = lean_ctor_get(v_r_322_, 2);
v_isSharedCheck_461_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; lean_object* v_unused_463_; lean_object* v_unused_464_; 
v_unused_462_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_r_322_, 0);
lean_dec(v_unused_464_);
v___x_440_ = v_r_322_;
v_isShared_441_ = v_isSharedCheck_461_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_v_438_);
lean_inc(v_k_437_);
lean_dec(v_r_322_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_461_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_k_442_; lean_object* v_v_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_457_; 
v_k_442_ = lean_ctor_get(v_l_417_, 1);
v_v_443_ = lean_ctor_get(v_l_417_, 2);
v_isSharedCheck_457_ = !lean_is_exclusive(v_l_417_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; 
v_unused_458_ = lean_ctor_get(v_l_417_, 4);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_l_417_, 3);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_l_417_, 0);
lean_dec(v_unused_460_);
v___x_445_ = v_l_417_;
v_isShared_446_ = v_isSharedCheck_457_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_v_443_);
lean_inc(v_k_442_);
lean_dec(v_l_417_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_457_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(3u);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 4, v_r_418_);
lean_ctor_set(v___x_445_, 3, v_r_418_);
lean_ctor_set(v___x_445_, 2, v_v_320_);
lean_ctor_set(v___x_445_, 1, v_k_319_);
lean_ctor_set(v___x_445_, 0, v___x_328_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_r_418_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_r_418_);
v___x_449_ = v_reuseFailAlloc_456_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 3, v_r_418_);
lean_ctor_set(v___x_440_, 0, v___x_328_);
v___x_451_ = v___x_440_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_k_437_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_v_438_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_r_418_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_r_418_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_453_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v___x_451_);
lean_ctor_set(v___x_324_, 3, v___x_449_);
lean_ctor_set(v___x_324_, 2, v_v_443_);
lean_ctor_set(v___x_324_, 1, v_k_442_);
lean_ctor_set(v___x_324_, 0, v___x_447_);
v___x_453_ = v___x_324_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_k_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_v_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_465_; 
v_r_465_ = lean_ctor_get(v_r_322_, 4);
lean_inc(v_r_465_);
if (lean_obj_tag(v_r_465_) == 0)
{
lean_object* v_k_466_; lean_object* v_v_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_478_; 
v_k_466_ = lean_ctor_get(v_r_322_, 1);
v_v_467_ = lean_ctor_get(v_r_322_, 2);
v_isSharedCheck_478_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_479_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_r_322_, 0);
lean_dec(v_unused_481_);
v___x_469_ = v_r_322_;
v_isShared_470_ = v_isSharedCheck_478_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_v_467_);
lean_inc(v_k_466_);
lean_dec(v_r_322_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_478_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_unsigned_to_nat(3u);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_l_417_);
lean_ctor_set(v___x_469_, 2, v_v_320_);
lean_ctor_set(v___x_469_, 1, v_k_319_);
lean_ctor_set(v___x_469_, 0, v___x_328_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_l_417_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_l_417_);
v___x_473_ = v_reuseFailAlloc_477_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_r_465_);
lean_ctor_set(v___x_324_, 3, v___x_473_);
lean_ctor_set(v___x_324_, 2, v_v_467_);
lean_ctor_set(v___x_324_, 1, v_k_466_);
lean_ctor_set(v___x_324_, 0, v___x_471_);
v___x_475_ = v___x_324_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_k_466_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_v_467_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_r_465_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_object* v_size_482_; lean_object* v_k_483_; lean_object* v_v_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_size_482_ = lean_ctor_get(v_r_322_, 0);
v_k_483_ = lean_ctor_get(v_r_322_, 1);
v_v_484_ = lean_ctor_get(v_r_322_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_497_);
v___x_486_ = v_r_322_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_v_484_);
lean_inc(v_k_483_);
lean_inc(v_size_482_);
lean_dec(v_r_322_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 3, v_r_465_);
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_482_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_r_465_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_r_465_);
v___x_489_ = v_reuseFailAlloc_494_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = lean_unsigned_to_nat(2u);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v___x_489_);
lean_ctor_set(v___x_324_, 3, v_r_465_);
lean_ctor_set(v___x_324_, 0, v___x_490_);
v___x_492_ = v___x_324_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_r_465_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v___x_489_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
else
{
lean_object* v___x_499_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 3, v_r_322_);
lean_ctor_set(v___x_324_, 0, v___x_328_);
v___x_499_ = v___x_324_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_r_322_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_r_322_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
case 1:
{
lean_del_object(v___x_324_);
lean_dec(v_v_320_);
lean_dec(v_k_319_);
if (lean_obj_tag(v_l_321_) == 0)
{
if (lean_obj_tag(v_r_322_) == 0)
{
lean_object* v_size_501_; lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v_l_504_; lean_object* v_r_505_; lean_object* v_size_506_; lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v_l_509_; lean_object* v_r_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_size_501_ = lean_ctor_get(v_l_321_, 0);
v_k_502_ = lean_ctor_get(v_l_321_, 1);
v_v_503_ = lean_ctor_get(v_l_321_, 2);
v_l_504_ = lean_ctor_get(v_l_321_, 3);
v_r_505_ = lean_ctor_get(v_l_321_, 4);
lean_inc(v_r_505_);
v_size_506_ = lean_ctor_get(v_r_322_, 0);
v_k_507_ = lean_ctor_get(v_r_322_, 1);
v_v_508_ = lean_ctor_get(v_r_322_, 2);
v_l_509_ = lean_ctor_get(v_r_322_, 3);
lean_inc(v_l_509_);
v_r_510_ = lean_ctor_get(v_r_322_, 4);
v___x_511_ = lean_unsigned_to_nat(1u);
v___x_512_ = lean_nat_dec_lt(v_size_501_, v_size_506_);
if (v___x_512_ == 0)
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_648_; 
lean_inc(v_l_504_);
lean_inc(v_v_503_);
lean_inc(v_k_502_);
v_isSharedCheck_648_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; 
v_unused_649_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_l_321_, 2);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_l_321_, 1);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_653_);
v___x_514_ = v_l_321_;
v_isShared_515_ = v_isSharedCheck_648_;
goto v_resetjp_513_;
}
else
{
lean_dec(v_l_321_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_648_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_tree_517_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_502_, v_v_503_, v_l_504_, v_r_505_);
v_tree_517_ = lean_ctor_get(v___x_516_, 2);
lean_inc(v_tree_517_);
if (lean_obj_tag(v_tree_517_) == 0)
{
lean_object* v_k_518_; lean_object* v_v_519_; lean_object* v_size_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_k_518_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_k_518_);
v_v_519_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_v_519_);
lean_dec_ref(v___x_516_);
v_size_520_ = lean_ctor_get(v_tree_517_, 0);
v___x_521_ = lean_unsigned_to_nat(3u);
v___x_522_ = lean_nat_mul(v___x_521_, v_size_520_);
v___x_523_ = lean_nat_dec_lt(v___x_522_, v_size_506_);
lean_dec(v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v_l_509_);
v___x_524_ = lean_nat_add(v___x_511_, v_size_520_);
v___x_525_ = lean_nat_add(v___x_524_, v_size_506_);
lean_dec(v___x_524_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v_r_322_);
lean_ctor_set(v___x_514_, 3, v_tree_517_);
lean_ctor_set(v___x_514_, 2, v_v_519_);
lean_ctor_set(v___x_514_, 1, v_k_518_);
lean_ctor_set(v___x_514_, 0, v___x_525_);
v___x_527_ = v___x_514_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_k_518_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_v_519_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v_tree_517_);
lean_ctor_set(v_reuseFailAlloc_528_, 4, v_r_322_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_583_; 
lean_inc(v_r_510_);
lean_inc(v_v_508_);
lean_inc(v_k_507_);
lean_inc(v_size_506_);
v_isSharedCheck_583_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; lean_object* v_unused_585_; lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; 
v_unused_584_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_584_);
v_unused_585_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_585_);
v_unused_586_ = lean_ctor_get(v_r_322_, 2);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_r_322_, 1);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_r_322_, 0);
lean_dec(v_unused_588_);
v___x_530_ = v_r_322_;
v_isShared_531_ = v_isSharedCheck_583_;
goto v_resetjp_529_;
}
else
{
lean_dec(v_r_322_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_583_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_size_532_; lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v_l_535_; lean_object* v_r_536_; lean_object* v_size_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_size_532_ = lean_ctor_get(v_l_509_, 0);
v_k_533_ = lean_ctor_get(v_l_509_, 1);
v_v_534_ = lean_ctor_get(v_l_509_, 2);
v_l_535_ = lean_ctor_get(v_l_509_, 3);
v_r_536_ = lean_ctor_get(v_l_509_, 4);
v_size_537_ = lean_ctor_get(v_r_510_, 0);
v___x_538_ = lean_unsigned_to_nat(2u);
v___x_539_ = lean_nat_mul(v___x_538_, v_size_537_);
v___x_540_ = lean_nat_dec_lt(v_size_532_, v___x_539_);
lean_dec(v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_568_; 
lean_inc(v_r_536_);
lean_inc(v_l_535_);
lean_inc(v_v_534_);
lean_inc(v_k_533_);
v_isSharedCheck_568_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; 
v_unused_569_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_l_509_, 2);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_l_509_, 1);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_573_);
v___x_542_ = v_l_509_;
v_isShared_543_ = v_isSharedCheck_568_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_l_509_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_568_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_558_; 
v___x_544_ = lean_nat_add(v___x_511_, v_size_520_);
v___x_545_ = lean_nat_add(v___x_544_, v_size_506_);
lean_dec(v_size_506_);
if (lean_obj_tag(v_l_535_) == 0)
{
lean_object* v_size_566_; 
v_size_566_ = lean_ctor_get(v_l_535_, 0);
lean_inc(v_size_566_);
v___y_558_ = v_size_566_;
goto v___jp_557_;
}
else
{
lean_object* v___x_567_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___y_558_ = v___x_567_;
goto v___jp_557_;
}
v___jp_546_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_nat_add(v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec(v___y_548_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_r_510_);
lean_ctor_set(v___x_542_, 3, v_r_536_);
lean_ctor_set(v___x_542_, 2, v_v_508_);
lean_ctor_set(v___x_542_, 1, v_k_507_);
lean_ctor_set(v___x_542_, 0, v___x_550_);
v___x_552_ = v___x_542_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_r_536_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_r_510_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v___x_552_);
lean_ctor_set(v___x_530_, 3, v___y_547_);
lean_ctor_set(v___x_530_, 2, v_v_534_);
lean_ctor_set(v___x_530_, 1, v_k_533_);
lean_ctor_set(v___x_530_, 0, v___x_545_);
v___x_554_ = v___x_530_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v___y_547_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_nat_add(v___x_544_, v___y_558_);
lean_dec(v___y_558_);
lean_dec(v___x_544_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v_l_535_);
lean_ctor_set(v___x_514_, 3, v_tree_517_);
lean_ctor_set(v___x_514_, 2, v_v_519_);
lean_ctor_set(v___x_514_, 1, v_k_518_);
lean_ctor_set(v___x_514_, 0, v___x_559_);
v___x_561_ = v___x_514_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_k_518_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_v_519_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_tree_517_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v_l_535_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; 
v___x_562_ = lean_nat_add(v___x_511_, v_size_537_);
if (lean_obj_tag(v_r_536_) == 0)
{
lean_object* v_size_563_; 
v_size_563_ = lean_ctor_get(v_r_536_, 0);
lean_inc(v_size_563_);
v___y_547_ = v___x_561_;
v___y_548_ = v___x_562_;
v___y_549_ = v_size_563_;
goto v___jp_546_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___y_547_ = v___x_561_;
v___y_548_ = v___x_562_;
v___y_549_ = v___x_564_;
goto v___jp_546_;
}
}
}
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_574_ = lean_nat_add(v___x_511_, v_size_520_);
v___x_575_ = lean_nat_add(v___x_574_, v_size_506_);
lean_dec(v_size_506_);
v___x_576_ = lean_nat_add(v___x_574_, v_size_532_);
lean_dec(v___x_574_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 4, v_l_509_);
lean_ctor_set(v___x_530_, 3, v_tree_517_);
lean_ctor_set(v___x_530_, 2, v_v_519_);
lean_ctor_set(v___x_530_, 1, v_k_518_);
lean_ctor_set(v___x_530_, 0, v___x_576_);
v___x_578_ = v___x_530_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_k_518_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_v_519_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_tree_517_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_l_509_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v_r_510_);
lean_ctor_set(v___x_514_, 3, v___x_578_);
lean_ctor_set(v___x_514_, 2, v_v_508_);
lean_ctor_set(v___x_514_, 1, v_k_507_);
lean_ctor_set(v___x_514_, 0, v___x_575_);
v___x_580_ = v___x_514_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_r_510_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
else
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_642_; 
lean_inc(v_r_510_);
lean_inc(v_v_508_);
lean_inc(v_k_507_);
lean_inc(v_size_506_);
v_isSharedCheck_642_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; 
v_unused_643_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_r_322_, 2);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_r_322_, 1);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_r_322_, 0);
lean_dec(v_unused_647_);
v___x_590_ = v_r_322_;
v_isShared_591_ = v_isSharedCheck_642_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_r_322_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_642_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
if (lean_obj_tag(v_l_509_) == 0)
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_k_592_; lean_object* v_v_593_; lean_object* v_size_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_k_592_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_k_592_);
v_v_593_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_v_593_);
lean_dec_ref(v___x_516_);
v_size_594_ = lean_ctor_get(v_l_509_, 0);
v___x_595_ = lean_nat_add(v___x_511_, v_size_506_);
lean_dec(v_size_506_);
v___x_596_ = lean_nat_add(v___x_511_, v_size_594_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 4, v_l_509_);
lean_ctor_set(v___x_590_, 3, v_tree_517_);
lean_ctor_set(v___x_590_, 2, v_v_593_);
lean_ctor_set(v___x_590_, 1, v_k_592_);
lean_ctor_set(v___x_590_, 0, v___x_596_);
v___x_598_ = v___x_590_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_k_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_v_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_tree_517_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_l_509_);
v___x_598_ = v_reuseFailAlloc_602_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v_r_510_);
lean_ctor_set(v___x_514_, 3, v___x_598_);
lean_ctor_set(v___x_514_, 2, v_v_508_);
lean_ctor_set(v___x_514_, 1, v_k_507_);
lean_ctor_set(v___x_514_, 0, v___x_595_);
v___x_600_ = v___x_514_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_r_510_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_k_603_; lean_object* v_v_604_; lean_object* v_k_605_; lean_object* v_v_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_size_506_);
v_k_603_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_k_603_);
v_v_604_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_v_604_);
lean_dec_ref(v___x_516_);
v_k_605_ = lean_ctor_get(v_l_509_, 1);
v_v_606_ = lean_ctor_get(v_l_509_, 2);
v_isSharedCheck_620_ = !lean_is_exclusive(v_l_509_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; 
v_unused_621_ = lean_ctor_get(v_l_509_, 4);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_l_509_, 3);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_l_509_, 0);
lean_dec(v_unused_623_);
v___x_608_ = v_l_509_;
v_isShared_609_ = v_isSharedCheck_620_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_v_606_);
lean_inc(v_k_605_);
lean_dec(v_l_509_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_620_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_unsigned_to_nat(3u);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 4, v_r_510_);
lean_ctor_set(v___x_608_, 3, v_r_510_);
lean_ctor_set(v___x_608_, 2, v_v_604_);
lean_ctor_set(v___x_608_, 1, v_k_603_);
lean_ctor_set(v___x_608_, 0, v___x_511_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_603_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_r_510_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_r_510_);
v___x_612_ = v_reuseFailAlloc_619_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 3, v_r_510_);
lean_ctor_set(v___x_590_, 0, v___x_511_);
v___x_614_ = v___x_590_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_r_510_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_r_510_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v___x_614_);
lean_ctor_set(v___x_514_, 3, v___x_612_);
lean_ctor_set(v___x_514_, 2, v_v_606_);
lean_ctor_set(v___x_514_, 1, v_k_605_);
lean_ctor_set(v___x_514_, 0, v___x_610_);
v___x_616_ = v___x_514_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_606_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_510_) == 0)
{
lean_object* v_k_624_; lean_object* v_v_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
lean_dec(v_size_506_);
v_k_624_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_k_624_);
v_v_625_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_v_625_);
lean_dec_ref(v___x_516_);
v___x_626_ = lean_unsigned_to_nat(3u);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 4, v_l_509_);
lean_ctor_set(v___x_590_, 2, v_v_625_);
lean_ctor_set(v___x_590_, 1, v_k_624_);
lean_ctor_set(v___x_590_, 0, v___x_511_);
v___x_628_ = v___x_590_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_l_509_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_l_509_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v_r_510_);
lean_ctor_set(v___x_514_, 3, v___x_628_);
lean_ctor_set(v___x_514_, 2, v_v_508_);
lean_ctor_set(v___x_514_, 1, v_k_507_);
lean_ctor_set(v___x_514_, 0, v___x_626_);
v___x_630_ = v___x_514_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_r_510_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_object* v_k_633_; lean_object* v_v_634_; lean_object* v___x_636_; 
v_k_633_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_k_633_);
v_v_634_ = lean_ctor_get(v___x_516_, 1);
lean_inc(v_v_634_);
lean_dec_ref(v___x_516_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 3, v_r_510_);
v___x_636_ = v___x_590_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_size_506_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_r_510_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_r_510_);
v___x_636_ = v_reuseFailAlloc_641_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(2u);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v___x_636_);
lean_ctor_set(v___x_514_, 3, v_r_510_);
lean_ctor_set(v___x_514_, 2, v_v_634_);
lean_ctor_set(v___x_514_, 1, v_k_633_);
lean_ctor_set(v___x_514_, 0, v___x_637_);
v___x_639_ = v___x_514_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_633_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_r_510_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v___x_636_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
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
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_806_; 
lean_inc(v_r_510_);
lean_inc(v_v_508_);
lean_inc(v_k_507_);
v_isSharedCheck_806_ = !lean_is_exclusive(v_r_322_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_807_ = lean_ctor_get(v_r_322_, 4);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_r_322_, 3);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_r_322_, 2);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_r_322_, 1);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_r_322_, 0);
lean_dec(v_unused_811_);
v___x_655_ = v_r_322_;
v_isShared_656_ = v_isSharedCheck_806_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_r_322_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_806_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v_tree_658_; 
v___x_657_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_507_, v_v_508_, v_l_509_, v_r_510_);
v_tree_658_ = lean_ctor_get(v___x_657_, 2);
lean_inc(v_tree_658_);
if (lean_obj_tag(v_tree_658_) == 0)
{
lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_size_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_k_659_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_k_659_);
v_v_660_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_v_660_);
lean_dec_ref(v___x_657_);
v_size_661_ = lean_ctor_get(v_tree_658_, 0);
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = lean_nat_mul(v___x_662_, v_size_661_);
v___x_664_ = lean_nat_dec_lt(v___x_663_, v_size_501_);
lean_dec(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_dec(v_r_505_);
v___x_665_ = lean_nat_add(v___x_511_, v_size_501_);
v___x_666_ = lean_nat_add(v___x_665_, v_size_661_);
lean_dec(v___x_665_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_tree_658_);
lean_ctor_set(v___x_655_, 3, v_l_321_);
lean_ctor_set(v___x_655_, 2, v_v_660_);
lean_ctor_set(v___x_655_, 1, v_k_659_);
lean_ctor_set(v___x_655_, 0, v___x_666_);
v___x_668_ = v___x_655_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_l_321_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_tree_658_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_735_; 
lean_inc(v_l_504_);
lean_inc(v_v_503_);
lean_inc(v_k_502_);
lean_inc(v_size_501_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_736_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_l_321_, 2);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_l_321_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_740_);
v___x_671_ = v_l_321_;
v_isShared_672_ = v_isSharedCheck_735_;
goto v_resetjp_670_;
}
else
{
lean_dec(v_l_321_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_735_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_size_673_; lean_object* v_size_674_; lean_object* v_k_675_; lean_object* v_v_676_; lean_object* v_l_677_; lean_object* v_r_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_size_673_ = lean_ctor_get(v_l_504_, 0);
v_size_674_ = lean_ctor_get(v_r_505_, 0);
v_k_675_ = lean_ctor_get(v_r_505_, 1);
v_v_676_ = lean_ctor_get(v_r_505_, 2);
v_l_677_ = lean_ctor_get(v_r_505_, 3);
v_r_678_ = lean_ctor_get(v_r_505_, 4);
v___x_679_ = lean_unsigned_to_nat(2u);
v___x_680_ = lean_nat_mul(v___x_679_, v_size_673_);
v___x_681_ = lean_nat_dec_lt(v_size_674_, v___x_680_);
lean_dec(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_719_; 
lean_inc(v_r_678_);
lean_inc(v_l_677_);
lean_inc(v_v_676_);
lean_inc(v_k_675_);
lean_del_object(v___x_671_);
v_isSharedCheck_719_ = !lean_is_exclusive(v_r_505_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; 
v_unused_720_ = lean_ctor_get(v_r_505_, 4);
lean_dec(v_unused_720_);
v_unused_721_ = lean_ctor_get(v_r_505_, 3);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_r_505_, 2);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_r_505_, 1);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_r_505_, 0);
lean_dec(v_unused_724_);
v___x_683_ = v_r_505_;
v_isShared_684_ = v_isSharedCheck_719_;
goto v_resetjp_682_;
}
else
{
lean_dec(v_r_505_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_719_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___x_707_; lean_object* v___y_709_; 
v___x_685_ = lean_nat_add(v___x_511_, v_size_501_);
lean_dec(v_size_501_);
v___x_686_ = lean_nat_add(v___x_685_, v_size_661_);
lean_dec(v___x_685_);
v___x_707_ = lean_nat_add(v___x_511_, v_size_673_);
if (lean_obj_tag(v_l_677_) == 0)
{
lean_object* v_size_717_; 
v_size_717_ = lean_ctor_get(v_l_677_, 0);
lean_inc(v_size_717_);
v___y_709_ = v_size_717_;
goto v___jp_708_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___y_709_ = v___x_718_;
goto v___jp_708_;
}
v___jp_687_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_nat_add(v___y_688_, v___y_690_);
lean_dec(v___y_690_);
lean_dec(v___y_688_);
lean_inc_ref(v_tree_658_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 4, v_tree_658_);
lean_ctor_set(v___x_683_, 3, v_r_678_);
lean_ctor_set(v___x_683_, 2, v_v_660_);
lean_ctor_set(v___x_683_, 1, v_k_659_);
lean_ctor_set(v___x_683_, 0, v___x_691_);
v___x_693_ = v___x_683_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_r_678_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_tree_658_);
v___x_693_ = v_reuseFailAlloc_706_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_isSharedCheck_700_ = !lean_is_exclusive(v_tree_658_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_701_ = lean_ctor_get(v_tree_658_, 4);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_tree_658_, 3);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_tree_658_, 2);
lean_dec(v_unused_703_);
v_unused_704_ = lean_ctor_get(v_tree_658_, 1);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_tree_658_, 0);
lean_dec(v_unused_705_);
v___x_695_ = v_tree_658_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_dec(v_tree_658_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 4, v___x_693_);
lean_ctor_set(v___x_695_, 3, v___y_689_);
lean_ctor_set(v___x_695_, 2, v_v_676_);
lean_ctor_set(v___x_695_, 1, v_k_675_);
lean_ctor_set(v___x_695_, 0, v___x_686_);
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_k_675_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_v_676_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___y_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_nat_add(v___x_707_, v___y_709_);
lean_dec(v___y_709_);
lean_dec(v___x_707_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_l_677_);
lean_ctor_set(v___x_655_, 3, v_l_504_);
lean_ctor_set(v___x_655_, 2, v_v_503_);
lean_ctor_set(v___x_655_, 1, v_k_502_);
lean_ctor_set(v___x_655_, 0, v___x_710_);
v___x_712_ = v___x_655_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_l_504_);
lean_ctor_set(v_reuseFailAlloc_716_, 4, v_l_677_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; 
v___x_713_ = lean_nat_add(v___x_511_, v_size_661_);
if (lean_obj_tag(v_r_678_) == 0)
{
lean_object* v_size_714_; 
v_size_714_ = lean_ctor_get(v_r_678_, 0);
lean_inc(v_size_714_);
v___y_688_ = v___x_713_;
v___y_689_ = v___x_712_;
v___y_690_ = v_size_714_;
goto v___jp_687_;
}
else
{
lean_object* v___x_715_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v___y_688_ = v___x_713_;
v___y_689_ = v___x_712_;
v___y_690_ = v___x_715_;
goto v___jp_687_;
}
}
}
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_725_ = lean_nat_add(v___x_511_, v_size_501_);
lean_dec(v_size_501_);
v___x_726_ = lean_nat_add(v___x_725_, v_size_661_);
lean_dec(v___x_725_);
v___x_727_ = lean_nat_add(v___x_511_, v_size_661_);
v___x_728_ = lean_nat_add(v___x_727_, v_size_674_);
lean_dec(v___x_727_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_tree_658_);
lean_ctor_set(v___x_655_, 3, v_r_505_);
lean_ctor_set(v___x_655_, 2, v_v_660_);
lean_ctor_set(v___x_655_, 1, v_k_659_);
lean_ctor_set(v___x_655_, 0, v___x_728_);
v___x_730_ = v___x_655_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_k_659_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_v_660_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_r_505_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_tree_658_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 4, v___x_730_);
lean_ctor_set(v___x_671_, 0, v___x_726_);
v___x_732_ = v___x_671_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_l_504_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_504_) == 0)
{
lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_764_; 
lean_inc_ref(v_l_504_);
lean_inc(v_v_503_);
lean_inc(v_k_502_);
lean_inc(v_size_501_);
v_isSharedCheck_764_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; 
v_unused_765_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_321_, 2);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_321_, 1);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_769_);
v___x_742_ = v_l_321_;
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
else
{
lean_dec(v_l_321_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_764_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
if (lean_obj_tag(v_r_505_) == 0)
{
lean_object* v_k_744_; lean_object* v_v_745_; lean_object* v_size_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v_k_744_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_k_744_);
v_v_745_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_v_745_);
lean_dec_ref(v___x_657_);
v_size_746_ = lean_ctor_get(v_r_505_, 0);
v___x_747_ = lean_nat_add(v___x_511_, v_size_501_);
lean_dec(v_size_501_);
v___x_748_ = lean_nat_add(v___x_511_, v_size_746_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_tree_658_);
lean_ctor_set(v___x_655_, 3, v_r_505_);
lean_ctor_set(v___x_655_, 2, v_v_745_);
lean_ctor_set(v___x_655_, 1, v_k_744_);
lean_ctor_set(v___x_655_, 0, v___x_748_);
v___x_750_ = v___x_655_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_744_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_745_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_r_505_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_tree_658_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v___x_750_);
lean_ctor_set(v___x_742_, 0, v___x_747_);
v___x_752_ = v___x_742_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_l_504_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v_k_755_; lean_object* v_v_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec(v_size_501_);
v_k_755_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_k_755_);
v_v_756_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_v_756_);
lean_dec_ref(v___x_657_);
v___x_757_ = lean_unsigned_to_nat(3u);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_r_505_);
lean_ctor_set(v___x_655_, 3, v_r_505_);
lean_ctor_set(v___x_655_, 2, v_v_756_);
lean_ctor_set(v___x_655_, 1, v_k_755_);
lean_ctor_set(v___x_655_, 0, v___x_511_);
v___x_759_ = v___x_655_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_r_505_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_r_505_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v___x_759_);
lean_ctor_set(v___x_742_, 0, v___x_757_);
v___x_761_ = v___x_742_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_l_504_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_505_) == 0)
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_794_; 
lean_inc(v_l_504_);
lean_inc(v_v_503_);
lean_inc(v_k_502_);
v_isSharedCheck_794_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_795_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_l_321_, 2);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_l_321_, 1);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_799_);
v___x_771_ = v_l_321_;
v_isShared_772_ = v_isSharedCheck_794_;
goto v_resetjp_770_;
}
else
{
lean_dec(v_l_321_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_794_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_k_773_; lean_object* v_v_774_; lean_object* v_k_775_; lean_object* v_v_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_790_; 
v_k_773_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_k_773_);
v_v_774_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_v_774_);
lean_dec_ref(v___x_657_);
v_k_775_ = lean_ctor_get(v_r_505_, 1);
v_v_776_ = lean_ctor_get(v_r_505_, 2);
v_isSharedCheck_790_ = !lean_is_exclusive(v_r_505_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_791_ = lean_ctor_get(v_r_505_, 4);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_r_505_, 3);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_r_505_, 0);
lean_dec(v_unused_793_);
v___x_778_ = v_r_505_;
v_isShared_779_ = v_isSharedCheck_790_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_v_776_);
lean_inc(v_k_775_);
lean_dec(v_r_505_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_790_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_unsigned_to_nat(3u);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v_l_504_);
lean_ctor_set(v___x_778_, 3, v_l_504_);
lean_ctor_set(v___x_778_, 2, v_v_503_);
lean_ctor_set(v___x_778_, 1, v_k_502_);
lean_ctor_set(v___x_778_, 0, v___x_511_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_l_504_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v_l_504_);
v___x_782_ = v_reuseFailAlloc_789_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_l_504_);
lean_ctor_set(v___x_655_, 3, v_l_504_);
lean_ctor_set(v___x_655_, 2, v_v_774_);
lean_ctor_set(v___x_655_, 1, v_k_773_);
lean_ctor_set(v___x_655_, 0, v___x_511_);
v___x_784_ = v___x_655_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_k_773_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_v_774_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_l_504_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v_l_504_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 4, v___x_784_);
lean_ctor_set(v___x_771_, 3, v___x_782_);
lean_ctor_set(v___x_771_, 2, v_v_776_);
lean_ctor_set(v___x_771_, 1, v_k_775_);
lean_ctor_set(v___x_771_, 0, v___x_780_);
v___x_786_ = v___x_771_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_775_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_776_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
else
{
lean_object* v_k_800_; lean_object* v_v_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v_k_800_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_k_800_);
v_v_801_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_v_801_);
lean_dec_ref(v___x_657_);
v___x_802_ = lean_unsigned_to_nat(2u);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_r_505_);
lean_ctor_set(v___x_655_, 3, v_l_321_);
lean_ctor_set(v___x_655_, 2, v_v_801_);
lean_ctor_set(v___x_655_, 1, v_k_800_);
lean_ctor_set(v___x_655_, 0, v___x_802_);
v___x_804_ = v___x_655_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_801_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_l_321_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_r_505_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
}
else
{
return v_l_321_;
}
}
else
{
return v_r_322_;
}
}
default: 
{
lean_object* v_impl_812_; lean_object* v___x_813_; 
v_impl_812_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_317_, v_r_322_);
v___x_813_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_812_) == 0)
{
if (lean_obj_tag(v_l_321_) == 0)
{
lean_object* v_size_814_; lean_object* v_size_815_; lean_object* v_k_816_; lean_object* v_v_817_; lean_object* v_l_818_; lean_object* v_r_819_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_size_814_ = lean_ctor_get(v_impl_812_, 0);
lean_inc(v_size_814_);
v_size_815_ = lean_ctor_get(v_l_321_, 0);
v_k_816_ = lean_ctor_get(v_l_321_, 1);
v_v_817_ = lean_ctor_get(v_l_321_, 2);
v_l_818_ = lean_ctor_get(v_l_321_, 3);
v_r_819_ = lean_ctor_get(v_l_321_, 4);
lean_inc(v_r_819_);
v___x_820_ = lean_unsigned_to_nat(3u);
v___x_821_ = lean_nat_mul(v___x_820_, v_size_814_);
v___x_822_ = lean_nat_dec_lt(v___x_821_, v_size_815_);
lean_dec(v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_dec(v_r_819_);
v___x_823_ = lean_nat_add(v___x_813_, v_size_815_);
v___x_824_ = lean_nat_add(v___x_823_, v_size_814_);
lean_dec(v_size_814_);
lean_dec(v___x_823_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_impl_812_);
lean_ctor_set(v___x_324_, 0, v___x_824_);
v___x_826_ = v___x_324_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v_l_321_);
lean_ctor_set(v_reuseFailAlloc_827_, 4, v_impl_812_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_893_; 
lean_inc(v_l_818_);
lean_inc(v_v_817_);
lean_inc(v_k_816_);
lean_inc(v_size_815_);
v_isSharedCheck_893_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; lean_object* v_unused_895_; lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; 
v_unused_894_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_l_321_, 2);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_l_321_, 1);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_898_);
v___x_829_ = v_l_321_;
v_isShared_830_ = v_isSharedCheck_893_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_l_321_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_893_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_size_831_; lean_object* v_size_832_; lean_object* v_k_833_; lean_object* v_v_834_; lean_object* v_l_835_; lean_object* v_r_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_size_831_ = lean_ctor_get(v_l_818_, 0);
v_size_832_ = lean_ctor_get(v_r_819_, 0);
v_k_833_ = lean_ctor_get(v_r_819_, 1);
v_v_834_ = lean_ctor_get(v_r_819_, 2);
v_l_835_ = lean_ctor_get(v_r_819_, 3);
v_r_836_ = lean_ctor_get(v_r_819_, 4);
v___x_837_ = lean_unsigned_to_nat(2u);
v___x_838_ = lean_nat_mul(v___x_837_, v_size_831_);
v___x_839_ = lean_nat_dec_lt(v_size_832_, v___x_838_);
lean_dec(v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_868_; 
lean_inc(v_r_836_);
lean_inc(v_l_835_);
lean_inc(v_v_834_);
lean_inc(v_k_833_);
v_isSharedCheck_868_ = !lean_is_exclusive(v_r_819_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_869_ = lean_ctor_get(v_r_819_, 4);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_r_819_, 3);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_r_819_, 2);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_r_819_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_r_819_, 0);
lean_dec(v_unused_873_);
v___x_841_ = v_r_819_;
v_isShared_842_ = v_isSharedCheck_868_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_r_819_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_868_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___x_856_; lean_object* v___y_858_; 
v___x_843_ = lean_nat_add(v___x_813_, v_size_815_);
lean_dec(v_size_815_);
v___x_844_ = lean_nat_add(v___x_843_, v_size_814_);
lean_dec(v___x_843_);
v___x_856_ = lean_nat_add(v___x_813_, v_size_831_);
if (lean_obj_tag(v_l_835_) == 0)
{
lean_object* v_size_866_; 
v_size_866_ = lean_ctor_get(v_l_835_, 0);
lean_inc(v_size_866_);
v___y_858_ = v_size_866_;
goto v___jp_857_;
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_unsigned_to_nat(0u);
v___y_858_ = v___x_867_;
goto v___jp_857_;
}
v___jp_845_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_nat_add(v___y_846_, v___y_848_);
lean_dec(v___y_848_);
lean_dec(v___y_846_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 4, v_impl_812_);
lean_ctor_set(v___x_841_, 3, v_r_836_);
lean_ctor_set(v___x_841_, 2, v_v_320_);
lean_ctor_set(v___x_841_, 1, v_k_319_);
lean_ctor_set(v___x_841_, 0, v___x_849_);
v___x_851_ = v___x_841_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_r_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_impl_812_);
v___x_851_ = v_reuseFailAlloc_855_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 4, v___x_851_);
lean_ctor_set(v___x_829_, 3, v___y_847_);
lean_ctor_set(v___x_829_, 2, v_v_834_);
lean_ctor_set(v___x_829_, 1, v_k_833_);
lean_ctor_set(v___x_829_, 0, v___x_844_);
v___x_853_ = v___x_829_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_833_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_834_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v___y_847_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_nat_add(v___x_856_, v___y_858_);
lean_dec(v___y_858_);
lean_dec(v___x_856_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_l_835_);
lean_ctor_set(v___x_324_, 3, v_l_818_);
lean_ctor_set(v___x_324_, 2, v_v_817_);
lean_ctor_set(v___x_324_, 1, v_k_816_);
lean_ctor_set(v___x_324_, 0, v___x_859_);
v___x_861_ = v___x_324_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_816_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_817_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_l_818_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_l_835_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = lean_nat_add(v___x_813_, v_size_814_);
lean_dec(v_size_814_);
if (lean_obj_tag(v_r_836_) == 0)
{
lean_object* v_size_863_; 
v_size_863_ = lean_ctor_get(v_r_836_, 0);
lean_inc(v_size_863_);
v___y_846_ = v___x_862_;
v___y_847_ = v___x_861_;
v___y_848_ = v_size_863_;
goto v___jp_845_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___y_846_ = v___x_862_;
v___y_847_ = v___x_861_;
v___y_848_ = v___x_864_;
goto v___jp_845_;
}
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
lean_del_object(v___x_324_);
v___x_874_ = lean_nat_add(v___x_813_, v_size_815_);
lean_dec(v_size_815_);
v___x_875_ = lean_nat_add(v___x_874_, v_size_814_);
lean_dec(v___x_874_);
v___x_876_ = lean_nat_add(v___x_813_, v_size_814_);
lean_dec(v_size_814_);
v___x_877_ = lean_nat_add(v___x_876_, v_size_832_);
lean_dec(v___x_876_);
lean_inc_ref(v_impl_812_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 4, v_impl_812_);
lean_ctor_set(v___x_829_, 3, v_r_819_);
lean_ctor_set(v___x_829_, 2, v_v_320_);
lean_ctor_set(v___x_829_, 1, v_k_319_);
lean_ctor_set(v___x_829_, 0, v___x_877_);
v___x_879_ = v___x_829_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_r_819_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_impl_812_);
v___x_879_ = v_reuseFailAlloc_892_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_isSharedCheck_886_ = !lean_is_exclusive(v_impl_812_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; lean_object* v_unused_888_; lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_887_ = lean_ctor_get(v_impl_812_, 4);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_impl_812_, 3);
lean_dec(v_unused_888_);
v_unused_889_ = lean_ctor_get(v_impl_812_, 2);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_impl_812_, 1);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_impl_812_, 0);
lean_dec(v_unused_891_);
v___x_881_ = v_impl_812_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_dec(v_impl_812_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 4, v___x_879_);
lean_ctor_set(v___x_881_, 3, v_l_818_);
lean_ctor_set(v___x_881_, 2, v_v_817_);
lean_ctor_set(v___x_881_, 1, v_k_816_);
lean_ctor_set(v___x_881_, 0, v___x_875_);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_816_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_817_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_l_818_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v___x_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v_size_899_ = lean_ctor_get(v_impl_812_, 0);
lean_inc(v_size_899_);
v___x_900_ = lean_nat_add(v___x_813_, v_size_899_);
lean_dec(v_size_899_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_impl_812_);
lean_ctor_set(v___x_324_, 0, v___x_900_);
v___x_902_ = v___x_324_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_l_321_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_impl_812_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
if (lean_obj_tag(v_l_321_) == 0)
{
lean_object* v_l_904_; 
v_l_904_ = lean_ctor_get(v_l_321_, 3);
if (lean_obj_tag(v_l_904_) == 0)
{
lean_object* v_r_905_; 
lean_inc_ref(v_l_904_);
v_r_905_ = lean_ctor_get(v_l_321_, 4);
lean_inc(v_r_905_);
if (lean_obj_tag(v_r_905_) == 0)
{
lean_object* v_size_906_; lean_object* v_k_907_; lean_object* v_v_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_921_; 
v_size_906_ = lean_ctor_get(v_l_321_, 0);
v_k_907_ = lean_ctor_get(v_l_321_, 1);
v_v_908_ = lean_ctor_get(v_l_321_, 2);
v_isSharedCheck_921_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; lean_object* v_unused_923_; 
v_unused_922_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_923_);
v___x_910_ = v_l_321_;
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_v_908_);
lean_inc(v_k_907_);
lean_inc(v_size_906_);
lean_dec(v_l_321_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_size_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v_size_912_ = lean_ctor_get(v_r_905_, 0);
v___x_913_ = lean_nat_add(v___x_813_, v_size_906_);
lean_dec(v_size_906_);
v___x_914_ = lean_nat_add(v___x_813_, v_size_912_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 4, v_impl_812_);
lean_ctor_set(v___x_910_, 3, v_r_905_);
lean_ctor_set(v___x_910_, 2, v_v_320_);
lean_ctor_set(v___x_910_, 1, v_k_319_);
lean_ctor_set(v___x_910_, 0, v___x_914_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_r_905_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_impl_812_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v___x_916_);
lean_ctor_set(v___x_324_, 3, v_l_904_);
lean_ctor_set(v___x_324_, 2, v_v_908_);
lean_ctor_set(v___x_324_, 1, v_k_907_);
lean_ctor_set(v___x_324_, 0, v___x_913_);
v___x_918_ = v___x_324_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_k_907_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_v_908_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_l_904_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_k_924_; lean_object* v_v_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_936_; 
v_k_924_ = lean_ctor_get(v_l_321_, 1);
v_v_925_ = lean_ctor_get(v_l_321_, 2);
v_isSharedCheck_936_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_937_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_939_);
v___x_927_ = v_l_321_;
v_isShared_928_ = v_isSharedCheck_936_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_v_925_);
lean_inc(v_k_924_);
lean_dec(v_l_321_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_936_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = lean_unsigned_to_nat(3u);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 3, v_r_905_);
lean_ctor_set(v___x_927_, 2, v_v_320_);
lean_ctor_set(v___x_927_, 1, v_k_319_);
lean_ctor_set(v___x_927_, 0, v___x_813_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_r_905_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_r_905_);
v___x_931_ = v_reuseFailAlloc_935_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v___x_931_);
lean_ctor_set(v___x_324_, 3, v_l_904_);
lean_ctor_set(v___x_324_, 2, v_v_925_);
lean_ctor_set(v___x_324_, 1, v_k_924_);
lean_ctor_set(v___x_324_, 0, v___x_929_);
v___x_933_ = v___x_324_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_k_924_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_v_925_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_l_904_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
else
{
lean_object* v_r_940_; 
v_r_940_ = lean_ctor_get(v_l_321_, 4);
lean_inc(v_r_940_);
if (lean_obj_tag(v_r_940_) == 0)
{
lean_object* v_k_941_; lean_object* v_v_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_965_; 
lean_inc(v_l_904_);
v_k_941_ = lean_ctor_get(v_l_321_, 1);
v_v_942_ = lean_ctor_get(v_l_321_, 2);
v_isSharedCheck_965_ = !lean_is_exclusive(v_l_321_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; lean_object* v_unused_967_; lean_object* v_unused_968_; 
v_unused_966_ = lean_ctor_get(v_l_321_, 4);
lean_dec(v_unused_966_);
v_unused_967_ = lean_ctor_get(v_l_321_, 3);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_l_321_, 0);
lean_dec(v_unused_968_);
v___x_944_ = v_l_321_;
v_isShared_945_ = v_isSharedCheck_965_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_v_942_);
lean_inc(v_k_941_);
lean_dec(v_l_321_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_965_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_k_946_; lean_object* v_v_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_961_; 
v_k_946_ = lean_ctor_get(v_r_940_, 1);
v_v_947_ = lean_ctor_get(v_r_940_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_r_940_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; 
v_unused_962_ = lean_ctor_get(v_r_940_, 4);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_r_940_, 3);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_r_940_, 0);
lean_dec(v_unused_964_);
v___x_949_ = v_r_940_;
v_isShared_950_ = v_isSharedCheck_961_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_v_947_);
lean_inc(v_k_946_);
lean_dec(v_r_940_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_961_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_unsigned_to_nat(3u);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 4, v_l_904_);
lean_ctor_set(v___x_949_, 3, v_l_904_);
lean_ctor_set(v___x_949_, 2, v_v_942_);
lean_ctor_set(v___x_949_, 1, v_k_941_);
lean_ctor_set(v___x_949_, 0, v___x_813_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_k_941_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_v_942_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_l_904_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_l_904_);
v___x_953_ = v_reuseFailAlloc_960_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_l_904_);
lean_ctor_set(v___x_944_, 2, v_v_320_);
lean_ctor_set(v___x_944_, 1, v_k_319_);
lean_ctor_set(v___x_944_, 0, v___x_813_);
v___x_955_ = v___x_944_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_l_904_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_l_904_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v___x_955_);
lean_ctor_set(v___x_324_, 3, v___x_953_);
lean_ctor_set(v___x_324_, 2, v_v_947_);
lean_ctor_set(v___x_324_, 1, v_k_946_);
lean_ctor_set(v___x_324_, 0, v___x_951_);
v___x_957_ = v___x_324_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_946_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_947_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v___x_955_);
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
}
}
else
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(2u);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_r_940_);
lean_ctor_set(v___x_324_, 0, v___x_969_);
v___x_971_ = v___x_324_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_l_321_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_r_940_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v___x_974_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 4, v_l_321_);
lean_ctor_set(v___x_324_, 0, v___x_813_);
v___x_974_ = v___x_324_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_l_321_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_l_321_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
}
else
{
return v_t_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object* v_k_978_, lean_object* v_t_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_978_, v_t_979_);
lean_dec(v_k_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object* v_o_981_, lean_object* v_k_982_){
_start:
{
lean_object* v_map_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_994_; 
v_map_983_ = lean_ctor_get(v_o_981_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v_o_981_);
if (v_isSharedCheck_994_ == 0)
{
v___x_985_ = v_o_981_;
v_isShared_986_ = v_isSharedCheck_994_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_map_983_);
lean_dec(v_o_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_994_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; lean_object* v___x_992_; 
lean_inc(v_map_983_);
v___x_987_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_982_, v_map_983_);
v___x_988_ = lean_box(0);
v___x_989_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v___x_988_, v_map_983_);
lean_dec(v_map_983_);
v___x_990_ = l_List_any___at___00Lean_Options_erase_spec__2(v___x_989_);
lean_dec(v___x_989_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_987_);
v___x_992_ = v___x_985_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_990_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object* v_o_995_, lean_object* v_k_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Options_erase(v_o_995_, v_k_996_);
lean_dec(v_k_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object* v_00_u03b2_998_, lean_object* v_k_999_, lean_object* v_t_1000_, lean_object* v_h_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_999_, v_t_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_k_1004_, lean_object* v_t_1005_, lean_object* v_h_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(v_00_u03b2_1003_, v_k_1004_, v_t_1005_, v_h_1006_);
lean_dec(v_k_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object* v_b_u2082_1008_, lean_object* v_f_1009_, lean_object* v_a_1010_, lean_object* v_x_1011_){
_start:
{
if (lean_obj_tag(v_x_1011_) == 0)
{
lean_object* v___x_1012_; 
lean_dec(v_a_1010_);
lean_dec_ref(v_f_1009_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_b_u2082_1008_);
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
v_val_1013_ = lean_ctor_get(v_x_1011_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_x_1011_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1015_ = v_x_1011_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_val_1013_);
lean_dec(v_x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_apply_3(v_f_1009_, v_a_1010_, v_val_1013_, v_b_u2082_1008_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object* v_b_u2082_1022_, lean_object* v_f_1023_, lean_object* v_a_1024_, lean_object* v_k_1025_, lean_object* v_t_1026_){
_start:
{
if (lean_obj_tag(v_t_1026_) == 0)
{
lean_object* v_size_1027_; lean_object* v_k_1028_; lean_object* v_v_1029_; lean_object* v_l_1030_; lean_object* v_r_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1046_; 
v_size_1027_ = lean_ctor_get(v_t_1026_, 0);
v_k_1028_ = lean_ctor_get(v_t_1026_, 1);
v_v_1029_ = lean_ctor_get(v_t_1026_, 2);
v_l_1030_ = lean_ctor_get(v_t_1026_, 3);
v_r_1031_ = lean_ctor_get(v_t_1026_, 4);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_t_1026_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1033_ = v_t_1026_;
v_isShared_1034_ = v_isSharedCheck_1046_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_r_1031_);
lean_inc(v_l_1030_);
lean_inc(v_v_1029_);
lean_inc(v_k_1028_);
lean_inc(v_size_1027_);
lean_dec(v_t_1026_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1046_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v___x_1035_; 
v___x_1035_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1025_, v_k_1028_);
switch(v___x_1035_)
{
case 0:
{
lean_object* v_impl_1036_; lean_object* v___x_1037_; 
lean_del_object(v___x_1033_);
lean_dec(v_size_1027_);
v_impl_1036_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1022_, v_f_1023_, v_a_1024_, v_k_1025_, v_l_1030_);
v___x_1037_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1028_, v_v_1029_, v_impl_1036_, v_r_1031_);
return v___x_1037_;
}
case 1:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_val_1040_; lean_object* v___x_1042_; 
lean_dec(v_k_1028_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_v_1029_);
v___x_1039_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1022_, v_f_1023_, v_a_1024_, v___x_1038_);
v_val_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1040_);
lean_dec(v___x_1039_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 2, v_val_1040_);
lean_ctor_set(v___x_1033_, 1, v_k_1025_);
v___x_1042_ = v___x_1033_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_1027_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_1025_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_val_1040_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_r_1031_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
default: 
{
lean_object* v_impl_1044_; lean_object* v___x_1045_; 
lean_del_object(v___x_1033_);
lean_dec(v_size_1027_);
v_impl_1044_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1022_, v_f_1023_, v_a_1024_, v_k_1025_, v_r_1031_);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1028_, v_v_1029_, v_l_1030_, v_impl_1044_);
return v___x_1045_;
}
}
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_val_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1022_, v_f_1023_, v_a_1024_, v___x_1047_);
v_val_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1049_);
lean_dec(v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_k_1025_);
lean_ctor_set(v___x_1051_, 2, v_val_1049_);
lean_ctor_set(v___x_1051_, 3, v_t_1026_);
lean_ctor_set(v___x_1051_, 4, v_t_1026_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object* v_f_1052_, lean_object* v_init_1053_, lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v_k_1055_; lean_object* v_v_1056_; lean_object* v_l_1057_; lean_object* v_r_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_k_1055_ = lean_ctor_get(v_x_1054_, 1);
lean_inc_n(v_k_1055_, 2);
v_v_1056_ = lean_ctor_get(v_x_1054_, 2);
lean_inc(v_v_1056_);
v_l_1057_ = lean_ctor_get(v_x_1054_, 3);
lean_inc(v_l_1057_);
v_r_1058_ = lean_ctor_get(v_x_1054_, 4);
lean_inc(v_r_1058_);
lean_dec_ref_known(v_x_1054_, 5);
lean_inc_ref_n(v_f_1052_, 2);
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1052_, v_init_1053_, v_l_1057_);
v___x_1060_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_1056_, v_f_1052_, v_k_1055_, v_k_1055_, v___x_1059_);
v_init_1053_ = v___x_1060_;
v_x_1054_ = v_r_1058_;
goto _start;
}
else
{
lean_dec_ref(v_f_1052_);
return v_init_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object* v_f_1062_, lean_object* v_o1_1063_, lean_object* v_o2_1064_){
_start:
{
lean_object* v_map_1065_; uint8_t v_hasTrace_1066_; lean_object* v_map_1067_; uint8_t v_hasTrace_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1079_; 
v_map_1065_ = lean_ctor_get(v_o1_1063_, 0);
lean_inc(v_map_1065_);
v_hasTrace_1066_ = lean_ctor_get_uint8(v_o1_1063_, sizeof(void*)*1);
lean_dec_ref(v_o1_1063_);
v_map_1067_ = lean_ctor_get(v_o2_1064_, 0);
v_hasTrace_1068_ = lean_ctor_get_uint8(v_o2_1064_, sizeof(void*)*1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_o2_1064_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1070_ = v_o2_1064_;
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_map_1067_);
lean_dec(v_o2_1064_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1079_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1062_, v_map_1065_, v_map_1067_);
if (v_hasTrace_1066_ == 0)
{
lean_object* v___x_1074_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*1, v_hasTrace_1068_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v___x_1077_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1077_ = v___x_1070_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1, v_hasTrace_1066_);
return v___x_1077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object* v_b_u2082_1080_, lean_object* v_f_1081_, lean_object* v_a_1082_, lean_object* v_k_1083_, lean_object* v_t_1084_, lean_object* v_hl_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1080_, v_f_1081_, v_a_1082_, v_k_1083_, v_t_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object* v_f_1087_, lean_object* v_init_1088_, lean_object* v_t_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1087_, v_init_1088_, v_t_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
v___x_1124_ = l_Lean_mkAtom(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
v___x_1126_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1127_ = lean_array_push(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
v___x_1137_ = l_Lean_mkAtom(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
v___x_1139_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1140_ = lean_array_push(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
v___x_1142_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
v___x_1143_ = lean_box(2);
v___x_1144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v___x_1142_);
lean_ctor_set(v___x_1144_, 2, v___x_1141_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
v___x_1146_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
v___x_1147_ = lean_array_push(v___x_1146_, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
v___x_1149_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
v___x_1150_ = lean_box(2);
v___x_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
lean_ctor_set(v___x_1151_, 2, v___x_1148_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
v___x_1153_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1154_ = lean_array_push(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
v___x_1156_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1157_ = lean_box(2);
v___x_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
lean_ctor_set(v___x_1158_, 2, v___x_1155_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
v___x_1160_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1161_ = lean_array_push(v___x_1160_, v___x_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
v___x_1163_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
v___x_1164_ = lean_box(2);
v___x_1165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v___x_1162_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
v___x_1167_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1168_ = lean_array_push(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
v___x_1170_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
v___x_1171_ = lean_box(2);
v___x_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1170_);
lean_ctor_set(v___x_1172_, 2, v___x_1169_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__3(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = ((lean_object*)(l_Lean_instInhabitedOptionDeprecation_default___closed__0));
v___x_1182_ = l_Lean_instInhabitedDataValue_default;
v___x_1183_ = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__2));
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1183_);
lean_ctor_set(v___x_1185_, 2, v___x_1182_);
lean_ctor_set(v___x_1185_, 3, v___x_1181_);
lean_ctor_set(v___x_1185_, 4, v___x_1180_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__3, &l_Lean_instInhabitedOptionDecl_default___closed__3_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__3);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_instInhabitedOptionDecl_default;
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* v_self_1193_){
_start:
{
lean_object* v_descr_1195_; lean_object* v_name_1198_; lean_object* v_descr_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_name_1198_ = lean_ctor_get(v_self_1193_, 0);
lean_inc(v_name_1198_);
v_descr_1199_ = lean_ctor_get(v_self_1193_, 3);
lean_inc_ref(v_descr_1199_);
lean_dec_ref(v_self_1193_);
v___x_1200_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
v___x_1201_ = l_Lean_Name_isPrefixOf(v___x_1200_, v_name_1198_);
lean_dec(v_name_1198_);
if (v___x_1201_ == 0)
{
return v_descr_1199_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_string_utf8_byte_size(v_descr_1199_);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_nat_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v_descr_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
v_descr_1206_ = lean_string_append(v_descr_1199_, v___x_1205_);
v_descr_1195_ = v_descr_1206_;
goto v___jp_1194_;
}
else
{
v_descr_1195_ = v_descr_1199_;
goto v___jp_1194_;
}
}
v___jp_1194_:
{
lean_object* v___x_1196_; lean_object* v_descr_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
v_descr_1197_ = lean_string_append(v_descr_1195_, v___x_1196_);
return v_descr_1197_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_box(1);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_box(1);
v___x_1210_ = lean_st_mk_ref(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return v_res_1213_;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l_Lean_registerOption___closed__0));
v___x_1216_ = lean_mk_io_user_error(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* v_name_1219_, lean_object* v_decl_1220_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = l_Lean_initializing();
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_decl_1220_);
lean_dec(v_name_1219_);
v___x_1223_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1225_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1226_ = lean_st_ref_get(v___x_1225_);
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1219_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1219_, v_decl_1220_, v___x_1226_);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_st_ref_swap(v___x_1225_, v___x_1228_);
lean_dec(v___x_1230_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v___x_1226_);
lean_dec_ref(v_decl_1220_);
v___x_1232_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1233_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1219_, v___x_1227_);
v___x_1234_ = lean_string_append(v___x_1232_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1236_ = lean_string_append(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_mk_io_user_error(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1239_, lean_object* v_decl_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = lean_register_option(v_name_1239_, v_decl_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1245_ = lean_st_ref_get(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_getOptionDecls();
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* v_init_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_k_1251_; lean_object* v_v_1252_; lean_object* v_l_1253_; lean_object* v_r_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_k_1251_ = lean_ctor_get(v_x_1250_, 1);
v_v_1252_ = lean_ctor_get(v_x_1250_, 2);
v_l_1253_ = lean_ctor_get(v_x_1250_, 3);
v_r_1254_ = lean_ctor_get(v_x_1250_, 4);
v___x_1255_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1249_, v_l_1253_);
lean_inc(v_v_1252_);
lean_inc(v_k_1251_);
v___x_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1256_, 0, v_k_1251_);
lean_ctor_set(v___x_1256_, 1, v_v_1252_);
v___x_1257_ = lean_array_push(v___x_1255_, v___x_1256_);
v_init_1249_ = v___x_1257_;
v_x_1250_ = v_r_1254_;
goto _start;
}
else
{
return v_init_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* v_init_1259_, lean_object* v_x_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1259_, v_x_1260_);
lean_dec(v_x_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(){
_start:
{
lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1275_; 
v___x_1265_ = l_Lean_getOptionDecls();
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1275_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1270_ = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
v___x_1271_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_1270_, v_a_1266_);
lean_dec(v_a_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1271_);
v___x_1273_ = v___x_1268_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = lean_get_option_decls_array();
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* v_init_1278_, lean_object* v_t_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1278_, v_t_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* v_init_1281_, lean_object* v_t_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(v_init_1281_, v_t_1282_);
lean_dec(v_t_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* v_name_1286_){
_start:
{
lean_object* v___x_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1308_; 
v___x_1288_ = l_Lean_getOptionDecls();
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1308_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1308_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1289_, v_name_1286_);
lean_dec(v_a_1289_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1296_; 
lean_dec(v_name_1286_);
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v___x_1293_, 1);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_val_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_val_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
else
{
lean_object* v___x_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
lean_dec(v___x_1293_);
v___x_1298_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1299_ = 1;
v___x_1300_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1286_, v___x_1299_);
v___x_1301_ = lean_string_append(v___x_1298_, v___x_1300_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1303_ = lean_string_append(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_mk_io_user_error(v___x_1303_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set_tag(v___x_1291_, 1);
lean_ctor_set(v___x_1291_, 0, v___x_1304_);
v___x_1306_ = v___x_1291_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_getOptionDecl(v_name_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_getOptionDecl(v_name_1312_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_defValue_1319_; lean_object* v___x_1321_; 
v_defValue_1319_ = lean_ctor_get(v_a_1315_, 2);
lean_inc_ref(v_defValue_1319_);
lean_dec(v_a_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_defValue_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_defValue_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_a_1324_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1314_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1314_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_getOptionDefaultValue(v_name_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* v_name_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_getOptionDecl(v_name_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1346_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1346_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_descr_1342_; lean_object* v___x_1344_; 
v_descr_1342_ = lean_ctor_get(v_a_1338_, 3);
lean_inc_ref(v_descr_1342_);
lean_dec(v_a_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_descr_1342_);
v___x_1344_ = v___x_1340_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_descr_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1347_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_getOptionDescr(v_name_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1358_, lean_object* v_inst_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_apply_2(v_inst_1358_, lean_box(0), v_inst_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1361_, lean_object* v_n_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_apply_2(v_inst_1363_, lean_box(0), v_inst_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1366_, lean_object* v_toPure_1367_, uint8_t v_defValue_1368_, lean_object* v_opts_1369_){
_start:
{
lean_object* v_map_1370_; lean_object* v___x_1371_; 
v_map_1370_ = lean_ctor_get(v_opts_1369_, 0);
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1370_, v_k_1366_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_box(v_defValue_1368_);
v___x_1373_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1372_);
return v___x_1373_;
}
else
{
lean_object* v_val_1374_; 
v_val_1374_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_val_1374_);
lean_dec_ref_known(v___x_1371_, 1);
if (lean_obj_tag(v_val_1374_) == 1)
{
uint8_t v_v_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_v_1375_ = lean_ctor_get_uint8(v_val_1374_, 0);
lean_dec_ref_known(v_val_1374_, 0);
v___x_1376_ = lean_box(v_v_1375_);
v___x_1377_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1376_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_val_1374_);
v___x_1378_ = lean_box(v_defValue_1368_);
v___x_1379_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1378_);
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1380_, lean_object* v_toPure_1381_, lean_object* v_defValue_1382_, lean_object* v_opts_1383_){
_start:
{
uint8_t v_defValue_boxed_1384_; lean_object* v_res_1385_; 
v_defValue_boxed_1384_ = lean_unbox(v_defValue_1382_);
v_res_1385_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1380_, v_toPure_1381_, v_defValue_boxed_1384_, v_opts_1383_);
lean_dec_ref(v_opts_1383_);
lean_dec(v_k_1380_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_k_1388_, uint8_t v_defValue_1389_){
_start:
{
lean_object* v_toApplicative_1390_; lean_object* v_toBind_1391_; lean_object* v_toPure_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; 
v_toApplicative_1390_ = lean_ctor_get(v_inst_1386_, 0);
lean_inc_ref(v_toApplicative_1390_);
v_toBind_1391_ = lean_ctor_get(v_inst_1386_, 1);
lean_inc(v_toBind_1391_);
lean_dec_ref(v_inst_1386_);
v_toPure_1392_ = lean_ctor_get(v_toApplicative_1390_, 1);
lean_inc(v_toPure_1392_);
lean_dec_ref(v_toApplicative_1390_);
v___x_1393_ = lean_box(v_defValue_1389_);
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1394_, 0, v_k_1388_);
lean_closure_set(v___f_1394_, 1, v_toPure_1392_);
lean_closure_set(v___f_1394_, 2, v___x_1393_);
v___x_1395_ = lean_apply_4(v_toBind_1391_, lean_box(0), lean_box(0), v_inst_1387_, v___f_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_k_1398_, lean_object* v_defValue_1399_){
_start:
{
uint8_t v_defValue_boxed_1400_; lean_object* v_res_1401_; 
v_defValue_boxed_1400_ = lean_unbox(v_defValue_1399_);
v_res_1401_ = l_Lean_getBoolOption___redArg(v_inst_1396_, v_inst_1397_, v_k_1398_, v_defValue_boxed_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* v_m_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_k_1405_, uint8_t v_defValue_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_getBoolOption___redArg(v_inst_1403_, v_inst_1404_, v_k_1405_, v_defValue_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_k_1411_, lean_object* v_defValue_1412_){
_start:
{
uint8_t v_defValue_boxed_1413_; lean_object* v_res_1414_; 
v_defValue_boxed_1413_ = lean_unbox(v_defValue_1412_);
v_res_1414_ = l_Lean_getBoolOption(v_m_1408_, v_inst_1409_, v_inst_1410_, v_k_1411_, v_defValue_boxed_1413_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1415_, lean_object* v_toPure_1416_, lean_object* v_defValue_1417_, lean_object* v_opts_1418_){
_start:
{
lean_object* v_map_1419_; lean_object* v___x_1420_; 
v_map_1419_ = lean_ctor_get(v_opts_1418_, 0);
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1419_, v_k_1415_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_apply_2(v_toPure_1416_, lean_box(0), v_defValue_1417_);
return v___x_1421_;
}
else
{
lean_object* v_val_1422_; 
v_val_1422_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v___x_1420_, 1);
if (lean_obj_tag(v_val_1422_) == 3)
{
lean_object* v_v_1423_; lean_object* v___x_1424_; 
lean_dec(v_defValue_1417_);
v_v_1423_ = lean_ctor_get(v_val_1422_, 0);
lean_inc(v_v_1423_);
lean_dec_ref_known(v_val_1422_, 1);
v___x_1424_ = lean_apply_2(v_toPure_1416_, lean_box(0), v_v_1423_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_val_1422_);
v___x_1425_ = lean_apply_2(v_toPure_1416_, lean_box(0), v_defValue_1417_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1426_, lean_object* v_toPure_1427_, lean_object* v_defValue_1428_, lean_object* v_opts_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Lean_getNatOption___redArg___lam__0(v_k_1426_, v_toPure_1427_, v_defValue_1428_, v_opts_1429_);
lean_dec_ref(v_opts_1429_);
lean_dec(v_k_1426_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1431_, lean_object* v_inst_1432_, lean_object* v_k_1433_, lean_object* v_defValue_1434_){
_start:
{
lean_object* v_toApplicative_1435_; lean_object* v_toBind_1436_; lean_object* v_toPure_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; 
v_toApplicative_1435_ = lean_ctor_get(v_inst_1431_, 0);
lean_inc_ref(v_toApplicative_1435_);
v_toBind_1436_ = lean_ctor_get(v_inst_1431_, 1);
lean_inc(v_toBind_1436_);
lean_dec_ref(v_inst_1431_);
v_toPure_1437_ = lean_ctor_get(v_toApplicative_1435_, 1);
lean_inc(v_toPure_1437_);
lean_dec_ref(v_toApplicative_1435_);
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1438_, 0, v_k_1433_);
lean_closure_set(v___f_1438_, 1, v_toPure_1437_);
lean_closure_set(v___f_1438_, 2, v_defValue_1434_);
v___x_1439_ = lean_apply_4(v_toBind_1436_, lean_box(0), lean_box(0), v_inst_1432_, v___f_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_k_1443_, lean_object* v_defValue_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_getNatOption___redArg(v_inst_1441_, v_inst_1442_, v_k_1443_, v_defValue_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1446_, lean_object* v_f_1447_, lean_object* v_00_u03b2_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_apply_3(v_inst_1446_, lean_box(0), v_f_1447_, v___y_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_00_u03b1_1453_, lean_object* v_f_1454_, lean_object* v_x_1455_){
_start:
{
lean_object* v___f_1456_; lean_object* v___x_1457_; 
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1456_, 0, v_inst_1451_);
lean_closure_set(v___f_1456_, 1, v_f_1454_);
v___x_1457_ = lean_apply_3(v_inst_1452_, lean_box(0), v___f_1456_, v_x_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1458_, lean_object* v_inst_1459_){
_start:
{
lean_object* v___f_1460_; 
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1460_, 0, v_inst_1459_);
lean_closure_set(v___f_1460_, 1, v_inst_1458_);
return v___f_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1461_, lean_object* v_n_1462_, lean_object* v_inst_1463_, lean_object* v_inst_1464_){
_start:
{
lean_object* v___f_1465_; 
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1465_, 0, v_inst_1464_);
lean_closure_set(v___f_1465_, 1, v_inst_1463_);
return v___f_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1469_, lean_object* v_o_1470_){
_start:
{
lean_object* v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1472_ = 1;
v___x_1473_ = lean_box(v___x_1472_);
v___x_1474_ = l_Lean_Options_set___redArg(v___x_1469_, v_o_1470_, v___x_1471_, v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___f_1476_; 
v___x_1475_ = l_Lean_KVMap_instValueBool;
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1476_, 0, v___x_1475_);
return v___f_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1477_, lean_object* v_x_1478_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
v___f_1479_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1480_ = lean_apply_3(v_inst_1477_, lean_box(0), v___f_1479_, v_x_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1481_, lean_object* v_00_u03b1_1482_, lean_object* v_inst_1483_, lean_object* v_x_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_withInPattern___redArg(v_inst_1483_, v_x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1486_){
_start:
{
lean_object* v_map_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v_map_1487_ = lean_ctor_get(v_o_1486_, 0);
v___x_1488_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1489_ = 0;
v___x_1490_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1487_, v___x_1488_);
if (lean_obj_tag(v___x_1490_) == 0)
{
return v___x_1489_;
}
else
{
lean_object* v_val_1491_; 
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v___x_1490_, 1);
if (lean_obj_tag(v_val_1491_) == 1)
{
uint8_t v_v_1492_; 
v_v_1492_ = lean_ctor_get_uint8(v_val_1491_, 0);
lean_dec_ref_known(v_val_1491_, 0);
return v_v_1492_;
}
else
{
lean_dec(v_val_1491_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Lean_Options_getInPattern(v_o_1493_);
lean_dec_ref(v_o_1493_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_inst_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_00_u03b1_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1504_, lean_object* v_inst_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1507_, lean_object* v_opts_1508_, lean_object* v_opt_1509_){
_start:
{
lean_object* v_name_1510_; lean_object* v_map_1511_; lean_object* v_ofDataValue_x3f_1512_; lean_object* v___x_1513_; 
v_name_1510_ = lean_ctor_get(v_opt_1509_, 0);
v_map_1511_ = lean_ctor_get(v_opts_1508_, 0);
v_ofDataValue_x3f_1512_ = lean_ctor_get(v_inst_1507_, 1);
lean_inc_ref(v_ofDataValue_x3f_1512_);
lean_dec_ref(v_inst_1507_);
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1511_, v_name_1510_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
lean_dec_ref(v_ofDataValue_x3f_1512_);
v___x_1514_ = lean_box(0);
return v___x_1514_;
}
else
{
lean_object* v_val_1515_; lean_object* v___x_1516_; 
v_val_1515_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1516_ = lean_apply_1(v_ofDataValue_x3f_1512_, v_val_1515_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1517_, lean_object* v_opts_1518_, lean_object* v_opt_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Option_get_x3f___redArg(v_inst_1517_, v_opts_1518_, v_opt_1519_);
lean_dec_ref(v_opt_1519_);
lean_dec_ref(v_opts_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1521_, lean_object* v_inst_1522_, lean_object* v_opts_1523_, lean_object* v_opt_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Option_get_x3f___redArg(v_inst_1522_, v_opts_1523_, v_opt_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_inst_1527_, lean_object* v_opts_1528_, lean_object* v_opt_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Option_get_x3f(v_00_u03b1_1526_, v_inst_1527_, v_opts_1528_, v_opt_1529_);
lean_dec_ref(v_opt_1529_);
lean_dec_ref(v_opts_1528_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1531_, lean_object* v_opts_1532_, lean_object* v_opt_1533_){
_start:
{
lean_object* v_name_1534_; lean_object* v_defValue_1535_; lean_object* v_map_1536_; lean_object* v_ofDataValue_x3f_1537_; lean_object* v___x_1538_; 
v_name_1534_ = lean_ctor_get(v_opt_1533_, 0);
v_defValue_1535_ = lean_ctor_get(v_opt_1533_, 1);
v_map_1536_ = lean_ctor_get(v_opts_1532_, 0);
v_ofDataValue_x3f_1537_ = lean_ctor_get(v_inst_1531_, 1);
lean_inc_ref(v_ofDataValue_x3f_1537_);
lean_dec_ref(v_inst_1531_);
v___x_1538_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1536_, v_name_1534_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1537_);
lean_inc(v_defValue_1535_);
return v_defValue_1535_;
}
else
{
lean_object* v_val_1539_; lean_object* v___x_1540_; 
v_val_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = lean_apply_1(v_ofDataValue_x3f_1537_, v_val_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_inc(v_defValue_1535_);
return v_defValue_1535_;
}
else
{
lean_object* v_val_1541_; 
v_val_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v___x_1540_, 1);
return v_val_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1542_, lean_object* v_opts_1543_, lean_object* v_opt_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Option_get___redArg(v_inst_1542_, v_opts_1543_, v_opt_1544_);
lean_dec_ref(v_opt_1544_);
lean_dec_ref(v_opts_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1546_, lean_object* v_inst_1547_, lean_object* v_opts_1548_, lean_object* v_opt_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Option_get___redArg(v_inst_1547_, v_opts_1548_, v_opt_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1551_, lean_object* v_inst_1552_, lean_object* v_opts_1553_, lean_object* v_opt_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Option_get(v_00_u03b1_1551_, v_inst_1552_, v_opts_1553_, v_opt_1554_);
lean_dec_ref(v_opt_1554_);
lean_dec_ref(v_opts_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* v_opts_1556_, lean_object* v_name_1557_, uint8_t v_defValue_1558_){
_start:
{
lean_object* v_map_1559_; lean_object* v___x_1560_; 
v_map_1559_ = lean_ctor_get(v_opts_1556_, 0);
lean_inc(v_map_1559_);
lean_dec_ref(v_opts_1556_);
v___x_1560_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1559_, v_name_1557_);
lean_dec(v_name_1557_);
lean_dec(v_map_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
return v_defValue_1558_;
}
else
{
lean_object* v_val_1561_; 
v_val_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v___x_1560_, 1);
if (lean_obj_tag(v_val_1561_) == 1)
{
uint8_t v_v_1562_; 
v_v_1562_ = lean_ctor_get_uint8(v_val_1561_, 0);
lean_dec_ref_known(v_val_1561_, 0);
return v_v_1562_;
}
else
{
lean_dec(v_val_1561_);
return v_defValue_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* v_opts_1563_, lean_object* v_name_1564_, lean_object* v_defValue_1565_){
_start:
{
uint8_t v_defValue_boxed_1566_; uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_defValue_boxed_1566_ = lean_unbox(v_defValue_1565_);
v_res_1567_ = lean_options_get_bool(v_opts_1563_, v_name_1564_, v_defValue_boxed_1566_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* v_inst_1569_, lean_object* v_opt_1570_, lean_object* v_toPure_1571_, lean_object* v_____do__lift_1572_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = l_Lean_Option_get___redArg(v_inst_1569_, v_____do__lift_1572_, v_opt_1570_);
v___x_1574_ = lean_apply_2(v_toPure_1571_, lean_box(0), v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* v_inst_1575_, lean_object* v_opt_1576_, lean_object* v_toPure_1577_, lean_object* v_____do__lift_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Option_getM___redArg___lam__0(v_inst_1575_, v_opt_1576_, v_toPure_1577_, v_____do__lift_1578_);
lean_dec_ref(v_____do__lift_1578_);
lean_dec_ref(v_opt_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_opt_1583_){
_start:
{
lean_object* v_toApplicative_1584_; lean_object* v_toBind_1585_; lean_object* v_toPure_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; 
v_toApplicative_1584_ = lean_ctor_get(v_inst_1580_, 0);
lean_inc_ref(v_toApplicative_1584_);
v_toBind_1585_ = lean_ctor_get(v_inst_1580_, 1);
lean_inc(v_toBind_1585_);
lean_dec_ref(v_inst_1580_);
v_toPure_1586_ = lean_ctor_get(v_toApplicative_1584_, 1);
lean_inc(v_toPure_1586_);
lean_dec_ref(v_toApplicative_1584_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1587_, 0, v_inst_1582_);
lean_closure_set(v___f_1587_, 1, v_opt_1583_);
lean_closure_set(v___f_1587_, 2, v_toPure_1586_);
v___x_1588_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v_inst_1581_, v___f_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* v_m_1589_, lean_object* v_00_u03b1_1590_, lean_object* v_inst_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_opt_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Option_getM___redArg(v_inst_1591_, v_inst_1592_, v_inst_1593_, v_opt_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* v_inst_1596_, lean_object* v_opts_1597_, lean_object* v_opt_1598_, lean_object* v_val_1599_){
_start:
{
lean_object* v_name_1600_; lean_object* v___x_1601_; 
v_name_1600_ = lean_ctor_get(v_opt_1598_, 0);
lean_inc(v_name_1600_);
lean_dec_ref(v_opt_1598_);
v___x_1601_ = l_Lean_Options_set___redArg(v_inst_1596_, v_opts_1597_, v_name_1600_, v_val_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* v_00_u03b1_1602_, lean_object* v_inst_1603_, lean_object* v_opts_1604_, lean_object* v_opt_1605_, lean_object* v_val_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Option_set___redArg(v_inst_1603_, v_opts_1604_, v_opt_1605_, v_val_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1608_, lean_object* v_k_1609_, uint8_t v_v_1610_){
_start:
{
lean_object* v_map_1611_; uint8_t v_hasTrace_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1626_; 
v_map_1611_ = lean_ctor_get(v_o_1608_, 0);
v_hasTrace_1612_ = lean_ctor_get_uint8(v_o_1608_, sizeof(void*)*1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_o_1608_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1614_ = v_o_1608_;
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_map_1611_);
lean_dec(v_o_1608_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1626_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1616_, 0, v_v_1610_);
lean_inc(v_k_1609_);
v___x_1617_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1609_, v___x_1616_, v_map_1611_);
if (v_hasTrace_1612_ == 0)
{
lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1621_; 
v___x_1618_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_1619_ = l_Lean_Name_isPrefixOf(v___x_1618_, v_k_1609_);
lean_dec(v_k_1609_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1617_);
v___x_1621_ = v___x_1614_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1617_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*1, v___x_1619_);
return v___x_1621_;
}
}
else
{
lean_object* v___x_1624_; 
lean_dec(v_k_1609_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1617_);
v___x_1624_ = v___x_1614_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*1, v_hasTrace_1612_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1627_, lean_object* v_k_1628_, lean_object* v_v_1629_){
_start:
{
uint8_t v_v_boxed_1630_; lean_object* v_res_1631_; 
v_v_boxed_1630_ = lean_unbox(v_v_1629_);
v_res_1631_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1627_, v_k_1628_, v_v_boxed_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* v_opts_1632_, lean_object* v_name_1633_, uint8_t v_val_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1632_, v_name_1633_, v_val_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1636_, lean_object* v_name_1637_, lean_object* v_val_1638_){
_start:
{
uint8_t v_val_boxed_1639_; lean_object* v_res_1640_; 
v_val_boxed_1639_ = lean_unbox(v_val_1638_);
v_res_1640_ = lean_options_update_bool(v_opts_1636_, v_name_1637_, v_val_boxed_1639_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1641_, lean_object* v_opts_1642_, lean_object* v_opt_1643_, lean_object* v_val_1644_){
_start:
{
lean_object* v_name_1645_; lean_object* v_map_1646_; uint8_t v___x_1647_; 
v_name_1645_ = lean_ctor_get(v_opt_1643_, 0);
v_map_1646_ = lean_ctor_get(v_opts_1642_, 0);
v___x_1647_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1645_, v_map_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Option_set___redArg(v_inst_1641_, v_opts_1642_, v_opt_1643_, v_val_1644_);
return v___x_1648_;
}
else
{
lean_dec(v_val_1644_);
lean_dec_ref(v_opt_1643_);
lean_dec_ref(v_inst_1641_);
return v_opts_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1649_, lean_object* v_inst_1650_, lean_object* v_opts_1651_, lean_object* v_opt_1652_, lean_object* v_val_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1650_, v_opts_1651_, v_opt_1652_, v_val_1653_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1656_, lean_object* v_name_1657_, lean_object* v_decl_1658_, lean_object* v_ref_1659_){
_start:
{
lean_object* v_toDataValue_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1690_; 
v_toDataValue_1661_ = lean_ctor_get(v_inst_1656_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_inst_1656_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v_inst_1656_, 1);
lean_dec(v_unused_1691_);
v___x_1663_ = v_inst_1656_;
v_isShared_1664_ = v_isSharedCheck_1690_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_toDataValue_1661_);
lean_dec(v_inst_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1690_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_defValue_1665_; lean_object* v_descr_1666_; lean_object* v_deprecation_x3f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_defValue_1665_ = lean_ctor_get(v_decl_1658_, 0);
lean_inc_n(v_defValue_1665_, 2);
v_descr_1666_ = lean_ctor_get(v_decl_1658_, 1);
lean_inc_ref(v_descr_1666_);
v_deprecation_x3f_1667_ = lean_ctor_get(v_decl_1658_, 2);
lean_inc(v_deprecation_x3f_1667_);
lean_dec_ref(v_decl_1658_);
v___x_1668_ = lean_apply_1(v_toDataValue_1661_, v_defValue_1665_);
lean_inc_n(v_name_1657_, 2);
v___x_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1669_, 0, v_name_1657_);
lean_ctor_set(v___x_1669_, 1, v_ref_1659_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_ctor_set(v___x_1669_, 3, v_descr_1666_);
lean_ctor_set(v___x_1669_, 4, v_deprecation_x3f_1667_);
v___x_1670_ = lean_register_option(v_name_1657_, v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1680_; 
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; 
v_unused_1681_ = lean_ctor_get(v___x_1670_, 0);
lean_dec(v_unused_1681_);
v___x_1672_ = v___x_1670_;
v_isShared_1673_ = v_isSharedCheck_1680_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v___x_1670_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1680_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v_defValue_1665_);
lean_ctor_set(v___x_1663_, 0, v_name_1657_);
v___x_1675_ = v___x_1663_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_name_1657_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_defValue_1665_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_defValue_1665_);
lean_del_object(v___x_1663_);
lean_dec(v_name_1657_);
v_a_1682_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1670_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1670_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1692_, lean_object* v_name_1693_, lean_object* v_decl_1694_, lean_object* v_ref_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Option_register___redArg(v_inst_1692_, v_name_1693_, v_decl_1694_, v_ref_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1698_, lean_object* v_inst_1699_, lean_object* v_name_1700_, lean_object* v_decl_1701_, lean_object* v_ref_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Option_register___redArg(v_inst_1699_, v_name_1700_, v_decl_1701_, v_ref_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_inst_1706_, lean_object* v_name_1707_, lean_object* v_decl_1708_, lean_object* v_ref_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Option_register(v_00_u03b1_1705_, v_inst_1706_, v_name_1707_, v_decl_1708_, v_ref_1709_);
return v_res_1711_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
v___x_1800_ = l_String_toRawSubstring_x27(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
v___x_1821_ = l_String_toRawSubstring_x27(v___x_1820_);
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29(void){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Array_mkArray0___redArg();
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* v_x_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_1853_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(v_x_1849_);
v___x_1854_ = l_Lean_Syntax_isOfKind(v_x_1849_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_x_1849_);
v___x_1855_ = lean_box(1);
v___x_1856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_a_1851_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_name_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1991_; lean_object* v___x_2002_; 
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1857_);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1859_);
v___x_1861_ = lean_unsigned_to_nat(3u);
v_name_1862_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1861_);
v___x_1863_ = lean_unsigned_to_nat(5u);
v___x_1864_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1863_);
v___x_1865_ = lean_unsigned_to_nat(7u);
v___x_1866_ = l_Lean_Syntax_getArg(v_x_1849_, v___x_1865_);
lean_dec(v_x_1849_);
v___x_2002_ = l_Lean_Syntax_getOptional_x3f(v___x_1860_);
lean_dec(v___x_1860_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_box(0);
v___y_1991_ = v___x_2003_;
goto v___jp_1990_;
}
else
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2002_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v___x_2002_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
v___y_1991_ = v___x_2009_;
goto v___jp_1990_;
}
}
}
v___jp_1867_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_inc_n(v___y_1878_, 2);
lean_inc_n(v___y_1870_, 6);
v___x_1881_ = l_Lean_Syntax_node2(v___y_1870_, v___y_1878_, v___y_1880_, v___x_1866_);
v___x_1882_ = l_Lean_Syntax_node2(v___y_1870_, v___y_1879_, v___y_1875_, v___x_1881_);
v___x_1883_ = l_Lean_Syntax_node1(v___y_1870_, v___y_1874_, v___x_1882_);
v___x_1884_ = l_Lean_Syntax_node2(v___y_1870_, v___y_1868_, v___x_1883_, v___y_1877_);
v___x_1885_ = l_Lean_Syntax_node1(v___y_1870_, v___y_1878_, v___x_1884_);
v___x_1886_ = l_Lean_Syntax_node1(v___y_1870_, v___y_1876_, v___x_1885_);
lean_inc(v___y_1869_);
v___x_1887_ = l_Lean_Syntax_node4(v___y_1870_, v___y_1869_, v___y_1873_, v___y_1872_, v___y_1871_, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_a_1851_);
return v___x_1888_;
}
v___jp_1889_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_inc_ref(v___y_1891_);
v___x_1902_ = l_Array_append___redArg(v___y_1891_, v___y_1901_);
lean_dec_ref(v___y_1901_);
lean_inc_n(v___y_1899_, 3);
lean_inc_n(v___y_1895_, 12);
v___x_1903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1895_);
lean_ctor_set(v___x_1903_, 1, v___y_1899_);
lean_ctor_set(v___x_1903_, 2, v___x_1902_);
lean_inc_n(v___y_1898_, 5);
lean_inc(v___y_1890_);
v___x_1904_ = l_Lean_Syntax_node7(v___y_1895_, v___y_1890_, v___y_1893_, v___y_1898_, v___x_1903_, v___y_1898_, v___y_1898_, v___y_1898_, v___y_1898_);
v___x_1905_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_1900_);
lean_inc_ref_n(v___y_1894_, 6);
v___x_1906_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___y_1900_, v___x_1905_);
v___x_1907_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
v___x_1908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___y_1895_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_Syntax_node1(v___y_1895_, v___x_1906_, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_1911_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_1912_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___x_1910_, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___y_1895_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_1916_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___x_1910_, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_1918_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v___y_1897_, 2);
lean_inc_n(v___y_1896_, 2);
v___x_1919_ = l_Lean_addMacroScope(v___y_1896_, v___x_1918_, v___y_1897_);
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_1922_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1895_);
lean_ctor_set(v___x_1922_, 1, v___x_1917_);
lean_ctor_set(v___x_1922_, 2, v___x_1919_);
lean_ctor_set(v___x_1922_, 3, v___x_1921_);
v___x_1923_ = l_Lean_Syntax_node1(v___y_1895_, v___y_1899_, v___x_1864_);
lean_inc(v___x_1916_);
v___x_1924_ = l_Lean_Syntax_node2(v___y_1895_, v___x_1916_, v___x_1922_, v___x_1923_);
v___x_1925_ = l_Lean_Syntax_node2(v___y_1895_, v___x_1912_, v___x_1914_, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_1927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___y_1895_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
lean_inc(v_name_1862_);
v___x_1928_ = l_Lean_Syntax_node3(v___y_1895_, v___y_1899_, v_name_1862_, v___x_1925_, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_1930_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___x_1910_, v___x_1929_);
v___x_1931_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_1932_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___x_1910_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_1934_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___x_1910_, v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_1936_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_1937_ = l_Lean_addMacroScope(v___y_1896_, v___x_1936_, v___y_1897_);
v___x_1938_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_1939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1895_);
lean_ctor_set(v___x_1939_, 1, v___x_1935_);
lean_ctor_set(v___x_1939_, 2, v___x_1937_);
lean_ctor_set(v___x_1939_, 3, v___x_1938_);
v___x_1940_ = l_Lean_TSyntax_getId(v_name_1862_);
lean_dec(v_name_1862_);
lean_inc(v___x_1940_);
v___x_1941_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_1920_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_quoteNameMk(v___x_1940_);
v___y_1868_ = v___x_1932_;
v___y_1869_ = v___y_1892_;
v___y_1870_ = v___y_1895_;
v___y_1871_ = v___x_1928_;
v___y_1872_ = v___x_1909_;
v___y_1873_ = v___x_1904_;
v___y_1874_ = v___x_1934_;
v___y_1875_ = v___x_1939_;
v___y_1876_ = v___x_1930_;
v___y_1877_ = v___y_1898_;
v___y_1878_ = v___y_1899_;
v___y_1879_ = v___x_1916_;
v___y_1880_ = v___x_1942_;
goto v___jp_1867_;
}
else
{
lean_object* v_val_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v___x_1940_);
v_val_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1944_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
lean_inc_ref(v___y_1894_);
v___x_1945_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1894_, v___x_1910_, v___x_1944_);
v___x_1946_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1947_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_1948_ = lean_string_intercalate(v___x_1947_, v_val_1943_);
v___x_1949_ = lean_string_append(v___x_1946_, v___x_1948_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = lean_box(2);
v___x_1951_ = l_Lean_Syntax_mkNameLit(v___x_1949_, v___x_1950_);
v___x_1952_ = lean_mk_empty_array_with_capacity(v___x_1859_);
v___x_1953_ = lean_array_push(v___x_1952_, v___x_1951_);
v___x_1954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1950_);
lean_ctor_set(v___x_1954_, 1, v___x_1945_);
lean_ctor_set(v___x_1954_, 2, v___x_1953_);
v___y_1868_ = v___x_1932_;
v___y_1869_ = v___y_1892_;
v___y_1870_ = v___y_1895_;
v___y_1871_ = v___x_1928_;
v___y_1872_ = v___x_1909_;
v___y_1873_ = v___x_1904_;
v___y_1874_ = v___x_1934_;
v___y_1875_ = v___x_1939_;
v___y_1876_ = v___x_1930_;
v___y_1877_ = v___y_1898_;
v___y_1878_ = v___y_1899_;
v___y_1879_ = v___x_1916_;
v___y_1880_ = v___x_1954_;
goto v___jp_1867_;
}
}
v___jp_1955_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_inc_ref_n(v___y_1957_, 2);
v___x_1967_ = l_Array_append___redArg(v___y_1957_, v___y_1966_);
lean_dec_ref(v___y_1966_);
lean_inc_n(v___y_1964_, 2);
lean_inc_n(v___y_1960_, 2);
v___x_1968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1960_);
lean_ctor_set(v___x_1968_, 1, v___y_1964_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1960_);
lean_ctor_set(v___x_1969_, 1, v___y_1964_);
lean_ctor_set(v___x_1969_, 2, v___y_1957_);
if (lean_obj_tag(v___y_1962_) == 1)
{
lean_object* v_val_1970_; lean_object* v___x_1971_; 
v_val_1970_ = lean_ctor_get(v___y_1962_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v___y_1962_, 1);
v___x_1971_ = l_Array_mkArray1___redArg(v_val_1970_);
v___y_1890_ = v___y_1956_;
v___y_1891_ = v___y_1957_;
v___y_1892_ = v___y_1958_;
v___y_1893_ = v___x_1968_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v___y_1960_;
v___y_1896_ = v___y_1961_;
v___y_1897_ = v___y_1963_;
v___y_1898_ = v___x_1969_;
v___y_1899_ = v___y_1964_;
v___y_1900_ = v___y_1965_;
v___y_1901_ = v___x_1971_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1972_; 
lean_dec(v___y_1962_);
v___x_1972_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1890_ = v___y_1956_;
v___y_1891_ = v___y_1957_;
v___y_1892_ = v___y_1958_;
v___y_1893_ = v___x_1968_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v___y_1960_;
v___y_1896_ = v___y_1961_;
v___y_1897_ = v___y_1963_;
v___y_1898_ = v___x_1969_;
v___y_1899_ = v___y_1964_;
v___y_1900_ = v___y_1965_;
v___y_1901_ = v___x_1972_;
goto v___jp_1889_;
}
}
v___jp_1973_:
{
lean_object* v_quotContext_1976_; lean_object* v_currMacroScope_1977_; lean_object* v_ref_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_quotContext_1976_ = lean_ctor_get(v_a_1850_, 1);
v_currMacroScope_1977_ = lean_ctor_get(v_a_1850_, 2);
v_ref_1978_ = lean_ctor_get(v_a_1850_, 5);
v___x_1979_ = 0;
v___x_1980_ = l_Lean_SourceInfo_fromRef(v_ref_1978_, v___x_1979_);
v___x_1981_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_1982_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_1983_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_1984_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__28));
v___x_1985_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1986_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
if (lean_obj_tag(v___y_1975_) == 1)
{
lean_object* v_val_1987_; lean_object* v___x_1988_; 
v_val_1987_ = lean_ctor_get(v___y_1975_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v___y_1975_, 1);
v___x_1988_ = l_Array_mkArray1___redArg(v_val_1987_);
v___y_1956_ = v___x_1984_;
v___y_1957_ = v___x_1986_;
v___y_1958_ = v___x_1983_;
v___y_1959_ = v___x_1981_;
v___y_1960_ = v___x_1980_;
v___y_1961_ = v_quotContext_1976_;
v___y_1962_ = v___y_1974_;
v___y_1963_ = v_currMacroScope_1977_;
v___y_1964_ = v___x_1985_;
v___y_1965_ = v___x_1982_;
v___y_1966_ = v___x_1988_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___y_1975_);
v___x_1989_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1956_ = v___x_1984_;
v___y_1957_ = v___x_1986_;
v___y_1958_ = v___x_1983_;
v___y_1959_ = v___x_1981_;
v___y_1960_ = v___x_1980_;
v___y_1961_ = v_quotContext_1976_;
v___y_1962_ = v___y_1974_;
v___y_1963_ = v_currMacroScope_1977_;
v___y_1964_ = v___x_1985_;
v___y_1965_ = v___x_1982_;
v___y_1966_ = v___x_1989_;
goto v___jp_1955_;
}
}
v___jp_1990_:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Syntax_getOptional_x3f(v___x_1858_);
lean_dec(v___x_1858_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_box(0);
v___y_1974_ = v___y_1991_;
v___y_1975_ = v___x_1993_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_val_1994_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1992_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v___x_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_val_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
v___y_1974_ = v___y_1991_;
v___y_1975_ = v___x_1999_;
goto v___jp_1973_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___boxed(lean_object* v_x_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(v_x_2012_, v_a_2013_, v_a_2014_);
lean_dec_ref(v_a_2013_);
return v_res_2015_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = ((lean_object*)(l_Lean_instInhabitedOptionDeprecation_default___closed__0));
v___x_2040_ = l_String_toRawSubstring_x27(v___x_2039_);
return v___x_2040_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__13));
v___x_2051_ = l_String_toRawSubstring_x27(v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__29));
v___x_2090_ = l_String_toRawSubstring_x27(v___x_2089_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__35));
v___x_2102_ = l_String_toRawSubstring_x27(v___x_2101_);
return v___x_2102_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__41));
v___x_2116_ = l_String_toRawSubstring_x27(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__45));
v___x_2122_ = l_String_toRawSubstring_x27(v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__48));
v___x_2127_ = l_String_toRawSubstring_x27(v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__54));
v___x_2139_ = l_String_toRawSubstring_x27(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__66));
v___x_2171_ = l_String_toRawSubstring_x27(v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(lean_object* v_attr_2192_, lean_object* v_type_2193_, lean_object* v_decl_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v_newName_2200_; lean_object* v_quotContext_2201_; lean_object* v_currMacroScope_2202_; lean_object* v_ref_2203_; lean_object* v___y_2204_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v_text_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v_since_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__76));
lean_inc(v_attr_2192_);
v___x_2409_ = l_Lean_Syntax_isOfKind(v_attr_2192_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; 
lean_dec(v_type_2193_);
lean_dec(v_attr_2192_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v_decl_2194_);
lean_ctor_set(v___x_2410_, 1, v_a_2196_);
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___y_2414_; lean_object* v_text_x3f_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v_id_x3f_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2435_ = l_Lean_Syntax_getArg(v_attr_2192_, v___x_2412_);
v___x_2436_ = l_Lean_Syntax_isNone(v___x_2435_);
if (v___x_2436_ == 0)
{
uint8_t v___x_2437_; 
lean_inc(v___x_2435_);
v___x_2437_ = l_Lean_Syntax_matchesNull(v___x_2435_, v___x_2412_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; 
lean_dec(v___x_2435_);
lean_dec(v_type_2193_);
lean_dec(v_attr_2192_);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v_decl_2194_);
lean_ctor_set(v___x_2438_, 1, v_a_2196_);
return v___x_2438_;
}
else
{
lean_object* v_id_x3f_2439_; lean_object* v___x_2440_; 
v_id_x3f_2439_ = l_Lean_Syntax_getArg(v___x_2435_, v___x_2411_);
lean_dec(v___x_2435_);
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_id_x3f_2439_);
v_id_x3f_2424_ = v___x_2440_;
v___y_2425_ = v_a_2195_;
v___y_2426_ = v_a_2196_;
goto v___jp_2423_;
}
}
else
{
lean_object* v___x_2441_; 
lean_dec(v___x_2435_);
v___x_2441_ = lean_box(0);
v_id_x3f_2424_ = v___x_2441_;
v___y_2425_ = v_a_2195_;
v___y_2426_ = v_a_2196_;
goto v___jp_2423_;
}
v___jp_2413_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = lean_unsigned_to_nat(3u);
v___x_2419_ = l_Lean_Syntax_getArg(v_attr_2192_, v___x_2418_);
v___x_2420_ = l_Lean_Syntax_isNone(v___x_2419_);
if (v___x_2420_ == 0)
{
uint8_t v___x_2421_; 
v___x_2421_ = l_Lean_Syntax_matchesNull(v___x_2419_, v___x_2412_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; 
lean_dec(v_text_x3f_2415_);
lean_dec(v___y_2414_);
lean_dec(v_type_2193_);
lean_dec(v_attr_2192_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_decl_2194_);
lean_ctor_set(v___x_2422_, 1, v___y_2417_);
return v___x_2422_;
}
else
{
v___y_2389_ = v___x_2418_;
v___y_2390_ = v___y_2414_;
v___y_2391_ = v_text_x3f_2415_;
v___y_2392_ = v___y_2416_;
v___y_2393_ = v___y_2417_;
goto v___jp_2388_;
}
}
else
{
lean_dec(v___x_2419_);
v___y_2389_ = v___x_2418_;
v___y_2390_ = v___y_2414_;
v___y_2391_ = v_text_x3f_2415_;
v___y_2392_ = v___y_2416_;
v___y_2393_ = v___y_2417_;
goto v___jp_2388_;
}
}
v___jp_2423_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2427_ = lean_unsigned_to_nat(2u);
v___x_2428_ = l_Lean_Syntax_getArg(v_attr_2192_, v___x_2427_);
v___x_2429_ = l_Lean_Syntax_isNone(v___x_2428_);
if (v___x_2429_ == 0)
{
uint8_t v___x_2430_; 
lean_inc(v___x_2428_);
v___x_2430_ = l_Lean_Syntax_matchesNull(v___x_2428_, v___x_2412_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_dec(v___x_2428_);
lean_dec(v_id_x3f_2424_);
lean_dec(v_type_2193_);
lean_dec(v_attr_2192_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_decl_2194_);
lean_ctor_set(v___x_2431_, 1, v___y_2426_);
return v___x_2431_;
}
else
{
lean_object* v_text_x3f_2432_; lean_object* v___x_2433_; 
v_text_x3f_2432_ = l_Lean_Syntax_getArg(v___x_2428_, v___x_2411_);
lean_dec(v___x_2428_);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_text_x3f_2432_);
v___y_2414_ = v_id_x3f_2424_;
v_text_x3f_2415_ = v___x_2433_;
v___y_2416_ = v___y_2425_;
v___y_2417_ = v___y_2426_;
goto v___jp_2413_;
}
}
else
{
lean_object* v___x_2434_; 
lean_dec(v___x_2428_);
v___x_2434_ = lean_box(0);
v___y_2414_ = v_id_x3f_2424_;
v_text_x3f_2415_ = v___x_2434_;
v___y_2416_ = v___y_2425_;
v___y_2417_ = v___y_2426_;
goto v___jp_2413_;
}
}
}
v___jp_2197_:
{
uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2205_ = 0;
v___x_2206_ = l_Lean_SourceInfo_fromRef(v_ref_2203_, v___x_2205_);
v___x_2207_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__1));
v___x_2208_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__2));
lean_inc_n(v___x_2206_, 48);
v___x_2209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2211_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__4));
v___x_2212_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6));
v___x_2213_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7));
v___x_2214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2206_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9));
v___x_2216_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10);
v___x_2217_ = lean_box(0);
lean_inc_n(v_currMacroScope_2202_, 6);
lean_inc_n(v_quotContext_2201_, 6);
v___x_2218_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2217_, v_currMacroScope_2202_);
v___x_2219_ = lean_box(0);
v___x_2220_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__11));
v___x_2221_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2206_);
lean_ctor_set(v___x_2221_, 1, v___x_2216_);
lean_ctor_set(v___x_2221_, 2, v___x_2218_);
lean_ctor_set(v___x_2221_, 3, v___x_2220_);
v___x_2222_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2215_, v___x_2221_);
v___x_2223_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2212_, v___x_2214_, v___x_2222_);
v___x_2224_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2206_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12));
v___x_2227_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__14);
v___x_2228_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__16));
v___x_2229_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2228_, v_currMacroScope_2202_);
v___x_2230_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__20));
v___x_2231_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2206_);
lean_ctor_set(v___x_2231_, 1, v___x_2227_);
lean_ctor_set(v___x_2231_, 2, v___x_2229_);
lean_ctor_set(v___x_2231_, 3, v___x_2230_);
v___x_2232_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2210_, v_type_2193_);
v___x_2233_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2226_, v___x_2231_, v___x_2232_);
v___x_2234_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2210_, v___x_2233_);
v___x_2235_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21));
v___x_2236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2206_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_Syntax_node5(v___x_2206_, v___x_2211_, v___x_2223_, v_decl_2194_, v___x_2225_, v___x_2234_, v___x_2236_);
v___x_2238_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2210_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__22));
v___x_2240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2206_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2210_, v___x_2238_, v___x_2240_);
v___x_2242_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__24));
v___x_2243_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__26));
v___x_2244_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__28));
v___x_2245_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__30);
v___x_2246_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31));
v___x_2247_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2246_, v_currMacroScope_2202_);
v___x_2248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2206_);
lean_ctor_set(v___x_2248_, 1, v___x_2245_);
lean_ctor_set(v___x_2248_, 2, v___x_2247_);
lean_ctor_set(v___x_2248_, 3, v___x_2219_);
v___x_2249_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2206_);
lean_ctor_set(v___x_2250_, 1, v___x_2210_);
lean_ctor_set(v___x_2250_, 2, v___x_2249_);
lean_inc_ref_n(v___x_2250_, 19);
v___x_2251_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2244_, v___x_2248_, v___x_2250_);
v___x_2252_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__33));
v___x_2253_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__34));
v___x_2254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2206_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36);
v___x_2256_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37));
v___x_2257_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2256_, v_currMacroScope_2202_);
v___x_2258_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__40));
v___x_2259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2206_);
lean_ctor_set(v___x_2259_, 1, v___x_2255_);
lean_ctor_set(v___x_2259_, 2, v___x_2257_);
lean_ctor_set(v___x_2259_, 3, v___x_2258_);
v___x_2260_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__42);
v___x_2261_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__43));
v___x_2262_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2261_, v_currMacroScope_2202_);
v___x_2263_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2206_);
lean_ctor_set(v___x_2263_, 1, v___x_2260_);
lean_ctor_set(v___x_2263_, 2, v___x_2262_);
lean_ctor_set(v___x_2263_, 3, v___x_2219_);
v___x_2264_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2244_, v___x_2263_, v___x_2250_);
lean_inc_ref_n(v___x_2254_, 3);
v___x_2265_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2252_, v___x_2254_, v___x_2250_, v___y_2199_);
v___x_2266_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2210_, v___x_2250_, v___x_2250_, v___x_2265_);
v___x_2267_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2243_, v___x_2264_, v___x_2266_);
v___x_2268_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__44));
v___x_2269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2206_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__46);
v___x_2271_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__47));
v___x_2272_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2271_, v_currMacroScope_2202_);
v___x_2273_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2206_);
lean_ctor_set(v___x_2273_, 1, v___x_2270_);
lean_ctor_set(v___x_2273_, 2, v___x_2272_);
lean_ctor_set(v___x_2273_, 3, v___x_2219_);
v___x_2274_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2244_, v___x_2273_, v___x_2250_);
v___x_2275_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2252_, v___x_2254_, v___x_2250_, v___y_2198_);
v___x_2276_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2210_, v___x_2250_, v___x_2250_, v___x_2275_);
v___x_2277_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2243_, v___x_2274_, v___x_2276_);
v___x_2278_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__49);
v___x_2279_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__50));
v___x_2280_ = l_Lean_addMacroScope(v_quotContext_2201_, v___x_2279_, v_currMacroScope_2202_);
v___x_2281_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2206_);
lean_ctor_set(v___x_2281_, 1, v___x_2278_);
lean_ctor_set(v___x_2281_, 2, v___x_2280_);
lean_ctor_set(v___x_2281_, 3, v___x_2219_);
v___x_2282_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2244_, v___x_2281_, v___x_2250_);
v___x_2283_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2252_, v___x_2254_, v___x_2250_, v_newName_2200_);
v___x_2284_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2210_, v___x_2250_, v___x_2250_, v___x_2283_);
v___x_2285_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2243_, v___x_2282_, v___x_2284_);
lean_inc_ref(v___x_2269_);
v___x_2286_ = l_Lean_Syntax_node5(v___x_2206_, v___x_2210_, v___x_2267_, v___x_2269_, v___x_2277_, v___x_2269_, v___x_2285_);
v___x_2287_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2242_, v___x_2286_);
v___x_2288_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__52));
v___x_2289_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2288_, v___x_2250_);
v___x_2290_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__53));
v___x_2291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2206_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
lean_inc_ref(v___x_2291_);
lean_inc(v___x_2289_);
lean_inc_ref(v___x_2209_);
v___x_2292_ = l_Lean_Syntax_node6(v___x_2206_, v___x_2207_, v___x_2209_, v___x_2250_, v___x_2287_, v___x_2289_, v___x_2250_, v___x_2291_);
v___x_2293_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2210_, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2226_, v___x_2259_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2252_, v___x_2254_, v___x_2250_, v___x_2294_);
v___x_2296_ = l_Lean_Syntax_node3(v___x_2206_, v___x_2210_, v___x_2250_, v___x_2250_, v___x_2295_);
v___x_2297_ = l_Lean_Syntax_node2(v___x_2206_, v___x_2243_, v___x_2251_, v___x_2296_);
v___x_2298_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2210_, v___x_2297_);
v___x_2299_ = l_Lean_Syntax_node1(v___x_2206_, v___x_2242_, v___x_2298_);
v___x_2300_ = l_Lean_Syntax_node6(v___x_2206_, v___x_2207_, v___x_2209_, v___x_2241_, v___x_2299_, v___x_2289_, v___x_2250_, v___x_2291_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___y_2204_);
return v___x_2301_;
}
v___jp_2302_:
{
if (lean_obj_tag(v___y_2304_) == 0)
{
lean_object* v_quotContext_2308_; lean_object* v_currMacroScope_2309_; lean_object* v_ref_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_quotContext_2308_ = lean_ctor_get(v___y_2306_, 1);
v_currMacroScope_2309_ = lean_ctor_get(v___y_2306_, 2);
v_ref_2310_ = lean_ctor_get(v___y_2306_, 5);
v___x_2311_ = 0;
v___x_2312_ = l_Lean_SourceInfo_fromRef(v_ref_2310_, v___x_2311_);
v___x_2313_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55);
v___x_2314_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56));
lean_inc_n(v_currMacroScope_2309_, 2);
lean_inc_n(v_quotContext_2308_, 2);
v___x_2315_ = l_Lean_addMacroScope(v_quotContext_2308_, v___x_2314_, v_currMacroScope_2309_);
v___x_2316_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59));
v___x_2317_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2312_);
lean_ctor_set(v___x_2317_, 1, v___x_2313_);
lean_ctor_set(v___x_2317_, 2, v___x_2315_);
lean_ctor_set(v___x_2317_, 3, v___x_2316_);
v___y_2198_ = v_text_2305_;
v___y_2199_ = v___y_2303_;
v_newName_2200_ = v___x_2317_;
v_quotContext_2201_ = v_quotContext_2308_;
v_currMacroScope_2202_ = v_currMacroScope_2309_;
v_ref_2203_ = v_ref_2310_;
v___y_2204_ = v___y_2307_;
goto v___jp_2197_;
}
else
{
lean_object* v_val_2318_; lean_object* v_quotContext_2319_; lean_object* v_currMacroScope_2320_; lean_object* v_ref_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_val_2318_ = lean_ctor_get(v___y_2304_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v___y_2304_, 1);
v_quotContext_2319_ = lean_ctor_get(v___y_2306_, 1);
v_currMacroScope_2320_ = lean_ctor_get(v___y_2306_, 2);
v_ref_2321_ = lean_ctor_get(v___y_2306_, 5);
v___x_2322_ = 0;
v___x_2323_ = l_Lean_SourceInfo_fromRef(v_ref_2321_, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12));
v___x_2325_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36);
v___x_2326_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37));
lean_inc_n(v_currMacroScope_2320_, 4);
lean_inc_n(v_quotContext_2319_, 4);
v___x_2327_ = l_Lean_addMacroScope(v_quotContext_2319_, v___x_2326_, v_currMacroScope_2320_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61));
lean_inc_n(v___x_2323_, 11);
v___x_2329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2323_);
lean_ctor_set(v___x_2329_, 1, v___x_2325_);
lean_ctor_set(v___x_2329_, 2, v___x_2327_);
lean_ctor_set(v___x_2329_, 3, v___x_2328_);
v___x_2330_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2331_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__63));
v___x_2332_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__65));
v___x_2333_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__6));
v___x_2334_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__7));
v___x_2335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2323_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__9));
v___x_2337_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__10);
v___x_2338_ = lean_box(0);
v___x_2339_ = l_Lean_addMacroScope(v_quotContext_2319_, v___x_2338_, v_currMacroScope_2320_);
v___x_2340_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__10));
v___x_2341_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2323_);
lean_ctor_set(v___x_2341_, 1, v___x_2337_);
lean_ctor_set(v___x_2341_, 2, v___x_2339_);
lean_ctor_set(v___x_2341_, 3, v___x_2340_);
v___x_2342_ = l_Lean_Syntax_node1(v___x_2323_, v___x_2336_, v___x_2341_);
v___x_2343_ = l_Lean_Syntax_node2(v___x_2323_, v___x_2333_, v___x_2335_, v___x_2342_);
v___x_2344_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__21));
v___x_2345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2323_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_Syntax_node3(v___x_2323_, v___x_2332_, v___x_2343_, v_val_2318_, v___x_2345_);
v___x_2347_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2323_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__67);
v___x_2350_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__68));
v___x_2351_ = l_Lean_addMacroScope(v_quotContext_2319_, v___x_2350_, v_currMacroScope_2320_);
v___x_2352_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__71));
v___x_2353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2323_);
lean_ctor_set(v___x_2353_, 1, v___x_2349_);
lean_ctor_set(v___x_2353_, 2, v___x_2351_);
lean_ctor_set(v___x_2353_, 3, v___x_2352_);
v___x_2354_ = l_Lean_Syntax_node3(v___x_2323_, v___x_2331_, v___x_2346_, v___x_2348_, v___x_2353_);
v___x_2355_ = l_Lean_Syntax_node1(v___x_2323_, v___x_2330_, v___x_2354_);
v___x_2356_ = l_Lean_Syntax_node2(v___x_2323_, v___x_2324_, v___x_2329_, v___x_2355_);
v___y_2198_ = v_text_2305_;
v___y_2199_ = v___y_2303_;
v_newName_2200_ = v___x_2356_;
v_quotContext_2201_ = v_quotContext_2319_;
v_currMacroScope_2202_ = v_currMacroScope_2320_;
v_ref_2203_ = v_ref_2321_;
v___y_2204_ = v___y_2307_;
goto v___jp_2197_;
}
}
v___jp_2357_:
{
if (lean_obj_tag(v___y_2359_) == 0)
{
lean_object* v_quotContext_2363_; lean_object* v_currMacroScope_2364_; lean_object* v_ref_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_quotContext_2363_ = lean_ctor_get(v___y_2361_, 1);
v_currMacroScope_2364_ = lean_ctor_get(v___y_2361_, 2);
v_ref_2365_ = lean_ctor_get(v___y_2361_, 5);
v___x_2366_ = 0;
v___x_2367_ = l_Lean_SourceInfo_fromRef(v_ref_2365_, v___x_2366_);
v___x_2368_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__55);
v___x_2369_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__56));
lean_inc(v_currMacroScope_2364_);
lean_inc(v_quotContext_2363_);
v___x_2370_ = l_Lean_addMacroScope(v_quotContext_2363_, v___x_2369_, v_currMacroScope_2364_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__59));
v___x_2372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2367_);
lean_ctor_set(v___x_2372_, 1, v___x_2368_);
lean_ctor_set(v___x_2372_, 2, v___x_2370_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
v___y_2303_ = v_since_2360_;
v___y_2304_ = v___y_2358_;
v_text_2305_ = v___x_2372_;
v___y_2306_ = v___y_2361_;
v___y_2307_ = v___y_2362_;
goto v___jp_2302_;
}
else
{
lean_object* v_val_2373_; lean_object* v_quotContext_2374_; lean_object* v_currMacroScope_2375_; lean_object* v_ref_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_val_2373_ = lean_ctor_get(v___y_2359_, 0);
lean_inc(v_val_2373_);
lean_dec_ref_known(v___y_2359_, 1);
v_quotContext_2374_ = lean_ctor_get(v___y_2361_, 1);
v_currMacroScope_2375_ = lean_ctor_get(v___y_2361_, 2);
v_ref_2376_ = lean_ctor_get(v___y_2361_, 5);
v___x_2377_ = 0;
v___x_2378_ = l_Lean_SourceInfo_fromRef(v_ref_2376_, v___x_2377_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__12));
v___x_2380_ = lean_obj_once(&l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36, &l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36_once, _init_l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__36);
v___x_2381_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__37));
lean_inc(v_currMacroScope_2375_);
lean_inc(v_quotContext_2374_);
v___x_2382_ = l_Lean_addMacroScope(v_quotContext_2374_, v___x_2381_, v_currMacroScope_2375_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__61));
lean_inc_n(v___x_2378_, 2);
v___x_2384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2378_);
lean_ctor_set(v___x_2384_, 1, v___x_2380_);
lean_ctor_set(v___x_2384_, 2, v___x_2382_);
lean_ctor_set(v___x_2384_, 3, v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2386_ = l_Lean_Syntax_node1(v___x_2378_, v___x_2385_, v_val_2373_);
v___x_2387_ = l_Lean_Syntax_node2(v___x_2378_, v___x_2379_, v___x_2384_, v___x_2386_);
v___y_2303_ = v_since_2360_;
v___y_2304_ = v___y_2358_;
v_text_2305_ = v___x_2387_;
v___y_2306_ = v___y_2361_;
v___y_2307_ = v___y_2362_;
goto v___jp_2302_;
}
}
v___jp_2388_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2394_ = lean_unsigned_to_nat(4u);
v___x_2395_ = l_Lean_Syntax_getArg(v_attr_2192_, v___x_2394_);
lean_dec(v_attr_2192_);
v___x_2396_ = l_Lean_Syntax_isNone(v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_2395_);
v___x_2398_ = l_Lean_Syntax_matchesNull(v___x_2395_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_dec(v___x_2395_);
lean_dec(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec(v_type_2193_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_decl_2194_);
lean_ctor_set(v___x_2399_, 1, v___y_2393_);
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Syntax_getArg(v___x_2395_, v___y_2389_);
lean_dec(v___x_2395_);
v___y_2358_ = v___y_2390_;
v___y_2359_ = v___y_2391_;
v_since_2360_ = v___x_2400_;
v___y_2361_ = v___y_2392_;
v___y_2362_ = v___y_2393_;
goto v___jp_2357_;
}
}
else
{
lean_object* v_ref_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v___x_2395_);
v_ref_2401_ = lean_ctor_get(v___y_2392_, 5);
v___x_2402_ = 0;
v___x_2403_ = l_Lean_SourceInfo_fromRef(v_ref_2401_, v___x_2402_);
v___x_2404_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__73));
v___x_2405_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__74));
lean_inc(v___x_2403_);
v___x_2406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2403_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2404_, v___x_2406_);
v___y_2358_ = v___y_2390_;
v___y_2359_ = v___y_2391_;
v_since_2360_ = v___x_2407_;
v___y_2361_ = v___y_2392_;
v___y_2362_ = v___y_2393_;
goto v___jp_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___boxed(lean_object* v_attr_2442_, lean_object* v_type_2443_, lean_object* v_decl_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(v_attr_2442_, v_type_2443_, v_decl_2444_, v_a_2445_, v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(lean_object* v_x_2489_){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2490_ = l_Lean_Syntax_getId(v_x_2489_);
v___x_2491_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__31));
v___x_2492_ = lean_name_eq(v___x_2490_, v___x_2491_);
lean_dec(v___x_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0___boxed(lean_object* v_x_2493_){
_start:
{
uint8_t v_res_2494_; lean_object* v_r_2495_; 
v_res_2494_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(v_x_2493_);
lean_dec(v_x_2493_);
v_r_2495_ = lean_box(v_res_2494_);
return v_r_2495_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(lean_object* v___x_2496_, lean_object* v_x_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2498_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75));
v___x_2499_ = l_Lean_Name_mkStr2(v___x_2496_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_isOfKind(v_x_2497_, v___x_2499_);
lean_dec(v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1___boxed(lean_object* v___x_2501_, lean_object* v_x_2502_){
_start:
{
uint8_t v_res_2503_; lean_object* v_r_2504_; 
v_res_2503_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(v___x_2501_, v_x_2502_);
v_r_2504_ = lean_box(v_res_2503_);
return v_r_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v_type_2509_, lean_object* v_name_2510_, lean_object* v___x_2511_, lean_object* v_decl_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_quotContext_2515_; lean_object* v_currMacroScope_2516_; lean_object* v_ref_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___y_2563_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_quotContext_2515_ = lean_ctor_get(v___y_2513_, 1);
v_currMacroScope_2516_ = lean_ctor_get(v___y_2513_, 2);
v_ref_2517_ = lean_ctor_get(v___y_2513_, 5);
v___x_2518_ = 0;
v___x_2519_ = l_Lean_SourceInfo_fromRef(v_ref_2517_, v___x_2518_);
v___x_2520_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25));
lean_inc_ref(v___x_2507_);
lean_inc_ref_n(v___x_2506_, 7);
lean_inc_ref_n(v___x_2505_, 9);
v___x_2521_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2507_, v___x_2520_);
v___x_2522_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
v___x_2523_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2507_, v___x_2522_);
lean_inc_n(v___x_2519_, 10);
v___x_2524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2519_);
lean_ctor_set(v___x_2524_, 1, v___x_2520_);
v___x_2525_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2523_, v___x_2524_);
v___x_2526_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2527_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_2528_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_2529_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2527_, v___x_2528_);
v___x_2530_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2519_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_2533_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2527_, v___x_2532_);
v___x_2534_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
lean_inc_ref(v___x_2508_);
v___x_2535_ = l_Lean_Name_mkStr2(v___x_2505_, v___x_2508_);
lean_inc_n(v_currMacroScope_2516_, 2);
lean_inc_n(v___x_2535_, 2);
lean_inc_n(v_quotContext_2515_, 2);
v___x_2536_ = l_Lean_addMacroScope(v_quotContext_2515_, v___x_2535_, v_currMacroScope_2516_);
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2535_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2535_);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v___x_2537_);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2538_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2519_);
lean_ctor_set(v___x_2542_, 1, v___x_2534_);
lean_ctor_set(v___x_2542_, 2, v___x_2536_);
lean_ctor_set(v___x_2542_, 3, v___x_2541_);
v___x_2543_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2526_, v_type_2509_);
lean_inc(v___x_2533_);
v___x_2544_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2533_, v___x_2542_, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2529_, v___x_2531_, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_2547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2519_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_inc(v_name_2510_);
v___x_2548_ = l_Lean_Syntax_node3(v___x_2519_, v___x_2526_, v_name_2510_, v___x_2545_, v___x_2547_);
v___x_2549_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_2550_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2527_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_2552_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2527_, v___x_2551_);
v___x_2553_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_2554_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2527_, v___x_2553_);
v___x_2555_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2556_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18));
v___x_2557_ = l_Lean_Name_mkStr3(v___x_2505_, v___x_2508_, v___x_2556_);
lean_inc(v___x_2557_);
v___x_2558_ = l_Lean_addMacroScope(v_quotContext_2515_, v___x_2557_, v_currMacroScope_2516_);
v___x_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2537_);
v___x_2560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___x_2537_);
v___x_2561_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2519_);
lean_ctor_set(v___x_2561_, 1, v___x_2555_);
lean_ctor_set(v___x_2561_, 2, v___x_2558_);
lean_ctor_set(v___x_2561_, 3, v___x_2560_);
v___x_2574_ = l_Lean_TSyntax_getId(v_name_2510_);
lean_dec(v_name_2510_);
lean_inc(v___x_2574_);
v___x_2575_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2537_, v___x_2574_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2576_; 
lean_dec_ref(v___x_2506_);
lean_dec_ref(v___x_2505_);
v___x_2576_ = l_Lean_quoteNameMk(v___x_2574_);
v___y_2563_ = v___x_2576_;
goto v___jp_2562_;
}
else
{
lean_object* v_val_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec(v___x_2574_);
v_val_2577_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_val_2577_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2578_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
v___x_2579_ = l_Lean_Name_mkStr4(v___x_2505_, v___x_2506_, v___x_2527_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_2581_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2582_ = lean_string_intercalate(v___x_2581_, v_val_2577_);
v___x_2583_ = lean_string_append(v___x_2580_, v___x_2582_);
lean_dec_ref(v___x_2582_);
v___x_2584_ = lean_box(2);
v___x_2585_ = l_Lean_Syntax_mkNameLit(v___x_2583_, v___x_2584_);
v___x_2586_ = lean_unsigned_to_nat(1u);
v___x_2587_ = lean_mk_empty_array_with_capacity(v___x_2586_);
v___x_2588_ = lean_array_push(v___x_2587_, v___x_2585_);
v___x_2589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2584_);
lean_ctor_set(v___x_2589_, 1, v___x_2579_);
lean_ctor_set(v___x_2589_, 2, v___x_2588_);
v___y_2563_ = v___x_2589_;
goto v___jp_2562_;
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_inc_n(v___x_2519_, 7);
v___x_2564_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2526_, v___y_2563_, v_decl_2512_);
v___x_2565_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2533_, v___x_2561_, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2554_, v___x_2565_);
v___x_2567_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2519_);
lean_ctor_set(v___x_2568_, 1, v___x_2526_);
lean_ctor_set(v___x_2568_, 2, v___x_2567_);
v___x_2569_ = l_Lean_Syntax_node2(v___x_2519_, v___x_2552_, v___x_2566_, v___x_2568_);
v___x_2570_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2526_, v___x_2569_);
v___x_2571_ = l_Lean_Syntax_node1(v___x_2519_, v___x_2550_, v___x_2570_);
v___x_2572_ = l_Lean_Syntax_node4(v___x_2519_, v___x_2521_, v___x_2511_, v___x_2525_, v___x_2548_, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v___y_2514_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2___boxed(lean_object* v___x_2590_, lean_object* v___x_2591_, lean_object* v___x_2592_, lean_object* v___x_2593_, lean_object* v_type_2594_, lean_object* v_name_2595_, lean_object* v___x_2596_, lean_object* v_decl_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2590_, v___x_2591_, v___x_2592_, v___x_2593_, v_type_2594_, v_name_2595_, v___x_2596_, v_decl_2597_, v___y_2598_, v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___y_2610_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2629_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_2630_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__0));
v___x_2631_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2606_);
v___x_2632_ = l_Lean_Syntax_isOfKind(v_x_2606_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec(v_x_2606_);
v___x_2633_ = lean_box(1);
v___x_2634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
lean_ctor_set(v___x_2634_, 1, v_a_2608_);
return v___x_2634_;
}
else
{
lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v_name_2640_; lean_object* v___x_2641_; lean_object* v_type_2642_; lean_object* v___x_2643_; lean_object* v_decl_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v_attr_x3f_2647_; lean_object* v_field_x3f_2648_; 
v___f_2635_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
v___f_2636_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = l_Lean_Syntax_getArg(v_x_2606_, v___x_2637_);
v___x_2639_ = lean_unsigned_to_nat(2u);
v_name_2640_ = l_Lean_Syntax_getArg(v_x_2606_, v___x_2639_);
v___x_2641_ = lean_unsigned_to_nat(4u);
v_type_2642_ = l_Lean_Syntax_getArg(v_x_2606_, v___x_2641_);
v___x_2643_ = lean_unsigned_to_nat(6u);
v_decl_2644_ = l_Lean_Syntax_getArg(v_x_2606_, v___x_2643_);
lean_dec(v_x_2606_);
v___x_2645_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_2646_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
lean_inc(v___x_2638_);
v_attr_x3f_2647_ = l_Lean_Syntax_find_x3f(v___x_2638_, v___f_2636_);
lean_inc(v_decl_2644_);
v_field_x3f_2648_ = l_Lean_Syntax_find_x3f(v_decl_2644_, v___f_2635_);
if (lean_obj_tag(v_attr_x3f_2647_) == 0)
{
if (lean_obj_tag(v_field_x3f_2648_) == 0)
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2629_, v___x_2645_, v___x_2646_, v___x_2630_, v_type_2642_, v_name_2640_, v___x_2638_, v_decl_2644_, v_a_2607_, v_a_2608_);
v___y_2610_ = v___x_2649_;
goto v___jp_2609_;
}
else
{
lean_object* v_val_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec(v_decl_2644_);
v_val_2650_ = lean_ctor_get(v_field_x3f_2648_, 0);
lean_inc(v_val_2650_);
lean_dec_ref_known(v_field_x3f_2648_, 1);
v___x_2651_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2652_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2650_, v___x_2651_, v_a_2607_, v_a_2608_);
lean_dec(v_val_2650_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_a_2654_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
v_a_2654_ = lean_ctor_get(v___x_2652_, 1);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2652_, 2);
v___x_2655_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2629_, v___x_2645_, v___x_2646_, v___x_2630_, v_type_2642_, v_name_2640_, v___x_2638_, v_a_2653_, v_a_2607_, v_a_2654_);
v___y_2610_ = v___x_2655_;
goto v___jp_2609_;
}
else
{
lean_dec(v_type_2642_);
lean_dec(v_name_2640_);
lean_dec(v___x_2638_);
v___y_2610_ = v___x_2652_;
goto v___jp_2609_;
}
}
}
else
{
if (lean_obj_tag(v_field_x3f_2648_) == 0)
{
lean_object* v_val_2656_; lean_object* v___x_2657_; lean_object* v_a_2658_; lean_object* v_a_2659_; lean_object* v___x_2660_; 
v_val_2656_ = lean_ctor_get(v_attr_x3f_2647_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v_attr_x3f_2647_, 1);
lean_inc(v_type_2642_);
v___x_2657_ = l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(v_val_2656_, v_type_2642_, v_decl_2644_, v_a_2607_, v_a_2608_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
v_a_2659_ = lean_ctor_get(v___x_2657_, 1);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2657_);
v___x_2660_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2629_, v___x_2645_, v___x_2646_, v___x_2630_, v_type_2642_, v_name_2640_, v___x_2638_, v_a_2658_, v_a_2607_, v_a_2659_);
v___y_2610_ = v___x_2660_;
goto v___jp_2609_;
}
else
{
lean_object* v_val_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec_ref_known(v_attr_x3f_2647_, 1);
lean_dec(v_decl_2644_);
v_val_2661_ = lean_ctor_get(v_field_x3f_2648_, 0);
lean_inc(v_val_2661_);
lean_dec_ref_known(v_field_x3f_2648_, 1);
v___x_2662_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2663_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2661_, v___x_2662_, v_a_2607_, v_a_2608_);
lean_dec(v_val_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v_a_2665_; lean_object* v___x_2666_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
v_a_2665_ = lean_ctor_get(v___x_2663_, 1);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2663_, 2);
v___x_2666_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2629_, v___x_2645_, v___x_2646_, v___x_2630_, v_type_2642_, v_name_2640_, v___x_2638_, v_a_2664_, v_a_2607_, v_a_2665_);
v___y_2610_ = v___x_2666_;
goto v___jp_2609_;
}
else
{
lean_dec(v_type_2642_);
lean_dec(v_name_2640_);
lean_dec(v___x_2638_);
v___y_2610_ = v___x_2663_;
goto v___jp_2609_;
}
}
}
}
v___jp_2609_:
{
if (lean_obj_tag(v___y_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
v_a_2611_ = lean_ctor_get(v___y_2610_, 0);
v_a_2612_ = lean_ctor_get(v___y_2610_, 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___y_2610_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___y_2610_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_inc(v_a_2611_);
lean_dec(v___y_2610_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2611_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_a_2620_ = lean_ctor_get(v___y_2610_, 0);
v_a_2621_ = lean_ctor_get(v___y_2610_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___y_2610_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___y_2610_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_inc(v_a_2620_);
lean_dec(v___y_2610_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2620_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(lean_object* v_x_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(v_x_2667_, v_a_2668_, v_a_2669_);
lean_dec_ref(v_a_2668_);
return v_res_2670_;
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
