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
lean_object* l_Lean_DataValue_str(lean_object*);
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
static const lean_closure_object l_Lean_Options_instToString___private__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_DataValue_str, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg(){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = ((lean_object*)(l_Lean_Options_empty));
return v___x_6_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Data_Options_0__Lean_Options_getEmpty___redArg();
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = ((lean_object*)(l_Lean_Options_empty));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___lam__0(lean_object* v_x1_13_, lean_object* v_x2_14_, lean_object* v_x3_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_x1_13_);
lean_ctor_set(v___x_16_, 1, v_x2_14_);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_x3_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object* v_o_43_){
_start:
{
lean_object* v_map_44_; lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_map_44_ = lean_ctor_get(v_o_43_, 0);
lean_inc(v_map_44_);
lean_dec_ref(v_o_43_);
v___f_45_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__0));
v___f_46_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__3));
v___x_47_ = lean_box(0);
v___x_48_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__13));
v___x_49_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_48_, v___f_45_, v___x_47_, v_map_44_);
v___x_50_ = l_List_toString___redArg(v___f_46_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___lam__1(lean_object* v___f_51_, lean_object* v_o_52_){
_start:
{
lean_object* v_map_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_map_53_ = lean_ctor_get(v_o_52_, 0);
lean_inc(v_map_53_);
lean_dec_ref(v_o_52_);
v___f_54_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__3));
v___x_55_ = lean_box(0);
v___x_56_ = ((lean_object*)(l_Lean_Options_instToString___private__1___closed__13));
v___x_57_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_56_, v___f_51_, v___x_55_, v_map_53_);
v___x_58_ = l_List_toString___redArg(v___f_54_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object* v_f_62_, lean_object* v_a_63_, lean_object* v_b_64_, lean_object* v_c_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v_a_63_);
lean_ctor_set(v___x_66_, 1, v_b_64_);
v___x_67_ = lean_apply_2(v_f_62_, v___x_66_, v_c_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object* v_toPure_68_, lean_object* v_____do__lift_69_){
_start:
{
lean_object* v_a_70_; lean_object* v___x_71_; 
v_a_70_ = lean_ctor_get(v_____do__lift_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref(v_____do__lift_69_);
v___x_71_ = lean_apply_2(v_toPure_68_, lean_box(0), v_a_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object* v_inst_72_, lean_object* v_o_73_, lean_object* v_init_74_, lean_object* v_f_75_){
_start:
{
lean_object* v_toApplicative_76_; lean_object* v_map_77_; lean_object* v_toBind_78_; lean_object* v_toPure_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___x_83_; 
v_toApplicative_76_ = lean_ctor_get(v_inst_72_, 0);
v_map_77_ = lean_ctor_get(v_o_73_, 0);
lean_inc(v_map_77_);
lean_dec_ref(v_o_73_);
v_toBind_78_ = lean_ctor_get(v_inst_72_, 1);
lean_inc(v_toBind_78_);
v_toPure_79_ = lean_ctor_get(v_toApplicative_76_, 1);
lean_inc(v_toPure_79_);
v___f_80_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_80_, 0, v_f_75_);
v___x_81_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_72_, v___f_80_, v_init_74_, v_map_77_);
v___f_82_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_82_, 0, v_toPure_79_);
v___x_83_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_81_, v___f_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object* v_m_84_, lean_object* v_inst_85_, lean_object* v_00_u03b2_86_, lean_object* v_o_87_, lean_object* v_init_88_, lean_object* v_f_89_){
_start:
{
lean_object* v_toApplicative_90_; lean_object* v_map_91_; lean_object* v_toBind_92_; lean_object* v_toPure_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
v_toApplicative_90_ = lean_ctor_get(v_inst_85_, 0);
v_map_91_ = lean_ctor_get(v_o_87_, 0);
lean_inc(v_map_91_);
lean_dec_ref(v_o_87_);
v_toBind_92_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_92_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_90_, 1);
lean_inc(v_toPure_93_);
v___f_94_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_94_, 0, v_f_89_);
v___x_95_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_85_, v___f_94_, v_init_88_, v_map_91_);
v___f_96_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_96_, 0, v_toPure_93_);
v___x_97_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_95_, v___f_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2(lean_object* v_inst_98_, lean_object* v_00_u03b2_99_, lean_object* v_o_100_, lean_object* v_init_101_, lean_object* v_f_102_){
_start:
{
lean_object* v_toApplicative_103_; lean_object* v_map_104_; lean_object* v_toBind_105_; lean_object* v_toPure_106_; lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_toApplicative_103_ = lean_ctor_get(v_inst_98_, 0);
v_map_104_ = lean_ctor_get(v_o_100_, 0);
lean_inc(v_map_104_);
lean_dec_ref(v_o_100_);
v_toBind_105_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_105_);
v_toPure_106_ = lean_ctor_get(v_toApplicative_103_, 1);
lean_inc(v_toPure_106_);
v___f_107_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_107_, 0, v_f_102_);
v___x_108_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_98_, v___f_107_, v_init_101_, v_map_104_);
v___f_109_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_109_, 0, v_toPure_106_);
v___x_110_ = lean_apply_4(v_toBind_105_, lean_box(0), lean_box(0), v___x_108_, v___f_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_111_){
_start:
{
lean_object* v___f_112_; 
v___f_112_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_112_, 0, v_inst_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object* v_m_113_, lean_object* v_inst_114_){
_start:
{
lean_object* v___f_115_; 
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_115_, 0, v_inst_114_);
return v___f_115_;
}
}
uint8_t l_Lean_Options_instBEq___private__1(lean_object* v_o1_118_, lean_object* v_o2_119_){
_start:
{
lean_object* v_map_120_; lean_object* v_map_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_map_120_ = lean_ctor_get(v_o1_118_, 0);
lean_inc(v_map_120_);
lean_dec_ref(v_o1_118_);
v_map_121_ = lean_ctor_get(v_o2_119_, 0);
lean_inc(v_map_121_);
lean_dec_ref(v_o2_119_);
v___x_122_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_123_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__1));
v___x_124_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v___x_123_, v___x_122_, v_map_120_, v_map_121_);
return v___x_124_;
}
}
LEAN_EXPORT void l_Lean_Options_instBEq___private__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o1_118_ = stack[0].m_obj;
lean_object* v_o2_119_ = stack[1].m_obj;
uint8_t v_res_125_;
v_res_125_ = l_Lean_Options_instBEq___private__1(v_o1_118_, v_o2_119_);
stack->m_num = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object* v_o1_126_, lean_object* v_o2_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_Options_instBEq___private__1(v_o1_126_, v_o2_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
uint8_t l_Lean_Options_instBEq___lam__0(lean_object* v_o1_130_, lean_object* v_o2_131_){
_start:
{
lean_object* v_map_132_; lean_object* v_map_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_map_132_ = lean_ctor_get(v_o1_130_, 0);
lean_inc(v_map_132_);
lean_dec_ref(v_o1_130_);
v_map_133_ = lean_ctor_get(v_o2_131_, 0);
lean_inc(v_map_133_);
lean_dec_ref(v_o2_131_);
v___x_134_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_135_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__1));
v___x_136_ = l_Std_DTreeMap_Internal_Impl_Const_beq___redArg(v___x_135_, v___x_134_, v_map_132_, v_map_133_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_Options_instBEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o1_130_ = stack[0].m_obj;
lean_object* v_o2_131_ = stack[1].m_obj;
uint8_t v_res_137_;
v_res_137_ = l_Lean_Options_instBEq___lam__0(v_o1_130_, v_o2_131_);
stack->m_num = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___lam__0___boxed(lean_object* v_o1_138_, lean_object* v_o2_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lean_Options_instBEq___lam__0(v_o1_138_, v_o2_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f(lean_object* v_o_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_map_147_; lean_object* v___x_148_; 
v_map_147_ = lean_ctor_get(v_o_145_, 0);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_147_, v_k_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f___boxed(lean_object* v_o_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Options_find_x3f(v_o_149_, v_k_150_);
lean_dec(v_k_150_);
lean_dec_ref(v_o_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find(lean_object* v_o_152_, lean_object* v_k_153_){
_start:
{
lean_object* v_map_154_; lean_object* v___x_155_; 
v_map_154_ = lean_ctor_get(v_o_152_, 0);
v___x_155_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_154_, v_k_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find___boxed(lean_object* v_o_156_, lean_object* v_k_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Options_find(v_o_156_, v_k_157_);
lean_dec(v_k_157_);
lean_dec_ref(v_o_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg(lean_object* v_inst_159_, lean_object* v_o_160_, lean_object* v_k_161_){
_start:
{
lean_object* v_map_162_; lean_object* v_ofDataValue_x3f_163_; lean_object* v___x_164_; 
v_map_162_ = lean_ctor_get(v_o_160_, 0);
v_ofDataValue_x3f_163_ = lean_ctor_get(v_inst_159_, 1);
lean_inc_ref(v_ofDataValue_x3f_163_);
lean_dec_ref(v_inst_159_);
v___x_164_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_162_, v_k_161_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; 
lean_dec_ref(v_ofDataValue_x3f_163_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
v_val_166_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_166_);
lean_dec_ref_known(v___x_164_, 1);
v___x_167_ = lean_apply_1(v_ofDataValue_x3f_163_, v_val_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg___boxed(lean_object* v_inst_168_, lean_object* v_o_169_, lean_object* v_k_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Options_get_x3f___redArg(v_inst_168_, v_o_169_, v_k_170_);
lean_dec(v_k_170_);
lean_dec_ref(v_o_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f(lean_object* v_00_u03b1_172_, lean_object* v_inst_173_, lean_object* v_o_174_, lean_object* v_k_175_){
_start:
{
lean_object* v_map_176_; lean_object* v_ofDataValue_x3f_177_; lean_object* v___x_178_; 
v_map_176_ = lean_ctor_get(v_o_174_, 0);
v_ofDataValue_x3f_177_ = lean_ctor_get(v_inst_173_, 1);
lean_inc_ref(v_ofDataValue_x3f_177_);
lean_dec_ref(v_inst_173_);
v___x_178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_176_, v_k_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v___x_179_; 
lean_dec_ref(v_ofDataValue_x3f_177_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; 
v_val_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v___x_178_, 1);
v___x_181_ = lean_apply_1(v_ofDataValue_x3f_177_, v_val_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___boxed(lean_object* v_00_u03b1_182_, lean_object* v_inst_183_, lean_object* v_o_184_, lean_object* v_k_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Options_get_x3f(v_00_u03b1_182_, v_inst_183_, v_o_184_, v_k_185_);
lean_dec(v_k_185_);
lean_dec_ref(v_o_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg(lean_object* v_inst_187_, lean_object* v_o_188_, lean_object* v_k_189_, lean_object* v_defVal_190_){
_start:
{
lean_object* v_map_191_; lean_object* v_ofDataValue_x3f_192_; lean_object* v___x_193_; 
v_map_191_ = lean_ctor_get(v_o_188_, 0);
v_ofDataValue_x3f_192_ = lean_ctor_get(v_inst_187_, 1);
lean_inc_ref(v_ofDataValue_x3f_192_);
lean_dec_ref(v_inst_187_);
v___x_193_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_191_, v_k_189_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_192_);
lean_inc(v_defVal_190_);
return v_defVal_190_;
}
else
{
lean_object* v_val_194_; lean_object* v___x_195_; 
v_val_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_193_, 1);
v___x_195_ = lean_apply_1(v_ofDataValue_x3f_192_, v_val_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_inc(v_defVal_190_);
return v_defVal_190_;
}
else
{
lean_object* v_val_196_; 
v_val_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v___x_195_, 1);
return v_val_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg___boxed(lean_object* v_inst_197_, lean_object* v_o_198_, lean_object* v_k_199_, lean_object* v_defVal_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Options_get___redArg(v_inst_197_, v_o_198_, v_k_199_, v_defVal_200_);
lean_dec(v_defVal_200_);
lean_dec(v_k_199_);
lean_dec_ref(v_o_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_o_204_, lean_object* v_k_205_, lean_object* v_defVal_206_){
_start:
{
lean_object* v_map_207_; lean_object* v_ofDataValue_x3f_208_; lean_object* v___x_209_; 
v_map_207_ = lean_ctor_get(v_o_204_, 0);
v_ofDataValue_x3f_208_ = lean_ctor_get(v_inst_203_, 1);
lean_inc_ref(v_ofDataValue_x3f_208_);
lean_dec_ref(v_inst_203_);
v___x_209_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_207_, v_k_205_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_208_);
lean_inc(v_defVal_206_);
return v_defVal_206_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; 
v_val_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_209_, 1);
v___x_211_ = lean_apply_1(v_ofDataValue_x3f_208_, v_val_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_inc(v_defVal_206_);
return v_defVal_206_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_211_, 1);
return v_val_212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___boxed(lean_object* v_00_u03b1_213_, lean_object* v_inst_214_, lean_object* v_o_215_, lean_object* v_k_216_, lean_object* v_defVal_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Options_get(v_00_u03b1_213_, v_inst_214_, v_o_215_, v_k_216_, v_defVal_217_);
lean_dec(v_defVal_217_);
lean_dec(v_k_216_);
lean_dec_ref(v_o_215_);
return v_res_218_;
}
}
uint8_t l_Lean_Options_getBool(lean_object* v_o_219_, lean_object* v_k_220_, uint8_t v_defVal_221_){
_start:
{
lean_object* v_map_222_; lean_object* v___x_223_; 
v_map_222_ = lean_ctor_get(v_o_219_, 0);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_222_, v_k_220_);
if (lean_obj_tag(v___x_223_) == 0)
{
return v_defVal_221_;
}
else
{
lean_object* v_val_224_; 
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
if (lean_obj_tag(v_val_224_) == 1)
{
uint8_t v_v_225_; 
v_v_225_ = lean_ctor_get_uint8(v_val_224_, 0);
lean_dec_ref_known(v_val_224_, 0);
return v_v_225_;
}
else
{
lean_dec(v_val_224_);
return v_defVal_221_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_getBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_219_ = stack[0].m_obj;
lean_object* v_k_220_ = stack[1].m_obj;
uint8_t v_defVal_221_ = stack[2].m_num;
uint8_t v_res_226_;
v_res_226_ = l_Lean_Options_getBool(v_o_219_, v_k_220_, v_defVal_221_);
stack->m_num = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_Options_getBool___boxed(lean_object* v_o_227_, lean_object* v_k_228_, lean_object* v_defVal_229_){
_start:
{
uint8_t v_defVal_boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_defVal_boxed_230_ = lean_unbox(v_defVal_229_);
v_res_231_ = l_Lean_Options_getBool(v_o_227_, v_k_228_, v_defVal_boxed_230_);
lean_dec(v_k_228_);
lean_dec_ref(v_o_227_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
uint8_t l_Lean_Options_contains(lean_object* v_o_233_, lean_object* v_k_234_){
_start:
{
lean_object* v_map_235_; uint8_t v___x_236_; 
v_map_235_ = lean_ctor_get(v_o_233_, 0);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_234_, v_map_235_);
return v___x_236_;
}
}
LEAN_EXPORT void l_Lean_Options_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_233_ = stack[0].m_obj;
lean_object* v_k_234_ = stack[1].m_obj;
uint8_t v_res_237_;
v_res_237_ = l_Lean_Options_contains(v_o_233_, v_k_234_);
stack->m_num = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object* v_o_238_, lean_object* v_k_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_Options_contains(v_o_238_, v_k_239_);
lean_dec(v_k_239_);
lean_dec_ref(v_o_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object* v_o_245_, lean_object* v_k_246_, lean_object* v_v_247_){
_start:
{
lean_object* v_map_248_; uint8_t v_hasTrace_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_262_; 
v_map_248_ = lean_ctor_get(v_o_245_, 0);
v_hasTrace_249_ = lean_ctor_get_uint8(v_o_245_, sizeof(void*)*1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_o_245_);
if (v_isSharedCheck_262_ == 0)
{
v___x_251_ = v_o_245_;
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_map_248_);
lean_dec(v_o_245_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; 
lean_inc(v_k_246_);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_246_, v_v_247_, v_map_248_);
if (v_hasTrace_249_ == 0)
{
lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_257_; 
v___x_254_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_255_ = l_Lean_Name_isPrefixOf(v___x_254_, v_k_246_);
lean_dec(v_k_246_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_253_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_255_);
return v___x_257_;
}
}
else
{
lean_object* v___x_260_; 
lean_dec(v_k_246_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_260_ = v___x_251_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_253_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*1, v_hasTrace_249_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object* v_inst_263_, lean_object* v_o_264_, lean_object* v_k_265_, lean_object* v_v_266_){
_start:
{
lean_object* v_toDataValue_267_; lean_object* v_map_268_; uint8_t v_hasTrace_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_283_; 
v_toDataValue_267_ = lean_ctor_get(v_inst_263_, 0);
lean_inc_ref(v_toDataValue_267_);
lean_dec_ref(v_inst_263_);
v_map_268_ = lean_ctor_get(v_o_264_, 0);
v_hasTrace_269_ = lean_ctor_get_uint8(v_o_264_, sizeof(void*)*1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_o_264_);
if (v_isSharedCheck_283_ == 0)
{
v___x_271_ = v_o_264_;
v_isShared_272_ = v_isSharedCheck_283_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_map_268_);
lean_dec(v_o_264_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_283_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_apply_1(v_toDataValue_267_, v_v_266_);
lean_inc(v_k_265_);
v___x_274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_265_, v___x_273_, v_map_268_);
if (v_hasTrace_269_ == 0)
{
lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_278_; 
v___x_275_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_276_ = l_Lean_Name_isPrefixOf(v___x_275_, v_k_265_);
lean_dec(v_k_265_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_278_ = v___x_271_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_274_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*1, v___x_276_);
return v___x_278_;
}
}
else
{
lean_object* v___x_281_; 
lean_dec(v_k_265_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_281_ = v___x_271_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, sizeof(void*)*1, v_hasTrace_269_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object* v_00_u03b1_284_, lean_object* v_inst_285_, lean_object* v_o_286_, lean_object* v_k_287_, lean_object* v_v_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Options_set___redArg(v_inst_285_, v_o_286_, v_k_287_, v_v_288_);
return v___x_289_;
}
}
lean_object* l_Lean_Options_setBool(lean_object* v_o_290_, lean_object* v_k_291_, uint8_t v_v_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = l_Lean_KVMap_instValueBool;
v___x_294_ = lean_box(v_v_292_);
v___x_295_ = l_Lean_Options_set___redArg(v___x_293_, v_o_290_, v_k_291_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_Options_setBool_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_290_ = stack[0].m_obj;
lean_object* v_k_291_ = stack[1].m_obj;
uint8_t v_v_292_ = stack[2].m_num;
lean_object* v_res_296_;
v_res_296_ = l_Lean_Options_setBool(v_o_290_, v_k_291_, v_v_292_);
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object* v_o_297_, lean_object* v_k_298_, lean_object* v_v_299_){
_start:
{
uint8_t v_v_boxed_300_; lean_object* v_res_301_; 
v_v_boxed_300_ = lean_unbox(v_v_299_);
v_res_301_ = l_Lean_Options_setBool(v_o_297_, v_k_298_, v_v_boxed_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object* v_init_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_k_304_; lean_object* v_l_305_; lean_object* v_r_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_k_304_ = lean_ctor_get(v_x_303_, 1);
v_l_305_ = lean_ctor_get(v_x_303_, 3);
v_r_306_ = lean_ctor_get(v_x_303_, 4);
v___x_307_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_302_, v_r_306_);
lean_inc(v_k_304_);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v_k_304_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v_init_302_ = v___x_308_;
v_x_303_ = v_l_305_;
goto _start;
}
else
{
return v_init_302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object* v_init_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_310_, v_x_311_);
lean_dec(v_x_311_);
return v_res_312_;
}
}
uint8_t l_List_any___at___00Lean_Options_erase_spec__2(lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
else
{
lean_object* v_head_315_; lean_object* v_tail_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_head_315_ = lean_ctor_get(v_x_313_, 0);
v_tail_316_ = lean_ctor_get(v_x_313_, 1);
v___x_317_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_318_ = l_Lean_Name_isPrefixOf(v___x_317_, v_head_315_);
if (v___x_318_ == 0)
{
v_x_313_ = v_tail_316_;
goto _start;
}
else
{
return v___x_318_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00Lean_Options_erase_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_313_ = stack[0].m_obj;
uint8_t v_res_320_;
v_res_320_ = l_List_any___at___00Lean_Options_erase_spec__2(v_x_313_);
stack->m_num = v_res_320_;
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Options_erase_spec__2___boxed(lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_List_any___at___00Lean_Options_erase_spec__2(v_x_321_);
lean_dec(v_x_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object* v_k_324_, lean_object* v_t_325_){
_start:
{
if (lean_obj_tag(v_t_325_) == 0)
{
lean_object* v_k_326_; lean_object* v_v_327_; lean_object* v_l_328_; lean_object* v_r_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_983_; 
v_k_326_ = lean_ctor_get(v_t_325_, 1);
v_v_327_ = lean_ctor_get(v_t_325_, 2);
v_l_328_ = lean_ctor_get(v_t_325_, 3);
v_r_329_ = lean_ctor_get(v_t_325_, 4);
v_isSharedCheck_983_ = !lean_is_exclusive(v_t_325_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_t_325_, 0);
lean_dec(v_unused_984_);
v___x_331_ = v_t_325_;
v_isShared_332_ = v_isSharedCheck_983_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_r_329_);
lean_inc(v_l_328_);
lean_inc(v_v_327_);
lean_inc(v_k_326_);
lean_dec(v_t_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_983_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
uint8_t v___x_333_; 
v___x_333_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_324_, v_k_326_);
switch(v___x_333_)
{
case 0:
{
lean_object* v_impl_334_; lean_object* v___x_335_; 
v_impl_334_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_324_, v_l_328_);
v___x_335_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_334_) == 0)
{
if (lean_obj_tag(v_r_329_) == 0)
{
lean_object* v_size_336_; lean_object* v_size_337_; lean_object* v_k_338_; lean_object* v_v_339_; lean_object* v_l_340_; lean_object* v_r_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_size_336_ = lean_ctor_get(v_impl_334_, 0);
v_size_337_ = lean_ctor_get(v_r_329_, 0);
v_k_338_ = lean_ctor_get(v_r_329_, 1);
v_v_339_ = lean_ctor_get(v_r_329_, 2);
v_l_340_ = lean_ctor_get(v_r_329_, 3);
lean_inc(v_l_340_);
v_r_341_ = lean_ctor_get(v_r_329_, 4);
v___x_342_ = lean_unsigned_to_nat(3u);
v___x_343_ = lean_nat_mul(v___x_342_, v_size_336_);
v___x_344_ = lean_nat_dec_lt(v___x_343_, v_size_337_);
lean_dec(v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec(v_l_340_);
v___x_345_ = lean_nat_add(v___x_335_, v_size_336_);
v___x_346_ = lean_nat_add(v___x_345_, v_size_337_);
lean_dec(v___x_345_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 3, v_impl_334_);
lean_ctor_set(v___x_331_, 0, v___x_346_);
v___x_348_ = v___x_331_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_impl_334_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_r_329_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
else
{
lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_413_; 
lean_inc(v_r_341_);
lean_inc(v_v_339_);
lean_inc(v_k_338_);
lean_inc(v_size_337_);
v_isSharedCheck_413_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; lean_object* v_unused_417_; lean_object* v_unused_418_; 
v_unused_414_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_r_329_, 2);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_r_329_, 1);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_r_329_, 0);
lean_dec(v_unused_418_);
v___x_351_ = v_r_329_;
v_isShared_352_ = v_isSharedCheck_413_;
goto v_resetjp_350_;
}
else
{
lean_dec(v_r_329_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_413_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_size_353_; lean_object* v_k_354_; lean_object* v_v_355_; lean_object* v_l_356_; lean_object* v_r_357_; lean_object* v_size_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_size_353_ = lean_ctor_get(v_l_340_, 0);
v_k_354_ = lean_ctor_get(v_l_340_, 1);
v_v_355_ = lean_ctor_get(v_l_340_, 2);
v_l_356_ = lean_ctor_get(v_l_340_, 3);
v_r_357_ = lean_ctor_get(v_l_340_, 4);
v_size_358_ = lean_ctor_get(v_r_341_, 0);
v___x_359_ = lean_unsigned_to_nat(2u);
v___x_360_ = lean_nat_mul(v___x_359_, v_size_358_);
v___x_361_ = lean_nat_dec_lt(v_size_353_, v___x_360_);
lean_dec(v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_389_; 
lean_inc(v_r_357_);
lean_inc(v_l_356_);
lean_inc(v_v_355_);
lean_inc(v_k_354_);
v_isSharedCheck_389_ = !lean_is_exclusive(v_l_340_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; lean_object* v_unused_391_; lean_object* v_unused_392_; lean_object* v_unused_393_; lean_object* v_unused_394_; 
v_unused_390_ = lean_ctor_get(v_l_340_, 4);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_l_340_, 3);
lean_dec(v_unused_391_);
v_unused_392_ = lean_ctor_get(v_l_340_, 2);
lean_dec(v_unused_392_);
v_unused_393_ = lean_ctor_get(v_l_340_, 1);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_l_340_, 0);
lean_dec(v_unused_394_);
v___x_363_ = v_l_340_;
v_isShared_364_ = v_isSharedCheck_389_;
goto v_resetjp_362_;
}
else
{
lean_dec(v_l_340_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_389_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_379_; 
v___x_365_ = lean_nat_add(v___x_335_, v_size_336_);
v___x_366_ = lean_nat_add(v___x_365_, v_size_337_);
lean_dec(v_size_337_);
if (lean_obj_tag(v_l_356_) == 0)
{
lean_object* v_size_387_; 
v_size_387_ = lean_ctor_get(v_l_356_, 0);
lean_inc(v_size_387_);
v___y_379_ = v_size_387_;
goto v___jp_378_;
}
else
{
lean_object* v___x_388_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___y_379_ = v___x_388_;
goto v___jp_378_;
}
v___jp_367_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_nat_add(v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec(v___y_369_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 4, v_r_341_);
lean_ctor_set(v___x_363_, 3, v_r_357_);
lean_ctor_set(v___x_363_, 2, v_v_339_);
lean_ctor_set(v___x_363_, 1, v_k_338_);
lean_ctor_set(v___x_363_, 0, v___x_371_);
v___x_373_ = v___x_363_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_338_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_339_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_r_357_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_r_341_);
v___x_373_ = v_reuseFailAlloc_377_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 4, v___x_373_);
lean_ctor_set(v___x_351_, 3, v___y_368_);
lean_ctor_set(v___x_351_, 2, v_v_355_);
lean_ctor_set(v___x_351_, 1, v_k_354_);
lean_ctor_set(v___x_351_, 0, v___x_366_);
v___x_375_ = v___x_351_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_k_354_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_v_355_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v___y_368_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_nat_add(v___x_365_, v___y_379_);
lean_dec(v___y_379_);
lean_dec(v___x_365_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_l_356_);
lean_ctor_set(v___x_331_, 3, v_impl_334_);
lean_ctor_set(v___x_331_, 0, v___x_380_);
v___x_382_ = v___x_331_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_impl_334_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v_l_356_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_nat_add(v___x_335_, v_size_358_);
if (lean_obj_tag(v_r_357_) == 0)
{
lean_object* v_size_384_; 
v_size_384_ = lean_ctor_get(v_r_357_, 0);
lean_inc(v_size_384_);
v___y_368_ = v___x_382_;
v___y_369_ = v___x_383_;
v___y_370_ = v_size_384_;
goto v___jp_367_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___y_368_ = v___x_382_;
v___y_369_ = v___x_383_;
v___y_370_ = v___x_385_;
goto v___jp_367_;
}
}
}
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
lean_del_object(v___x_331_);
v___x_395_ = lean_nat_add(v___x_335_, v_size_336_);
v___x_396_ = lean_nat_add(v___x_395_, v_size_337_);
lean_dec(v_size_337_);
v___x_397_ = lean_nat_add(v___x_395_, v_size_353_);
lean_dec(v___x_395_);
lean_inc_ref(v_impl_334_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 4, v_l_340_);
lean_ctor_set(v___x_351_, 3, v_impl_334_);
lean_ctor_set(v___x_351_, 2, v_v_327_);
lean_ctor_set(v___x_351_, 1, v_k_326_);
lean_ctor_set(v___x_351_, 0, v___x_397_);
v___x_399_ = v___x_351_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_impl_334_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_l_340_);
v___x_399_ = v_reuseFailAlloc_412_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_isSharedCheck_406_ = !lean_is_exclusive(v_impl_334_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_407_ = lean_ctor_get(v_impl_334_, 4);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_impl_334_, 3);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_impl_334_, 2);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_impl_334_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_impl_334_, 0);
lean_dec(v_unused_411_);
v___x_401_ = v_impl_334_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_dec(v_impl_334_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 4, v_r_341_);
lean_ctor_set(v___x_401_, 3, v___x_399_);
lean_ctor_set(v___x_401_, 2, v_v_339_);
lean_ctor_set(v___x_401_, 1, v_k_338_);
lean_ctor_set(v___x_401_, 0, v___x_396_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_k_338_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_v_339_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_r_341_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v_size_419_ = lean_ctor_get(v_impl_334_, 0);
v___x_420_ = lean_nat_add(v___x_335_, v_size_419_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 3, v_impl_334_);
lean_ctor_set(v___x_331_, 0, v___x_420_);
v___x_422_ = v___x_331_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_impl_334_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_r_329_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
if (lean_obj_tag(v_r_329_) == 0)
{
lean_object* v_l_424_; 
v_l_424_ = lean_ctor_get(v_r_329_, 3);
lean_inc(v_l_424_);
if (lean_obj_tag(v_l_424_) == 0)
{
lean_object* v_r_425_; 
v_r_425_ = lean_ctor_get(v_r_329_, 4);
lean_inc(v_r_425_);
if (lean_obj_tag(v_r_425_) == 0)
{
lean_object* v_size_426_; lean_object* v_k_427_; lean_object* v_v_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_441_; 
v_size_426_ = lean_ctor_get(v_r_329_, 0);
v_k_427_ = lean_ctor_get(v_r_329_, 1);
v_v_428_ = lean_ctor_get(v_r_329_, 2);
v_isSharedCheck_441_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_442_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_443_);
v___x_430_ = v_r_329_;
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_v_428_);
lean_inc(v_k_427_);
lean_inc(v_size_426_);
lean_dec(v_r_329_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_size_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v_size_432_ = lean_ctor_get(v_l_424_, 0);
v___x_433_ = lean_nat_add(v___x_335_, v_size_426_);
lean_dec(v_size_426_);
v___x_434_ = lean_nat_add(v___x_335_, v_size_432_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 4, v_l_424_);
lean_ctor_set(v___x_430_, 3, v_impl_334_);
lean_ctor_set(v___x_430_, 2, v_v_327_);
lean_ctor_set(v___x_430_, 1, v_k_326_);
lean_ctor_set(v___x_430_, 0, v___x_434_);
v___x_436_ = v___x_430_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_impl_334_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_l_424_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_r_425_);
lean_ctor_set(v___x_331_, 3, v___x_436_);
lean_ctor_set(v___x_331_, 2, v_v_428_);
lean_ctor_set(v___x_331_, 1, v_k_427_);
lean_ctor_set(v___x_331_, 0, v___x_433_);
v___x_438_ = v___x_331_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_k_427_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_v_428_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_r_425_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_468_; 
v_k_444_ = lean_ctor_get(v_r_329_, 1);
v_v_445_ = lean_ctor_get(v_r_329_, 2);
v_isSharedCheck_468_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_469_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_r_329_, 0);
lean_dec(v_unused_471_);
v___x_447_ = v_r_329_;
v_isShared_448_ = v_isSharedCheck_468_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_v_445_);
lean_inc(v_k_444_);
lean_dec(v_r_329_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_468_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_k_449_; lean_object* v_v_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_464_; 
v_k_449_ = lean_ctor_get(v_l_424_, 1);
v_v_450_ = lean_ctor_get(v_l_424_, 2);
v_isSharedCheck_464_ = !lean_is_exclusive(v_l_424_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; 
v_unused_465_ = lean_ctor_get(v_l_424_, 4);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_l_424_, 3);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_l_424_, 0);
lean_dec(v_unused_467_);
v___x_452_ = v_l_424_;
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_v_450_);
lean_inc(v_k_449_);
lean_dec(v_l_424_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(3u);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_r_425_);
lean_ctor_set(v___x_452_, 3, v_r_425_);
lean_ctor_set(v___x_452_, 2, v_v_327_);
lean_ctor_set(v___x_452_, 1, v_k_326_);
lean_ctor_set(v___x_452_, 0, v___x_335_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_r_425_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_r_425_);
v___x_456_ = v_reuseFailAlloc_463_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 3, v_r_425_);
lean_ctor_set(v___x_447_, 0, v___x_335_);
v___x_458_ = v___x_447_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_k_444_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_v_445_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_r_425_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_r_425_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_458_);
lean_ctor_set(v___x_331_, 3, v___x_456_);
lean_ctor_set(v___x_331_, 2, v_v_450_);
lean_ctor_set(v___x_331_, 1, v_k_449_);
lean_ctor_set(v___x_331_, 0, v___x_454_);
v___x_460_ = v___x_331_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_k_449_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_v_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_472_; 
v_r_472_ = lean_ctor_get(v_r_329_, 4);
lean_inc(v_r_472_);
if (lean_obj_tag(v_r_472_) == 0)
{
lean_object* v_k_473_; lean_object* v_v_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
v_k_473_ = lean_ctor_get(v_r_329_, 1);
v_v_474_ = lean_ctor_get(v_r_329_, 2);
v_isSharedCheck_485_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_486_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_r_329_, 0);
lean_dec(v_unused_488_);
v___x_476_ = v_r_329_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_v_474_);
lean_inc(v_k_473_);
lean_dec(v_r_329_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(3u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v_l_424_);
lean_ctor_set(v___x_476_, 2, v_v_327_);
lean_ctor_set(v___x_476_, 1, v_k_326_);
lean_ctor_set(v___x_476_, 0, v___x_335_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_l_424_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_l_424_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_r_472_);
lean_ctor_set(v___x_331_, 3, v___x_480_);
lean_ctor_set(v___x_331_, 2, v_v_474_);
lean_ctor_set(v___x_331_, 1, v_k_473_);
lean_ctor_set(v___x_331_, 0, v___x_478_);
v___x_482_ = v___x_331_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_k_473_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_v_474_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_483_, 4, v_r_472_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_size_489_; lean_object* v_k_490_; lean_object* v_v_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_502_; 
v_size_489_ = lean_ctor_get(v_r_329_, 0);
v_k_490_ = lean_ctor_get(v_r_329_, 1);
v_v_491_ = lean_ctor_get(v_r_329_, 2);
v_isSharedCheck_502_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; lean_object* v_unused_504_; 
v_unused_503_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_504_);
v___x_493_ = v_r_329_;
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_v_491_);
lean_inc(v_k_490_);
lean_inc(v_size_489_);
lean_dec(v_r_329_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v_r_472_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_size_489_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_k_490_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_v_491_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_r_472_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_r_472_);
v___x_496_ = v_reuseFailAlloc_501_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(2u);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_496_);
lean_ctor_set(v___x_331_, 3, v_r_472_);
lean_ctor_set(v___x_331_, 0, v___x_497_);
v___x_499_ = v___x_331_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_r_472_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v___x_496_);
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
}
}
else
{
lean_object* v___x_506_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 3, v_r_329_);
lean_ctor_set(v___x_331_, 0, v___x_335_);
v___x_506_ = v___x_331_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_r_329_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_r_329_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
case 1:
{
lean_del_object(v___x_331_);
lean_dec(v_v_327_);
lean_dec(v_k_326_);
if (lean_obj_tag(v_l_328_) == 0)
{
if (lean_obj_tag(v_r_329_) == 0)
{
lean_object* v_size_508_; lean_object* v_k_509_; lean_object* v_v_510_; lean_object* v_l_511_; lean_object* v_r_512_; lean_object* v_size_513_; lean_object* v_k_514_; lean_object* v_v_515_; lean_object* v_l_516_; lean_object* v_r_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_size_508_ = lean_ctor_get(v_l_328_, 0);
v_k_509_ = lean_ctor_get(v_l_328_, 1);
v_v_510_ = lean_ctor_get(v_l_328_, 2);
v_l_511_ = lean_ctor_get(v_l_328_, 3);
v_r_512_ = lean_ctor_get(v_l_328_, 4);
lean_inc(v_r_512_);
v_size_513_ = lean_ctor_get(v_r_329_, 0);
v_k_514_ = lean_ctor_get(v_r_329_, 1);
v_v_515_ = lean_ctor_get(v_r_329_, 2);
v_l_516_ = lean_ctor_get(v_r_329_, 3);
lean_inc(v_l_516_);
v_r_517_ = lean_ctor_get(v_r_329_, 4);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_dec_lt(v_size_508_, v_size_513_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_655_; 
lean_inc(v_l_511_);
lean_inc(v_v_510_);
lean_inc(v_k_509_);
v_isSharedCheck_655_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; lean_object* v_unused_657_; lean_object* v_unused_658_; lean_object* v_unused_659_; lean_object* v_unused_660_; 
v_unused_656_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_l_328_, 2);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_l_328_, 1);
lean_dec(v_unused_659_);
v_unused_660_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_660_);
v___x_521_ = v_l_328_;
v_isShared_522_ = v_isSharedCheck_655_;
goto v_resetjp_520_;
}
else
{
lean_dec(v_l_328_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_655_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v_tree_524_; 
v___x_523_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_509_, v_v_510_, v_l_511_, v_r_512_);
v_tree_524_ = lean_ctor_get(v___x_523_, 2);
if (lean_obj_tag(v_tree_524_) == 0)
{
lean_object* v_k_525_; lean_object* v_v_526_; lean_object* v_size_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
lean_inc_ref(v_tree_524_);
v_k_525_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_k_525_);
v_v_526_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_v_526_);
lean_dec_ref(v___x_523_);
v_size_527_ = lean_ctor_get(v_tree_524_, 0);
v___x_528_ = lean_unsigned_to_nat(3u);
v___x_529_ = lean_nat_mul(v___x_528_, v_size_527_);
v___x_530_ = lean_nat_dec_lt(v___x_529_, v_size_513_);
lean_dec(v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec(v_l_516_);
v___x_531_ = lean_nat_add(v___x_518_, v_size_527_);
v___x_532_ = lean_nat_add(v___x_531_, v_size_513_);
lean_dec(v___x_531_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v_r_329_);
lean_ctor_set(v___x_521_, 3, v_tree_524_);
lean_ctor_set(v___x_521_, 2, v_v_526_);
lean_ctor_set(v___x_521_, 1, v_k_525_);
lean_ctor_set(v___x_521_, 0, v___x_532_);
v___x_534_ = v___x_521_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_k_525_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_v_526_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_tree_524_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_r_329_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
else
{
lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_590_; 
lean_inc(v_r_517_);
lean_inc(v_v_515_);
lean_inc(v_k_514_);
lean_inc(v_size_513_);
v_isSharedCheck_590_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; 
v_unused_591_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_r_329_, 2);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_r_329_, 1);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_r_329_, 0);
lean_dec(v_unused_595_);
v___x_537_ = v_r_329_;
v_isShared_538_ = v_isSharedCheck_590_;
goto v_resetjp_536_;
}
else
{
lean_dec(v_r_329_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_590_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_size_539_; lean_object* v_k_540_; lean_object* v_v_541_; lean_object* v_l_542_; lean_object* v_r_543_; lean_object* v_size_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_size_539_ = lean_ctor_get(v_l_516_, 0);
v_k_540_ = lean_ctor_get(v_l_516_, 1);
v_v_541_ = lean_ctor_get(v_l_516_, 2);
v_l_542_ = lean_ctor_get(v_l_516_, 3);
v_r_543_ = lean_ctor_get(v_l_516_, 4);
v_size_544_ = lean_ctor_get(v_r_517_, 0);
v___x_545_ = lean_unsigned_to_nat(2u);
v___x_546_ = lean_nat_mul(v___x_545_, v_size_544_);
v___x_547_ = lean_nat_dec_lt(v_size_539_, v___x_546_);
lean_dec(v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_575_; 
lean_inc(v_r_543_);
lean_inc(v_l_542_);
lean_inc(v_v_541_);
lean_inc(v_k_540_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_l_516_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; lean_object* v_unused_580_; 
v_unused_576_ = lean_ctor_get(v_l_516_, 4);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_l_516_, 3);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_l_516_, 2);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_l_516_, 1);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_l_516_, 0);
lean_dec(v_unused_580_);
v___x_549_ = v_l_516_;
v_isShared_550_ = v_isSharedCheck_575_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_l_516_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_575_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_565_; 
v___x_551_ = lean_nat_add(v___x_518_, v_size_527_);
v___x_552_ = lean_nat_add(v___x_551_, v_size_513_);
lean_dec(v_size_513_);
if (lean_obj_tag(v_l_542_) == 0)
{
lean_object* v_size_573_; 
v_size_573_ = lean_ctor_get(v_l_542_, 0);
lean_inc(v_size_573_);
v___y_565_ = v_size_573_;
goto v___jp_564_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___y_565_ = v___x_574_;
goto v___jp_564_;
}
v___jp_553_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_nat_add(v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 4, v_r_517_);
lean_ctor_set(v___x_549_, 3, v_r_543_);
lean_ctor_set(v___x_549_, 2, v_v_515_);
lean_ctor_set(v___x_549_, 1, v_k_514_);
lean_ctor_set(v___x_549_, 0, v___x_557_);
v___x_559_ = v___x_549_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_r_543_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_r_517_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 4, v___x_559_);
lean_ctor_set(v___x_537_, 3, v___y_554_);
lean_ctor_set(v___x_537_, 2, v_v_541_);
lean_ctor_set(v___x_537_, 1, v_k_540_);
lean_ctor_set(v___x_537_, 0, v___x_552_);
v___x_561_ = v___x_537_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_541_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v___y_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_nat_add(v___x_551_, v___y_565_);
lean_dec(v___y_565_);
lean_dec(v___x_551_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v_l_542_);
lean_ctor_set(v___x_521_, 3, v_tree_524_);
lean_ctor_set(v___x_521_, 2, v_v_526_);
lean_ctor_set(v___x_521_, 1, v_k_525_);
lean_ctor_set(v___x_521_, 0, v___x_566_);
v___x_568_ = v___x_521_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_k_525_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_v_526_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_tree_524_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_l_542_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_nat_add(v___x_518_, v_size_544_);
if (lean_obj_tag(v_r_543_) == 0)
{
lean_object* v_size_570_; 
v_size_570_ = lean_ctor_get(v_r_543_, 0);
lean_inc(v_size_570_);
v___y_554_ = v___x_568_;
v___y_555_ = v___x_569_;
v___y_556_ = v_size_570_;
goto v___jp_553_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___y_554_ = v___x_568_;
v___y_555_ = v___x_569_;
v___y_556_ = v___x_571_;
goto v___jp_553_;
}
}
}
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_581_ = lean_nat_add(v___x_518_, v_size_527_);
v___x_582_ = lean_nat_add(v___x_581_, v_size_513_);
lean_dec(v_size_513_);
v___x_583_ = lean_nat_add(v___x_581_, v_size_539_);
lean_dec(v___x_581_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 4, v_l_516_);
lean_ctor_set(v___x_537_, 3, v_tree_524_);
lean_ctor_set(v___x_537_, 2, v_v_526_);
lean_ctor_set(v___x_537_, 1, v_k_525_);
lean_ctor_set(v___x_537_, 0, v___x_583_);
v___x_585_ = v___x_537_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_525_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_526_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_tree_524_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_l_516_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v_r_517_);
lean_ctor_set(v___x_521_, 3, v___x_585_);
lean_ctor_set(v___x_521_, 2, v_v_515_);
lean_ctor_set(v___x_521_, 1, v_k_514_);
lean_ctor_set(v___x_521_, 0, v___x_582_);
v___x_587_ = v___x_521_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_r_517_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
else
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_649_; 
lean_inc(v_r_517_);
lean_inc(v_v_515_);
lean_inc(v_k_514_);
lean_inc(v_size_513_);
v_isSharedCheck_649_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; lean_object* v_unused_653_; lean_object* v_unused_654_; 
v_unused_650_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_r_329_, 2);
lean_dec(v_unused_652_);
v_unused_653_ = lean_ctor_get(v_r_329_, 1);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_r_329_, 0);
lean_dec(v_unused_654_);
v___x_597_ = v_r_329_;
v_isShared_598_ = v_isSharedCheck_649_;
goto v_resetjp_596_;
}
else
{
lean_dec(v_r_329_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_649_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
if (lean_obj_tag(v_l_516_) == 0)
{
if (lean_obj_tag(v_r_517_) == 0)
{
lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v_size_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
lean_inc(v_tree_524_);
v_k_599_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_k_599_);
v_v_600_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_v_600_);
lean_dec_ref(v___x_523_);
v_size_601_ = lean_ctor_get(v_l_516_, 0);
v___x_602_ = lean_nat_add(v___x_518_, v_size_513_);
lean_dec(v_size_513_);
v___x_603_ = lean_nat_add(v___x_518_, v_size_601_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v_l_516_);
lean_ctor_set(v___x_597_, 3, v_tree_524_);
lean_ctor_set(v___x_597_, 2, v_v_600_);
lean_ctor_set(v___x_597_, 1, v_k_599_);
lean_ctor_set(v___x_597_, 0, v___x_603_);
v___x_605_ = v___x_597_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_599_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_600_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_tree_524_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_l_516_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v_r_517_);
lean_ctor_set(v___x_521_, 3, v___x_605_);
lean_ctor_set(v___x_521_, 2, v_v_515_);
lean_ctor_set(v___x_521_, 1, v_k_514_);
lean_ctor_set(v___x_521_, 0, v___x_602_);
v___x_607_ = v___x_521_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_r_517_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_k_610_; lean_object* v_v_611_; lean_object* v_k_612_; lean_object* v_v_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_size_513_);
v_k_610_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_k_610_);
v_v_611_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_v_611_);
lean_dec_ref(v___x_523_);
v_k_612_ = lean_ctor_get(v_l_516_, 1);
v_v_613_ = lean_ctor_get(v_l_516_, 2);
v_isSharedCheck_627_ = !lean_is_exclusive(v_l_516_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_628_ = lean_ctor_get(v_l_516_, 4);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_l_516_, 3);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_l_516_, 0);
lean_dec(v_unused_630_);
v___x_615_ = v_l_516_;
v_isShared_616_ = v_isSharedCheck_627_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_v_613_);
lean_inc(v_k_612_);
lean_dec(v_l_516_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_627_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_unsigned_to_nat(3u);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 4, v_r_517_);
lean_ctor_set(v___x_615_, 3, v_r_517_);
lean_ctor_set(v___x_615_, 2, v_v_611_);
lean_ctor_set(v___x_615_, 1, v_k_610_);
lean_ctor_set(v___x_615_, 0, v___x_518_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_k_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_v_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_r_517_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_r_517_);
v___x_619_ = v_reuseFailAlloc_626_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 3, v_r_517_);
lean_ctor_set(v___x_597_, 0, v___x_518_);
v___x_621_ = v___x_597_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_r_517_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_r_517_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v___x_621_);
lean_ctor_set(v___x_521_, 3, v___x_619_);
lean_ctor_set(v___x_521_, 2, v_v_613_);
lean_ctor_set(v___x_521_, 1, v_k_612_);
lean_ctor_set(v___x_521_, 0, v___x_617_);
v___x_623_ = v___x_521_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_k_612_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_v_613_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_517_) == 0)
{
lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_dec(v_size_513_);
v_k_631_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_k_631_);
v_v_632_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_v_632_);
lean_dec_ref(v___x_523_);
v___x_633_ = lean_unsigned_to_nat(3u);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v_l_516_);
lean_ctor_set(v___x_597_, 2, v_v_632_);
lean_ctor_set(v___x_597_, 1, v_k_631_);
lean_ctor_set(v___x_597_, 0, v___x_518_);
v___x_635_ = v___x_597_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_631_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_632_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_l_516_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_l_516_);
v___x_635_ = v_reuseFailAlloc_639_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v_r_517_);
lean_ctor_set(v___x_521_, 3, v___x_635_);
lean_ctor_set(v___x_521_, 2, v_v_515_);
lean_ctor_set(v___x_521_, 1, v_k_514_);
lean_ctor_set(v___x_521_, 0, v___x_633_);
v___x_637_ = v___x_521_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_r_517_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_object* v_k_640_; lean_object* v_v_641_; lean_object* v___x_643_; 
v_k_640_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_k_640_);
v_v_641_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_v_641_);
lean_dec_ref(v___x_523_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 3, v_r_517_);
v___x_643_ = v___x_597_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_size_513_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_515_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_r_517_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_r_517_);
v___x_643_ = v_reuseFailAlloc_648_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(2u);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 4, v___x_643_);
lean_ctor_set(v___x_521_, 3, v_r_517_);
lean_ctor_set(v___x_521_, 2, v_v_641_);
lean_ctor_set(v___x_521_, 1, v_k_640_);
lean_ctor_set(v___x_521_, 0, v___x_644_);
v___x_646_ = v___x_521_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_640_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_v_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_r_517_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v___x_643_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
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
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_813_; 
lean_inc(v_r_517_);
lean_inc(v_v_515_);
lean_inc(v_k_514_);
v_isSharedCheck_813_ = !lean_is_exclusive(v_r_329_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_814_ = lean_ctor_get(v_r_329_, 4);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_r_329_, 3);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_r_329_, 2);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_r_329_, 1);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_r_329_, 0);
lean_dec(v_unused_818_);
v___x_662_ = v_r_329_;
v_isShared_663_ = v_isSharedCheck_813_;
goto v_resetjp_661_;
}
else
{
lean_dec(v_r_329_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_813_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v_tree_665_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_514_, v_v_515_, v_l_516_, v_r_517_);
v_tree_665_ = lean_ctor_get(v___x_664_, 2);
lean_inc(v_tree_665_);
if (lean_obj_tag(v_tree_665_) == 0)
{
lean_object* v_k_666_; lean_object* v_v_667_; lean_object* v_size_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_k_666_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_k_666_);
v_v_667_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_v_667_);
lean_dec_ref(v___x_664_);
v_size_668_ = lean_ctor_get(v_tree_665_, 0);
v___x_669_ = lean_unsigned_to_nat(3u);
v___x_670_ = lean_nat_mul(v___x_669_, v_size_668_);
v___x_671_ = lean_nat_dec_lt(v___x_670_, v_size_508_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_dec(v_r_512_);
v___x_672_ = lean_nat_add(v___x_518_, v_size_508_);
v___x_673_ = lean_nat_add(v___x_672_, v_size_668_);
lean_dec(v___x_672_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_tree_665_);
lean_ctor_set(v___x_662_, 3, v_l_328_);
lean_ctor_set(v___x_662_, 2, v_v_667_);
lean_ctor_set(v___x_662_, 1, v_k_666_);
lean_ctor_set(v___x_662_, 0, v___x_673_);
v___x_675_ = v___x_662_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_tree_665_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_742_; 
lean_inc(v_l_511_);
lean_inc(v_v_510_);
lean_inc(v_k_509_);
lean_inc(v_size_508_);
v_isSharedCheck_742_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_743_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_l_328_, 2);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_l_328_, 1);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_747_);
v___x_678_ = v_l_328_;
v_isShared_679_ = v_isSharedCheck_742_;
goto v_resetjp_677_;
}
else
{
lean_dec(v_l_328_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_742_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_size_680_; lean_object* v_size_681_; lean_object* v_k_682_; lean_object* v_v_683_; lean_object* v_l_684_; lean_object* v_r_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_size_680_ = lean_ctor_get(v_l_511_, 0);
v_size_681_ = lean_ctor_get(v_r_512_, 0);
v_k_682_ = lean_ctor_get(v_r_512_, 1);
v_v_683_ = lean_ctor_get(v_r_512_, 2);
v_l_684_ = lean_ctor_get(v_r_512_, 3);
v_r_685_ = lean_ctor_get(v_r_512_, 4);
v___x_686_ = lean_unsigned_to_nat(2u);
v___x_687_ = lean_nat_mul(v___x_686_, v_size_680_);
v___x_688_ = lean_nat_dec_lt(v_size_681_, v___x_687_);
lean_dec(v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_726_; 
lean_inc(v_r_685_);
lean_inc(v_l_684_);
lean_inc(v_v_683_);
lean_inc(v_k_682_);
lean_del_object(v___x_678_);
v_isSharedCheck_726_ = !lean_is_exclusive(v_r_512_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; 
v_unused_727_ = lean_ctor_get(v_r_512_, 4);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_r_512_, 3);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_r_512_, 2);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_r_512_, 1);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_r_512_, 0);
lean_dec(v_unused_731_);
v___x_690_ = v_r_512_;
v_isShared_691_ = v_isSharedCheck_726_;
goto v_resetjp_689_;
}
else
{
lean_dec(v_r_512_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_726_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___x_714_; lean_object* v___y_716_; 
v___x_692_ = lean_nat_add(v___x_518_, v_size_508_);
lean_dec(v_size_508_);
v___x_693_ = lean_nat_add(v___x_692_, v_size_668_);
lean_dec(v___x_692_);
v___x_714_ = lean_nat_add(v___x_518_, v_size_680_);
if (lean_obj_tag(v_l_684_) == 0)
{
lean_object* v_size_724_; 
v_size_724_ = lean_ctor_get(v_l_684_, 0);
lean_inc(v_size_724_);
v___y_716_ = v_size_724_;
goto v___jp_715_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___y_716_ = v___x_725_;
goto v___jp_715_;
}
v___jp_694_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = lean_nat_add(v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_inc_ref(v_tree_665_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v_tree_665_);
lean_ctor_set(v___x_690_, 3, v_r_685_);
lean_ctor_set(v___x_690_, 2, v_v_667_);
lean_ctor_set(v___x_690_, 1, v_k_666_);
lean_ctor_set(v___x_690_, 0, v___x_698_);
v___x_700_ = v___x_690_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_r_685_);
lean_ctor_set(v_reuseFailAlloc_713_, 4, v_tree_665_);
v___x_700_ = v_reuseFailAlloc_713_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v_tree_665_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_708_ = lean_ctor_get(v_tree_665_, 4);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_tree_665_, 3);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_tree_665_, 2);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_tree_665_, 1);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_tree_665_, 0);
lean_dec(v_unused_712_);
v___x_702_ = v_tree_665_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_tree_665_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v___x_700_);
lean_ctor_set(v___x_702_, 3, v___y_695_);
lean_ctor_set(v___x_702_, 2, v_v_683_);
lean_ctor_set(v___x_702_, 1, v_k_682_);
lean_ctor_set(v___x_702_, 0, v___x_693_);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_k_682_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_v_683_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v___y_695_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v___x_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_nat_add(v___x_714_, v___y_716_);
lean_dec(v___y_716_);
lean_dec(v___x_714_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_l_684_);
lean_ctor_set(v___x_662_, 3, v_l_511_);
lean_ctor_set(v___x_662_, 2, v_v_510_);
lean_ctor_set(v___x_662_, 1, v_k_509_);
lean_ctor_set(v___x_662_, 0, v___x_717_);
v___x_719_ = v___x_662_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_509_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_510_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_l_511_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_l_684_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
v___x_720_ = lean_nat_add(v___x_518_, v_size_668_);
if (lean_obj_tag(v_r_685_) == 0)
{
lean_object* v_size_721_; 
v_size_721_ = lean_ctor_get(v_r_685_, 0);
lean_inc(v_size_721_);
v___y_695_ = v___x_719_;
v___y_696_ = v___x_720_;
v___y_697_ = v_size_721_;
goto v___jp_694_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___y_695_ = v___x_719_;
v___y_696_ = v___x_720_;
v___y_697_ = v___x_722_;
goto v___jp_694_;
}
}
}
}
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_732_ = lean_nat_add(v___x_518_, v_size_508_);
lean_dec(v_size_508_);
v___x_733_ = lean_nat_add(v___x_732_, v_size_668_);
lean_dec(v___x_732_);
v___x_734_ = lean_nat_add(v___x_518_, v_size_668_);
v___x_735_ = lean_nat_add(v___x_734_, v_size_681_);
lean_dec(v___x_734_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_tree_665_);
lean_ctor_set(v___x_662_, 3, v_r_512_);
lean_ctor_set(v___x_662_, 2, v_v_667_);
lean_ctor_set(v___x_662_, 1, v_k_666_);
lean_ctor_set(v___x_662_, 0, v___x_735_);
v___x_737_ = v___x_662_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_r_512_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_tree_665_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v___x_737_);
lean_ctor_set(v___x_678_, 0, v___x_733_);
v___x_739_ = v___x_678_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_509_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_510_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_l_511_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_511_) == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_771_; 
lean_inc_ref(v_l_511_);
lean_inc(v_v_510_);
lean_inc(v_k_509_);
lean_inc(v_size_508_);
v_isSharedCheck_771_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_772_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_772_);
v_unused_773_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_l_328_, 2);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_l_328_, 1);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_776_);
v___x_749_ = v_l_328_;
v_isShared_750_ = v_isSharedCheck_771_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_l_328_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_771_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
if (lean_obj_tag(v_r_512_) == 0)
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v_size_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v_k_751_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_k_751_);
v_v_752_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_v_752_);
lean_dec_ref(v___x_664_);
v_size_753_ = lean_ctor_get(v_r_512_, 0);
v___x_754_ = lean_nat_add(v___x_518_, v_size_508_);
lean_dec(v_size_508_);
v___x_755_ = lean_nat_add(v___x_518_, v_size_753_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_tree_665_);
lean_ctor_set(v___x_662_, 3, v_r_512_);
lean_ctor_set(v___x_662_, 2, v_v_752_);
lean_ctor_set(v___x_662_, 1, v_k_751_);
lean_ctor_set(v___x_662_, 0, v___x_755_);
v___x_757_ = v___x_662_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_r_512_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_tree_665_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v___x_757_);
lean_ctor_set(v___x_749_, 0, v___x_754_);
v___x_759_ = v___x_749_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_509_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_510_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_l_511_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_object* v_k_762_; lean_object* v_v_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
lean_dec(v_size_508_);
v_k_762_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_k_762_);
v_v_763_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_v_763_);
lean_dec_ref(v___x_664_);
v___x_764_ = lean_unsigned_to_nat(3u);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_r_512_);
lean_ctor_set(v___x_662_, 3, v_r_512_);
lean_ctor_set(v___x_662_, 2, v_v_763_);
lean_ctor_set(v___x_662_, 1, v_k_762_);
lean_ctor_set(v___x_662_, 0, v___x_518_);
v___x_766_ = v___x_662_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_762_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_r_512_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_r_512_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v___x_766_);
lean_ctor_set(v___x_749_, 0, v___x_764_);
v___x_768_ = v___x_749_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_509_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_510_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_l_511_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_512_) == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_801_; 
lean_inc(v_l_511_);
lean_inc(v_v_510_);
lean_inc(v_k_509_);
v_isSharedCheck_801_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; lean_object* v_unused_803_; lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; 
v_unused_802_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_803_);
v_unused_804_ = lean_ctor_get(v_l_328_, 2);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_l_328_, 1);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_806_);
v___x_778_ = v_l_328_;
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_l_328_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_801_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v_k_782_; lean_object* v_v_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_797_; 
v_k_780_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_k_780_);
v_v_781_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_v_781_);
lean_dec_ref(v___x_664_);
v_k_782_ = lean_ctor_get(v_r_512_, 1);
v_v_783_ = lean_ctor_get(v_r_512_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_r_512_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; 
v_unused_798_ = lean_ctor_get(v_r_512_, 4);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_r_512_, 3);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_r_512_, 0);
lean_dec(v_unused_800_);
v___x_785_ = v_r_512_;
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_v_783_);
lean_inc(v_k_782_);
lean_dec(v_r_512_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_797_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_unsigned_to_nat(3u);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 4, v_l_511_);
lean_ctor_set(v___x_785_, 3, v_l_511_);
lean_ctor_set(v___x_785_, 2, v_v_510_);
lean_ctor_set(v___x_785_, 1, v_k_509_);
lean_ctor_set(v___x_785_, 0, v___x_518_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_509_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_510_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_l_511_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_l_511_);
v___x_789_ = v_reuseFailAlloc_796_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_l_511_);
lean_ctor_set(v___x_662_, 3, v_l_511_);
lean_ctor_set(v___x_662_, 2, v_v_781_);
lean_ctor_set(v___x_662_, 1, v_k_780_);
lean_ctor_set(v___x_662_, 0, v___x_518_);
v___x_791_ = v___x_662_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_l_511_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_l_511_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 4, v___x_791_);
lean_ctor_set(v___x_778_, 3, v___x_789_);
lean_ctor_set(v___x_778_, 2, v_v_783_);
lean_ctor_set(v___x_778_, 1, v_k_782_);
lean_ctor_set(v___x_778_, 0, v___x_787_);
v___x_793_ = v___x_778_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_k_782_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_v_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
}
else
{
lean_object* v_k_807_; lean_object* v_v_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_k_807_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_k_807_);
v_v_808_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_v_808_);
lean_dec_ref(v___x_664_);
v___x_809_ = lean_unsigned_to_nat(2u);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 4, v_r_512_);
lean_ctor_set(v___x_662_, 3, v_l_328_);
lean_ctor_set(v___x_662_, 2, v_v_808_);
lean_ctor_set(v___x_662_, 1, v_k_807_);
lean_ctor_set(v___x_662_, 0, v___x_809_);
v___x_811_ = v___x_662_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_807_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_808_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_r_512_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
}
else
{
return v_l_328_;
}
}
else
{
return v_r_329_;
}
}
default: 
{
lean_object* v_impl_819_; lean_object* v___x_820_; 
v_impl_819_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_324_, v_r_329_);
v___x_820_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_819_) == 0)
{
if (lean_obj_tag(v_l_328_) == 0)
{
lean_object* v_size_821_; lean_object* v_size_822_; lean_object* v_k_823_; lean_object* v_v_824_; lean_object* v_l_825_; lean_object* v_r_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_size_821_ = lean_ctor_get(v_impl_819_, 0);
v_size_822_ = lean_ctor_get(v_l_328_, 0);
v_k_823_ = lean_ctor_get(v_l_328_, 1);
v_v_824_ = lean_ctor_get(v_l_328_, 2);
v_l_825_ = lean_ctor_get(v_l_328_, 3);
v_r_826_ = lean_ctor_get(v_l_328_, 4);
lean_inc(v_r_826_);
v___x_827_ = lean_unsigned_to_nat(3u);
v___x_828_ = lean_nat_mul(v___x_827_, v_size_821_);
v___x_829_ = lean_nat_dec_lt(v___x_828_, v_size_822_);
lean_dec(v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v_r_826_);
v___x_830_ = lean_nat_add(v___x_820_, v_size_822_);
v___x_831_ = lean_nat_add(v___x_830_, v_size_821_);
lean_dec(v___x_830_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_impl_819_);
lean_ctor_set(v___x_331_, 0, v___x_831_);
v___x_833_ = v___x_331_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v_impl_819_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_900_; 
lean_inc(v_l_825_);
lean_inc(v_v_824_);
lean_inc(v_k_823_);
lean_inc(v_size_822_);
v_isSharedCheck_900_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; lean_object* v_unused_902_; lean_object* v_unused_903_; lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_901_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_l_328_, 2);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_l_328_, 1);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_905_);
v___x_836_ = v_l_328_;
v_isShared_837_ = v_isSharedCheck_900_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_l_328_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_900_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_size_838_; lean_object* v_size_839_; lean_object* v_k_840_; lean_object* v_v_841_; lean_object* v_l_842_; lean_object* v_r_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_size_838_ = lean_ctor_get(v_l_825_, 0);
v_size_839_ = lean_ctor_get(v_r_826_, 0);
v_k_840_ = lean_ctor_get(v_r_826_, 1);
v_v_841_ = lean_ctor_get(v_r_826_, 2);
v_l_842_ = lean_ctor_get(v_r_826_, 3);
v_r_843_ = lean_ctor_get(v_r_826_, 4);
v___x_844_ = lean_unsigned_to_nat(2u);
v___x_845_ = lean_nat_mul(v___x_844_, v_size_838_);
v___x_846_ = lean_nat_dec_lt(v_size_839_, v___x_845_);
lean_dec(v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_875_; 
lean_inc(v_r_843_);
lean_inc(v_l_842_);
lean_inc(v_v_841_);
lean_inc(v_k_840_);
v_isSharedCheck_875_ = !lean_is_exclusive(v_r_826_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_876_ = lean_ctor_get(v_r_826_, 4);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_r_826_, 3);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_r_826_, 2);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_r_826_, 1);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_r_826_, 0);
lean_dec(v_unused_880_);
v___x_848_ = v_r_826_;
v_isShared_849_ = v_isSharedCheck_875_;
goto v_resetjp_847_;
}
else
{
lean_dec(v_r_826_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_875_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___x_863_; lean_object* v___y_865_; 
v___x_850_ = lean_nat_add(v___x_820_, v_size_822_);
lean_dec(v_size_822_);
v___x_851_ = lean_nat_add(v___x_850_, v_size_821_);
lean_dec(v___x_850_);
v___x_863_ = lean_nat_add(v___x_820_, v_size_838_);
if (lean_obj_tag(v_l_842_) == 0)
{
lean_object* v_size_873_; 
v_size_873_ = lean_ctor_get(v_l_842_, 0);
lean_inc(v_size_873_);
v___y_865_ = v_size_873_;
goto v___jp_864_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v___y_865_ = v___x_874_;
goto v___jp_864_;
}
v___jp_852_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_nat_add(v___y_853_, v___y_855_);
lean_dec(v___y_855_);
lean_dec(v___y_853_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 4, v_impl_819_);
lean_ctor_set(v___x_848_, 3, v_r_843_);
lean_ctor_set(v___x_848_, 2, v_v_327_);
lean_ctor_set(v___x_848_, 1, v_k_326_);
lean_ctor_set(v___x_848_, 0, v___x_856_);
v___x_858_ = v___x_848_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_r_843_);
lean_ctor_set(v_reuseFailAlloc_862_, 4, v_impl_819_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 4, v___x_858_);
lean_ctor_set(v___x_836_, 3, v___y_854_);
lean_ctor_set(v___x_836_, 2, v_v_841_);
lean_ctor_set(v___x_836_, 1, v_k_840_);
lean_ctor_set(v___x_836_, 0, v___x_851_);
v___x_860_ = v___x_836_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_840_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_841_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v___y_854_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
v___jp_864_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = lean_nat_add(v___x_863_, v___y_865_);
lean_dec(v___y_865_);
lean_dec(v___x_863_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_l_842_);
lean_ctor_set(v___x_331_, 3, v_l_825_);
lean_ctor_set(v___x_331_, 2, v_v_824_);
lean_ctor_set(v___x_331_, 1, v_k_823_);
lean_ctor_set(v___x_331_, 0, v___x_866_);
v___x_868_ = v___x_331_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_l_825_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_l_842_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = lean_nat_add(v___x_820_, v_size_821_);
if (lean_obj_tag(v_r_843_) == 0)
{
lean_object* v_size_870_; 
v_size_870_ = lean_ctor_get(v_r_843_, 0);
lean_inc(v_size_870_);
v___y_853_ = v___x_869_;
v___y_854_ = v___x_868_;
v___y_855_ = v_size_870_;
goto v___jp_852_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___y_853_ = v___x_869_;
v___y_854_ = v___x_868_;
v___y_855_ = v___x_871_;
goto v___jp_852_;
}
}
}
}
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
lean_del_object(v___x_331_);
v___x_881_ = lean_nat_add(v___x_820_, v_size_822_);
lean_dec(v_size_822_);
v___x_882_ = lean_nat_add(v___x_881_, v_size_821_);
lean_dec(v___x_881_);
v___x_883_ = lean_nat_add(v___x_820_, v_size_821_);
v___x_884_ = lean_nat_add(v___x_883_, v_size_839_);
lean_dec(v___x_883_);
lean_inc_ref(v_impl_819_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 4, v_impl_819_);
lean_ctor_set(v___x_836_, 3, v_r_826_);
lean_ctor_set(v___x_836_, 2, v_v_327_);
lean_ctor_set(v___x_836_, 1, v_k_326_);
lean_ctor_set(v___x_836_, 0, v___x_884_);
v___x_886_ = v___x_836_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_r_826_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_impl_819_);
v___x_886_ = v_reuseFailAlloc_899_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_isSharedCheck_893_ = !lean_is_exclusive(v_impl_819_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; lean_object* v_unused_895_; lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; 
v_unused_894_ = lean_ctor_get(v_impl_819_, 4);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_impl_819_, 3);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_impl_819_, 2);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_impl_819_, 1);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_impl_819_, 0);
lean_dec(v_unused_898_);
v___x_888_ = v_impl_819_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_dec(v_impl_819_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v___x_886_);
lean_ctor_set(v___x_888_, 3, v_l_825_);
lean_ctor_set(v___x_888_, 2, v_v_824_);
lean_ctor_set(v___x_888_, 1, v_k_823_);
lean_ctor_set(v___x_888_, 0, v___x_882_);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_l_825_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v___x_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_size_906_ = lean_ctor_get(v_impl_819_, 0);
v___x_907_ = lean_nat_add(v___x_820_, v_size_906_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_impl_819_);
lean_ctor_set(v___x_331_, 0, v___x_907_);
v___x_909_ = v___x_331_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_impl_819_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
if (lean_obj_tag(v_l_328_) == 0)
{
lean_object* v_l_911_; 
v_l_911_ = lean_ctor_get(v_l_328_, 3);
if (lean_obj_tag(v_l_911_) == 0)
{
lean_object* v_r_912_; 
lean_inc_ref(v_l_911_);
v_r_912_ = lean_ctor_get(v_l_328_, 4);
lean_inc(v_r_912_);
if (lean_obj_tag(v_r_912_) == 0)
{
lean_object* v_size_913_; lean_object* v_k_914_; lean_object* v_v_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_928_; 
v_size_913_ = lean_ctor_get(v_l_328_, 0);
v_k_914_ = lean_ctor_get(v_l_328_, 1);
v_v_915_ = lean_ctor_get(v_l_328_, 2);
v_isSharedCheck_928_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; lean_object* v_unused_930_; 
v_unused_929_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_930_);
v___x_917_ = v_l_328_;
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_v_915_);
lean_inc(v_k_914_);
lean_inc(v_size_913_);
lean_dec(v_l_328_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_928_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_size_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v_size_919_ = lean_ctor_get(v_r_912_, 0);
v___x_920_ = lean_nat_add(v___x_820_, v_size_913_);
lean_dec(v_size_913_);
v___x_921_ = lean_nat_add(v___x_820_, v_size_919_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 4, v_impl_819_);
lean_ctor_set(v___x_917_, 3, v_r_912_);
lean_ctor_set(v___x_917_, 2, v_v_327_);
lean_ctor_set(v___x_917_, 1, v_k_326_);
lean_ctor_set(v___x_917_, 0, v___x_921_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_r_912_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_impl_819_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_923_);
lean_ctor_set(v___x_331_, 3, v_l_911_);
lean_ctor_set(v___x_331_, 2, v_v_915_);
lean_ctor_set(v___x_331_, 1, v_k_914_);
lean_ctor_set(v___x_331_, 0, v___x_920_);
v___x_925_ = v___x_331_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_915_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_l_911_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_k_931_; lean_object* v_v_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_943_; 
v_k_931_ = lean_ctor_get(v_l_328_, 1);
v_v_932_ = lean_ctor_get(v_l_328_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; lean_object* v_unused_945_; lean_object* v_unused_946_; 
v_unused_944_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_945_);
v_unused_946_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_946_);
v___x_934_ = v_l_328_;
v_isShared_935_ = v_isSharedCheck_943_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_v_932_);
lean_inc(v_k_931_);
lean_dec(v_l_328_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_943_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_unsigned_to_nat(3u);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 3, v_r_912_);
lean_ctor_set(v___x_934_, 2, v_v_327_);
lean_ctor_set(v___x_934_, 1, v_k_326_);
lean_ctor_set(v___x_934_, 0, v___x_820_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_r_912_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_r_912_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_938_);
lean_ctor_set(v___x_331_, 3, v_l_911_);
lean_ctor_set(v___x_331_, 2, v_v_932_);
lean_ctor_set(v___x_331_, 1, v_k_931_);
lean_ctor_set(v___x_331_, 0, v___x_936_);
v___x_940_ = v___x_331_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_l_911_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
else
{
lean_object* v_r_947_; 
v_r_947_ = lean_ctor_get(v_l_328_, 4);
lean_inc(v_r_947_);
if (lean_obj_tag(v_r_947_) == 0)
{
lean_object* v_k_948_; lean_object* v_v_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_972_; 
lean_inc(v_l_911_);
v_k_948_ = lean_ctor_get(v_l_328_, 1);
v_v_949_ = lean_ctor_get(v_l_328_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_973_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_975_);
v___x_951_ = v_l_328_;
v_isShared_952_ = v_isSharedCheck_972_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_v_949_);
lean_inc(v_k_948_);
lean_dec(v_l_328_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_972_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_k_953_; lean_object* v_v_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_968_; 
v_k_953_ = lean_ctor_get(v_r_947_, 1);
v_v_954_ = lean_ctor_get(v_r_947_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v_r_947_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; lean_object* v_unused_971_; 
v_unused_969_ = lean_ctor_get(v_r_947_, 4);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_r_947_, 3);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_r_947_, 0);
lean_dec(v_unused_971_);
v___x_956_ = v_r_947_;
v_isShared_957_ = v_isSharedCheck_968_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_v_954_);
lean_inc(v_k_953_);
lean_dec(v_r_947_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_968_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = lean_unsigned_to_nat(3u);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 4, v_l_911_);
lean_ctor_set(v___x_956_, 3, v_l_911_);
lean_ctor_set(v___x_956_, 2, v_v_949_);
lean_ctor_set(v___x_956_, 1, v_k_948_);
lean_ctor_set(v___x_956_, 0, v___x_820_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_948_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_949_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_911_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_l_911_);
v___x_960_ = v_reuseFailAlloc_967_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 4, v_l_911_);
lean_ctor_set(v___x_951_, 2, v_v_327_);
lean_ctor_set(v___x_951_, 1, v_k_326_);
lean_ctor_set(v___x_951_, 0, v___x_820_);
v___x_962_ = v___x_951_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_l_911_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_l_911_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v___x_962_);
lean_ctor_set(v___x_331_, 3, v___x_960_);
lean_ctor_set(v___x_331_, 2, v_v_954_);
lean_ctor_set(v___x_331_, 1, v_k_953_);
lean_ctor_set(v___x_331_, 0, v___x_958_);
v___x_964_ = v___x_331_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_k_953_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_v_954_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_unsigned_to_nat(2u);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_r_947_);
lean_ctor_set(v___x_331_, 0, v___x_976_);
v___x_978_ = v___x_331_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_r_947_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v___x_981_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 4, v_l_328_);
lean_ctor_set(v___x_331_, 0, v___x_820_);
v___x_981_ = v___x_331_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_326_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_327_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_l_328_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
}
else
{
return v_t_325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object* v_k_985_, lean_object* v_t_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_985_, v_t_986_);
lean_dec(v_k_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object* v_o_988_, lean_object* v_k_989_){
_start:
{
lean_object* v_map_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1001_; 
v_map_990_ = lean_ctor_get(v_o_988_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_o_988_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_992_ = v_o_988_;
v_isShared_993_ = v_isSharedCheck_1001_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_map_990_);
lean_dec(v_o_988_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1001_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_999_; 
lean_inc(v_map_990_);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_989_, v_map_990_);
v___x_995_ = lean_box(0);
v___x_996_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v___x_995_, v_map_990_);
lean_dec(v_map_990_);
v___x_997_ = l_List_any___at___00Lean_Options_erase_spec__2(v___x_996_);
lean_dec(v___x_996_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_999_ = v___x_992_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_997_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object* v_o_1002_, lean_object* v_k_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Options_erase(v_o_1002_, v_k_1003_);
lean_dec(v_k_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object* v_00_u03b2_1005_, lean_object* v_k_1006_, lean_object* v_t_1007_, lean_object* v_h_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_1006_, v_t_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object* v_00_u03b2_1010_, lean_object* v_k_1011_, lean_object* v_t_1012_, lean_object* v_h_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(v_00_u03b2_1010_, v_k_1011_, v_t_1012_, v_h_1013_);
lean_dec(v_k_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object* v_b_u2082_1015_, lean_object* v_f_1016_, lean_object* v_a_1017_, lean_object* v_x_1018_){
_start:
{
if (lean_obj_tag(v_x_1018_) == 0)
{
lean_object* v___x_1019_; 
lean_dec(v_a_1017_);
lean_dec_ref(v_f_1016_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_b_u2082_1015_);
return v___x_1019_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_val_1020_ = lean_ctor_get(v_x_1018_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_x_1018_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v_x_1018_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_dec(v_x_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_apply_3(v_f_1016_, v_a_1017_, v_val_1020_, v_b_u2082_1015_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object* v_b_u2082_1029_, lean_object* v_f_1030_, lean_object* v_a_1031_, lean_object* v_k_1032_, lean_object* v_t_1033_){
_start:
{
if (lean_obj_tag(v_t_1033_) == 0)
{
lean_object* v_size_1034_; lean_object* v_k_1035_; lean_object* v_v_1036_; lean_object* v_l_1037_; lean_object* v_r_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1053_; 
v_size_1034_ = lean_ctor_get(v_t_1033_, 0);
v_k_1035_ = lean_ctor_get(v_t_1033_, 1);
v_v_1036_ = lean_ctor_get(v_t_1033_, 2);
v_l_1037_ = lean_ctor_get(v_t_1033_, 3);
v_r_1038_ = lean_ctor_get(v_t_1033_, 4);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_t_1033_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1040_ = v_t_1033_;
v_isShared_1041_ = v_isSharedCheck_1053_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_r_1038_);
lean_inc(v_l_1037_);
lean_inc(v_v_1036_);
lean_inc(v_k_1035_);
lean_inc(v_size_1034_);
lean_dec(v_t_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1053_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
uint8_t v___x_1042_; 
v___x_1042_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1032_, v_k_1035_);
switch(v___x_1042_)
{
case 0:
{
lean_object* v_impl_1043_; lean_object* v___x_1044_; 
lean_del_object(v___x_1040_);
lean_dec(v_size_1034_);
v_impl_1043_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1029_, v_f_1030_, v_a_1031_, v_k_1032_, v_l_1037_);
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1035_, v_v_1036_, v_impl_1043_, v_r_1038_);
return v___x_1044_;
}
case 1:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_val_1047_; lean_object* v___x_1049_; 
lean_dec(v_k_1035_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_v_1036_);
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1029_, v_f_1030_, v_a_1031_, v___x_1045_);
v_val_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_val_1047_);
lean_dec(v___x_1046_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 2, v_val_1047_);
lean_ctor_set(v___x_1040_, 1, v_k_1032_);
v___x_1049_ = v___x_1040_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_size_1034_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_k_1032_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_val_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_l_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_r_1038_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
default: 
{
lean_object* v_impl_1051_; lean_object* v___x_1052_; 
lean_del_object(v___x_1040_);
lean_dec(v_size_1034_);
v_impl_1051_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1029_, v_f_1030_, v_a_1031_, v_k_1032_, v_r_1038_);
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1035_, v_v_1036_, v_l_1037_, v_impl_1051_);
return v___x_1052_;
}
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_val_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1029_, v_f_1030_, v_a_1031_, v___x_1054_);
v_val_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_val_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_k_1032_);
lean_ctor_set(v___x_1058_, 2, v_val_1056_);
lean_ctor_set(v___x_1058_, 3, v_t_1033_);
lean_ctor_set(v___x_1058_, 4, v_t_1033_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object* v_f_1059_, lean_object* v_init_1060_, lean_object* v_x_1061_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v_l_1064_; lean_object* v_r_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_k_1062_ = lean_ctor_get(v_x_1061_, 1);
lean_inc_n(v_k_1062_, 2);
v_v_1063_ = lean_ctor_get(v_x_1061_, 2);
lean_inc(v_v_1063_);
v_l_1064_ = lean_ctor_get(v_x_1061_, 3);
lean_inc(v_l_1064_);
v_r_1065_ = lean_ctor_get(v_x_1061_, 4);
lean_inc(v_r_1065_);
lean_dec_ref_known(v_x_1061_, 5);
lean_inc_ref_n(v_f_1059_, 2);
v___x_1066_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1059_, v_init_1060_, v_l_1064_);
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_1063_, v_f_1059_, v_k_1062_, v_k_1062_, v___x_1066_);
v_init_1060_ = v___x_1067_;
v_x_1061_ = v_r_1065_;
goto _start;
}
else
{
lean_dec_ref(v_f_1059_);
return v_init_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object* v_f_1069_, lean_object* v_o1_1070_, lean_object* v_o2_1071_){
_start:
{
lean_object* v_map_1072_; uint8_t v_hasTrace_1073_; lean_object* v_map_1074_; uint8_t v_hasTrace_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1086_; 
v_map_1072_ = lean_ctor_get(v_o1_1070_, 0);
lean_inc(v_map_1072_);
v_hasTrace_1073_ = lean_ctor_get_uint8(v_o1_1070_, sizeof(void*)*1);
lean_dec_ref(v_o1_1070_);
v_map_1074_ = lean_ctor_get(v_o2_1071_, 0);
v_hasTrace_1075_ = lean_ctor_get_uint8(v_o2_1071_, sizeof(void*)*1);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_o2_1071_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1077_ = v_o2_1071_;
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_map_1074_);
lean_dec(v_o2_1071_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1086_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1069_, v_map_1072_, v_map_1074_);
if (v_hasTrace_1073_ == 0)
{
lean_object* v___x_1081_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*1, v_hasTrace_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1084_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1084_ = v___x_1077_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v_hasTrace_1073_);
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object* v_b_u2082_1087_, lean_object* v_f_1088_, lean_object* v_a_1089_, lean_object* v_k_1090_, lean_object* v_t_1091_, lean_object* v_hl_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1087_, v_f_1088_, v_a_1089_, v_k_1090_, v_t_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object* v_f_1094_, lean_object* v_init_1095_, lean_object* v_t_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1094_, v_init_1095_, v_t_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
v___x_1131_ = l_Lean_mkAtom(v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
v___x_1133_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1134_ = lean_array_push(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
v___x_1144_ = l_Lean_mkAtom(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
v___x_1146_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1147_ = lean_array_push(v___x_1146_, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
v___x_1149_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
v___x_1150_ = lean_box(2);
v___x_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
lean_ctor_set(v___x_1151_, 2, v___x_1148_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
v___x_1153_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
v___x_1154_ = lean_array_push(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1155_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
v___x_1156_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
v___x_1157_ = lean_box(2);
v___x_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___x_1156_);
lean_ctor_set(v___x_1158_, 2, v___x_1155_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
v___x_1160_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1161_ = lean_array_push(v___x_1160_, v___x_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
v___x_1163_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1164_ = lean_box(2);
v___x_1165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1163_);
lean_ctor_set(v___x_1165_, 2, v___x_1162_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
v___x_1167_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1168_ = lean_array_push(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
v___x_1170_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
v___x_1171_ = lean_box(2);
v___x_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1170_);
lean_ctor_set(v___x_1172_, 2, v___x_1169_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
v___x_1174_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1175_ = lean_array_push(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
v___x_1177_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
v___x_1178_ = lean_box(2);
v___x_1179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
lean_ctor_set(v___x_1179_, 2, v___x_1176_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__3(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1187_ = lean_box(0);
v___x_1188_ = ((lean_object*)(l_Lean_instInhabitedOptionDeprecation_default___closed__0));
v___x_1189_ = l_Lean_instInhabitedDataValue_default;
v___x_1190_ = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__2));
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
lean_ctor_set(v___x_1192_, 2, v___x_1189_);
lean_ctor_set(v___x_1192_, 3, v___x_1188_);
lean_ctor_set(v___x_1192_, 4, v___x_1187_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__3, &l_Lean_instInhabitedOptionDecl_default___closed__3_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__3);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_instInhabitedOptionDecl_default;
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* v_self_1200_){
_start:
{
lean_object* v_descr_1202_; lean_object* v_name_1205_; lean_object* v_descr_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_name_1205_ = lean_ctor_get(v_self_1200_, 0);
lean_inc(v_name_1205_);
v_descr_1206_ = lean_ctor_get(v_self_1200_, 3);
lean_inc_ref(v_descr_1206_);
lean_dec_ref(v_self_1200_);
v___x_1207_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
v___x_1208_ = l_Lean_Name_isPrefixOf(v___x_1207_, v_name_1205_);
lean_dec(v_name_1205_);
if (v___x_1208_ == 0)
{
return v_descr_1206_;
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = lean_string_utf8_byte_size(v_descr_1206_);
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = lean_nat_dec_eq(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v_descr_1213_; 
v___x_1212_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
v_descr_1213_ = lean_string_append(v_descr_1206_, v___x_1212_);
v_descr_1202_ = v_descr_1213_;
goto v___jp_1201_;
}
else
{
v_descr_1202_ = v_descr_1206_;
goto v___jp_1201_;
}
}
v___jp_1201_:
{
lean_object* v___x_1203_; lean_object* v_descr_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
v_descr_1204_ = lean_string_append(v_descr_1202_, v___x_1203_);
return v_descr_1204_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_box(1);
return v___x_1214_;
}
}
lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(1);
v___x_1217_ = lean_st_mk_ref(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT void l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1219_;
v_res_1219_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return v_res_1221_;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_registerOption___closed__0));
v___x_1224_ = lean_mk_io_user_error(v___x_1223_);
return v___x_1224_;
}
}
lean_object* lean_register_option(lean_object* v_name_1227_, lean_object* v_decl_1228_){
_start:
{
uint8_t v___x_1230_; 
v___x_1230_ = l_Lean_initializing();
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref(v_decl_1228_);
lean_dec(v_name_1227_);
v___x_1231_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
v___x_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1233_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1234_ = lean_st_ref_get(v___x_1233_);
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1227_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1236_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1227_, v_decl_1228_, v___x_1234_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_st_ref_swap(v___x_1233_, v___x_1236_);
lean_dec(v___x_1238_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v___x_1234_);
lean_dec_ref(v_decl_1228_);
v___x_1240_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1227_, v___x_1235_);
v___x_1242_ = lean_string_append(v___x_1240_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
v___x_1245_ = lean_mk_io_user_error(v___x_1244_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
}
}
LEAN_EXPORT void lean_register_option_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1227_ = stack[0].m_obj;
lean_object* v_decl_1228_ = stack[1].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = lean_register_option(v_name_1227_, v_decl_1228_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1248_, lean_object* v_decl_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = lean_register_option(v_name_1248_, v_decl_1249_);
return v_res_1251_;
}
}
lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1254_ = lean_st_ref_get(v___x_1253_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT void l_Lean_getOptionDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1256_;
v_res_1256_ = l_Lean_getOptionDecls();
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_getOptionDecls();
return v_res_1258_;
}
}
lean_object* l_Lean_getOptionDecl(lean_object* v_name_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1283_; 
v___x_1263_ = l_Lean_getOptionDecls();
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1264_, v_name_1261_);
lean_dec(v_a_1264_);
if (lean_obj_tag(v___x_1268_) == 1)
{
lean_object* v_val_1269_; lean_object* v___x_1271_; 
lean_dec(v_name_1261_);
v_val_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1268_, 1);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_val_1269_);
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_val_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec(v___x_1268_);
v___x_1273_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1274_ = 1;
v___x_1275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1261_, v___x_1274_);
v___x_1276_ = lean_string_append(v___x_1273_, v___x_1275_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1278_ = lean_string_append(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_mk_io_user_error(v___x_1278_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1279_);
v___x_1281_ = v___x_1266_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT void l_Lean_getOptionDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1261_ = stack[0].m_obj;
lean_object* v_res_1284_;
v_res_1284_ = l_Lean_getOptionDecl(v_name_1261_);
stack->m_obj
 = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_getOptionDecl(v_name_1285_);
return v_res_1287_;
}
}
lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_getOptionDecl(v_name_1288_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_defValue_1295_; lean_object* v___x_1297_; 
v_defValue_1295_ = lean_ctor_get(v_a_1291_, 2);
lean_inc_ref(v_defValue_1295_);
lean_dec(v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_defValue_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_defValue_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1290_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1290_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getOptionDefaultValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1288_ = stack[0].m_obj;
lean_object* v_res_1308_;
v_res_1308_ = l_Lean_getOptionDefaultValue(v_name_1288_);
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_getOptionDefaultValue(v_name_1309_);
return v_res_1311_;
}
}
lean_object* l_Lean_getOptionDescr(lean_object* v_name_1312_){
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
lean_object* v_descr_1319_; lean_object* v___x_1321_; 
v_descr_1319_ = lean_ctor_get(v_a_1315_, 3);
lean_inc_ref(v_descr_1319_);
lean_dec(v_a_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_descr_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_descr_1319_);
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
LEAN_EXPORT void l_Lean_getOptionDescr_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1312_ = stack[0].m_obj;
lean_object* v_res_1332_;
v_res_1332_ = l_Lean_getOptionDescr(v_name_1312_);
stack->m_obj
 = v_res_1332_;
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_getOptionDescr(v_name_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1336_, lean_object* v_inst_1337_){
_start:
{
lean_object* v_getOptions_1338_; lean_object* v_getOptionsUnrestricted_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
v_getOptions_1338_ = lean_ctor_get(v_inst_1337_, 0);
v_getOptionsUnrestricted_1339_ = lean_ctor_get(v_inst_1337_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_inst_1337_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1341_ = v_inst_1337_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_getOptionsUnrestricted_1339_);
lean_inc(v_getOptions_1338_);
lean_dec(v_inst_1337_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
lean_inc(v_inst_1336_);
v___x_1343_ = lean_apply_2(v_inst_1336_, lean_box(0), v_getOptions_1338_);
v___x_1344_ = lean_apply_2(v_inst_1336_, lean_box(0), v_getOptionsUnrestricted_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1344_);
lean_ctor_set(v___x_1341_, 0, v___x_1343_);
v___x_1346_ = v___x_1341_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1349_, lean_object* v_n_1350_, lean_object* v_inst_1351_, lean_object* v_inst_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v_inst_1351_, v_inst_1352_);
return v___x_1353_;
}
}
lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1354_, lean_object* v_toPure_1355_, uint8_t v_defValue_1356_, lean_object* v_opts_1357_){
_start:
{
lean_object* v_map_1358_; lean_object* v___x_1359_; 
v_map_1358_ = lean_ctor_get(v_opts_1357_, 0);
v___x_1359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1358_, v_k_1354_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_box(v_defValue_1356_);
v___x_1361_ = lean_apply_2(v_toPure_1355_, lean_box(0), v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1359_, 1);
if (lean_obj_tag(v_val_1362_) == 1)
{
uint8_t v_v_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_v_1363_ = lean_ctor_get_uint8(v_val_1362_, 0);
lean_dec_ref_known(v_val_1362_, 0);
v___x_1364_ = lean_box(v_v_1363_);
v___x_1365_ = lean_apply_2(v_toPure_1355_, lean_box(0), v___x_1364_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_val_1362_);
v___x_1366_ = lean_box(v_defValue_1356_);
v___x_1367_ = lean_apply_2(v_toPure_1355_, lean_box(0), v___x_1366_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT void l_Lean_getBoolOption___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1354_ = stack[0].m_obj;
lean_object* v_toPure_1355_ = stack[1].m_obj;
uint8_t v_defValue_1356_ = stack[2].m_num;
lean_object* v_opts_1357_ = stack[3].m_obj;
lean_object* v_res_1368_;
v_res_1368_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1354_, v_toPure_1355_, v_defValue_1356_, v_opts_1357_);
stack->m_obj
 = v_res_1368_;
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1369_, lean_object* v_toPure_1370_, lean_object* v_defValue_1371_, lean_object* v_opts_1372_){
_start:
{
uint8_t v_defValue_boxed_1373_; lean_object* v_res_1374_; 
v_defValue_boxed_1373_ = lean_unbox(v_defValue_1371_);
v_res_1374_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1369_, v_toPure_1370_, v_defValue_boxed_1373_, v_opts_1372_);
lean_dec_ref(v_opts_1372_);
lean_dec(v_k_1369_);
return v_res_1374_;
}
}
lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_k_1377_, uint8_t v_defValue_1378_){
_start:
{
lean_object* v_toApplicative_1379_; lean_object* v_toBind_1380_; lean_object* v_getOptions_1381_; lean_object* v_toPure_1382_; lean_object* v___x_1383_; lean_object* v___f_1384_; lean_object* v___x_1385_; 
v_toApplicative_1379_ = lean_ctor_get(v_inst_1375_, 0);
lean_inc_ref(v_toApplicative_1379_);
v_toBind_1380_ = lean_ctor_get(v_inst_1375_, 1);
lean_inc(v_toBind_1380_);
lean_dec_ref(v_inst_1375_);
v_getOptions_1381_ = lean_ctor_get(v_inst_1376_, 0);
lean_inc(v_getOptions_1381_);
lean_dec_ref(v_inst_1376_);
v_toPure_1382_ = lean_ctor_get(v_toApplicative_1379_, 1);
lean_inc(v_toPure_1382_);
lean_dec_ref(v_toApplicative_1379_);
v___x_1383_ = lean_box(v_defValue_1378_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1384_, 0, v_k_1377_);
lean_closure_set(v___f_1384_, 1, v_toPure_1382_);
lean_closure_set(v___f_1384_, 2, v___x_1383_);
v___x_1385_ = lean_apply_4(v_toBind_1380_, lean_box(0), lean_box(0), v_getOptions_1381_, v___f_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT void l_Lean_getBoolOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1375_ = stack[0].m_obj;
lean_object* v_inst_1376_ = stack[1].m_obj;
lean_object* v_k_1377_ = stack[2].m_obj;
uint8_t v_defValue_1378_ = stack[3].m_num;
lean_object* v_res_1386_;
v_res_1386_ = l_Lean_getBoolOption___redArg(v_inst_1375_, v_inst_1376_, v_k_1377_, v_defValue_1378_);
stack->m_obj
 = v_res_1386_;
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_k_1389_, lean_object* v_defValue_1390_){
_start:
{
uint8_t v_defValue_boxed_1391_; lean_object* v_res_1392_; 
v_defValue_boxed_1391_ = lean_unbox(v_defValue_1390_);
v_res_1392_ = l_Lean_getBoolOption___redArg(v_inst_1387_, v_inst_1388_, v_k_1389_, v_defValue_boxed_1391_);
return v_res_1392_;
}
}
lean_object* l_Lean_getBoolOption(lean_object* v_m_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_k_1396_, uint8_t v_defValue_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_getBoolOption___redArg(v_inst_1394_, v_inst_1395_, v_k_1396_, v_defValue_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT void l_Lean_getBoolOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1394_ = stack[1].m_obj;
lean_object* v_inst_1395_ = stack[2].m_obj;
lean_object* v_k_1396_ = stack[3].m_obj;
uint8_t v_defValue_1397_ = stack[4].m_num;
lean_object* v_res_1399_;
v_res_1399_ = l_Lean_getBoolOption(lean_box(0), v_inst_1394_, v_inst_1395_, v_k_1396_, v_defValue_1397_);
stack->m_obj
 = v_res_1399_;
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_k_1403_, lean_object* v_defValue_1404_){
_start:
{
uint8_t v_defValue_boxed_1405_; lean_object* v_res_1406_; 
v_defValue_boxed_1405_ = lean_unbox(v_defValue_1404_);
v_res_1406_ = l_Lean_getBoolOption(v_m_1400_, v_inst_1401_, v_inst_1402_, v_k_1403_, v_defValue_boxed_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1407_, lean_object* v_toPure_1408_, lean_object* v_defValue_1409_, lean_object* v_opts_1410_){
_start:
{
lean_object* v_map_1411_; lean_object* v___x_1412_; 
v_map_1411_ = lean_ctor_get(v_opts_1410_, 0);
v___x_1412_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1411_, v_k_1407_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_apply_2(v_toPure_1408_, lean_box(0), v_defValue_1409_);
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v___x_1412_, 1);
if (lean_obj_tag(v_val_1414_) == 3)
{
lean_object* v_v_1415_; lean_object* v___x_1416_; 
lean_dec(v_defValue_1409_);
v_v_1415_ = lean_ctor_get(v_val_1414_, 0);
lean_inc(v_v_1415_);
lean_dec_ref_known(v_val_1414_, 1);
v___x_1416_ = lean_apply_2(v_toPure_1408_, lean_box(0), v_v_1415_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_val_1414_);
v___x_1417_ = lean_apply_2(v_toPure_1408_, lean_box(0), v_defValue_1409_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1418_, lean_object* v_toPure_1419_, lean_object* v_defValue_1420_, lean_object* v_opts_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_getNatOption___redArg___lam__0(v_k_1418_, v_toPure_1419_, v_defValue_1420_, v_opts_1421_);
lean_dec_ref(v_opts_1421_);
lean_dec(v_k_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_k_1425_, lean_object* v_defValue_1426_){
_start:
{
lean_object* v_toApplicative_1427_; lean_object* v_toBind_1428_; lean_object* v_getOptions_1429_; lean_object* v_toPure_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; 
v_toApplicative_1427_ = lean_ctor_get(v_inst_1423_, 0);
lean_inc_ref(v_toApplicative_1427_);
v_toBind_1428_ = lean_ctor_get(v_inst_1423_, 1);
lean_inc(v_toBind_1428_);
lean_dec_ref(v_inst_1423_);
v_getOptions_1429_ = lean_ctor_get(v_inst_1424_, 0);
lean_inc(v_getOptions_1429_);
lean_dec_ref(v_inst_1424_);
v_toPure_1430_ = lean_ctor_get(v_toApplicative_1427_, 1);
lean_inc(v_toPure_1430_);
lean_dec_ref(v_toApplicative_1427_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1431_, 0, v_k_1425_);
lean_closure_set(v___f_1431_, 1, v_toPure_1430_);
lean_closure_set(v___f_1431_, 2, v_defValue_1426_);
v___x_1432_ = lean_apply_4(v_toBind_1428_, lean_box(0), lean_box(0), v_getOptions_1429_, v___f_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_k_1436_, lean_object* v_defValue_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_getNatOption___redArg(v_inst_1434_, v_inst_1435_, v_k_1436_, v_defValue_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1439_, lean_object* v_f_1440_, lean_object* v_00_u03b2_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_apply_3(v_inst_1439_, lean_box(0), v_f_1440_, v___y_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_00_u03b1_1446_, lean_object* v_f_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___f_1449_; lean_object* v___x_1450_; 
v___f_1449_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1449_, 0, v_inst_1444_);
lean_closure_set(v___f_1449_, 1, v_f_1447_);
v___x_1450_ = lean_apply_3(v_inst_1445_, lean_box(0), v___f_1449_, v_x_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1451_, lean_object* v_inst_1452_){
_start:
{
lean_object* v___f_1453_; 
v___f_1453_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1453_, 0, v_inst_1452_);
lean_closure_set(v___f_1453_, 1, v_inst_1451_);
return v___f_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1454_, lean_object* v_n_1455_, lean_object* v_inst_1456_, lean_object* v_inst_1457_){
_start:
{
lean_object* v___f_1458_; 
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1458_, 0, v_inst_1457_);
lean_closure_set(v___f_1458_, 1, v_inst_1456_);
return v___f_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1462_, lean_object* v_o_1463_){
_start:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1464_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1465_ = 1;
v___x_1466_ = lean_box(v___x_1465_);
v___x_1467_ = l_Lean_Options_set___redArg(v___x_1462_, v_o_1463_, v___x_1464_, v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___f_1469_; 
v___x_1468_ = l_Lean_KVMap_instValueBool;
v___f_1469_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1469_, 0, v___x_1468_);
return v___f_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___f_1472_; lean_object* v___x_1473_; 
v___f_1472_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1473_ = lean_apply_3(v_inst_1470_, lean_box(0), v___f_1472_, v_x_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1474_, lean_object* v_00_u03b1_1475_, lean_object* v_inst_1476_, lean_object* v_x_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_withInPattern___redArg(v_inst_1476_, v_x_1477_);
return v___x_1478_;
}
}
uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1479_){
_start:
{
lean_object* v_map_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v_map_1480_ = lean_ctor_get(v_o_1479_, 0);
v___x_1481_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1482_ = 0;
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1480_, v___x_1481_);
if (lean_obj_tag(v___x_1483_) == 0)
{
return v___x_1482_;
}
else
{
lean_object* v_val_1484_; 
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___x_1483_, 1);
if (lean_obj_tag(v_val_1484_) == 1)
{
uint8_t v_v_1485_; 
v_v_1485_ = lean_ctor_get_uint8(v_val_1484_, 0);
lean_dec_ref_known(v_val_1484_, 0);
return v_v_1485_;
}
else
{
lean_dec(v_val_1484_);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_getInPattern_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1479_ = stack[0].m_obj;
uint8_t v_res_1486_;
v_res_1486_ = l_Lean_Options_getInPattern(v_o_1479_);
stack->m_num = v_res_1486_;
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1487_){
_start:
{
uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_res_1488_ = l_Lean_Options_getInPattern(v_o_1487_);
lean_dec_ref(v_o_1487_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v_inst_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_00_u03b1_1493_, lean_object* v_inst_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1498_, lean_object* v_inst_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1501_, lean_object* v_opts_1502_, lean_object* v_opt_1503_){
_start:
{
lean_object* v_name_1504_; lean_object* v_map_1505_; lean_object* v_ofDataValue_x3f_1506_; lean_object* v___x_1507_; 
v_name_1504_ = lean_ctor_get(v_opt_1503_, 0);
v_map_1505_ = lean_ctor_get(v_opts_1502_, 0);
v_ofDataValue_x3f_1506_ = lean_ctor_get(v_inst_1501_, 1);
lean_inc_ref(v_ofDataValue_x3f_1506_);
lean_dec_ref(v_inst_1501_);
v___x_1507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1505_, v_name_1504_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref(v_ofDataValue_x3f_1506_);
v___x_1508_ = lean_box(0);
return v___x_1508_;
}
else
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_val_1509_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1510_ = lean_apply_1(v_ofDataValue_x3f_1506_, v_val_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1511_, lean_object* v_opts_1512_, lean_object* v_opt_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Option_get_x3f___redArg(v_inst_1511_, v_opts_1512_, v_opt_1513_);
lean_dec_ref(v_opt_1513_);
lean_dec_ref(v_opts_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1515_, lean_object* v_inst_1516_, lean_object* v_opts_1517_, lean_object* v_opt_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Option_get_x3f___redArg(v_inst_1516_, v_opts_1517_, v_opt_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_inst_1521_, lean_object* v_opts_1522_, lean_object* v_opt_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Option_get_x3f(v_00_u03b1_1520_, v_inst_1521_, v_opts_1522_, v_opt_1523_);
lean_dec_ref(v_opt_1523_);
lean_dec_ref(v_opts_1522_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1525_, lean_object* v_opts_1526_, lean_object* v_opt_1527_){
_start:
{
lean_object* v_name_1528_; lean_object* v_defValue_1529_; lean_object* v_map_1530_; lean_object* v_ofDataValue_x3f_1531_; lean_object* v___x_1532_; 
v_name_1528_ = lean_ctor_get(v_opt_1527_, 0);
v_defValue_1529_ = lean_ctor_get(v_opt_1527_, 1);
v_map_1530_ = lean_ctor_get(v_opts_1526_, 0);
v_ofDataValue_x3f_1531_ = lean_ctor_get(v_inst_1525_, 1);
lean_inc_ref(v_ofDataValue_x3f_1531_);
lean_dec_ref(v_inst_1525_);
v___x_1532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1530_, v_name_1528_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1531_);
lean_inc(v_defValue_1529_);
return v_defValue_1529_;
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1534_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = lean_apply_1(v_ofDataValue_x3f_1531_, v_val_1533_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_inc(v_defValue_1529_);
return v_defValue_1529_;
}
else
{
lean_object* v_val_1535_; 
v_val_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v___x_1534_, 1);
return v_val_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1536_, lean_object* v_opts_1537_, lean_object* v_opt_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Option_get___redArg(v_inst_1536_, v_opts_1537_, v_opt_1538_);
lean_dec_ref(v_opt_1538_);
lean_dec_ref(v_opts_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1540_, lean_object* v_inst_1541_, lean_object* v_opts_1542_, lean_object* v_opt_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Option_get___redArg(v_inst_1541_, v_opts_1542_, v_opt_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1545_, lean_object* v_inst_1546_, lean_object* v_opts_1547_, lean_object* v_opt_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Option_get(v_00_u03b1_1545_, v_inst_1546_, v_opts_1547_, v_opt_1548_);
lean_dec_ref(v_opt_1548_);
lean_dec_ref(v_opts_1547_);
return v_res_1549_;
}
}
uint8_t lean_options_get_bool(lean_object* v_opts_1550_, lean_object* v_name_1551_, uint8_t v_defValue_1552_){
_start:
{
lean_object* v_map_1553_; lean_object* v___x_1554_; 
v_map_1553_ = lean_ctor_get(v_opts_1550_, 0);
lean_inc(v_map_1553_);
lean_dec_ref(v_opts_1550_);
v___x_1554_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1553_, v_name_1551_);
lean_dec(v_name_1551_);
lean_dec(v_map_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
return v_defValue_1552_;
}
else
{
lean_object* v_val_1555_; 
v_val_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1554_, 1);
if (lean_obj_tag(v_val_1555_) == 1)
{
uint8_t v_v_1556_; 
v_v_1556_ = lean_ctor_get_uint8(v_val_1555_, 0);
lean_dec_ref_known(v_val_1555_, 0);
return v_v_1556_;
}
else
{
lean_dec(v_val_1555_);
return v_defValue_1552_;
}
}
}
}
LEAN_EXPORT void lean_options_get_bool_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1550_ = stack[0].m_obj;
lean_object* v_name_1551_ = stack[1].m_obj;
uint8_t v_defValue_1552_ = stack[2].m_num;
uint8_t v_res_1557_;
v_res_1557_ = lean_options_get_bool(v_opts_1550_, v_name_1551_, v_defValue_1552_);
stack->m_num = v_res_1557_;
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
lean_object* v_toApplicative_1579_; lean_object* v_toBind_1580_; lean_object* v_getOptions_1581_; lean_object* v_toPure_1582_; lean_object* v___f_1583_; lean_object* v___x_1584_; 
v_toApplicative_1579_ = lean_ctor_get(v_inst_1575_, 0);
lean_inc_ref(v_toApplicative_1579_);
v_toBind_1580_ = lean_ctor_get(v_inst_1575_, 1);
lean_inc(v_toBind_1580_);
lean_dec_ref(v_inst_1575_);
v_getOptions_1581_ = lean_ctor_get(v_inst_1576_, 0);
lean_inc(v_getOptions_1581_);
lean_dec_ref(v_inst_1576_);
v_toPure_1582_ = lean_ctor_get(v_toApplicative_1579_, 1);
lean_inc(v_toPure_1582_);
lean_dec_ref(v_toApplicative_1579_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1583_, 0, v_inst_1577_);
lean_closure_set(v___f_1583_, 1, v_opt_1578_);
lean_closure_set(v___f_1583_, 2, v_toPure_1582_);
v___x_1584_ = lean_apply_4(v_toBind_1580_, lean_box(0), lean_box(0), v_getOptions_1581_, v___f_1583_);
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
lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1604_, lean_object* v_k_1605_, uint8_t v_v_1606_){
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
LEAN_EXPORT void l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1604_ = stack[0].m_obj;
lean_object* v_k_1605_ = stack[1].m_obj;
uint8_t v_v_1606_ = stack[2].m_num;
lean_object* v_res_1623_;
v_res_1623_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1604_, v_k_1605_, v_v_1606_);
stack->m_obj
 = v_res_1623_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1624_, lean_object* v_k_1625_, lean_object* v_v_1626_){
_start:
{
uint8_t v_v_boxed_1627_; lean_object* v_res_1628_; 
v_v_boxed_1627_ = lean_unbox(v_v_1626_);
v_res_1628_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1624_, v_k_1625_, v_v_boxed_1627_);
return v_res_1628_;
}
}
lean_object* lean_options_update_bool(lean_object* v_opts_1629_, lean_object* v_name_1630_, uint8_t v_val_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1629_, v_name_1630_, v_val_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT void lean_options_update_bool_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1629_ = stack[0].m_obj;
lean_object* v_name_1630_ = stack[1].m_obj;
uint8_t v_val_1631_ = stack[2].m_num;
lean_object* v_res_1633_;
v_res_1633_ = lean_options_update_bool(v_opts_1629_, v_name_1630_, v_val_1631_);
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1634_, lean_object* v_name_1635_, lean_object* v_val_1636_){
_start:
{
uint8_t v_val_boxed_1637_; lean_object* v_res_1638_; 
v_val_boxed_1637_ = lean_unbox(v_val_1636_);
v_res_1638_ = lean_options_update_bool(v_opts_1634_, v_name_1635_, v_val_boxed_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1639_, lean_object* v_opts_1640_, lean_object* v_opt_1641_, lean_object* v_val_1642_){
_start:
{
lean_object* v_name_1643_; lean_object* v_map_1644_; uint8_t v___x_1645_; 
v_name_1643_ = lean_ctor_get(v_opt_1641_, 0);
v_map_1644_ = lean_ctor_get(v_opts_1640_, 0);
v___x_1645_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1643_, v_map_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Option_set___redArg(v_inst_1639_, v_opts_1640_, v_opt_1641_, v_val_1642_);
return v___x_1646_;
}
else
{
lean_dec(v_val_1642_);
lean_dec_ref(v_opt_1641_);
lean_dec_ref(v_inst_1639_);
return v_opts_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1647_, lean_object* v_inst_1648_, lean_object* v_opts_1649_, lean_object* v_opt_1650_, lean_object* v_val_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1648_, v_opts_1649_, v_opt_1650_, v_val_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1653_;
}
}
lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1654_, lean_object* v_name_1655_, lean_object* v_decl_1656_, lean_object* v_ref_1657_){
_start:
{
lean_object* v_toDataValue_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1688_; 
v_toDataValue_1659_ = lean_ctor_get(v_inst_1654_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_inst_1654_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v_inst_1654_, 1);
lean_dec(v_unused_1689_);
v___x_1661_ = v_inst_1654_;
v_isShared_1662_ = v_isSharedCheck_1688_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_toDataValue_1659_);
lean_dec(v_inst_1654_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1688_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v_defValue_1663_; lean_object* v_descr_1664_; lean_object* v_deprecation_x3f_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_defValue_1663_ = lean_ctor_get(v_decl_1656_, 0);
lean_inc_n(v_defValue_1663_, 2);
v_descr_1664_ = lean_ctor_get(v_decl_1656_, 1);
lean_inc_ref(v_descr_1664_);
v_deprecation_x3f_1665_ = lean_ctor_get(v_decl_1656_, 2);
lean_inc(v_deprecation_x3f_1665_);
lean_dec_ref(v_decl_1656_);
v___x_1666_ = lean_apply_1(v_toDataValue_1659_, v_defValue_1663_);
lean_inc_n(v_name_1655_, 2);
v___x_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1667_, 0, v_name_1655_);
lean_ctor_set(v___x_1667_, 1, v_ref_1657_);
lean_ctor_set(v___x_1667_, 2, v___x_1666_);
lean_ctor_set(v___x_1667_, 3, v_descr_1664_);
lean_ctor_set(v___x_1667_, 4, v_deprecation_x3f_1665_);
v___x_1668_ = lean_register_option(v_name_1655_, v___x_1667_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1678_; 
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1679_);
v___x_1670_ = v___x_1668_;
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
else
{
lean_dec(v___x_1668_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v_defValue_1663_);
lean_ctor_set(v___x_1661_, 0, v_name_1655_);
v___x_1673_ = v___x_1661_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_name_1655_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_defValue_1663_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_defValue_1663_);
lean_del_object(v___x_1661_);
lean_dec(v_name_1655_);
v_a_1680_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1668_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1668_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
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
}
}
LEAN_EXPORT void l_Lean_Option_register___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1654_ = stack[0].m_obj;
lean_object* v_name_1655_ = stack[1].m_obj;
lean_object* v_decl_1656_ = stack[2].m_obj;
lean_object* v_ref_1657_ = stack[3].m_obj;
lean_object* v_res_1690_;
v_res_1690_ = l_Lean_Option_register___redArg(v_inst_1654_, v_name_1655_, v_decl_1656_, v_ref_1657_);
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1691_, lean_object* v_name_1692_, lean_object* v_decl_1693_, lean_object* v_ref_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Option_register___redArg(v_inst_1691_, v_name_1692_, v_decl_1693_, v_ref_1694_);
return v_res_1696_;
}
}
lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1697_, lean_object* v_inst_1698_, lean_object* v_name_1699_, lean_object* v_decl_1700_, lean_object* v_ref_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Option_register___redArg(v_inst_1698_, v_name_1699_, v_decl_1700_, v_ref_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT void l_Lean_Option_register_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1698_ = stack[1].m_obj;
lean_object* v_name_1699_ = stack[2].m_obj;
lean_object* v_decl_1700_ = stack[3].m_obj;
lean_object* v_ref_1701_ = stack[4].m_obj;
lean_object* v_res_1704_;
v_res_1704_ = l_Lean_Option_register(lean_box(0), v_inst_1698_, v_name_1699_, v_decl_1700_, v_ref_1701_);
stack->m_obj
 = v_res_1704_;
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
lean_inc_n(v___y_1868_, 2);
lean_inc_n(v___y_1869_, 6);
v___x_1881_ = l_Lean_Syntax_node2(v___y_1869_, v___y_1868_, v___y_1880_, v___x_1866_);
v___x_1882_ = l_Lean_Syntax_node2(v___y_1869_, v___y_1873_, v___y_1878_, v___x_1881_);
v___x_1883_ = l_Lean_Syntax_node1(v___y_1869_, v___y_1872_, v___x_1882_);
v___x_1884_ = l_Lean_Syntax_node2(v___y_1869_, v___y_1870_, v___x_1883_, v___y_1879_);
v___x_1885_ = l_Lean_Syntax_node1(v___y_1869_, v___y_1868_, v___x_1884_);
v___x_1886_ = l_Lean_Syntax_node1(v___y_1869_, v___y_1877_, v___x_1885_);
lean_inc(v___y_1875_);
v___x_1887_ = l_Lean_Syntax_node4(v___y_1869_, v___y_1875_, v___y_1874_, v___y_1876_, v___y_1871_, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_a_1851_);
return v___x_1888_;
}
v___jp_1889_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_inc_ref(v___y_1895_);
v___x_1902_ = l_Array_append___redArg(v___y_1895_, v___y_1901_);
lean_dec_ref(v___y_1901_);
lean_inc_n(v___y_1890_, 3);
lean_inc_n(v___y_1891_, 12);
v___x_1903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1891_);
lean_ctor_set(v___x_1903_, 1, v___y_1890_);
lean_ctor_set(v___x_1903_, 2, v___x_1902_);
lean_inc_n(v___y_1900_, 5);
lean_inc(v___y_1899_);
v___x_1904_ = l_Lean_Syntax_node7(v___y_1891_, v___y_1899_, v___y_1898_, v___y_1900_, v___x_1903_, v___y_1900_, v___y_1900_, v___y_1900_, v___y_1900_);
v___x_1905_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_1894_);
lean_inc_ref_n(v___y_1892_, 6);
v___x_1906_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___y_1894_, v___x_1905_);
v___x_1907_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
v___x_1908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___y_1891_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l_Lean_Syntax_node1(v___y_1891_, v___x_1906_, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_1911_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_1912_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___x_1910_, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___y_1891_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_1916_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___x_1910_, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_1918_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc_n(v___y_1897_, 2);
lean_inc_n(v___y_1893_, 2);
v___x_1919_ = l_Lean_addMacroScope(v___y_1893_, v___x_1918_, v___y_1897_);
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
v___x_1922_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1891_);
lean_ctor_set(v___x_1922_, 1, v___x_1917_);
lean_ctor_set(v___x_1922_, 2, v___x_1919_);
lean_ctor_set(v___x_1922_, 3, v___x_1921_);
v___x_1923_ = l_Lean_Syntax_node1(v___y_1891_, v___y_1890_, v___x_1864_);
lean_inc(v___x_1916_);
v___x_1924_ = l_Lean_Syntax_node2(v___y_1891_, v___x_1916_, v___x_1922_, v___x_1923_);
v___x_1925_ = l_Lean_Syntax_node2(v___y_1891_, v___x_1912_, v___x_1914_, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_1927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___y_1891_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
lean_inc(v_name_1862_);
v___x_1928_ = l_Lean_Syntax_node3(v___y_1891_, v___y_1890_, v_name_1862_, v___x_1925_, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_1930_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___x_1910_, v___x_1929_);
v___x_1931_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_1932_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___x_1910_, v___x_1931_);
v___x_1933_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_1934_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___x_1910_, v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_1936_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_1937_ = l_Lean_addMacroScope(v___y_1893_, v___x_1936_, v___y_1897_);
v___x_1938_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
v___x_1939_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1891_);
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
v___y_1868_ = v___y_1890_;
v___y_1869_ = v___y_1891_;
v___y_1870_ = v___x_1932_;
v___y_1871_ = v___x_1928_;
v___y_1872_ = v___x_1934_;
v___y_1873_ = v___x_1916_;
v___y_1874_ = v___x_1904_;
v___y_1875_ = v___y_1896_;
v___y_1876_ = v___x_1909_;
v___y_1877_ = v___x_1930_;
v___y_1878_ = v___x_1939_;
v___y_1879_ = v___y_1900_;
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
lean_inc_ref(v___y_1892_);
v___x_1945_ = l_Lean_Name_mkStr4(v___x_1852_, v___y_1892_, v___x_1910_, v___x_1944_);
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
v___y_1868_ = v___y_1890_;
v___y_1869_ = v___y_1891_;
v___y_1870_ = v___x_1932_;
v___y_1871_ = v___x_1928_;
v___y_1872_ = v___x_1934_;
v___y_1873_ = v___x_1916_;
v___y_1874_ = v___x_1904_;
v___y_1875_ = v___y_1896_;
v___y_1876_ = v___x_1909_;
v___y_1877_ = v___x_1930_;
v___y_1878_ = v___x_1939_;
v___y_1879_ = v___y_1900_;
v___y_1880_ = v___x_1954_;
goto v___jp_1867_;
}
}
v___jp_1955_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_inc_ref_n(v___y_1962_, 2);
v___x_1967_ = l_Array_append___redArg(v___y_1962_, v___y_1966_);
lean_dec_ref(v___y_1966_);
lean_inc_n(v___y_1956_, 2);
lean_inc_n(v___y_1957_, 2);
v___x_1968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1957_);
lean_ctor_set(v___x_1968_, 1, v___y_1956_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1957_);
lean_ctor_set(v___x_1969_, 1, v___y_1956_);
lean_ctor_set(v___x_1969_, 2, v___y_1962_);
if (lean_obj_tag(v___y_1961_) == 1)
{
lean_object* v_val_1970_; lean_object* v___x_1971_; 
v_val_1970_ = lean_ctor_get(v___y_1961_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v___y_1961_, 1);
v___x_1971_ = l_Array_mkArray1___redArg(v_val_1970_);
v___y_1890_ = v___y_1956_;
v___y_1891_ = v___y_1957_;
v___y_1892_ = v___y_1958_;
v___y_1893_ = v___y_1960_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v___y_1962_;
v___y_1896_ = v___y_1964_;
v___y_1897_ = v___y_1963_;
v___y_1898_ = v___x_1968_;
v___y_1899_ = v___y_1965_;
v___y_1900_ = v___x_1969_;
v___y_1901_ = v___x_1971_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1972_; 
lean_dec(v___y_1961_);
v___x_1972_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1890_ = v___y_1956_;
v___y_1891_ = v___y_1957_;
v___y_1892_ = v___y_1958_;
v___y_1893_ = v___y_1960_;
v___y_1894_ = v___y_1959_;
v___y_1895_ = v___y_1962_;
v___y_1896_ = v___y_1964_;
v___y_1897_ = v___y_1963_;
v___y_1898_ = v___x_1968_;
v___y_1899_ = v___y_1965_;
v___y_1900_ = v___x_1969_;
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
v___y_1956_ = v___x_1985_;
v___y_1957_ = v___x_1980_;
v___y_1958_ = v___x_1981_;
v___y_1959_ = v___x_1982_;
v___y_1960_ = v_quotContext_1976_;
v___y_1961_ = v___y_1974_;
v___y_1962_ = v___x_1986_;
v___y_1963_ = v_currMacroScope_1977_;
v___y_1964_ = v___x_1983_;
v___y_1965_ = v___x_1984_;
v___y_1966_ = v___x_1988_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___y_1975_);
v___x_1989_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_1956_ = v___x_1985_;
v___y_1957_ = v___x_1980_;
v___y_1958_ = v___x_1981_;
v___y_1959_ = v___x_1982_;
v___y_1960_ = v_quotContext_1976_;
v___y_1961_ = v___y_1974_;
v___y_1962_ = v___x_1986_;
v___y_1963_ = v_currMacroScope_1977_;
v___y_1964_ = v___x_1983_;
v___y_1965_ = v___x_1984_;
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
v___y_2389_ = v___y_2414_;
v___y_2390_ = v___x_2418_;
v___y_2391_ = v_text_x3f_2415_;
v___y_2392_ = v___y_2416_;
v___y_2393_ = v___y_2417_;
goto v___jp_2388_;
}
}
else
{
lean_dec(v___x_2419_);
v___y_2389_ = v___y_2414_;
v___y_2390_ = v___x_2418_;
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
if (lean_obj_tag(v___y_2303_) == 0)
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
v___y_2199_ = v___y_2304_;
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
v_val_2318_ = lean_ctor_get(v___y_2303_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v___y_2303_, 1);
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
v___y_2199_ = v___y_2304_;
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
v___y_2303_ = v___y_2358_;
v___y_2304_ = v_since_2360_;
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
v___y_2303_ = v___y_2358_;
v___y_2304_ = v_since_2360_;
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
lean_dec(v___y_2389_);
lean_dec(v_type_2193_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_decl_2194_);
lean_ctor_set(v___x_2399_, 1, v___y_2393_);
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Syntax_getArg(v___x_2395_, v___y_2390_);
lean_dec(v___x_2395_);
v___y_2358_ = v___y_2389_;
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
v___y_2358_ = v___y_2389_;
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
uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(lean_object* v_x_2489_){
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
LEAN_EXPORT void l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2489_ = stack[0].m_obj;
uint8_t v_res_2493_;
v_res_2493_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(v_x_2489_);
stack->m_num = v_res_2493_;
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0___boxed(lean_object* v_x_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__0(v_x_2494_);
lean_dec(v_x_2494_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
uint8_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(lean_object* v___x_2497_, lean_object* v_x_2498_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation___closed__75));
v___x_2500_ = l_Lean_Name_mkStr2(v___x_2497_, v___x_2499_);
v___x_2501_ = l_Lean_Syntax_isOfKind(v_x_2498_, v___x_2500_);
lean_dec(v___x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT void l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2497_ = stack[0].m_obj;
lean_object* v_x_2498_ = stack[1].m_obj;
uint8_t v_res_2502_;
v_res_2502_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(v___x_2497_, v_x_2498_);
stack->m_num = v_res_2502_;
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1___boxed(lean_object* v___x_2503_, lean_object* v_x_2504_){
_start:
{
uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_res_2505_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__1(v___x_2503_, v_x_2504_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(lean_object* v___x_2507_, lean_object* v___x_2508_, lean_object* v___x_2509_, lean_object* v___x_2510_, lean_object* v_type_2511_, lean_object* v_name_2512_, lean_object* v___x_2513_, lean_object* v_decl_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_quotContext_2517_; lean_object* v_currMacroScope_2518_; lean_object* v_ref_2519_; uint8_t v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___y_2565_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_quotContext_2517_ = lean_ctor_get(v___y_2515_, 1);
v_currMacroScope_2518_ = lean_ctor_get(v___y_2515_, 2);
v_ref_2519_ = lean_ctor_get(v___y_2515_, 5);
v___x_2520_ = 0;
v___x_2521_ = l_Lean_SourceInfo_fromRef(v_ref_2519_, v___x_2520_);
v___x_2522_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25));
lean_inc_ref(v___x_2509_);
lean_inc_ref_n(v___x_2508_, 7);
lean_inc_ref_n(v___x_2507_, 9);
v___x_2523_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_2522_);
v___x_2524_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
v___x_2525_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2509_, v___x_2524_);
lean_inc_n(v___x_2521_, 10);
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2521_);
lean_ctor_set(v___x_2526_, 1, v___x_2522_);
v___x_2527_ = l_Lean_Syntax_node1(v___x_2521_, v___x_2525_, v___x_2526_);
v___x_2528_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2529_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_2530_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
v___x_2531_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2529_, v___x_2530_);
v___x_2532_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
v___x_2533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2521_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
v___x_2535_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2529_, v___x_2534_);
v___x_2536_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
lean_inc_ref(v___x_2510_);
v___x_2537_ = l_Lean_Name_mkStr2(v___x_2507_, v___x_2510_);
lean_inc_n(v_currMacroScope_2518_, 2);
lean_inc_n(v___x_2537_, 2);
lean_inc_n(v_quotContext_2517_, 2);
v___x_2538_ = l_Lean_addMacroScope(v_quotContext_2517_, v___x_2537_, v_currMacroScope_2518_);
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2537_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2537_);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___x_2539_);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2540_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2521_);
lean_ctor_set(v___x_2544_, 1, v___x_2536_);
lean_ctor_set(v___x_2544_, 2, v___x_2538_);
lean_ctor_set(v___x_2544_, 3, v___x_2543_);
v___x_2545_ = l_Lean_Syntax_node1(v___x_2521_, v___x_2528_, v_type_2511_);
lean_inc(v___x_2535_);
v___x_2546_ = l_Lean_Syntax_node2(v___x_2521_, v___x_2535_, v___x_2544_, v___x_2545_);
v___x_2547_ = l_Lean_Syntax_node2(v___x_2521_, v___x_2531_, v___x_2533_, v___x_2546_);
v___x_2548_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2521_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
lean_inc(v_name_2512_);
v___x_2550_ = l_Lean_Syntax_node3(v___x_2521_, v___x_2528_, v_name_2512_, v___x_2547_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
v___x_2552_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2529_, v___x_2551_);
v___x_2553_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
v___x_2554_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2529_, v___x_2553_);
v___x_2555_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_2556_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2529_, v___x_2555_);
v___x_2557_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2558_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__18));
v___x_2559_ = l_Lean_Name_mkStr3(v___x_2507_, v___x_2510_, v___x_2558_);
lean_inc(v___x_2559_);
v___x_2560_ = l_Lean_addMacroScope(v_quotContext_2517_, v___x_2559_, v_currMacroScope_2518_);
v___x_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2539_);
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v___x_2539_);
v___x_2563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2521_);
lean_ctor_set(v___x_2563_, 1, v___x_2557_);
lean_ctor_set(v___x_2563_, 2, v___x_2560_);
lean_ctor_set(v___x_2563_, 3, v___x_2562_);
v___x_2576_ = l_Lean_TSyntax_getId(v_name_2512_);
lean_dec(v_name_2512_);
lean_inc(v___x_2576_);
v___x_2577_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_2539_, v___x_2576_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; 
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2507_);
v___x_2578_ = l_Lean_quoteNameMk(v___x_2576_);
v___y_2565_ = v___x_2578_;
goto v___jp_2564_;
}
else
{
lean_object* v_val_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v___x_2576_);
v_val_2579_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2580_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
v___x_2581_ = l_Lean_Name_mkStr4(v___x_2507_, v___x_2508_, v___x_2529_, v___x_2580_);
v___x_2582_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_2583_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2584_ = lean_string_intercalate(v___x_2583_, v_val_2579_);
v___x_2585_ = lean_string_append(v___x_2582_, v___x_2584_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = lean_box(2);
v___x_2587_ = l_Lean_Syntax_mkNameLit(v___x_2585_, v___x_2586_);
v___x_2588_ = lean_unsigned_to_nat(1u);
v___x_2589_ = lean_mk_empty_array_with_capacity(v___x_2588_);
v___x_2590_ = lean_array_push(v___x_2589_, v___x_2587_);
v___x_2591_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2586_);
lean_ctor_set(v___x_2591_, 1, v___x_2581_);
lean_ctor_set(v___x_2591_, 2, v___x_2590_);
v___y_2565_ = v___x_2591_;
goto v___jp_2564_;
}
v___jp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_inc_n(v___x_2521_, 7);
v___x_2566_ = l_Lean_Syntax_node2(v___x_2521_, v___x_2528_, v___y_2565_, v_decl_2514_);
v___x_2567_ = l_Lean_Syntax_node2(v___x_2521_, v___x_2535_, v___x_2563_, v___x_2566_);
v___x_2568_ = l_Lean_Syntax_node1(v___x_2521_, v___x_2556_, v___x_2567_);
v___x_2569_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__29);
v___x_2570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2521_);
lean_ctor_set(v___x_2570_, 1, v___x_2528_);
lean_ctor_set(v___x_2570_, 2, v___x_2569_);
v___x_2571_ = l_Lean_Syntax_node2(v___x_2521_, v___x_2554_, v___x_2568_, v___x_2570_);
v___x_2572_ = l_Lean_Syntax_node1(v___x_2521_, v___x_2528_, v___x_2571_);
v___x_2573_ = l_Lean_Syntax_node1(v___x_2521_, v___x_2552_, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node4(v___x_2521_, v___x_2523_, v___x_2513_, v___x_2527_, v___x_2550_, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___y_2516_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2___boxed(lean_object* v___x_2592_, lean_object* v___x_2593_, lean_object* v___x_2594_, lean_object* v___x_2595_, lean_object* v_type_2596_, lean_object* v_name_2597_, lean_object* v___x_2598_, lean_object* v_decl_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2592_, v___x_2593_, v___x_2594_, v___x_2595_, v_type_2596_, v_name_2597_, v___x_2598_, v_decl_2599_, v___y_2600_, v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___y_2612_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2631_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_2632_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__0));
v___x_2633_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2608_);
v___x_2634_ = l_Lean_Syntax_isOfKind(v_x_2608_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec(v_x_2608_);
v___x_2635_ = lean_box(1);
v___x_2636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v_a_2610_);
return v___x_2636_;
}
else
{
lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_name_2642_; lean_object* v___x_2643_; lean_object* v_type_2644_; lean_object* v___x_2645_; lean_object* v_decl_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v_attr_x3f_2649_; lean_object* v_field_x3f_2650_; 
v___f_2637_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
v___f_2638_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = l_Lean_Syntax_getArg(v_x_2608_, v___x_2639_);
v___x_2641_ = lean_unsigned_to_nat(2u);
v_name_2642_ = l_Lean_Syntax_getArg(v_x_2608_, v___x_2641_);
v___x_2643_ = lean_unsigned_to_nat(4u);
v_type_2644_ = l_Lean_Syntax_getArg(v_x_2608_, v___x_2643_);
v___x_2645_ = lean_unsigned_to_nat(6u);
v_decl_2646_ = l_Lean_Syntax_getArg(v_x_2608_, v___x_2645_);
lean_dec(v_x_2608_);
v___x_2647_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_2648_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
lean_inc(v___x_2640_);
v_attr_x3f_2649_ = l_Lean_Syntax_find_x3f(v___x_2640_, v___f_2638_);
lean_inc(v_decl_2646_);
v_field_x3f_2650_ = l_Lean_Syntax_find_x3f(v_decl_2646_, v___f_2637_);
if (lean_obj_tag(v_attr_x3f_2649_) == 0)
{
if (lean_obj_tag(v_field_x3f_2650_) == 0)
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2631_, v___x_2647_, v___x_2648_, v___x_2632_, v_type_2644_, v_name_2642_, v___x_2640_, v_decl_2646_, v_a_2609_, v_a_2610_);
v___y_2612_ = v___x_2651_;
goto v___jp_2611_;
}
else
{
lean_object* v_val_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v_decl_2646_);
v_val_2652_ = lean_ctor_get(v_field_x3f_2650_, 0);
lean_inc(v_val_2652_);
lean_dec_ref_known(v_field_x3f_2650_, 1);
v___x_2653_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2654_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2652_, v___x_2653_, v_a_2609_, v_a_2610_);
lean_dec(v_val_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_a_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
v_a_2656_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2654_, 2);
v___x_2657_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2631_, v___x_2647_, v___x_2648_, v___x_2632_, v_type_2644_, v_name_2642_, v___x_2640_, v_a_2655_, v_a_2609_, v_a_2656_);
v___y_2612_ = v___x_2657_;
goto v___jp_2611_;
}
else
{
lean_dec(v_type_2644_);
lean_dec(v_name_2642_);
lean_dec(v___x_2640_);
v___y_2612_ = v___x_2654_;
goto v___jp_2611_;
}
}
}
else
{
if (lean_obj_tag(v_field_x3f_2650_) == 0)
{
lean_object* v_val_2658_; lean_object* v___x_2659_; lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_val_2658_ = lean_ctor_get(v_attr_x3f_2649_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v_attr_x3f_2649_, 1);
lean_inc(v_type_2644_);
v___x_2659_ = l___private_Lean_Data_Options_0__Lean_Option_declWithDeprecation(v_val_2658_, v_type_2644_, v_decl_2646_, v_a_2609_, v_a_2610_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
v_a_2661_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2659_);
v___x_2662_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2631_, v___x_2647_, v___x_2648_, v___x_2632_, v_type_2644_, v_name_2642_, v___x_2640_, v_a_2660_, v_a_2609_, v_a_2661_);
v___y_2612_ = v___x_2662_;
goto v___jp_2611_;
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec_ref_known(v_attr_x3f_2649_, 1);
lean_dec(v_decl_2646_);
v_val_2663_ = lean_ctor_get(v_field_x3f_2650_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_field_x3f_2650_, 1);
v___x_2664_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2665_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2663_, v___x_2664_, v_a_2609_, v_a_2610_);
lean_dec(v_val_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_a_2667_; lean_object* v___x_2668_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
v_a_2667_ = lean_ctor_get(v___x_2665_, 1);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2665_, 2);
v___x_2668_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___lam__2(v___x_2631_, v___x_2647_, v___x_2648_, v___x_2632_, v_type_2644_, v_name_2642_, v___x_2640_, v_a_2666_, v_a_2609_, v_a_2667_);
v___y_2612_ = v___x_2668_;
goto v___jp_2611_;
}
else
{
lean_dec(v_type_2644_);
lean_dec(v_name_2642_);
lean_dec(v___x_2640_);
v___y_2612_ = v___x_2665_;
goto v___jp_2611_;
}
}
}
}
v___jp_2611_:
{
if (lean_obj_tag(v___y_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2613_ = lean_ctor_get(v___y_2612_, 0);
v_a_2614_ = lean_ctor_get(v___y_2612_, 1);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___y_2612_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___y_2612_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_inc(v_a_2613_);
lean_dec(v___y_2612_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2613_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_a_2622_ = lean_ctor_get(v___y_2612_, 0);
v_a_2623_ = lean_ctor_get(v___y_2612_, 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___y_2612_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___y_2612_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_inc(v_a_2622_);
lean_dec(v___y_2612_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2622_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___boxed(lean_object* v_x_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(v_x_2669_, v_a_2670_, v_a_2671_);
lean_dec_ref(v_a_2670_);
return v_res_2672_;
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
