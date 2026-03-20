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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_data_value_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqDataValue_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDataValue_default;
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Options_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Options_empty___closed__0 = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_empty = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_Options_instInhabited = (const lean_object*)&l_Lean_Options_empty___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Options_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Options_instToString___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___closed__0 = (const lean_object*)&l_Lean_Options_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_instToString = (const lean_object*)&l_Lean_Options_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_instBEq___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instBEq___private__1___closed__0 = (const lean_object*)&l_Lean_Options_instBEq___private__1___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Options_instBEq___private__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24_value;
static const lean_string_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value;
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value_aux_2),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26 = (const lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26_value;
static lean_once_cell_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27;
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Option_registerOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "registerOption"};
static const lean_object* l_Lean_Option_registerOption___closed__0 = (const lean_object*)&l_Lean_Option_registerOption___closed__0_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Option_registerOption___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__1_value_aux_0),((lean_object*)&l_Lean_Option_registerBuiltinOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l_Lean_Option_registerOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option_registerOption___closed__1_value_aux_1),((lean_object*)&l_Lean_Option_registerOption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 95, 60, 142, 241, 184, 36, 53)}};
static const lean_object* l_Lean_Option_registerOption___closed__1 = (const lean_object*)&l_Lean_Option_registerOption___closed__1_value;
static const lean_ctor_object l_Lean_Option_registerOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(113, 135, 0, 93, 130, 217, 220, 132)}};
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
static const lean_ctor_object l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0_value_aux_1),((lean_object*)&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
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
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = ((lean_object*)(l_Lean_Options_empty));
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(lean_object* v_init_8_, lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v_k_10_; lean_object* v_v_11_; lean_object* v_l_12_; lean_object* v_r_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_k_10_ = lean_ctor_get(v_x_9_, 1);
v_v_11_ = lean_ctor_get(v_x_9_, 2);
v_l_12_ = lean_ctor_get(v_x_9_, 3);
v_r_13_ = lean_ctor_get(v_x_9_, 4);
v___x_14_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(v_init_8_, v_r_13_);
lean_inc(v_v_11_);
lean_inc(v_k_10_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_k_10_);
lean_ctor_set(v___x_15_, 1, v_v_11_);
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
v_init_8_ = v___x_16_;
v_x_9_ = v_l_12_;
goto _start;
}
else
{
return v_init_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0___boxed(lean_object* v_init_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(v_init_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
return v_x_24_;
}
else
{
lean_object* v_head_26_; lean_object* v_tail_27_; lean_object* v_fst_28_; lean_object* v_snd_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_head_26_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_head_26_);
v_tail_27_ = lean_ctor_get(v_x_25_, 1);
lean_inc(v_tail_27_);
lean_dec_ref(v_x_25_);
v_fst_28_ = lean_ctor_get(v_head_26_, 0);
lean_inc(v_fst_28_);
v_snd_29_ = lean_ctor_get(v_head_26_, 1);
lean_inc(v_snd_29_);
lean_dec(v_head_26_);
v___x_30_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0));
v___x_31_ = lean_string_append(v_x_24_, v___x_30_);
v___x_32_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1));
v___x_33_ = 1;
v___x_34_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_28_, v___x_33_);
v___x_35_ = lean_string_append(v___x_32_, v___x_34_);
lean_dec_ref(v___x_34_);
v___x_36_ = lean_string_append(v___x_35_, v___x_30_);
v___x_37_ = lean_data_value_to_string(v_snd_29_);
v___x_38_ = lean_string_append(v___x_36_, v___x_37_);
lean_dec_ref(v___x_37_);
v___x_39_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2));
v___x_40_ = lean_string_append(v___x_38_, v___x_39_);
v___x_41_ = lean_string_append(v___x_31_, v___x_40_);
lean_dec_ref(v___x_40_);
v_x_24_ = v___x_41_;
v_x_25_ = v_tail_27_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1(lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_47_; 
v___x_47_ = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0));
return v___x_47_;
}
else
{
lean_object* v_tail_48_; 
v_tail_48_ = lean_ctor_get(v_x_46_, 1);
if (lean_obj_tag(v_tail_48_) == 0)
{
lean_object* v_head_49_; lean_object* v_fst_50_; lean_object* v_snd_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_head_49_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_49_);
lean_dec_ref(v_x_46_);
v_fst_50_ = lean_ctor_get(v_head_49_, 0);
lean_inc(v_fst_50_);
v_snd_51_ = lean_ctor_get(v_head_49_, 1);
lean_inc(v_snd_51_);
lean_dec(v_head_49_);
v___x_52_ = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1));
v___x_53_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1));
v___x_54_ = 1;
v___x_55_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_50_, v___x_54_);
v___x_56_ = lean_string_append(v___x_53_, v___x_55_);
lean_dec_ref(v___x_55_);
v___x_57_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0));
v___x_58_ = lean_string_append(v___x_56_, v___x_57_);
v___x_59_ = lean_data_value_to_string(v_snd_51_);
v___x_60_ = lean_string_append(v___x_58_, v___x_59_);
lean_dec_ref(v___x_59_);
v___x_61_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2));
v___x_62_ = lean_string_append(v___x_60_, v___x_61_);
v___x_63_ = lean_string_append(v___x_52_, v___x_62_);
lean_dec_ref(v___x_62_);
v___x_64_ = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2));
v___x_65_ = lean_string_append(v___x_63_, v___x_64_);
return v___x_65_;
}
else
{
lean_object* v_head_66_; lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint32_t v___x_82_; lean_object* v___x_83_; 
lean_inc(v_tail_48_);
v_head_66_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_66_);
lean_dec_ref(v_x_46_);
v_fst_67_ = lean_ctor_get(v_head_66_, 0);
lean_inc(v_fst_67_);
v_snd_68_ = lean_ctor_get(v_head_66_, 1);
lean_inc(v_snd_68_);
lean_dec(v_head_66_);
v___x_69_ = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1));
v___x_70_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1));
v___x_71_ = 1;
v___x_72_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_67_, v___x_71_);
v___x_73_ = lean_string_append(v___x_70_, v___x_72_);
lean_dec_ref(v___x_72_);
v___x_74_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0));
v___x_75_ = lean_string_append(v___x_73_, v___x_74_);
v___x_76_ = lean_data_value_to_string(v_snd_68_);
v___x_77_ = lean_string_append(v___x_75_, v___x_76_);
lean_dec_ref(v___x_76_);
v___x_78_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2));
v___x_79_ = lean_string_append(v___x_77_, v___x_78_);
v___x_80_ = lean_string_append(v___x_69_, v___x_79_);
lean_dec_ref(v___x_79_);
v___x_81_ = l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1(v___x_80_, v_tail_48_);
v___x_82_ = 93;
v___x_83_ = lean_string_push(v___x_81_, v___x_82_);
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object* v_o_84_){
_start:
{
lean_object* v_map_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_map_85_ = lean_ctor_get(v_o_84_, 0);
v___x_86_ = lean_box(0);
v___x_87_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(v___x_86_, v_map_85_);
v___x_88_ = l_List_toString___at___00Lean_Options_instToString___private__1_spec__1(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___boxed(lean_object* v_o_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Options_instToString___private__1(v_o_89_);
lean_dec_ref(v_o_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object* v_f_93_, lean_object* v_a_94_, lean_object* v_b_95_, lean_object* v_c_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_a_94_);
lean_ctor_set(v___x_97_, 1, v_b_95_);
v___x_98_ = lean_apply_2(v_f_93_, v___x_97_, v_c_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object* v_toPure_99_, lean_object* v_____do__lift_100_){
_start:
{
lean_object* v_a_101_; lean_object* v___x_102_; 
v_a_101_ = lean_ctor_get(v_____do__lift_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref(v_____do__lift_100_);
v___x_102_ = lean_apply_2(v_toPure_99_, lean_box(0), v_a_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object* v_inst_103_, lean_object* v_o_104_, lean_object* v_init_105_, lean_object* v_f_106_){
_start:
{
lean_object* v_toApplicative_107_; lean_object* v_map_108_; lean_object* v_toBind_109_; lean_object* v_toPure_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___f_113_; lean_object* v___x_114_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_103_, 0);
v_map_108_ = lean_ctor_get(v_o_104_, 0);
lean_inc(v_map_108_);
lean_dec_ref(v_o_104_);
v_toBind_109_ = lean_ctor_get(v_inst_103_, 1);
lean_inc(v_toBind_109_);
v_toPure_110_ = lean_ctor_get(v_toApplicative_107_, 1);
lean_inc(v_toPure_110_);
v___f_111_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_111_, 0, v_f_106_);
v___x_112_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_103_, v___f_111_, v_init_105_, v_map_108_);
v___f_113_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_113_, 0, v_toPure_110_);
v___x_114_ = lean_apply_4(v_toBind_109_, lean_box(0), lean_box(0), v___x_112_, v___f_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_00_u03b2_117_, lean_object* v_o_118_, lean_object* v_init_119_, lean_object* v_f_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(v_inst_116_, v_o_118_, v_init_119_, v_f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object* v_inst_122_, lean_object* v_00_u03b2_123_, lean_object* v_o_124_, lean_object* v_init_125_, lean_object* v_f_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(v_inst_122_, v_o_124_, v_init_125_, v_f_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object* v_inst_128_){
_start:
{
lean_object* v___f_129_; 
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_129_, 0, v_inst_128_);
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object* v_m_130_, lean_object* v_inst_131_){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_132_, 0, v_inst_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_cmp_133_, lean_object* v_t_134_, lean_object* v_k_135_){
_start:
{
if (lean_obj_tag(v_t_134_) == 0)
{
lean_object* v_k_136_; lean_object* v_v_137_; lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_k_136_ = lean_ctor_get(v_t_134_, 1);
lean_inc(v_k_136_);
v_v_137_ = lean_ctor_get(v_t_134_, 2);
lean_inc(v_v_137_);
v_l_138_ = lean_ctor_get(v_t_134_, 3);
lean_inc(v_l_138_);
v_r_139_ = lean_ctor_get(v_t_134_, 4);
lean_inc(v_r_139_);
lean_dec_ref(v_t_134_);
lean_inc_ref(v_cmp_133_);
lean_inc(v_k_135_);
v___x_140_ = lean_apply_2(v_cmp_133_, v_k_135_, v_k_136_);
v___x_141_ = lean_unbox(v___x_140_);
switch(v___x_141_)
{
case 0:
{
lean_dec(v_r_139_);
lean_dec(v_v_137_);
v_t_134_ = v_l_138_;
goto _start;
}
case 1:
{
lean_object* v___x_143_; 
lean_dec(v_r_139_);
lean_dec(v_l_138_);
lean_dec(v_k_135_);
lean_dec_ref(v_cmp_133_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v_v_137_);
return v___x_143_;
}
default: 
{
lean_dec(v_l_138_);
lean_dec(v_v_137_);
v_t_134_ = v_r_139_;
goto _start;
}
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v_k_135_);
lean_dec_ref(v_cmp_133_);
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
if (lean_obj_tag(v_x_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 1;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec_ref(v_x_147_);
v___x_149_ = 0;
return v___x_149_;
}
}
else
{
if (lean_obj_tag(v_x_147_) == 0)
{
uint8_t v___x_150_; 
lean_dec_ref(v_x_146_);
v___x_150_ = 0;
return v___x_150_;
}
else
{
lean_object* v_val_151_; lean_object* v_val_152_; uint8_t v___x_153_; 
v_val_151_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v_x_146_);
v_val_152_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_val_152_);
lean_dec_ref(v_x_147_);
v___x_153_ = l_Lean_instBEqDataValue_beq(v_val_151_, v_val_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(v_x_154_, v_x_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_cmp_161_, lean_object* v_t_u2082_162_, lean_object* v_init_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v_k_165_; lean_object* v_v_166_; lean_object* v_l_167_; lean_object* v_r_168_; lean_object* v___x_169_; 
v_k_165_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_k_165_);
v_v_166_ = lean_ctor_get(v_x_164_, 2);
lean_inc(v_v_166_);
v_l_167_ = lean_ctor_get(v_x_164_, 3);
lean_inc(v_l_167_);
v_r_168_ = lean_ctor_get(v_x_164_, 4);
lean_inc(v_r_168_);
lean_dec_ref(v_x_164_);
lean_inc(v_t_u2082_162_);
lean_inc_ref(v_cmp_161_);
v___x_169_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_161_, v_t_u2082_162_, v_init_163_, v_l_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_dec(v_r_168_);
lean_dec(v_v_166_);
lean_dec(v_k_165_);
lean_dec(v_t_u2082_162_);
lean_dec_ref(v_cmp_161_);
return v___x_169_;
}
else
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_185_; 
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_169_, 0);
lean_dec(v_unused_186_);
v___x_171_ = v___x_169_;
v_isShared_172_ = v_isSharedCheck_185_;
goto v_resetjp_170_;
}
else
{
lean_dec(v___x_169_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_185_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_173_ = lean_box(0);
lean_inc(v_t_u2082_162_);
lean_inc_ref(v_cmp_161_);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_161_, v_t_u2082_162_, v_k_165_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v_v_166_);
v___x_176_ = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_dec(v_r_168_);
lean_dec(v_t_u2082_162_);
lean_dec_ref(v_cmp_161_);
v___x_177_ = lean_box(v___x_176_);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_173_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 0);
lean_ctor_set(v___x_171_, 0, v___x_179_);
v___x_181_ = v___x_171_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
else
{
lean_object* v___x_183_; 
lean_del_object(v___x_171_);
v___x_183_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v_init_163_ = v___x_183_;
v_x_164_ = v_r_168_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_187_; 
lean_dec(v_t_u2082_162_);
lean_dec_ref(v_cmp_161_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_init_163_);
return v___x_187_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(lean_object* v_cmp_188_, lean_object* v_t_u2081_189_, lean_object* v_t_u2082_190_){
_start:
{
lean_object* v___y_192_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_205_; 
if (lean_obj_tag(v_t_u2081_189_) == 0)
{
lean_object* v_size_208_; 
v_size_208_ = lean_ctor_get(v_t_u2081_189_, 0);
lean_inc(v_size_208_);
v___y_205_ = v_size_208_;
goto v___jp_204_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___y_205_ = v___x_209_;
goto v___jp_204_;
}
v___jp_191_:
{
lean_object* v_fst_193_; 
v_fst_193_ = lean_ctor_get(v___y_192_, 0);
lean_inc(v_fst_193_);
lean_dec_ref(v___y_192_);
if (lean_obj_tag(v_fst_193_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 1;
return v___x_194_;
}
else
{
lean_object* v_val_195_; uint8_t v___x_196_; 
v_val_195_ = lean_ctor_get(v_fst_193_, 0);
lean_inc(v_val_195_);
lean_dec_ref(v_fst_193_);
v___x_196_ = lean_unbox(v_val_195_);
lean_dec(v_val_195_);
return v___x_196_;
}
}
v___jp_197_:
{
uint8_t v___x_200_; 
v___x_200_ = lean_nat_dec_eq(v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec(v___y_198_);
if (v___x_200_ == 0)
{
lean_dec(v_t_u2082_190_);
lean_dec(v_t_u2081_189_);
lean_dec_ref(v_cmp_188_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_a_203_; 
v___x_201_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_202_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_188_, v_t_u2082_190_, v___x_201_, v_t_u2081_189_);
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref(v___x_202_);
v___y_192_ = v_a_203_;
goto v___jp_191_;
}
}
v___jp_204_:
{
if (lean_obj_tag(v_t_u2082_190_) == 0)
{
lean_object* v_size_206_; 
v_size_206_ = lean_ctor_get(v_t_u2082_190_, 0);
lean_inc(v_size_206_);
v___y_198_ = v___y_205_;
v___y_199_ = v_size_206_;
goto v___jp_197_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(0u);
v___y_198_ = v___y_205_;
v___y_199_ = v___x_207_;
goto v___jp_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cmp_210_, lean_object* v_t_u2081_211_, lean_object* v_t_u2082_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v_cmp_210_, v_t_u2081_211_, v_t_u2082_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___private__1(lean_object* v_o1_216_, lean_object* v_o2_217_){
_start:
{
lean_object* v_map_218_; lean_object* v_map_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_map_218_ = lean_ctor_get(v_o1_216_, 0);
lean_inc(v_map_218_);
lean_dec_ref(v_o1_216_);
v_map_219_ = lean_ctor_get(v_o2_217_, 0);
lean_inc(v_map_219_);
lean_dec_ref(v_o2_217_);
v___x_220_ = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
v___x_221_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v___x_220_, v_map_218_, v_map_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object* v_o1_222_, lean_object* v_o2_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Lean_Options_instBEq___private__1(v_o1_222_, v_o2_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg(lean_object* v_cmp_226_, lean_object* v_t_u2081_227_, lean_object* v_t_u2082_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v_cmp_226_, v_t_u2081_227_, v_t_u2082_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg___boxed(lean_object* v_cmp_230_, lean_object* v_t_u2081_231_, lean_object* v_t_u2082_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg(v_cmp_230_, v_t_u2081_231_, v_t_u2082_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0(lean_object* v_00_u03b1_235_, lean_object* v_cmp_236_, lean_object* v_t_u2081_237_, lean_object* v_t_u2082_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v_cmp_236_, v_t_u2081_237_, v_t_u2082_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___boxed(lean_object* v_00_u03b1_240_, lean_object* v_cmp_241_, lean_object* v_t_u2081_242_, lean_object* v_t_u2082_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0(v_00_u03b1_240_, v_cmp_241_, v_t_u2081_242_, v_t_u2082_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg(lean_object* v_cmp_246_, lean_object* v_t_u2081_247_, lean_object* v_t_u2082_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v_cmp_246_, v_t_u2081_247_, v_t_u2082_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg___boxed(lean_object* v_cmp_250_, lean_object* v_t_u2081_251_, lean_object* v_t_u2082_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg(v_cmp_250_, v_t_u2081_251_, v_t_u2082_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0(lean_object* v_00_u03b1_255_, lean_object* v_cmp_256_, lean_object* v_t_u2081_257_, lean_object* v_t_u2082_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v_cmp_256_, v_t_u2081_257_, v_t_u2082_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___boxed(lean_object* v_00_u03b1_260_, lean_object* v_cmp_261_, lean_object* v_t_u2081_262_, lean_object* v_t_u2082_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0(v_00_u03b1_260_, v_cmp_261_, v_t_u2081_262_, v_t_u2082_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_266_, lean_object* v_cmp_267_, lean_object* v_t_u2081_268_, lean_object* v_t_u2082_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(v_cmp_267_, v_t_u2081_268_, v_t_u2082_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_271_, lean_object* v_cmp_272_, lean_object* v_t_u2081_273_, lean_object* v_t_u2082_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1(v_00_u03b1_271_, v_cmp_272_, v_t_u2081_273_, v_t_u2082_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_277_, lean_object* v_cmp_278_, lean_object* v_00_u03b4_279_, lean_object* v_t_280_, lean_object* v_k_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(v_cmp_278_, v_t_280_, v_k_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_283_, lean_object* v_cmp_284_, lean_object* v_t_u2082_285_, lean_object* v_init_286_, lean_object* v_x_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(v_cmp_284_, v_t_u2082_285_, v_init_286_, v_x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f(lean_object* v_o_292_, lean_object* v_k_293_){
_start:
{
lean_object* v_map_294_; lean_object* v___x_295_; 
v_map_294_ = lean_ctor_get(v_o_292_, 0);
v___x_295_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_294_, v_k_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f___boxed(lean_object* v_o_296_, lean_object* v_k_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Options_find_x3f(v_o_296_, v_k_297_);
lean_dec(v_k_297_);
lean_dec_ref(v_o_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find(lean_object* v_o_299_, lean_object* v_k_300_){
_start:
{
lean_object* v_map_301_; lean_object* v___x_302_; 
v_map_301_ = lean_ctor_get(v_o_299_, 0);
v___x_302_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_301_, v_k_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find___boxed(lean_object* v_o_303_, lean_object* v_k_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Options_find(v_o_303_, v_k_304_);
lean_dec(v_k_304_);
lean_dec_ref(v_o_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg(lean_object* v_inst_306_, lean_object* v_o_307_, lean_object* v_k_308_){
_start:
{
lean_object* v_map_309_; lean_object* v_ofDataValue_x3f_310_; lean_object* v___x_311_; 
v_map_309_ = lean_ctor_get(v_o_307_, 0);
v_ofDataValue_x3f_310_ = lean_ctor_get(v_inst_306_, 1);
lean_inc_ref(v_ofDataValue_x3f_310_);
lean_dec_ref(v_inst_306_);
v___x_311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_309_, v_k_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v_ofDataValue_x3f_310_);
v___x_312_ = lean_box(0);
return v___x_312_;
}
else
{
lean_object* v_val_313_; lean_object* v___x_314_; 
v_val_313_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_313_);
lean_dec_ref(v___x_311_);
v___x_314_ = lean_apply_1(v_ofDataValue_x3f_310_, v_val_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg___boxed(lean_object* v_inst_315_, lean_object* v_o_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Options_get_x3f___redArg(v_inst_315_, v_o_316_, v_k_317_);
lean_dec(v_k_317_);
lean_dec_ref(v_o_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_o_321_, lean_object* v_k_322_){
_start:
{
lean_object* v_map_323_; lean_object* v_ofDataValue_x3f_324_; lean_object* v___x_325_; 
v_map_323_ = lean_ctor_get(v_o_321_, 0);
v_ofDataValue_x3f_324_ = lean_ctor_get(v_inst_320_, 1);
lean_inc_ref(v_ofDataValue_x3f_324_);
lean_dec_ref(v_inst_320_);
v___x_325_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_323_, v_k_322_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v_ofDataValue_x3f_324_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v_val_327_; lean_object* v___x_328_; 
v_val_327_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_327_);
lean_dec_ref(v___x_325_);
v___x_328_ = lean_apply_1(v_ofDataValue_x3f_324_, v_val_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___boxed(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_o_331_, lean_object* v_k_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Options_get_x3f(v_00_u03b1_329_, v_inst_330_, v_o_331_, v_k_332_);
lean_dec(v_k_332_);
lean_dec_ref(v_o_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg(lean_object* v_inst_334_, lean_object* v_o_335_, lean_object* v_k_336_, lean_object* v_defVal_337_){
_start:
{
lean_object* v_map_338_; lean_object* v_ofDataValue_x3f_339_; lean_object* v___x_340_; 
v_map_338_ = lean_ctor_get(v_o_335_, 0);
v_ofDataValue_x3f_339_ = lean_ctor_get(v_inst_334_, 1);
lean_inc_ref(v_ofDataValue_x3f_339_);
lean_dec_ref(v_inst_334_);
v___x_340_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_338_, v_k_336_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_339_);
lean_inc(v_defVal_337_);
return v_defVal_337_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_342_; 
v_val_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_val_341_);
lean_dec_ref(v___x_340_);
v___x_342_ = lean_apply_1(v_ofDataValue_x3f_339_, v_val_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_inc(v_defVal_337_);
return v_defVal_337_;
}
else
{
lean_object* v_val_343_; 
v_val_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref(v___x_342_);
return v_val_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg___boxed(lean_object* v_inst_344_, lean_object* v_o_345_, lean_object* v_k_346_, lean_object* v_defVal_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Options_get___redArg(v_inst_344_, v_o_345_, v_k_346_, v_defVal_347_);
lean_dec(v_defVal_347_);
lean_dec(v_k_346_);
lean_dec_ref(v_o_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_o_351_, lean_object* v_k_352_, lean_object* v_defVal_353_){
_start:
{
lean_object* v_map_354_; lean_object* v_ofDataValue_x3f_355_; lean_object* v___x_356_; 
v_map_354_ = lean_ctor_get(v_o_351_, 0);
v_ofDataValue_x3f_355_ = lean_ctor_get(v_inst_350_, 1);
lean_inc_ref(v_ofDataValue_x3f_355_);
lean_dec_ref(v_inst_350_);
v___x_356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_354_, v_k_352_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_355_);
lean_inc(v_defVal_353_);
return v_defVal_353_;
}
else
{
lean_object* v_val_357_; lean_object* v___x_358_; 
v_val_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_val_357_);
lean_dec_ref(v___x_356_);
v___x_358_ = lean_apply_1(v_ofDataValue_x3f_355_, v_val_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_inc(v_defVal_353_);
return v_defVal_353_;
}
else
{
lean_object* v_val_359_; 
v_val_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_val_359_);
lean_dec_ref(v___x_358_);
return v_val_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___boxed(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_o_362_, lean_object* v_k_363_, lean_object* v_defVal_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Options_get(v_00_u03b1_360_, v_inst_361_, v_o_362_, v_k_363_, v_defVal_364_);
lean_dec(v_defVal_364_);
lean_dec(v_k_363_);
lean_dec_ref(v_o_362_);
return v_res_365_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getBool(lean_object* v_o_366_, lean_object* v_k_367_, uint8_t v_defVal_368_){
_start:
{
lean_object* v_map_369_; lean_object* v___x_370_; 
v_map_369_ = lean_ctor_get(v_o_366_, 0);
v___x_370_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_369_, v_k_367_);
if (lean_obj_tag(v___x_370_) == 0)
{
return v_defVal_368_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v___x_370_);
if (lean_obj_tag(v_val_371_) == 1)
{
uint8_t v_v_372_; 
v_v_372_ = lean_ctor_get_uint8(v_val_371_, 0);
lean_dec_ref(v_val_371_);
return v_v_372_;
}
else
{
lean_dec(v_val_371_);
return v_defVal_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getBool___boxed(lean_object* v_o_373_, lean_object* v_k_374_, lean_object* v_defVal_375_){
_start:
{
uint8_t v_defVal_boxed_376_; uint8_t v_res_377_; lean_object* v_r_378_; 
v_defVal_boxed_376_ = lean_unbox(v_defVal_375_);
v_res_377_ = l_Lean_Options_getBool(v_o_373_, v_k_374_, v_defVal_boxed_376_);
lean_dec(v_k_374_);
lean_dec_ref(v_o_373_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_contains(lean_object* v_o_379_, lean_object* v_k_380_){
_start:
{
lean_object* v_map_381_; uint8_t v___x_382_; 
v_map_381_ = lean_ctor_get(v_o_379_, 0);
v___x_382_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_380_, v_map_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object* v_o_383_, lean_object* v_k_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Lean_Options_contains(v_o_383_, v_k_384_);
lean_dec(v_k_384_);
lean_dec_ref(v_o_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object* v_o_390_, lean_object* v_k_391_, lean_object* v_v_392_){
_start:
{
lean_object* v_map_393_; uint8_t v_hasTrace_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_407_; 
v_map_393_ = lean_ctor_get(v_o_390_, 0);
v_hasTrace_394_ = lean_ctor_get_uint8(v_o_390_, sizeof(void*)*1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_o_390_);
if (v_isSharedCheck_407_ == 0)
{
v___x_396_ = v_o_390_;
v_isShared_397_ = v_isSharedCheck_407_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_map_393_);
lean_dec(v_o_390_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_407_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; 
lean_inc(v_k_391_);
v___x_398_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_391_, v_v_392_, v_map_393_);
if (v_hasTrace_394_ == 0)
{
lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_402_; 
v___x_399_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_400_ = l_Lean_Name_isPrefixOf(v___x_399_, v_k_391_);
lean_dec(v_k_391_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_402_ = v___x_396_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_398_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*1, v___x_400_);
return v___x_402_;
}
}
else
{
lean_object* v___x_405_; 
lean_dec(v_k_391_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_406_, sizeof(void*)*1, v_hasTrace_394_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object* v_inst_408_, lean_object* v_o_409_, lean_object* v_k_410_, lean_object* v_v_411_){
_start:
{
lean_object* v_toDataValue_412_; lean_object* v_map_413_; uint8_t v_hasTrace_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_428_; 
v_toDataValue_412_ = lean_ctor_get(v_inst_408_, 0);
lean_inc_ref(v_toDataValue_412_);
lean_dec_ref(v_inst_408_);
v_map_413_ = lean_ctor_get(v_o_409_, 0);
v_hasTrace_414_ = lean_ctor_get_uint8(v_o_409_, sizeof(void*)*1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_o_409_);
if (v_isSharedCheck_428_ == 0)
{
v___x_416_ = v_o_409_;
v_isShared_417_ = v_isSharedCheck_428_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_map_413_);
lean_dec(v_o_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_428_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_apply_1(v_toDataValue_412_, v_v_411_);
lean_inc(v_k_410_);
v___x_419_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_410_, v___x_418_, v_map_413_);
if (v_hasTrace_414_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; lean_object* v___x_423_; 
v___x_420_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_421_ = l_Lean_Name_isPrefixOf(v___x_420_, v_k_410_);
lean_dec(v_k_410_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_419_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_421_);
return v___x_423_;
}
}
else
{
lean_object* v___x_426_; 
lean_dec(v_k_410_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_426_ = v___x_416_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*1, v_hasTrace_414_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object* v_00_u03b1_429_, lean_object* v_inst_430_, lean_object* v_o_431_, lean_object* v_k_432_, lean_object* v_v_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Options_set___redArg(v_inst_430_, v_o_431_, v_k_432_, v_v_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool(lean_object* v_o_435_, lean_object* v_k_436_, uint8_t v_v_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_KVMap_instValueBool;
v___x_439_ = lean_box(v_v_437_);
v___x_440_ = l_Lean_Options_set___redArg(v___x_438_, v_o_435_, v_k_436_, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object* v_o_441_, lean_object* v_k_442_, lean_object* v_v_443_){
_start:
{
uint8_t v_v_boxed_444_; lean_object* v_res_445_; 
v_v_boxed_444_ = lean_unbox(v_v_443_);
v_res_445_ = l_Lean_Options_setBool(v_o_441_, v_k_442_, v_v_boxed_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object* v_init_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v_k_448_; lean_object* v_l_449_; lean_object* v_r_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_k_448_ = lean_ctor_get(v_x_447_, 1);
v_l_449_ = lean_ctor_get(v_x_447_, 3);
v_r_450_ = lean_ctor_get(v_x_447_, 4);
v___x_451_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_446_, v_r_450_);
lean_inc(v_k_448_);
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v_k_448_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v_init_446_ = v___x_452_;
v_x_447_ = v_l_449_;
goto _start;
}
else
{
return v_init_446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object* v_init_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v_init_454_, v_x_455_);
lean_dec(v_x_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object* v_k_457_, lean_object* v_t_458_){
_start:
{
if (lean_obj_tag(v_t_458_) == 0)
{
lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v_l_461_; lean_object* v_r_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_1116_; 
v_k_459_ = lean_ctor_get(v_t_458_, 1);
v_v_460_ = lean_ctor_get(v_t_458_, 2);
v_l_461_ = lean_ctor_get(v_t_458_, 3);
v_r_462_ = lean_ctor_get(v_t_458_, 4);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_t_458_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v_t_458_, 0);
lean_dec(v_unused_1117_);
v___x_464_ = v_t_458_;
v_isShared_465_ = v_isSharedCheck_1116_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_r_462_);
lean_inc(v_l_461_);
lean_inc(v_v_460_);
lean_inc(v_k_459_);
lean_dec(v_t_458_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_1116_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_457_, v_k_459_);
switch(v___x_466_)
{
case 0:
{
lean_object* v_impl_467_; lean_object* v___x_468_; 
v_impl_467_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_457_, v_l_461_);
v___x_468_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_467_) == 0)
{
if (lean_obj_tag(v_r_462_) == 0)
{
lean_object* v_size_469_; lean_object* v_size_470_; lean_object* v_k_471_; lean_object* v_v_472_; lean_object* v_l_473_; lean_object* v_r_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_size_469_ = lean_ctor_get(v_impl_467_, 0);
lean_inc(v_size_469_);
v_size_470_ = lean_ctor_get(v_r_462_, 0);
v_k_471_ = lean_ctor_get(v_r_462_, 1);
v_v_472_ = lean_ctor_get(v_r_462_, 2);
v_l_473_ = lean_ctor_get(v_r_462_, 3);
lean_inc(v_l_473_);
v_r_474_ = lean_ctor_get(v_r_462_, 4);
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_nat_mul(v___x_475_, v_size_469_);
v___x_477_ = lean_nat_dec_lt(v___x_476_, v_size_470_);
lean_dec(v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_l_473_);
v___x_478_ = lean_nat_add(v___x_468_, v_size_469_);
lean_dec(v_size_469_);
v___x_479_ = lean_nat_add(v___x_478_, v_size_470_);
lean_dec(v___x_478_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 3, v_impl_467_);
lean_ctor_set(v___x_464_, 0, v___x_479_);
v___x_481_ = v___x_464_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_r_462_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_546_; 
lean_inc(v_r_474_);
lean_inc(v_v_472_);
lean_inc(v_k_471_);
lean_inc(v_size_470_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_547_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_r_462_, 2);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_r_462_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_551_);
v___x_484_ = v_r_462_;
v_isShared_485_ = v_isSharedCheck_546_;
goto v_resetjp_483_;
}
else
{
lean_dec(v_r_462_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_546_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_size_486_; lean_object* v_k_487_; lean_object* v_v_488_; lean_object* v_l_489_; lean_object* v_r_490_; lean_object* v_size_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_size_486_ = lean_ctor_get(v_l_473_, 0);
v_k_487_ = lean_ctor_get(v_l_473_, 1);
v_v_488_ = lean_ctor_get(v_l_473_, 2);
v_l_489_ = lean_ctor_get(v_l_473_, 3);
v_r_490_ = lean_ctor_get(v_l_473_, 4);
v_size_491_ = lean_ctor_get(v_r_474_, 0);
v___x_492_ = lean_unsigned_to_nat(2u);
v___x_493_ = lean_nat_mul(v___x_492_, v_size_491_);
v___x_494_ = lean_nat_dec_lt(v_size_486_, v___x_493_);
lean_dec(v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_522_; 
lean_inc(v_r_490_);
lean_inc(v_l_489_);
lean_inc(v_v_488_);
lean_inc(v_k_487_);
v_isSharedCheck_522_ = !lean_is_exclusive(v_l_473_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; lean_object* v_unused_524_; lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_523_ = lean_ctor_get(v_l_473_, 4);
lean_dec(v_unused_523_);
v_unused_524_ = lean_ctor_get(v_l_473_, 3);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_l_473_, 2);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_l_473_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_l_473_, 0);
lean_dec(v_unused_527_);
v___x_496_ = v_l_473_;
v_isShared_497_ = v_isSharedCheck_522_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_l_473_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_522_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_512_; 
v___x_498_ = lean_nat_add(v___x_468_, v_size_469_);
lean_dec(v_size_469_);
v___x_499_ = lean_nat_add(v___x_498_, v_size_470_);
lean_dec(v_size_470_);
if (lean_obj_tag(v_l_489_) == 0)
{
lean_object* v_size_520_; 
v_size_520_ = lean_ctor_get(v_l_489_, 0);
lean_inc(v_size_520_);
v___y_512_ = v_size_520_;
goto v___jp_511_;
}
else
{
lean_object* v___x_521_; 
v___x_521_ = lean_unsigned_to_nat(0u);
v___y_512_ = v___x_521_;
goto v___jp_511_;
}
v___jp_500_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_nat_add(v___y_501_, v___y_503_);
lean_dec(v___y_503_);
lean_dec(v___y_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 4, v_r_474_);
lean_ctor_set(v___x_496_, 3, v_r_490_);
lean_ctor_set(v___x_496_, 2, v_v_472_);
lean_ctor_set(v___x_496_, 1, v_k_471_);
lean_ctor_set(v___x_496_, 0, v___x_504_);
v___x_506_ = v___x_496_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_r_490_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_r_474_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 4, v___x_506_);
lean_ctor_set(v___x_484_, 3, v___y_502_);
lean_ctor_set(v___x_484_, 2, v_v_488_);
lean_ctor_set(v___x_484_, 1, v_k_487_);
lean_ctor_set(v___x_484_, 0, v___x_499_);
v___x_508_ = v___x_484_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_k_487_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_v_488_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v___y_502_);
lean_ctor_set(v_reuseFailAlloc_509_, 4, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_nat_add(v___x_498_, v___y_512_);
lean_dec(v___y_512_);
lean_dec(v___x_498_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_l_489_);
lean_ctor_set(v___x_464_, 3, v_impl_467_);
lean_ctor_set(v___x_464_, 0, v___x_513_);
v___x_515_ = v___x_464_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_l_489_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_nat_add(v___x_468_, v_size_491_);
if (lean_obj_tag(v_r_490_) == 0)
{
lean_object* v_size_517_; 
v_size_517_ = lean_ctor_get(v_r_490_, 0);
lean_inc(v_size_517_);
v___y_501_ = v___x_516_;
v___y_502_ = v___x_515_;
v___y_503_ = v_size_517_;
goto v___jp_500_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___y_501_ = v___x_516_;
v___y_502_ = v___x_515_;
v___y_503_ = v___x_518_;
goto v___jp_500_;
}
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
lean_del_object(v___x_464_);
v___x_528_ = lean_nat_add(v___x_468_, v_size_469_);
lean_dec(v_size_469_);
v___x_529_ = lean_nat_add(v___x_528_, v_size_470_);
lean_dec(v_size_470_);
v___x_530_ = lean_nat_add(v___x_528_, v_size_486_);
lean_dec(v___x_528_);
lean_inc_ref(v_impl_467_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 4, v_l_473_);
lean_ctor_set(v___x_484_, 3, v_impl_467_);
lean_ctor_set(v___x_484_, 2, v_v_460_);
lean_ctor_set(v___x_484_, 1, v_k_459_);
lean_ctor_set(v___x_484_, 0, v___x_530_);
v___x_532_ = v___x_484_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_l_473_);
v___x_532_ = v_reuseFailAlloc_545_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_isSharedCheck_539_ = !lean_is_exclusive(v_impl_467_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; lean_object* v_unused_544_; 
v_unused_540_ = lean_ctor_get(v_impl_467_, 4);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_impl_467_, 3);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_impl_467_, 2);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_impl_467_, 1);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_impl_467_, 0);
lean_dec(v_unused_544_);
v___x_534_ = v_impl_467_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_dec(v_impl_467_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 4, v_r_474_);
lean_ctor_set(v___x_534_, 3, v___x_532_);
lean_ctor_set(v___x_534_, 2, v_v_472_);
lean_ctor_set(v___x_534_, 1, v_k_471_);
lean_ctor_set(v___x_534_, 0, v___x_529_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_k_471_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_v_472_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_r_474_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v_size_552_ = lean_ctor_get(v_impl_467_, 0);
lean_inc(v_size_552_);
v___x_553_ = lean_nat_add(v___x_468_, v_size_552_);
lean_dec(v_size_552_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 3, v_impl_467_);
lean_ctor_set(v___x_464_, 0, v___x_553_);
v___x_555_ = v___x_464_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_r_462_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
else
{
if (lean_obj_tag(v_r_462_) == 0)
{
lean_object* v_l_557_; 
v_l_557_ = lean_ctor_get(v_r_462_, 3);
lean_inc(v_l_557_);
if (lean_obj_tag(v_l_557_) == 0)
{
lean_object* v_r_558_; 
v_r_558_ = lean_ctor_get(v_r_462_, 4);
lean_inc(v_r_558_);
if (lean_obj_tag(v_r_558_) == 0)
{
lean_object* v_size_559_; lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_574_; 
v_size_559_ = lean_ctor_get(v_r_462_, 0);
v_k_560_ = lean_ctor_get(v_r_462_, 1);
v_v_561_ = lean_ctor_get(v_r_462_, 2);
v_isSharedCheck_574_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_575_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_576_);
v___x_563_ = v_r_462_;
v_isShared_564_ = v_isSharedCheck_574_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_v_561_);
lean_inc(v_k_560_);
lean_inc(v_size_559_);
lean_dec(v_r_462_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_574_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_size_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v_size_565_ = lean_ctor_get(v_l_557_, 0);
v___x_566_ = lean_nat_add(v___x_468_, v_size_559_);
lean_dec(v_size_559_);
v___x_567_ = lean_nat_add(v___x_468_, v_size_565_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 4, v_l_557_);
lean_ctor_set(v___x_563_, 3, v_impl_467_);
lean_ctor_set(v___x_563_, 2, v_v_460_);
lean_ctor_set(v___x_563_, 1, v_k_459_);
lean_ctor_set(v___x_563_, 0, v___x_567_);
v___x_569_ = v___x_563_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_impl_467_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_l_557_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_r_558_);
lean_ctor_set(v___x_464_, 3, v___x_569_);
lean_ctor_set(v___x_464_, 2, v_v_561_);
lean_ctor_set(v___x_464_, 1, v_k_560_);
lean_ctor_set(v___x_464_, 0, v___x_566_);
v___x_571_ = v___x_464_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_r_558_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v_k_577_; lean_object* v_v_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_k_577_ = lean_ctor_get(v_r_462_, 1);
v_v_578_ = lean_ctor_get(v_r_462_, 2);
v_isSharedCheck_601_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; lean_object* v_unused_603_; lean_object* v_unused_604_; 
v_unused_602_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_604_);
v___x_580_ = v_r_462_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_v_578_);
lean_inc(v_k_577_);
lean_dec(v_r_462_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_k_582_; lean_object* v_v_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_597_; 
v_k_582_ = lean_ctor_get(v_l_557_, 1);
v_v_583_ = lean_ctor_get(v_l_557_, 2);
v_isSharedCheck_597_ = !lean_is_exclusive(v_l_557_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_598_ = lean_ctor_get(v_l_557_, 4);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_l_557_, 3);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_l_557_, 0);
lean_dec(v_unused_600_);
v___x_585_ = v_l_557_;
v_isShared_586_ = v_isSharedCheck_597_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_v_583_);
lean_inc(v_k_582_);
lean_dec(v_l_557_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_597_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(3u);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v_r_558_);
lean_ctor_set(v___x_585_, 3, v_r_558_);
lean_ctor_set(v___x_585_, 2, v_v_460_);
lean_ctor_set(v___x_585_, 1, v_k_459_);
lean_ctor_set(v___x_585_, 0, v___x_468_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_r_558_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_r_558_);
v___x_589_ = v_reuseFailAlloc_596_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_591_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 3, v_r_558_);
lean_ctor_set(v___x_580_, 0, v___x_468_);
v___x_591_ = v___x_580_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_k_577_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_v_578_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_r_558_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_r_558_);
v___x_591_ = v_reuseFailAlloc_595_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v___x_591_);
lean_ctor_set(v___x_464_, 3, v___x_589_);
lean_ctor_set(v___x_464_, 2, v_v_583_);
lean_ctor_set(v___x_464_, 1, v_k_582_);
lean_ctor_set(v___x_464_, 0, v___x_587_);
v___x_593_ = v___x_464_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_582_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_583_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_605_; 
v_r_605_ = lean_ctor_get(v_r_462_, 4);
lean_inc(v_r_605_);
if (lean_obj_tag(v_r_605_) == 0)
{
lean_object* v_k_606_; lean_object* v_v_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_618_; 
v_k_606_ = lean_ctor_get(v_r_462_, 1);
v_v_607_ = lean_ctor_get(v_r_462_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_619_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_621_);
v___x_609_ = v_r_462_;
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_v_607_);
lean_inc(v_k_606_);
lean_dec(v_r_462_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(3u);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v_l_557_);
lean_ctor_set(v___x_609_, 2, v_v_460_);
lean_ctor_set(v___x_609_, 1, v_k_459_);
lean_ctor_set(v___x_609_, 0, v___x_468_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_l_557_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_l_557_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_r_605_);
lean_ctor_set(v___x_464_, 3, v___x_613_);
lean_ctor_set(v___x_464_, 2, v_v_607_);
lean_ctor_set(v___x_464_, 1, v_k_606_);
lean_ctor_set(v___x_464_, 0, v___x_611_);
v___x_615_ = v___x_464_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_606_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_r_605_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_size_622_; lean_object* v_k_623_; lean_object* v_v_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_635_; 
v_size_622_ = lean_ctor_get(v_r_462_, 0);
v_k_623_ = lean_ctor_get(v_r_462_, 1);
v_v_624_ = lean_ctor_get(v_r_462_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; lean_object* v_unused_637_; 
v_unused_636_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_637_);
v___x_626_ = v_r_462_;
v_isShared_627_ = v_isSharedCheck_635_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_v_624_);
lean_inc(v_k_623_);
lean_inc(v_size_622_);
lean_dec(v_r_462_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_635_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 3, v_r_605_);
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_size_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_k_623_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_v_624_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_r_605_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_r_605_);
v___x_629_ = v_reuseFailAlloc_634_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(2u);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v___x_629_);
lean_ctor_set(v___x_464_, 3, v_r_605_);
lean_ctor_set(v___x_464_, 0, v___x_630_);
v___x_632_ = v___x_464_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_r_605_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v___x_629_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
else
{
lean_object* v___x_639_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 3, v_r_462_);
lean_ctor_set(v___x_464_, 0, v___x_468_);
v___x_639_ = v___x_464_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_r_462_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_r_462_);
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
case 1:
{
lean_del_object(v___x_464_);
lean_dec(v_v_460_);
lean_dec(v_k_459_);
if (lean_obj_tag(v_l_461_) == 0)
{
if (lean_obj_tag(v_r_462_) == 0)
{
lean_object* v_size_641_; lean_object* v_k_642_; lean_object* v_v_643_; lean_object* v_l_644_; lean_object* v_r_645_; lean_object* v_size_646_; lean_object* v_k_647_; lean_object* v_v_648_; lean_object* v_l_649_; lean_object* v_r_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_size_641_ = lean_ctor_get(v_l_461_, 0);
v_k_642_ = lean_ctor_get(v_l_461_, 1);
v_v_643_ = lean_ctor_get(v_l_461_, 2);
v_l_644_ = lean_ctor_get(v_l_461_, 3);
v_r_645_ = lean_ctor_get(v_l_461_, 4);
lean_inc(v_r_645_);
v_size_646_ = lean_ctor_get(v_r_462_, 0);
v_k_647_ = lean_ctor_get(v_r_462_, 1);
v_v_648_ = lean_ctor_get(v_r_462_, 2);
v_l_649_ = lean_ctor_get(v_r_462_, 3);
lean_inc(v_l_649_);
v_r_650_ = lean_ctor_get(v_r_462_, 4);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_dec_lt(v_size_641_, v_size_646_);
if (v___x_652_ == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_788_; 
lean_inc(v_l_644_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
v_isSharedCheck_788_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_789_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_l_461_, 2);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_l_461_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_793_);
v___x_654_ = v_l_461_;
v_isShared_655_ = v_isSharedCheck_788_;
goto v_resetjp_653_;
}
else
{
lean_dec(v_l_461_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_788_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v_tree_657_; 
v___x_656_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_642_, v_v_643_, v_l_644_, v_r_645_);
v_tree_657_ = lean_ctor_get(v___x_656_, 2);
lean_inc(v_tree_657_);
if (lean_obj_tag(v_tree_657_) == 0)
{
lean_object* v_k_658_; lean_object* v_v_659_; lean_object* v_size_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_k_658_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_k_658_);
v_v_659_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_v_659_);
lean_dec_ref(v___x_656_);
v_size_660_ = lean_ctor_get(v_tree_657_, 0);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_nat_mul(v___x_661_, v_size_660_);
v___x_663_ = lean_nat_dec_lt(v___x_662_, v_size_646_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_l_649_);
v___x_664_ = lean_nat_add(v___x_651_, v_size_660_);
v___x_665_ = lean_nat_add(v___x_664_, v_size_646_);
lean_dec(v___x_664_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_r_462_);
lean_ctor_set(v___x_654_, 3, v_tree_657_);
lean_ctor_set(v___x_654_, 2, v_v_659_);
lean_ctor_set(v___x_654_, 1, v_k_658_);
lean_ctor_set(v___x_654_, 0, v___x_665_);
v___x_667_ = v___x_654_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_658_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_659_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_tree_657_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_r_462_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_723_; 
lean_inc(v_r_650_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
lean_inc(v_size_646_);
v_isSharedCheck_723_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_724_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_r_462_, 2);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_r_462_, 1);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_728_);
v___x_670_ = v_r_462_;
v_isShared_671_ = v_isSharedCheck_723_;
goto v_resetjp_669_;
}
else
{
lean_dec(v_r_462_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_723_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_size_672_; lean_object* v_k_673_; lean_object* v_v_674_; lean_object* v_l_675_; lean_object* v_r_676_; lean_object* v_size_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_size_672_ = lean_ctor_get(v_l_649_, 0);
v_k_673_ = lean_ctor_get(v_l_649_, 1);
v_v_674_ = lean_ctor_get(v_l_649_, 2);
v_l_675_ = lean_ctor_get(v_l_649_, 3);
v_r_676_ = lean_ctor_get(v_l_649_, 4);
v_size_677_ = lean_ctor_get(v_r_650_, 0);
v___x_678_ = lean_unsigned_to_nat(2u);
v___x_679_ = lean_nat_mul(v___x_678_, v_size_677_);
v___x_680_ = lean_nat_dec_lt(v_size_672_, v___x_679_);
lean_dec(v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_708_; 
lean_inc(v_r_676_);
lean_inc(v_l_675_);
lean_inc(v_v_674_);
lean_inc(v_k_673_);
v_isSharedCheck_708_ = !lean_is_exclusive(v_l_649_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_709_ = lean_ctor_get(v_l_649_, 4);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_l_649_, 3);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_l_649_, 2);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_l_649_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_l_649_, 0);
lean_dec(v_unused_713_);
v___x_682_ = v_l_649_;
v_isShared_683_ = v_isSharedCheck_708_;
goto v_resetjp_681_;
}
else
{
lean_dec(v_l_649_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_708_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_698_; 
v___x_684_ = lean_nat_add(v___x_651_, v_size_660_);
v___x_685_ = lean_nat_add(v___x_684_, v_size_646_);
lean_dec(v_size_646_);
if (lean_obj_tag(v_l_675_) == 0)
{
lean_object* v_size_706_; 
v_size_706_ = lean_ctor_get(v_l_675_, 0);
lean_inc(v_size_706_);
v___y_698_ = v_size_706_;
goto v___jp_697_;
}
else
{
lean_object* v___x_707_; 
v___x_707_ = lean_unsigned_to_nat(0u);
v___y_698_ = v___x_707_;
goto v___jp_697_;
}
v___jp_686_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = lean_nat_add(v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 4, v_r_650_);
lean_ctor_set(v___x_682_, 3, v_r_676_);
lean_ctor_set(v___x_682_, 2, v_v_648_);
lean_ctor_set(v___x_682_, 1, v_k_647_);
lean_ctor_set(v___x_682_, 0, v___x_690_);
v___x_692_ = v___x_682_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_r_676_);
lean_ctor_set(v_reuseFailAlloc_696_, 4, v_r_650_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 4, v___x_692_);
lean_ctor_set(v___x_670_, 3, v___y_687_);
lean_ctor_set(v___x_670_, 2, v_v_674_);
lean_ctor_set(v___x_670_, 1, v_k_673_);
lean_ctor_set(v___x_670_, 0, v___x_685_);
v___x_694_ = v___x_670_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_674_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v___y_687_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_nat_add(v___x_684_, v___y_698_);
lean_dec(v___y_698_);
lean_dec(v___x_684_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_l_675_);
lean_ctor_set(v___x_654_, 3, v_tree_657_);
lean_ctor_set(v___x_654_, 2, v_v_659_);
lean_ctor_set(v___x_654_, 1, v_k_658_);
lean_ctor_set(v___x_654_, 0, v___x_699_);
v___x_701_ = v___x_654_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_k_658_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_v_659_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_tree_657_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_l_675_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_nat_add(v___x_651_, v_size_677_);
if (lean_obj_tag(v_r_676_) == 0)
{
lean_object* v_size_703_; 
v_size_703_ = lean_ctor_get(v_r_676_, 0);
lean_inc(v_size_703_);
v___y_687_ = v___x_701_;
v___y_688_ = v___x_702_;
v___y_689_ = v_size_703_;
goto v___jp_686_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___y_687_ = v___x_701_;
v___y_688_ = v___x_702_;
v___y_689_ = v___x_704_;
goto v___jp_686_;
}
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_714_ = lean_nat_add(v___x_651_, v_size_660_);
v___x_715_ = lean_nat_add(v___x_714_, v_size_646_);
lean_dec(v_size_646_);
v___x_716_ = lean_nat_add(v___x_714_, v_size_672_);
lean_dec(v___x_714_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 4, v_l_649_);
lean_ctor_set(v___x_670_, 3, v_tree_657_);
lean_ctor_set(v___x_670_, 2, v_v_659_);
lean_ctor_set(v___x_670_, 1, v_k_658_);
lean_ctor_set(v___x_670_, 0, v___x_716_);
v___x_718_ = v___x_670_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_658_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_659_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_tree_657_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_l_649_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_r_650_);
lean_ctor_set(v___x_654_, 3, v___x_718_);
lean_ctor_set(v___x_654_, 2, v_v_648_);
lean_ctor_set(v___x_654_, 1, v_k_647_);
lean_ctor_set(v___x_654_, 0, v___x_715_);
v___x_720_ = v___x_654_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_r_650_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
else
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_782_; 
lean_inc(v_r_650_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
lean_inc(v_size_646_);
v_isSharedCheck_782_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_783_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_r_462_, 2);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_r_462_, 1);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_787_);
v___x_730_ = v_r_462_;
v_isShared_731_ = v_isSharedCheck_782_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_r_462_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_782_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
if (lean_obj_tag(v_l_649_) == 0)
{
if (lean_obj_tag(v_r_650_) == 0)
{
lean_object* v_k_732_; lean_object* v_v_733_; lean_object* v_size_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v_k_732_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_k_732_);
v_v_733_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_v_733_);
lean_dec_ref(v___x_656_);
v_size_734_ = lean_ctor_get(v_l_649_, 0);
v___x_735_ = lean_nat_add(v___x_651_, v_size_646_);
lean_dec(v_size_646_);
v___x_736_ = lean_nat_add(v___x_651_, v_size_734_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v_l_649_);
lean_ctor_set(v___x_730_, 3, v_tree_657_);
lean_ctor_set(v___x_730_, 2, v_v_733_);
lean_ctor_set(v___x_730_, 1, v_k_732_);
lean_ctor_set(v___x_730_, 0, v___x_736_);
v___x_738_ = v___x_730_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_k_732_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_v_733_);
lean_ctor_set(v_reuseFailAlloc_742_, 3, v_tree_657_);
lean_ctor_set(v_reuseFailAlloc_742_, 4, v_l_649_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_r_650_);
lean_ctor_set(v___x_654_, 3, v___x_738_);
lean_ctor_set(v___x_654_, 2, v_v_648_);
lean_ctor_set(v___x_654_, 1, v_k_647_);
lean_ctor_set(v___x_654_, 0, v___x_735_);
v___x_740_ = v___x_654_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_r_650_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v_k_743_; lean_object* v_v_744_; lean_object* v_k_745_; lean_object* v_v_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_size_646_);
v_k_743_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_k_743_);
v_v_744_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_v_744_);
lean_dec_ref(v___x_656_);
v_k_745_ = lean_ctor_get(v_l_649_, 1);
v_v_746_ = lean_ctor_get(v_l_649_, 2);
v_isSharedCheck_760_ = !lean_is_exclusive(v_l_649_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; 
v_unused_761_ = lean_ctor_get(v_l_649_, 4);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_649_, 3);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_l_649_, 0);
lean_dec(v_unused_763_);
v___x_748_ = v_l_649_;
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_v_746_);
lean_inc(v_k_745_);
lean_dec(v_l_649_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_760_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_unsigned_to_nat(3u);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 4, v_r_650_);
lean_ctor_set(v___x_748_, 3, v_r_650_);
lean_ctor_set(v___x_748_, 2, v_v_744_);
lean_ctor_set(v___x_748_, 1, v_k_743_);
lean_ctor_set(v___x_748_, 0, v___x_651_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_743_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_744_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_r_650_);
v___x_752_ = v_reuseFailAlloc_759_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 3, v_r_650_);
lean_ctor_set(v___x_730_, 0, v___x_651_);
v___x_754_ = v___x_730_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_r_650_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v___x_754_);
lean_ctor_set(v___x_654_, 3, v___x_752_);
lean_ctor_set(v___x_654_, 2, v_v_746_);
lean_ctor_set(v___x_654_, 1, v_k_745_);
lean_ctor_set(v___x_654_, 0, v___x_750_);
v___x_756_ = v___x_654_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_745_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_746_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_650_) == 0)
{
lean_object* v_k_764_; lean_object* v_v_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v_size_646_);
v_k_764_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_k_764_);
v_v_765_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_v_765_);
lean_dec_ref(v___x_656_);
v___x_766_ = lean_unsigned_to_nat(3u);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v_l_649_);
lean_ctor_set(v___x_730_, 2, v_v_765_);
lean_ctor_set(v___x_730_, 1, v_k_764_);
lean_ctor_set(v___x_730_, 0, v___x_651_);
v___x_768_ = v___x_730_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_l_649_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v_r_650_);
lean_ctor_set(v___x_654_, 3, v___x_768_);
lean_ctor_set(v___x_654_, 2, v_v_648_);
lean_ctor_set(v___x_654_, 1, v_k_647_);
lean_ctor_set(v___x_654_, 0, v___x_766_);
v___x_770_ = v___x_654_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_r_650_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_k_773_; lean_object* v_v_774_; lean_object* v___x_776_; 
v_k_773_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_k_773_);
v_v_774_ = lean_ctor_get(v___x_656_, 1);
lean_inc(v_v_774_);
lean_dec_ref(v___x_656_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 3, v_r_650_);
v___x_776_ = v___x_730_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_size_646_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_r_650_);
v___x_776_ = v_reuseFailAlloc_781_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_unsigned_to_nat(2u);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v___x_776_);
lean_ctor_set(v___x_654_, 3, v_r_650_);
lean_ctor_set(v___x_654_, 2, v_v_774_);
lean_ctor_set(v___x_654_, 1, v_k_773_);
lean_ctor_set(v___x_654_, 0, v___x_777_);
v___x_779_ = v___x_654_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_k_773_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_v_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v___x_776_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
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
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_946_; 
lean_inc(v_r_650_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_r_462_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; lean_object* v_unused_950_; lean_object* v_unused_951_; 
v_unused_947_ = lean_ctor_get(v_r_462_, 4);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_r_462_, 3);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_r_462_, 2);
lean_dec(v_unused_949_);
v_unused_950_ = lean_ctor_get(v_r_462_, 1);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_r_462_, 0);
lean_dec(v_unused_951_);
v___x_795_ = v_r_462_;
v_isShared_796_ = v_isSharedCheck_946_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_r_462_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_946_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_tree_798_; 
v___x_797_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_647_, v_v_648_, v_l_649_, v_r_650_);
v_tree_798_ = lean_ctor_get(v___x_797_, 2);
lean_inc(v_tree_798_);
if (lean_obj_tag(v_tree_798_) == 0)
{
lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v_size_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_k_799_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_k_799_);
v_v_800_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_v_800_);
lean_dec_ref(v___x_797_);
v_size_801_ = lean_ctor_get(v_tree_798_, 0);
v___x_802_ = lean_unsigned_to_nat(3u);
v___x_803_ = lean_nat_mul(v___x_802_, v_size_801_);
v___x_804_ = lean_nat_dec_lt(v___x_803_, v_size_641_);
lean_dec(v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
lean_dec(v_r_645_);
v___x_805_ = lean_nat_add(v___x_651_, v_size_641_);
v___x_806_ = lean_nat_add(v___x_805_, v_size_801_);
lean_dec(v___x_805_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_tree_798_);
lean_ctor_set(v___x_795_, 3, v_l_461_);
lean_ctor_set(v___x_795_, 2, v_v_800_);
lean_ctor_set(v___x_795_, 1, v_k_799_);
lean_ctor_set(v___x_795_, 0, v___x_806_);
v___x_808_ = v___x_795_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_tree_798_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_875_; 
lean_inc(v_l_644_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
lean_inc(v_size_641_);
v_isSharedCheck_875_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_876_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_l_461_, 2);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_l_461_, 1);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_880_);
v___x_811_ = v_l_461_;
v_isShared_812_ = v_isSharedCheck_875_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_l_461_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_875_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_size_813_; lean_object* v_size_814_; lean_object* v_k_815_; lean_object* v_v_816_; lean_object* v_l_817_; lean_object* v_r_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_size_813_ = lean_ctor_get(v_l_644_, 0);
v_size_814_ = lean_ctor_get(v_r_645_, 0);
v_k_815_ = lean_ctor_get(v_r_645_, 1);
v_v_816_ = lean_ctor_get(v_r_645_, 2);
v_l_817_ = lean_ctor_get(v_r_645_, 3);
v_r_818_ = lean_ctor_get(v_r_645_, 4);
v___x_819_ = lean_unsigned_to_nat(2u);
v___x_820_ = lean_nat_mul(v___x_819_, v_size_813_);
v___x_821_ = lean_nat_dec_lt(v_size_814_, v___x_820_);
lean_dec(v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_859_; 
lean_inc(v_r_818_);
lean_inc(v_l_817_);
lean_inc(v_v_816_);
lean_inc(v_k_815_);
lean_del_object(v___x_811_);
v_isSharedCheck_859_ = !lean_is_exclusive(v_r_645_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; lean_object* v_unused_864_; 
v_unused_860_ = lean_ctor_get(v_r_645_, 4);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v_r_645_, 3);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_r_645_, 2);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_r_645_, 1);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_r_645_, 0);
lean_dec(v_unused_864_);
v___x_823_ = v_r_645_;
v_isShared_824_ = v_isSharedCheck_859_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_r_645_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_859_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___x_847_; lean_object* v___y_849_; 
v___x_825_ = lean_nat_add(v___x_651_, v_size_641_);
lean_dec(v_size_641_);
v___x_826_ = lean_nat_add(v___x_825_, v_size_801_);
lean_dec(v___x_825_);
v___x_847_ = lean_nat_add(v___x_651_, v_size_813_);
if (lean_obj_tag(v_l_817_) == 0)
{
lean_object* v_size_857_; 
v_size_857_ = lean_ctor_get(v_l_817_, 0);
lean_inc(v_size_857_);
v___y_849_ = v_size_857_;
goto v___jp_848_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___y_849_ = v___x_858_;
goto v___jp_848_;
}
v___jp_827_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_nat_add(v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
lean_inc_ref(v_tree_798_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 4, v_tree_798_);
lean_ctor_set(v___x_823_, 3, v_r_818_);
lean_ctor_set(v___x_823_, 2, v_v_800_);
lean_ctor_set(v___x_823_, 1, v_k_799_);
lean_ctor_set(v___x_823_, 0, v___x_831_);
v___x_833_ = v___x_823_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_r_818_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_tree_798_);
v___x_833_ = v_reuseFailAlloc_846_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v_tree_798_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_841_ = lean_ctor_get(v_tree_798_, 4);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_tree_798_, 3);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_tree_798_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_tree_798_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_tree_798_, 0);
lean_dec(v_unused_845_);
v___x_835_ = v_tree_798_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_tree_798_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 4, v___x_833_);
lean_ctor_set(v___x_835_, 3, v___y_828_);
lean_ctor_set(v___x_835_, 2, v_v_816_);
lean_ctor_set(v___x_835_, 1, v_k_815_);
lean_ctor_set(v___x_835_, 0, v___x_826_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_k_815_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_v_816_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v___y_828_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v___x_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
v___jp_848_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_nat_add(v___x_847_, v___y_849_);
lean_dec(v___y_849_);
lean_dec(v___x_847_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_l_817_);
lean_ctor_set(v___x_795_, 3, v_l_644_);
lean_ctor_set(v___x_795_, 2, v_v_643_);
lean_ctor_set(v___x_795_, 1, v_k_642_);
lean_ctor_set(v___x_795_, 0, v___x_850_);
v___x_852_ = v___x_795_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v_l_817_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; 
v___x_853_ = lean_nat_add(v___x_651_, v_size_801_);
if (lean_obj_tag(v_r_818_) == 0)
{
lean_object* v_size_854_; 
v_size_854_ = lean_ctor_get(v_r_818_, 0);
lean_inc(v_size_854_);
v___y_828_ = v___x_852_;
v___y_829_ = v___x_853_;
v___y_830_ = v_size_854_;
goto v___jp_827_;
}
else
{
lean_object* v___x_855_; 
v___x_855_ = lean_unsigned_to_nat(0u);
v___y_828_ = v___x_852_;
v___y_829_ = v___x_853_;
v___y_830_ = v___x_855_;
goto v___jp_827_;
}
}
}
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_865_ = lean_nat_add(v___x_651_, v_size_641_);
lean_dec(v_size_641_);
v___x_866_ = lean_nat_add(v___x_865_, v_size_801_);
lean_dec(v___x_865_);
v___x_867_ = lean_nat_add(v___x_651_, v_size_801_);
v___x_868_ = lean_nat_add(v___x_867_, v_size_814_);
lean_dec(v___x_867_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_tree_798_);
lean_ctor_set(v___x_795_, 3, v_r_645_);
lean_ctor_set(v___x_795_, 2, v_v_800_);
lean_ctor_set(v___x_795_, 1, v_k_799_);
lean_ctor_set(v___x_795_, 0, v___x_868_);
v___x_870_ = v___x_795_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v_r_645_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v_tree_798_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 4, v___x_870_);
lean_ctor_set(v___x_811_, 0, v___x_866_);
v___x_872_ = v___x_811_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_873_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_873_, 4, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_644_) == 0)
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_904_; 
lean_inc_ref(v_l_644_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
lean_inc(v_size_641_);
v_isSharedCheck_904_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; lean_object* v_unused_906_; lean_object* v_unused_907_; lean_object* v_unused_908_; lean_object* v_unused_909_; 
v_unused_905_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_l_461_, 2);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_l_461_, 1);
lean_dec(v_unused_908_);
v_unused_909_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_909_);
v___x_882_ = v_l_461_;
v_isShared_883_ = v_isSharedCheck_904_;
goto v_resetjp_881_;
}
else
{
lean_dec(v_l_461_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_904_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
if (lean_obj_tag(v_r_645_) == 0)
{
lean_object* v_k_884_; lean_object* v_v_885_; lean_object* v_size_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v_k_884_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_k_884_);
v_v_885_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_v_885_);
lean_dec_ref(v___x_797_);
v_size_886_ = lean_ctor_get(v_r_645_, 0);
v___x_887_ = lean_nat_add(v___x_651_, v_size_641_);
lean_dec(v_size_641_);
v___x_888_ = lean_nat_add(v___x_651_, v_size_886_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_tree_798_);
lean_ctor_set(v___x_795_, 3, v_r_645_);
lean_ctor_set(v___x_795_, 2, v_v_885_);
lean_ctor_set(v___x_795_, 1, v_k_884_);
lean_ctor_set(v___x_795_, 0, v___x_888_);
v___x_890_ = v___x_795_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_884_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_v_885_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_r_645_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_tree_798_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_890_);
lean_ctor_set(v___x_882_, 0, v___x_887_);
v___x_892_ = v___x_882_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_object* v_k_895_; lean_object* v_v_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_size_641_);
v_k_895_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_k_895_);
v_v_896_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_v_896_);
lean_dec_ref(v___x_797_);
v___x_897_ = lean_unsigned_to_nat(3u);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_r_645_);
lean_ctor_set(v___x_795_, 3, v_r_645_);
lean_ctor_set(v___x_795_, 2, v_v_896_);
lean_ctor_set(v___x_795_, 1, v_k_895_);
lean_ctor_set(v___x_795_, 0, v___x_651_);
v___x_899_ = v___x_795_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_k_895_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_v_896_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_r_645_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v_r_645_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_899_);
lean_ctor_set(v___x_882_, 0, v___x_897_);
v___x_901_ = v___x_882_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_645_) == 0)
{
lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_934_; 
lean_inc(v_l_644_);
lean_inc(v_v_643_);
lean_inc(v_k_642_);
v_isSharedCheck_934_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_935_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_l_461_, 2);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_l_461_, 1);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_939_);
v___x_911_ = v_l_461_;
v_isShared_912_ = v_isSharedCheck_934_;
goto v_resetjp_910_;
}
else
{
lean_dec(v_l_461_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_934_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_k_913_; lean_object* v_v_914_; lean_object* v_k_915_; lean_object* v_v_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_930_; 
v_k_913_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_k_913_);
v_v_914_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_v_914_);
lean_dec_ref(v___x_797_);
v_k_915_ = lean_ctor_get(v_r_645_, 1);
v_v_916_ = lean_ctor_get(v_r_645_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v_r_645_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; 
v_unused_931_ = lean_ctor_get(v_r_645_, 4);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_r_645_, 3);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_r_645_, 0);
lean_dec(v_unused_933_);
v___x_918_ = v_r_645_;
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_v_916_);
lean_inc(v_k_915_);
lean_dec(v_r_645_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_unsigned_to_nat(3u);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 4, v_l_644_);
lean_ctor_set(v___x_918_, 3, v_l_644_);
lean_ctor_set(v___x_918_, 2, v_v_643_);
lean_ctor_set(v___x_918_, 1, v_k_642_);
lean_ctor_set(v___x_918_, 0, v___x_651_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_642_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_v_643_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_l_644_);
v___x_922_ = v_reuseFailAlloc_929_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_l_644_);
lean_ctor_set(v___x_795_, 3, v_l_644_);
lean_ctor_set(v___x_795_, 2, v_v_914_);
lean_ctor_set(v___x_795_, 1, v_k_913_);
lean_ctor_set(v___x_795_, 0, v___x_651_);
v___x_924_ = v___x_795_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_k_913_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_v_914_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_l_644_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_l_644_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 4, v___x_924_);
lean_ctor_set(v___x_911_, 3, v___x_922_);
lean_ctor_set(v___x_911_, 2, v_v_916_);
lean_ctor_set(v___x_911_, 1, v_k_915_);
lean_ctor_set(v___x_911_, 0, v___x_920_);
v___x_926_ = v___x_911_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_915_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
lean_object* v_k_940_; lean_object* v_v_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v_k_940_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_k_940_);
v_v_941_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_v_941_);
lean_dec_ref(v___x_797_);
v___x_942_ = lean_unsigned_to_nat(2u);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_r_645_);
lean_ctor_set(v___x_795_, 3, v_l_461_);
lean_ctor_set(v___x_795_, 2, v_v_941_);
lean_ctor_set(v___x_795_, 1, v_k_940_);
lean_ctor_set(v___x_795_, 0, v___x_942_);
v___x_944_ = v___x_795_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_941_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_r_645_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
}
}
else
{
return v_l_461_;
}
}
else
{
return v_r_462_;
}
}
default: 
{
lean_object* v_impl_952_; lean_object* v___x_953_; 
v_impl_952_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_457_, v_r_462_);
v___x_953_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_952_) == 0)
{
if (lean_obj_tag(v_l_461_) == 0)
{
lean_object* v_size_954_; lean_object* v_size_955_; lean_object* v_k_956_; lean_object* v_v_957_; lean_object* v_l_958_; lean_object* v_r_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_size_954_ = lean_ctor_get(v_impl_952_, 0);
lean_inc(v_size_954_);
v_size_955_ = lean_ctor_get(v_l_461_, 0);
v_k_956_ = lean_ctor_get(v_l_461_, 1);
v_v_957_ = lean_ctor_get(v_l_461_, 2);
v_l_958_ = lean_ctor_get(v_l_461_, 3);
v_r_959_ = lean_ctor_get(v_l_461_, 4);
lean_inc(v_r_959_);
v___x_960_ = lean_unsigned_to_nat(3u);
v___x_961_ = lean_nat_mul(v___x_960_, v_size_954_);
v___x_962_ = lean_nat_dec_lt(v___x_961_, v_size_955_);
lean_dec(v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_r_959_);
v___x_963_ = lean_nat_add(v___x_953_, v_size_955_);
v___x_964_ = lean_nat_add(v___x_963_, v_size_954_);
lean_dec(v_size_954_);
lean_dec(v___x_963_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_impl_952_);
lean_ctor_set(v___x_464_, 0, v___x_964_);
v___x_966_ = v___x_464_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_impl_952_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1033_; 
lean_inc(v_l_958_);
lean_inc(v_v_957_);
lean_inc(v_k_956_);
lean_inc(v_size_955_);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; lean_object* v_unused_1037_; lean_object* v_unused_1038_; 
v_unused_1034_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_l_461_, 2);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_l_461_, 1);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_1038_);
v___x_969_ = v_l_461_;
v_isShared_970_ = v_isSharedCheck_1033_;
goto v_resetjp_968_;
}
else
{
lean_dec(v_l_461_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1033_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_size_971_; lean_object* v_size_972_; lean_object* v_k_973_; lean_object* v_v_974_; lean_object* v_l_975_; lean_object* v_r_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_size_971_ = lean_ctor_get(v_l_958_, 0);
v_size_972_ = lean_ctor_get(v_r_959_, 0);
v_k_973_ = lean_ctor_get(v_r_959_, 1);
v_v_974_ = lean_ctor_get(v_r_959_, 2);
v_l_975_ = lean_ctor_get(v_r_959_, 3);
v_r_976_ = lean_ctor_get(v_r_959_, 4);
v___x_977_ = lean_unsigned_to_nat(2u);
v___x_978_ = lean_nat_mul(v___x_977_, v_size_971_);
v___x_979_ = lean_nat_dec_lt(v_size_972_, v___x_978_);
lean_dec(v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1008_; 
lean_inc(v_r_976_);
lean_inc(v_l_975_);
lean_inc(v_v_974_);
lean_inc(v_k_973_);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_r_959_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1009_ = lean_ctor_get(v_r_959_, 4);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_r_959_, 3);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_r_959_, 2);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_r_959_, 1);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_r_959_, 0);
lean_dec(v_unused_1013_);
v___x_981_ = v_r_959_;
v_isShared_982_ = v_isSharedCheck_1008_;
goto v_resetjp_980_;
}
else
{
lean_dec(v_r_959_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1008_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___x_996_; lean_object* v___y_998_; 
v___x_983_ = lean_nat_add(v___x_953_, v_size_955_);
lean_dec(v_size_955_);
v___x_984_ = lean_nat_add(v___x_983_, v_size_954_);
lean_dec(v___x_983_);
v___x_996_ = lean_nat_add(v___x_953_, v_size_971_);
if (lean_obj_tag(v_l_975_) == 0)
{
lean_object* v_size_1006_; 
v_size_1006_ = lean_ctor_get(v_l_975_, 0);
lean_inc(v_size_1006_);
v___y_998_ = v_size_1006_;
goto v___jp_997_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___y_998_ = v___x_1007_;
goto v___jp_997_;
}
v___jp_985_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_nat_add(v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec(v___y_987_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 4, v_impl_952_);
lean_ctor_set(v___x_981_, 3, v_r_976_);
lean_ctor_set(v___x_981_, 2, v_v_460_);
lean_ctor_set(v___x_981_, 1, v_k_459_);
lean_ctor_set(v___x_981_, 0, v___x_989_);
v___x_991_ = v___x_981_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_r_976_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_impl_952_);
v___x_991_ = v_reuseFailAlloc_995_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v___x_991_);
lean_ctor_set(v___x_969_, 3, v___y_986_);
lean_ctor_set(v___x_969_, 2, v_v_974_);
lean_ctor_set(v___x_969_, 1, v_k_973_);
lean_ctor_set(v___x_969_, 0, v___x_984_);
v___x_993_ = v___x_969_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_973_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_974_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v___y_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
v___jp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_nat_add(v___x_996_, v___y_998_);
lean_dec(v___y_998_);
lean_dec(v___x_996_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_l_975_);
lean_ctor_set(v___x_464_, 3, v_l_958_);
lean_ctor_set(v___x_464_, 2, v_v_957_);
lean_ctor_set(v___x_464_, 1, v_k_956_);
lean_ctor_set(v___x_464_, 0, v___x_999_);
v___x_1001_ = v___x_464_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_k_956_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_v_957_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_l_958_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_l_975_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_nat_add(v___x_953_, v_size_954_);
lean_dec(v_size_954_);
if (lean_obj_tag(v_r_976_) == 0)
{
lean_object* v_size_1003_; 
v_size_1003_ = lean_ctor_get(v_r_976_, 0);
lean_inc(v_size_1003_);
v___y_986_ = v___x_1001_;
v___y_987_ = v___x_1002_;
v___y_988_ = v_size_1003_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___y_986_ = v___x_1001_;
v___y_987_ = v___x_1002_;
v___y_988_ = v___x_1004_;
goto v___jp_985_;
}
}
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
lean_del_object(v___x_464_);
v___x_1014_ = lean_nat_add(v___x_953_, v_size_955_);
lean_dec(v_size_955_);
v___x_1015_ = lean_nat_add(v___x_1014_, v_size_954_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_nat_add(v___x_953_, v_size_954_);
lean_dec(v_size_954_);
v___x_1017_ = lean_nat_add(v___x_1016_, v_size_972_);
lean_dec(v___x_1016_);
lean_inc_ref(v_impl_952_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v_impl_952_);
lean_ctor_set(v___x_969_, 3, v_r_959_);
lean_ctor_set(v___x_969_, 2, v_v_460_);
lean_ctor_set(v___x_969_, 1, v_k_459_);
lean_ctor_set(v___x_969_, 0, v___x_1017_);
v___x_1019_ = v___x_969_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_r_959_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_impl_952_);
v___x_1019_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_isSharedCheck_1026_ = !lean_is_exclusive(v_impl_952_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; lean_object* v_unused_1030_; lean_object* v_unused_1031_; 
v_unused_1027_ = lean_ctor_get(v_impl_952_, 4);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_impl_952_, 3);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_impl_952_, 2);
lean_dec(v_unused_1029_);
v_unused_1030_ = lean_ctor_get(v_impl_952_, 1);
lean_dec(v_unused_1030_);
v_unused_1031_ = lean_ctor_get(v_impl_952_, 0);
lean_dec(v_unused_1031_);
v___x_1021_ = v_impl_952_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_dec(v_impl_952_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v___x_1019_);
lean_ctor_set(v___x_1021_, 3, v_l_958_);
lean_ctor_set(v___x_1021_, 2, v_v_957_);
lean_ctor_set(v___x_1021_, 1, v_k_956_);
lean_ctor_set(v___x_1021_, 0, v___x_1015_);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_k_956_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_v_957_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_l_958_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v___x_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v_size_1039_ = lean_ctor_get(v_impl_952_, 0);
lean_inc(v_size_1039_);
v___x_1040_ = lean_nat_add(v___x_953_, v_size_1039_);
lean_dec(v_size_1039_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_impl_952_);
lean_ctor_set(v___x_464_, 0, v___x_1040_);
v___x_1042_ = v___x_464_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_impl_952_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
if (lean_obj_tag(v_l_461_) == 0)
{
lean_object* v_l_1044_; 
v_l_1044_ = lean_ctor_get(v_l_461_, 3);
if (lean_obj_tag(v_l_1044_) == 0)
{
lean_object* v_r_1045_; 
lean_inc_ref(v_l_1044_);
v_r_1045_ = lean_ctor_get(v_l_461_, 4);
lean_inc(v_r_1045_);
if (lean_obj_tag(v_r_1045_) == 0)
{
lean_object* v_size_1046_; lean_object* v_k_1047_; lean_object* v_v_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1061_; 
v_size_1046_ = lean_ctor_get(v_l_461_, 0);
v_k_1047_ = lean_ctor_get(v_l_461_, 1);
v_v_1048_ = lean_ctor_get(v_l_461_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; 
v_unused_1062_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_1063_);
v___x_1050_ = v_l_461_;
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_v_1048_);
lean_inc(v_k_1047_);
lean_inc(v_size_1046_);
lean_dec(v_l_461_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_size_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v_size_1052_ = lean_ctor_get(v_r_1045_, 0);
v___x_1053_ = lean_nat_add(v___x_953_, v_size_1046_);
lean_dec(v_size_1046_);
v___x_1054_ = lean_nat_add(v___x_953_, v_size_1052_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 4, v_impl_952_);
lean_ctor_set(v___x_1050_, 3, v_r_1045_);
lean_ctor_set(v___x_1050_, 2, v_v_460_);
lean_ctor_set(v___x_1050_, 1, v_k_459_);
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_r_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_impl_952_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v___x_1056_);
lean_ctor_set(v___x_464_, 3, v_l_1044_);
lean_ctor_set(v___x_464_, 2, v_v_1048_);
lean_ctor_set(v___x_464_, 1, v_k_1047_);
lean_ctor_set(v___x_464_, 0, v___x_1053_);
v___x_1058_ = v___x_464_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
else
{
lean_object* v_k_1064_; lean_object* v_v_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1076_; 
v_k_1064_ = lean_ctor_get(v_l_461_, 1);
v_v_1065_ = lean_ctor_get(v_l_461_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1077_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_1079_);
v___x_1067_ = v_l_461_;
v_isShared_1068_ = v_isSharedCheck_1076_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_v_1065_);
lean_inc(v_k_1064_);
lean_dec(v_l_461_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1076_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1069_ = lean_unsigned_to_nat(3u);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 3, v_r_1045_);
lean_ctor_set(v___x_1067_, 2, v_v_460_);
lean_ctor_set(v___x_1067_, 1, v_k_459_);
lean_ctor_set(v___x_1067_, 0, v___x_953_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_r_1045_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_r_1045_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v___x_1071_);
lean_ctor_set(v___x_464_, 3, v_l_1044_);
lean_ctor_set(v___x_464_, 2, v_v_1065_);
lean_ctor_set(v___x_464_, 1, v_k_1064_);
lean_ctor_set(v___x_464_, 0, v___x_1069_);
v___x_1073_ = v___x_464_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
else
{
lean_object* v_r_1080_; 
v_r_1080_ = lean_ctor_get(v_l_461_, 4);
lean_inc(v_r_1080_);
if (lean_obj_tag(v_r_1080_) == 0)
{
lean_object* v_k_1081_; lean_object* v_v_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1105_; 
lean_inc(v_l_1044_);
v_k_1081_ = lean_ctor_get(v_l_461_, 1);
v_v_1082_ = lean_ctor_get(v_l_461_, 2);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_l_461_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; lean_object* v_unused_1107_; lean_object* v_unused_1108_; 
v_unused_1106_ = lean_ctor_get(v_l_461_, 4);
lean_dec(v_unused_1106_);
v_unused_1107_ = lean_ctor_get(v_l_461_, 3);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_l_461_, 0);
lean_dec(v_unused_1108_);
v___x_1084_ = v_l_461_;
v_isShared_1085_ = v_isSharedCheck_1105_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_v_1082_);
lean_inc(v_k_1081_);
lean_dec(v_l_461_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1105_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_k_1086_; lean_object* v_v_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1101_; 
v_k_1086_ = lean_ctor_get(v_r_1080_, 1);
v_v_1087_ = lean_ctor_get(v_r_1080_, 2);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_r_1080_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; lean_object* v_unused_1103_; lean_object* v_unused_1104_; 
v_unused_1102_ = lean_ctor_get(v_r_1080_, 4);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_r_1080_, 3);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_r_1080_, 0);
lean_dec(v_unused_1104_);
v___x_1089_ = v_r_1080_;
v_isShared_1090_ = v_isSharedCheck_1101_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_v_1087_);
lean_inc(v_k_1086_);
lean_dec(v_r_1080_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1101_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_unsigned_to_nat(3u);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1044_);
lean_ctor_set(v___x_1089_, 3, v_l_1044_);
lean_ctor_set(v___x_1089_, 2, v_v_1082_);
lean_ctor_set(v___x_1089_, 1, v_k_1081_);
lean_ctor_set(v___x_1089_, 0, v___x_953_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v_l_1044_);
v___x_1093_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 4, v_l_1044_);
lean_ctor_set(v___x_1084_, 2, v_v_460_);
lean_ctor_set(v___x_1084_, 1, v_k_459_);
lean_ctor_set(v___x_1084_, 0, v___x_953_);
v___x_1095_ = v___x_1084_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_l_1044_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_l_1044_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v___x_1095_);
lean_ctor_set(v___x_464_, 3, v___x_1093_);
lean_ctor_set(v___x_464_, 2, v_v_1087_);
lean_ctor_set(v___x_464_, 1, v_k_1086_);
lean_ctor_set(v___x_464_, 0, v___x_1091_);
v___x_1097_ = v___x_464_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(2u);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_r_1080_);
lean_ctor_set(v___x_464_, 0, v___x_1109_);
v___x_1111_ = v___x_464_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_1080_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1114_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 4, v_l_461_);
lean_ctor_set(v___x_464_, 0, v___x_953_);
v___x_1114_ = v___x_464_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_l_461_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_l_461_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
}
else
{
return v_t_458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object* v_k_1118_, lean_object* v_t_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_1118_, v_t_1119_);
lean_dec(v_k_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object* v_o_1123_, lean_object* v_k_1124_){
_start:
{
lean_object* v_map_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
v_map_1125_ = lean_ctor_get(v_o_1123_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_o_1123_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v_o_1123_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_map_1125_);
lean_dec(v_o_1123_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1135_; 
lean_inc(v_map_1125_);
v___x_1129_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_1124_, v_map_1125_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(v___x_1130_, v_map_1125_);
lean_dec(v_map_1125_);
v___x_1132_ = ((lean_object*)(l_Lean_Options_erase___closed__0));
v___x_1133_ = l_List_any___redArg(v___x_1131_, v___x_1132_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1129_);
v___x_1135_ = v___x_1127_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*1, v___x_1133_);
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object* v_o_1138_, lean_object* v_k_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Options_erase(v_o_1138_, v_k_1139_);
lean_dec(v_k_1139_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object* v_00_u03b2_1141_, lean_object* v_k_1142_, lean_object* v_t_1143_, lean_object* v_h_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(v_k_1142_, v_t_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_k_1147_, lean_object* v_t_1148_, lean_object* v_h_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(v_00_u03b2_1146_, v_k_1147_, v_t_1148_, v_h_1149_);
lean_dec(v_k_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object* v_b_u2082_1151_, lean_object* v_f_1152_, lean_object* v_a_1153_, lean_object* v_x_1154_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
lean_object* v___x_1155_; 
lean_dec(v_a_1153_);
lean_dec_ref(v_f_1152_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_b_u2082_1151_);
return v___x_1155_;
}
else
{
lean_object* v_val_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1164_; 
v_val_1156_ = lean_ctor_get(v_x_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1158_ = v_x_1154_;
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_val_1156_);
lean_dec(v_x_1154_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_apply_3(v_f_1152_, v_a_1153_, v_val_1156_, v_b_u2082_1151_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object* v_b_u2082_1165_, lean_object* v_f_1166_, lean_object* v_a_1167_, lean_object* v_k_1168_, lean_object* v_t_1169_){
_start:
{
if (lean_obj_tag(v_t_1169_) == 0)
{
lean_object* v_size_1170_; lean_object* v_k_1171_; lean_object* v_v_1172_; lean_object* v_l_1173_; lean_object* v_r_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1189_; 
v_size_1170_ = lean_ctor_get(v_t_1169_, 0);
v_k_1171_ = lean_ctor_get(v_t_1169_, 1);
v_v_1172_ = lean_ctor_get(v_t_1169_, 2);
v_l_1173_ = lean_ctor_get(v_t_1169_, 3);
v_r_1174_ = lean_ctor_get(v_t_1169_, 4);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_t_1169_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1176_ = v_t_1169_;
v_isShared_1177_ = v_isSharedCheck_1189_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_r_1174_);
lean_inc(v_l_1173_);
lean_inc(v_v_1172_);
lean_inc(v_k_1171_);
lean_inc(v_size_1170_);
lean_dec(v_t_1169_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1189_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
uint8_t v___x_1178_; 
v___x_1178_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1168_, v_k_1171_);
switch(v___x_1178_)
{
case 0:
{
lean_object* v_impl_1179_; lean_object* v___x_1180_; 
lean_del_object(v___x_1176_);
lean_dec(v_size_1170_);
v_impl_1179_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1165_, v_f_1166_, v_a_1167_, v_k_1168_, v_l_1173_);
v___x_1180_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1171_, v_v_1172_, v_impl_1179_, v_r_1174_);
return v___x_1180_;
}
case 1:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_val_1183_; lean_object* v___x_1185_; 
lean_dec(v_k_1171_);
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_v_1172_);
v___x_1182_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1165_, v_f_1166_, v_a_1167_, v___x_1181_);
v_val_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_val_1183_);
lean_dec(v___x_1182_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 2, v_val_1183_);
lean_ctor_set(v___x_1176_, 1, v_k_1168_);
v___x_1185_ = v___x_1176_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_size_1170_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_1168_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_val_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_l_1173_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_r_1174_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
default: 
{
lean_object* v_impl_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1176_);
lean_dec(v_size_1170_);
v_impl_1187_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1165_, v_f_1166_, v_a_1167_, v_k_1168_, v_r_1174_);
v___x_1188_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_1171_, v_v_1172_, v_l_1173_, v_impl_1187_);
return v___x_1188_;
}
}
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_val_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(v_b_u2082_1165_, v_f_1166_, v_a_1167_, v___x_1190_);
v_val_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1192_);
lean_dec(v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_k_1168_);
lean_ctor_set(v___x_1194_, 2, v_val_1192_);
lean_ctor_set(v___x_1194_, 3, v_t_1169_);
lean_ctor_set(v___x_1194_, 4, v_t_1169_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object* v_f_1195_, lean_object* v_init_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
lean_object* v_k_1198_; lean_object* v_v_1199_; lean_object* v_l_1200_; lean_object* v_r_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_k_1198_ = lean_ctor_get(v_x_1197_, 1);
lean_inc(v_k_1198_);
v_v_1199_ = lean_ctor_get(v_x_1197_, 2);
lean_inc(v_v_1199_);
v_l_1200_ = lean_ctor_get(v_x_1197_, 3);
lean_inc(v_l_1200_);
v_r_1201_ = lean_ctor_get(v_x_1197_, 4);
lean_inc(v_r_1201_);
lean_dec_ref(v_x_1197_);
lean_inc_ref(v_f_1195_);
v___x_1202_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1195_, v_init_1196_, v_l_1200_);
lean_inc(v_k_1198_);
lean_inc_ref(v_f_1195_);
v___x_1203_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_v_1199_, v_f_1195_, v_k_1198_, v_k_1198_, v___x_1202_);
v_init_1196_ = v___x_1203_;
v_x_1197_ = v_r_1201_;
goto _start;
}
else
{
lean_dec_ref(v_f_1195_);
return v_init_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object* v_f_1205_, lean_object* v_o1_1206_, lean_object* v_o2_1207_){
_start:
{
lean_object* v_map_1208_; uint8_t v_hasTrace_1209_; lean_object* v_map_1210_; uint8_t v_hasTrace_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1222_; 
v_map_1208_ = lean_ctor_get(v_o1_1206_, 0);
lean_inc(v_map_1208_);
v_hasTrace_1209_ = lean_ctor_get_uint8(v_o1_1206_, sizeof(void*)*1);
lean_dec_ref(v_o1_1206_);
v_map_1210_ = lean_ctor_get(v_o2_1207_, 0);
v_hasTrace_1211_ = lean_ctor_get_uint8(v_o2_1207_, sizeof(void*)*1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_o2_1207_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1213_ = v_o2_1207_;
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_map_1210_);
lean_dec(v_o2_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1222_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1205_, v_map_1208_, v_map_1210_);
if (v_hasTrace_1209_ == 0)
{
lean_object* v___x_1217_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*1, v_hasTrace_1211_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
else
{
lean_object* v___x_1220_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1220_ = v___x_1213_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*1, v_hasTrace_1209_);
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object* v_b_u2082_1223_, lean_object* v_f_1224_, lean_object* v_a_1225_, lean_object* v_k_1226_, lean_object* v_t_1227_, lean_object* v_hl_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(v_b_u2082_1223_, v_f_1224_, v_a_1225_, v_k_1226_, v_t_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object* v_f_1230_, lean_object* v_init_1231_, lean_object* v_t_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(v_f_1230_, v_init_1231_, v_t_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__12(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
v___x_1261_ = l_Lean_mkAtom(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
v___x_1263_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1264_ = lean_array_push(v___x_1263_, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
v___x_1274_ = l_Lean_mkAtom(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
v___x_1276_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1277_ = lean_array_push(v___x_1276_, v___x_1275_);
return v___x_1277_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
v___x_1279_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
v___x_1280_ = lean_box(2);
v___x_1281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_ctor_set(v___x_1281_, 2, v___x_1278_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
v___x_1283_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
v___x_1284_ = lean_array_push(v___x_1283_, v___x_1282_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
v___x_1286_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
v___x_1287_ = lean_box(2);
v___x_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1286_);
lean_ctor_set(v___x_1288_, 2, v___x_1285_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
v___x_1290_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1291_ = lean_array_push(v___x_1290_, v___x_1289_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
v___x_1293_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_1294_ = lean_box(2);
v___x_1295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
lean_ctor_set(v___x_1295_, 2, v___x_1292_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
v___x_1297_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1298_ = lean_array_push(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
v___x_1300_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
v___x_1301_ = lean_box(2);
v___x_1302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1300_);
lean_ctor_set(v___x_1302_, 2, v___x_1299_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
v___x_1304_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___x_1305_ = lean_array_push(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1306_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
v___x_1307_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
v___x_1308_ = lean_box(2);
v___x_1309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v___x_1307_);
lean_ctor_set(v___x_1309_, 2, v___x_1306_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1310_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__1(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__0));
v___x_1313_ = l_Lean_instInhabitedDataValue_default;
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set(v___x_1315_, 2, v___x_1313_);
lean_ctor_set(v___x_1315_, 3, v___x_1312_);
return v___x_1315_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__1, &l_Lean_instInhabitedOptionDecl_default___closed__1_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__1);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_instInhabitedOptionDecl_default;
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* v_self_1323_){
_start:
{
lean_object* v_descr_1325_; lean_object* v_name_1328_; lean_object* v_descr_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_name_1328_ = lean_ctor_get(v_self_1323_, 0);
lean_inc(v_name_1328_);
v_descr_1329_ = lean_ctor_get(v_self_1323_, 3);
lean_inc_ref(v_descr_1329_);
lean_dec_ref(v_self_1323_);
v___x_1330_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
v___x_1331_ = l_Lean_Name_isPrefixOf(v___x_1330_, v_name_1328_);
lean_dec(v_name_1328_);
if (v___x_1331_ == 0)
{
return v_descr_1329_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = lean_string_utf8_byte_size(v_descr_1329_);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_nat_dec_eq(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v_descr_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
v_descr_1336_ = lean_string_append(v_descr_1329_, v___x_1335_);
v_descr_1325_ = v_descr_1336_;
goto v___jp_1324_;
}
else
{
v_descr_1325_ = v_descr_1329_;
goto v___jp_1324_;
}
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v_descr_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
v_descr_1327_ = lean_string_append(v_descr_1325_, v___x_1326_);
return v_descr_1327_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_box(1);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_box(1);
v___x_1340_ = lean_st_mk_ref(v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return v_res_1343_;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_registerOption___closed__0));
v___x_1346_ = lean_mk_io_user_error(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* v_name_1349_, lean_object* v_decl_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1379_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1379_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1379_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_unbox(v_a_1353_);
lean_dec(v_a_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_dec_ref(v_decl_1350_);
lean_dec(v_name_1349_);
v___x_1358_ = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 0, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1363_ = lean_st_ref_get(v___x_1362_);
v___x_1364_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1349_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1349_, v_decl_1350_, v___x_1363_);
v___x_1366_ = lean_st_ref_set(v___x_1362_, v___x_1365_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1366_);
v___x_1368_ = v___x_1355_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v___x_1363_);
lean_dec_ref(v_decl_1350_);
v___x_1370_ = ((lean_object*)(l_Lean_registerOption___closed__2));
v___x_1371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1349_, v___x_1364_);
v___x_1372_ = lean_string_append(v___x_1370_, v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = ((lean_object*)(l_Lean_registerOption___closed__3));
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_mk_io_user_error(v___x_1374_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 0, v___x_1375_);
v___x_1377_ = v___x_1355_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v_decl_1350_);
lean_dec(v_name_1349_);
v_a_1380_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1352_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1352_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* v_name_1388_, lean_object* v_decl_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = lean_register_option(v_name_1388_, v_decl_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
v___x_1394_ = lean_st_ref_get(v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_getOptionDecls();
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* v_init_1398_, lean_object* v_x_1399_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_l_1402_; lean_object* v_r_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_k_1400_ = lean_ctor_get(v_x_1399_, 1);
v_v_1401_ = lean_ctor_get(v_x_1399_, 2);
v_l_1402_ = lean_ctor_get(v_x_1399_, 3);
v_r_1403_ = lean_ctor_get(v_x_1399_, 4);
v___x_1404_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1398_, v_l_1402_);
lean_inc(v_v_1401_);
lean_inc(v_k_1400_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_k_1400_);
lean_ctor_set(v___x_1405_, 1, v_v_1401_);
v___x_1406_ = lean_array_push(v___x_1404_, v___x_1405_);
v_init_1398_ = v___x_1406_;
v_x_1399_ = v_r_1403_;
goto _start;
}
else
{
return v_init_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* v_init_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1408_, v_x_1409_);
lean_dec(v_x_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(){
_start:
{
lean_object* v___x_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1424_; 
v___x_1414_ = l_Lean_getOptionDecls();
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
v___x_1420_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v___x_1419_, v_a_1415_);
lean_dec(v_a_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1420_);
v___x_1422_ = v___x_1417_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = lean_get_option_decls_array();
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* v_init_1427_, lean_object* v_t_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(v_init_1427_, v_t_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* v_init_1430_, lean_object* v_t_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(v_init_1430_, v_t_1431_);
lean_dec(v_t_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* v_name_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1457_; 
v___x_1437_ = l_Lean_getOptionDecls();
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1457_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1457_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1438_, v_name_1435_);
lean_dec(v_a_1438_);
if (lean_obj_tag(v___x_1442_) == 1)
{
lean_object* v_val_1443_; lean_object* v___x_1445_; 
lean_dec(v_name_1435_);
v_val_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_val_1443_);
lean_dec_ref(v___x_1442_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_val_1443_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_val_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
lean_dec(v___x_1442_);
v___x_1447_ = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
v___x_1448_ = 1;
v___x_1449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1435_, v___x_1448_);
v___x_1450_ = lean_string_append(v___x_1447_, v___x_1449_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
v___x_1452_ = lean_string_append(v___x_1450_, v___x_1451_);
v___x_1453_ = lean_mk_io_user_error(v___x_1452_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
lean_ctor_set(v___x_1440_, 0, v___x_1453_);
v___x_1455_ = v___x_1440_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* v_name_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_getOptionDecl(v_name_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* v_name_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_getOptionDecl(v_name_1461_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_defValue_1468_; lean_object* v___x_1470_; 
v_defValue_1468_ = lean_ctor_get(v_a_1464_, 2);
lean_inc_ref(v_defValue_1468_);
lean_dec(v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_defValue_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_defValue_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1463_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1463_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* v_name_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_getOptionDefaultValue(v_name_1481_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* v_name_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_getOptionDecl(v_name_1484_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_descr_1491_; lean_object* v___x_1493_; 
v_descr_1491_ = lean_ctor_get(v_a_1487_, 3);
lean_inc_ref(v_descr_1491_);
lean_dec(v_a_1487_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v_descr_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_descr_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1486_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1486_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* v_name_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_getOptionDescr(v_name_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* v_inst_1507_, lean_object* v_inst_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_apply_2(v_inst_1507_, lean_box(0), v_inst_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* v_m_1510_, lean_object* v_n_1511_, lean_object* v_inst_1512_, lean_object* v_inst_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_apply_2(v_inst_1512_, lean_box(0), v_inst_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* v_k_1515_, lean_object* v_toPure_1516_, uint8_t v_defValue_1517_, lean_object* v_opts_1518_){
_start:
{
lean_object* v_map_1519_; lean_object* v___x_1520_; 
v_map_1519_ = lean_ctor_get(v_opts_1518_, 0);
v___x_1520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1519_, v_k_1515_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_box(v_defValue_1517_);
v___x_1522_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1521_);
return v___x_1522_;
}
else
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___x_1520_);
if (lean_obj_tag(v_val_1523_) == 1)
{
uint8_t v_v_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_v_1524_ = lean_ctor_get_uint8(v_val_1523_, 0);
lean_dec_ref(v_val_1523_);
v___x_1525_ = lean_box(v_v_1524_);
v___x_1526_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1525_);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_val_1523_);
v___x_1527_ = lean_box(v_defValue_1517_);
v___x_1528_ = lean_apply_2(v_toPure_1516_, lean_box(0), v___x_1527_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* v_k_1529_, lean_object* v_toPure_1530_, lean_object* v_defValue_1531_, lean_object* v_opts_1532_){
_start:
{
uint8_t v_defValue_boxed_1533_; lean_object* v_res_1534_; 
v_defValue_boxed_1533_ = lean_unbox(v_defValue_1531_);
v_res_1534_ = l_Lean_getBoolOption___redArg___lam__0(v_k_1529_, v_toPure_1530_, v_defValue_boxed_1533_, v_opts_1532_);
lean_dec_ref(v_opts_1532_);
lean_dec(v_k_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* v_inst_1535_, lean_object* v_inst_1536_, lean_object* v_k_1537_, uint8_t v_defValue_1538_){
_start:
{
lean_object* v_toApplicative_1539_; lean_object* v_toBind_1540_; lean_object* v_toPure_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; lean_object* v___x_1544_; 
v_toApplicative_1539_ = lean_ctor_get(v_inst_1535_, 0);
lean_inc_ref(v_toApplicative_1539_);
v_toBind_1540_ = lean_ctor_get(v_inst_1535_, 1);
lean_inc(v_toBind_1540_);
lean_dec_ref(v_inst_1535_);
v_toPure_1541_ = lean_ctor_get(v_toApplicative_1539_, 1);
lean_inc(v_toPure_1541_);
lean_dec_ref(v_toApplicative_1539_);
v___x_1542_ = lean_box(v_defValue_1538_);
v___f_1543_ = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1543_, 0, v_k_1537_);
lean_closure_set(v___f_1543_, 1, v_toPure_1541_);
lean_closure_set(v___f_1543_, 2, v___x_1542_);
v___x_1544_ = lean_apply_4(v_toBind_1540_, lean_box(0), lean_box(0), v_inst_1536_, v___f_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_k_1547_, lean_object* v_defValue_1548_){
_start:
{
uint8_t v_defValue_boxed_1549_; lean_object* v_res_1550_; 
v_defValue_boxed_1549_ = lean_unbox(v_defValue_1548_);
v_res_1550_ = l_Lean_getBoolOption___redArg(v_inst_1545_, v_inst_1546_, v_k_1547_, v_defValue_boxed_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* v_m_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_k_1554_, uint8_t v_defValue_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_getBoolOption___redArg(v_inst_1552_, v_inst_1553_, v_k_1554_, v_defValue_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* v_m_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_k_1560_, lean_object* v_defValue_1561_){
_start:
{
uint8_t v_defValue_boxed_1562_; lean_object* v_res_1563_; 
v_defValue_boxed_1562_ = lean_unbox(v_defValue_1561_);
v_res_1563_ = l_Lean_getBoolOption(v_m_1557_, v_inst_1558_, v_inst_1559_, v_k_1560_, v_defValue_boxed_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* v_k_1564_, lean_object* v_toPure_1565_, lean_object* v_defValue_1566_, lean_object* v_opts_1567_){
_start:
{
lean_object* v_map_1568_; lean_object* v___x_1569_; 
v_map_1568_ = lean_ctor_get(v_opts_1567_, 0);
v___x_1569_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1568_, v_k_1564_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_apply_2(v_toPure_1565_, lean_box(0), v_defValue_1566_);
return v___x_1570_;
}
else
{
lean_object* v_val_1571_; 
v_val_1571_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v___x_1569_);
if (lean_obj_tag(v_val_1571_) == 3)
{
lean_object* v_v_1572_; lean_object* v___x_1573_; 
lean_dec(v_defValue_1566_);
v_v_1572_ = lean_ctor_get(v_val_1571_, 0);
lean_inc(v_v_1572_);
lean_dec_ref(v_val_1571_);
v___x_1573_ = lean_apply_2(v_toPure_1565_, lean_box(0), v_v_1572_);
return v___x_1573_;
}
else
{
lean_object* v___x_1574_; 
lean_dec(v_val_1571_);
v___x_1574_ = lean_apply_2(v_toPure_1565_, lean_box(0), v_defValue_1566_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* v_k_1575_, lean_object* v_toPure_1576_, lean_object* v_defValue_1577_, lean_object* v_opts_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_getNatOption___redArg___lam__0(v_k_1575_, v_toPure_1576_, v_defValue_1577_, v_opts_1578_);
lean_dec_ref(v_opts_1578_);
lean_dec(v_k_1575_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_k_1582_, lean_object* v_defValue_1583_){
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
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1587_, 0, v_k_1582_);
lean_closure_set(v___f_1587_, 1, v_toPure_1586_);
lean_closure_set(v___f_1587_, 2, v_defValue_1583_);
v___x_1588_ = lean_apply_4(v_toBind_1585_, lean_box(0), lean_box(0), v_inst_1581_, v___f_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* v_m_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_k_1592_, lean_object* v_defValue_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_getNatOption___redArg(v_inst_1590_, v_inst_1591_, v_k_1592_, v_defValue_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* v_inst_1595_, lean_object* v_f_1596_, lean_object* v_00_u03b2_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_apply_3(v_inst_1595_, lean_box(0), v_f_1596_, v___y_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_00_u03b1_1602_, lean_object* v_f_1603_, lean_object* v_x_1604_){
_start:
{
lean_object* v___f_1605_; lean_object* v___x_1606_; 
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1605_, 0, v_inst_1600_);
lean_closure_set(v___f_1605_, 1, v_f_1603_);
v___x_1606_ = lean_apply_3(v_inst_1601_, lean_box(0), v___f_1605_, v_x_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* v_inst_1607_, lean_object* v_inst_1608_){
_start:
{
lean_object* v___f_1609_; 
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1609_, 0, v_inst_1608_);
lean_closure_set(v___f_1609_, 1, v_inst_1607_);
return v___f_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* v_m_1610_, lean_object* v_n_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_){
_start:
{
lean_object* v___f_1614_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1614_, 0, v_inst_1613_);
lean_closure_set(v___f_1614_, 1, v_inst_1612_);
return v___f_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* v___x_1618_, lean_object* v_o_1619_){
_start:
{
lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1620_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1621_ = 1;
v___x_1622_ = lean_box(v___x_1621_);
v___x_1623_ = l_Lean_Options_set___redArg(v___x_1618_, v_o_1619_, v___x_1620_, v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___f_1625_; 
v___x_1624_ = l_Lean_KVMap_instValueBool;
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1625_, 0, v___x_1624_);
return v___f_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* v_inst_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___f_1628_; lean_object* v___x_1629_; 
v___f_1628_ = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
v___x_1629_ = lean_apply_3(v_inst_1626_, lean_box(0), v___f_1628_, v_x_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* v_m_1630_, lean_object* v_00_u03b1_1631_, lean_object* v_inst_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_withInPattern___redArg(v_inst_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* v_o_1635_){
_start:
{
lean_object* v_map_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; lean_object* v___x_1639_; 
v_map_1636_ = lean_ctor_get(v_o_1635_, 0);
v___x_1637_ = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
v___x_1638_ = 0;
v___x_1639_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1636_, v___x_1637_);
if (lean_obj_tag(v___x_1639_) == 0)
{
return v___x_1638_;
}
else
{
lean_object* v_val_1640_; 
v_val_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_val_1640_);
lean_dec_ref(v___x_1639_);
if (lean_obj_tag(v_val_1640_) == 1)
{
uint8_t v_v_1641_; 
v_v_1641_ = lean_ctor_get_uint8(v_val_1640_, 0);
lean_dec_ref(v_val_1640_);
return v_v_1641_;
}
else
{
lean_dec(v_val_1640_);
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* v_o_1642_){
_start:
{
uint8_t v_res_1643_; lean_object* v_r_1644_; 
v_res_1643_ = l_Lean_Options_getInPattern(v_o_1642_);
lean_dec_ref(v_o_1642_);
v_r_1644_ = lean_box(v_res_1643_);
return v_r_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* v_inst_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
lean_ctor_set(v___x_1647_, 1, v_inst_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* v_a_1648_, lean_object* v_inst_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* v_inst_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* v_a_1653_, lean_object* v_inst_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_instInhabitedOption_default___redArg(v_inst_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* v_inst_1656_, lean_object* v_opts_1657_, lean_object* v_opt_1658_){
_start:
{
lean_object* v_name_1659_; lean_object* v_map_1660_; lean_object* v_ofDataValue_x3f_1661_; lean_object* v___x_1662_; 
v_name_1659_ = lean_ctor_get(v_opt_1658_, 0);
v_map_1660_ = lean_ctor_get(v_opts_1657_, 0);
v_ofDataValue_x3f_1661_ = lean_ctor_get(v_inst_1656_, 1);
lean_inc_ref(v_ofDataValue_x3f_1661_);
lean_dec_ref(v_inst_1656_);
v___x_1662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1660_, v_name_1659_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref(v_ofDataValue_x3f_1661_);
v___x_1663_ = lean_box(0);
return v___x_1663_;
}
else
{
lean_object* v_val_1664_; lean_object* v___x_1665_; 
v_val_1664_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_val_1664_);
lean_dec_ref(v___x_1662_);
v___x_1665_ = lean_apply_1(v_ofDataValue_x3f_1661_, v_val_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* v_inst_1666_, lean_object* v_opts_1667_, lean_object* v_opt_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_Option_get_x3f___redArg(v_inst_1666_, v_opts_1667_, v_opt_1668_);
lean_dec_ref(v_opt_1668_);
lean_dec_ref(v_opts_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* v_00_u03b1_1670_, lean_object* v_inst_1671_, lean_object* v_opts_1672_, lean_object* v_opt_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Option_get_x3f___redArg(v_inst_1671_, v_opts_1672_, v_opt_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_inst_1676_, lean_object* v_opts_1677_, lean_object* v_opt_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Option_get_x3f(v_00_u03b1_1675_, v_inst_1676_, v_opts_1677_, v_opt_1678_);
lean_dec_ref(v_opt_1678_);
lean_dec_ref(v_opts_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* v_inst_1680_, lean_object* v_opts_1681_, lean_object* v_opt_1682_){
_start:
{
lean_object* v_name_1683_; lean_object* v_defValue_1684_; lean_object* v_map_1685_; lean_object* v_ofDataValue_x3f_1686_; lean_object* v___x_1687_; 
v_name_1683_ = lean_ctor_get(v_opt_1682_, 0);
v_defValue_1684_ = lean_ctor_get(v_opt_1682_, 1);
v_map_1685_ = lean_ctor_get(v_opts_1681_, 0);
v_ofDataValue_x3f_1686_ = lean_ctor_get(v_inst_1680_, 1);
lean_inc_ref(v_ofDataValue_x3f_1686_);
lean_dec_ref(v_inst_1680_);
v___x_1687_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1685_, v_name_1683_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_1686_);
lean_inc(v_defValue_1684_);
return v_defValue_1684_;
}
else
{
lean_object* v_val_1688_; lean_object* v___x_1689_; 
v_val_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1688_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = lean_apply_1(v_ofDataValue_x3f_1686_, v_val_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_inc(v_defValue_1684_);
return v_defValue_1684_;
}
else
{
lean_object* v_val_1690_; 
v_val_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_val_1690_);
lean_dec_ref(v___x_1689_);
return v_val_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* v_inst_1691_, lean_object* v_opts_1692_, lean_object* v_opt_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Option_get___redArg(v_inst_1691_, v_opts_1692_, v_opt_1693_);
lean_dec_ref(v_opt_1693_);
lean_dec_ref(v_opts_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* v_00_u03b1_1695_, lean_object* v_inst_1696_, lean_object* v_opts_1697_, lean_object* v_opt_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Option_get___redArg(v_inst_1696_, v_opts_1697_, v_opt_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_inst_1701_, lean_object* v_opts_1702_, lean_object* v_opt_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Option_get(v_00_u03b1_1700_, v_inst_1701_, v_opts_1702_, v_opt_1703_);
lean_dec_ref(v_opt_1703_);
lean_dec_ref(v_opts_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* v_opts_1705_, lean_object* v_name_1706_, uint8_t v_defValue_1707_){
_start:
{
lean_object* v_map_1708_; lean_object* v___x_1709_; 
v_map_1708_ = lean_ctor_get(v_opts_1705_, 0);
lean_inc(v_map_1708_);
lean_dec_ref(v_opts_1705_);
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1708_, v_name_1706_);
lean_dec(v_name_1706_);
lean_dec(v_map_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
return v_defValue_1707_;
}
else
{
lean_object* v_val_1710_; 
v_val_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_val_1710_);
lean_dec_ref(v___x_1709_);
if (lean_obj_tag(v_val_1710_) == 1)
{
uint8_t v_v_1711_; 
v_v_1711_ = lean_ctor_get_uint8(v_val_1710_, 0);
lean_dec_ref(v_val_1710_);
return v_v_1711_;
}
else
{
lean_dec(v_val_1710_);
return v_defValue_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* v_opts_1712_, lean_object* v_name_1713_, lean_object* v_defValue_1714_){
_start:
{
uint8_t v_defValue_boxed_1715_; uint8_t v_res_1716_; lean_object* v_r_1717_; 
v_defValue_boxed_1715_ = lean_unbox(v_defValue_1714_);
v_res_1716_ = lean_options_get_bool(v_opts_1712_, v_name_1713_, v_defValue_boxed_1715_);
v_r_1717_ = lean_box(v_res_1716_);
return v_r_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* v_inst_1718_, lean_object* v_opt_1719_, lean_object* v_toPure_1720_, lean_object* v_____do__lift_1721_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = l_Lean_Option_get___redArg(v_inst_1718_, v_____do__lift_1721_, v_opt_1719_);
v___x_1723_ = lean_apply_2(v_toPure_1720_, lean_box(0), v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* v_inst_1724_, lean_object* v_opt_1725_, lean_object* v_toPure_1726_, lean_object* v_____do__lift_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_Option_getM___redArg___lam__0(v_inst_1724_, v_opt_1725_, v_toPure_1726_, v_____do__lift_1727_);
lean_dec_ref(v_____do__lift_1727_);
lean_dec_ref(v_opt_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_opt_1732_){
_start:
{
lean_object* v_toApplicative_1733_; lean_object* v_toBind_1734_; lean_object* v_toPure_1735_; lean_object* v___f_1736_; lean_object* v___x_1737_; 
v_toApplicative_1733_ = lean_ctor_get(v_inst_1729_, 0);
lean_inc_ref(v_toApplicative_1733_);
v_toBind_1734_ = lean_ctor_get(v_inst_1729_, 1);
lean_inc(v_toBind_1734_);
lean_dec_ref(v_inst_1729_);
v_toPure_1735_ = lean_ctor_get(v_toApplicative_1733_, 1);
lean_inc(v_toPure_1735_);
lean_dec_ref(v_toApplicative_1733_);
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1736_, 0, v_inst_1731_);
lean_closure_set(v___f_1736_, 1, v_opt_1732_);
lean_closure_set(v___f_1736_, 2, v_toPure_1735_);
v___x_1737_ = lean_apply_4(v_toBind_1734_, lean_box(0), lean_box(0), v_inst_1730_, v___f_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* v_m_1738_, lean_object* v_00_u03b1_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_opt_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Option_getM___redArg(v_inst_1740_, v_inst_1741_, v_inst_1742_, v_opt_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* v_inst_1745_, lean_object* v_opts_1746_, lean_object* v_opt_1747_, lean_object* v_val_1748_){
_start:
{
lean_object* v_name_1749_; lean_object* v___x_1750_; 
v_name_1749_ = lean_ctor_get(v_opt_1747_, 0);
lean_inc(v_name_1749_);
lean_dec_ref(v_opt_1747_);
v___x_1750_ = l_Lean_Options_set___redArg(v_inst_1745_, v_opts_1746_, v_name_1749_, v_val_1748_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* v_00_u03b1_1751_, lean_object* v_inst_1752_, lean_object* v_opts_1753_, lean_object* v_opt_1754_, lean_object* v_val_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Option_set___redArg(v_inst_1752_, v_opts_1753_, v_opt_1754_, v_val_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* v_o_1757_, lean_object* v_k_1758_, uint8_t v_v_1759_){
_start:
{
lean_object* v_map_1760_; uint8_t v_hasTrace_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1775_; 
v_map_1760_ = lean_ctor_get(v_o_1757_, 0);
v_hasTrace_1761_ = lean_ctor_get_uint8(v_o_1757_, sizeof(void*)*1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_o_1757_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1763_ = v_o_1757_;
v_isShared_1764_ = v_isSharedCheck_1775_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_map_1760_);
lean_dec(v_o_1757_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1775_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1765_, 0, v_v_1759_);
lean_inc(v_k_1758_);
v___x_1766_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1758_, v___x_1765_, v_map_1760_);
if (v_hasTrace_1761_ == 0)
{
lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1770_; 
v___x_1767_ = ((lean_object*)(l_Lean_Options_insert___closed__1));
v___x_1768_ = l_Lean_Name_isPrefixOf(v___x_1767_, v_k_1758_);
lean_dec(v_k_1758_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1770_ = v___x_1763_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1766_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*1, v___x_1768_);
return v___x_1770_;
}
}
else
{
lean_object* v___x_1773_; 
lean_dec(v_k_1758_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1773_ = v___x_1763_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1766_);
lean_ctor_set_uint8(v_reuseFailAlloc_1774_, sizeof(void*)*1, v_hasTrace_1761_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* v_o_1776_, lean_object* v_k_1777_, lean_object* v_v_1778_){
_start:
{
uint8_t v_v_boxed_1779_; lean_object* v_res_1780_; 
v_v_boxed_1779_ = lean_unbox(v_v_1778_);
v_res_1780_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_o_1776_, v_k_1777_, v_v_boxed_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* v_opts_1781_, lean_object* v_name_1782_, uint8_t v_val_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(v_opts_1781_, v_name_1782_, v_val_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* v_opts_1785_, lean_object* v_name_1786_, lean_object* v_val_1787_){
_start:
{
uint8_t v_val_boxed_1788_; lean_object* v_res_1789_; 
v_val_boxed_1788_ = lean_unbox(v_val_1787_);
v_res_1789_ = lean_options_update_bool(v_opts_1785_, v_name_1786_, v_val_boxed_1788_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* v_inst_1790_, lean_object* v_opts_1791_, lean_object* v_opt_1792_, lean_object* v_val_1793_){
_start:
{
lean_object* v_name_1794_; lean_object* v_map_1795_; uint8_t v___x_1796_; 
v_name_1794_ = lean_ctor_get(v_opt_1792_, 0);
v_map_1795_ = lean_ctor_get(v_opts_1791_, 0);
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1794_, v_map_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Option_set___redArg(v_inst_1790_, v_opts_1791_, v_opt_1792_, v_val_1793_);
return v___x_1797_;
}
else
{
lean_dec(v_val_1793_);
lean_dec_ref(v_opt_1792_);
lean_dec_ref(v_inst_1790_);
return v_opts_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* v_00_u03b1_1798_, lean_object* v_inst_1799_, lean_object* v_opts_1800_, lean_object* v_opt_1801_, lean_object* v_val_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Option_setIfNotSet___redArg(v_inst_1799_, v_opts_1800_, v_opt_1801_, v_val_1802_);
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* v_inst_1805_, lean_object* v_name_1806_, lean_object* v_decl_1807_, lean_object* v_ref_1808_){
_start:
{
lean_object* v_toDataValue_1810_; lean_object* v_defValue_1811_; lean_object* v_descr_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1838_; 
v_toDataValue_1810_ = lean_ctor_get(v_inst_1805_, 0);
lean_inc_ref(v_toDataValue_1810_);
lean_dec_ref(v_inst_1805_);
v_defValue_1811_ = lean_ctor_get(v_decl_1807_, 0);
v_descr_1812_ = lean_ctor_get(v_decl_1807_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_decl_1807_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1814_ = v_decl_1807_;
v_isShared_1815_ = v_isSharedCheck_1838_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_descr_1812_);
lean_inc(v_defValue_1811_);
lean_dec(v_decl_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1838_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_inc(v_defValue_1811_);
v___x_1816_ = lean_apply_1(v_toDataValue_1810_, v_defValue_1811_);
lean_inc(v_name_1806_);
v___x_1817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1817_, 0, v_name_1806_);
lean_ctor_set(v___x_1817_, 1, v_ref_1808_);
lean_ctor_set(v___x_1817_, 2, v___x_1816_);
lean_ctor_set(v___x_1817_, 3, v_descr_1812_);
lean_inc(v_name_1806_);
v___x_1818_ = lean_register_option(v_name_1806_, v___x_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1829_);
v___x_1820_ = v___x_1818_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1818_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v_defValue_1811_);
lean_ctor_set(v___x_1814_, 0, v_name_1806_);
v___x_1823_ = v___x_1814_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_name_1806_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_defValue_1811_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_del_object(v___x_1814_);
lean_dec(v_defValue_1811_);
lean_dec(v_name_1806_);
v_a_1830_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1818_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1818_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* v_inst_1839_, lean_object* v_name_1840_, lean_object* v_decl_1841_, lean_object* v_ref_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Option_register___redArg(v_inst_1839_, v_name_1840_, v_decl_1841_, v_ref_1842_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* v_00_u03b1_1845_, lean_object* v_inst_1846_, lean_object* v_name_1847_, lean_object* v_decl_1848_, lean_object* v_ref_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_Option_register___redArg(v_inst_1846_, v_name_1847_, v_decl_1848_, v_ref_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_inst_1853_, lean_object* v_name_1854_, lean_object* v_decl_1855_, lean_object* v_ref_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Option_register(v_00_u03b1_1852_, v_inst_1853_, v_name_1854_, v_decl_1855_, v_ref_1856_);
return v_res_1858_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
v___x_1947_ = l_String_toRawSubstring_x27(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
v___x_1968_ = l_String_toRawSubstring_x27(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27(void){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Array_mkArray0(lean_box(0));
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* v_x_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
v___x_1998_ = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(v_x_1994_);
v___x_1999_ = l_Lean_Syntax_isOfKind(v_x_1994_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref(v_a_1995_);
lean_dec(v_x_1994_);
v___x_2000_ = lean_box(1);
v___x_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_a_1996_);
return v___x_2001_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v_name_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2108_; lean_object* v___x_2119_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2002_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2004_);
v___x_2006_ = lean_unsigned_to_nat(3u);
v_name_2007_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2006_);
v___x_2008_ = lean_unsigned_to_nat(5u);
v___x_2009_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2008_);
v___x_2010_ = lean_unsigned_to_nat(7u);
v___x_2011_ = l_Lean_Syntax_getArg(v_x_1994_, v___x_2010_);
lean_dec(v_x_1994_);
v___x_2119_ = l_Lean_Syntax_getOptional_x3f(v___x_2005_);
lean_dec(v___x_2005_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_box(0);
v___y_2108_ = v___x_2120_;
goto v___jp_2107_;
}
else
{
lean_object* v_val_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_val_2121_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2119_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_val_2121_);
lean_dec(v___x_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_val_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
v___y_2108_ = v___x_2126_;
goto v___jp_2107_;
}
}
}
v___jp_2012_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2025_ = l_Array_append___redArg(v___y_2018_, v___y_2024_);
lean_dec_ref(v___y_2024_);
lean_inc(v___y_2015_);
lean_inc(v___y_2023_);
v___x_2026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2026_, 0, v___y_2023_);
lean_ctor_set(v___x_2026_, 1, v___y_2015_);
lean_ctor_set(v___x_2026_, 2, v___x_2025_);
lean_inc_n(v___y_2020_, 5);
lean_inc(v___y_2023_);
v___x_2027_ = l_Lean_Syntax_node7(v___y_2023_, v___y_2013_, v___y_2016_, v___y_2020_, v___x_2026_, v___y_2020_, v___y_2020_, v___y_2020_, v___y_2020_);
v___x_2028_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(v___y_2022_);
v___x_2029_ = l_Lean_Name_mkStr4(v___x_1997_, v___y_2022_, v___y_2017_, v___x_2028_);
v___x_2030_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
lean_inc(v___y_2023_);
v___x_2031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___y_2023_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
lean_inc(v___y_2023_);
v___x_2032_ = l_Lean_Syntax_node1(v___y_2023_, v___x_2029_, v___x_2031_);
v___x_2033_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
v___x_2034_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
lean_inc_ref(v___y_2022_);
v___x_2035_ = l_Lean_Name_mkStr4(v___x_1997_, v___y_2022_, v___x_2033_, v___x_2034_);
v___x_2036_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
lean_inc(v___y_2023_);
v___x_2037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___y_2023_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
lean_inc_ref(v___y_2022_);
v___x_2039_ = l_Lean_Name_mkStr4(v___x_1997_, v___y_2022_, v___x_2033_, v___x_2038_);
v___x_2040_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_2041_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc(v___y_2021_);
lean_inc(v___y_2019_);
v___x_2042_ = l_Lean_addMacroScope(v___y_2019_, v___x_2041_, v___y_2021_);
v___x_2043_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
lean_inc(v___y_2023_);
v___x_2044_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2044_, 0, v___y_2023_);
lean_ctor_set(v___x_2044_, 1, v___x_2040_);
lean_ctor_set(v___x_2044_, 2, v___x_2042_);
lean_ctor_set(v___x_2044_, 3, v___x_2043_);
lean_inc(v___y_2015_);
lean_inc(v___y_2023_);
v___x_2045_ = l_Lean_Syntax_node1(v___y_2023_, v___y_2015_, v___x_2009_);
lean_inc(v___x_2039_);
lean_inc(v___y_2023_);
v___x_2046_ = l_Lean_Syntax_node2(v___y_2023_, v___x_2039_, v___x_2044_, v___x_2045_);
lean_inc(v___y_2023_);
v___x_2047_ = l_Lean_Syntax_node2(v___y_2023_, v___x_2035_, v___x_2037_, v___x_2046_);
v___x_2048_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
lean_inc(v___y_2023_);
v___x_2049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___y_2023_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
lean_inc(v_name_2007_);
lean_inc(v___y_2015_);
lean_inc(v___y_2023_);
v___x_2050_ = l_Lean_Syntax_node3(v___y_2023_, v___y_2015_, v_name_2007_, v___x_2047_, v___x_2049_);
v___x_2051_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
lean_inc_ref(v___y_2022_);
v___x_2052_ = l_Lean_Name_mkStr4(v___x_1997_, v___y_2022_, v___x_2033_, v___x_2051_);
v___x_2053_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
lean_inc_ref(v___y_2022_);
v___x_2054_ = l_Lean_Name_mkStr4(v___x_1997_, v___y_2022_, v___x_2033_, v___x_2053_);
v___x_2055_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
v___x_2056_ = l_Lean_Name_mkStr4(v___x_1997_, v___y_2022_, v___x_2033_, v___x_2055_);
v___x_2057_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2058_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_2059_ = l_Lean_addMacroScope(v___y_2019_, v___x_2058_, v___y_2021_);
v___x_2060_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
lean_inc(v___y_2023_);
v___x_2061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2023_);
lean_ctor_set(v___x_2061_, 1, v___x_2057_);
lean_ctor_set(v___x_2061_, 2, v___x_2059_);
lean_ctor_set(v___x_2061_, 3, v___x_2060_);
v___x_2062_ = l_Lean_TSyntax_getId(v_name_2007_);
lean_dec(v_name_2007_);
v___x_2063_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_2062_);
lean_inc(v___y_2015_);
lean_inc(v___y_2023_);
v___x_2064_ = l_Lean_Syntax_node2(v___y_2023_, v___y_2015_, v___x_2063_, v___x_2011_);
lean_inc(v___y_2023_);
v___x_2065_ = l_Lean_Syntax_node2(v___y_2023_, v___x_2039_, v___x_2061_, v___x_2064_);
lean_inc(v___y_2023_);
v___x_2066_ = l_Lean_Syntax_node1(v___y_2023_, v___x_2056_, v___x_2065_);
lean_inc(v___y_2023_);
v___x_2067_ = l_Lean_Syntax_node2(v___y_2023_, v___x_2054_, v___x_2066_, v___y_2020_);
lean_inc(v___y_2023_);
v___x_2068_ = l_Lean_Syntax_node1(v___y_2023_, v___y_2015_, v___x_2067_);
lean_inc(v___y_2023_);
v___x_2069_ = l_Lean_Syntax_node1(v___y_2023_, v___x_2052_, v___x_2068_);
v___x_2070_ = l_Lean_Syntax_node4(v___y_2023_, v___y_2014_, v___x_2027_, v___x_2032_, v___x_2050_, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_a_1996_);
return v___x_2071_;
}
v___jp_2072_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_inc_ref(v___y_2077_);
v___x_2084_ = l_Array_append___redArg(v___y_2077_, v___y_2083_);
lean_dec_ref(v___y_2083_);
lean_inc(v___y_2075_);
lean_inc(v___y_2082_);
v___x_2085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2085_, 0, v___y_2082_);
lean_ctor_set(v___x_2085_, 1, v___y_2075_);
lean_ctor_set(v___x_2085_, 2, v___x_2084_);
lean_inc_ref(v___y_2077_);
lean_inc(v___y_2075_);
lean_inc(v___y_2082_);
v___x_2086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2086_, 0, v___y_2082_);
lean_ctor_set(v___x_2086_, 1, v___y_2075_);
lean_ctor_set(v___x_2086_, 2, v___y_2077_);
if (lean_obj_tag(v___y_2079_) == 1)
{
lean_object* v_val_2087_; lean_object* v___x_2088_; 
v_val_2087_ = lean_ctor_get(v___y_2079_, 0);
lean_inc(v_val_2087_);
lean_dec_ref(v___y_2079_);
v___x_2088_ = l_Array_mkArray1___redArg(v_val_2087_);
v___y_2013_ = v___y_2073_;
v___y_2014_ = v___y_2074_;
v___y_2015_ = v___y_2075_;
v___y_2016_ = v___x_2085_;
v___y_2017_ = v___y_2076_;
v___y_2018_ = v___y_2077_;
v___y_2019_ = v___y_2078_;
v___y_2020_ = v___x_2086_;
v___y_2021_ = v___y_2080_;
v___y_2022_ = v___y_2081_;
v___y_2023_ = v___y_2082_;
v___y_2024_ = v___x_2088_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2089_; 
lean_dec(v___y_2079_);
v___x_2089_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_2013_ = v___y_2073_;
v___y_2014_ = v___y_2074_;
v___y_2015_ = v___y_2075_;
v___y_2016_ = v___x_2085_;
v___y_2017_ = v___y_2076_;
v___y_2018_ = v___y_2077_;
v___y_2019_ = v___y_2078_;
v___y_2020_ = v___x_2086_;
v___y_2021_ = v___y_2080_;
v___y_2022_ = v___y_2081_;
v___y_2023_ = v___y_2082_;
v___y_2024_ = v___x_2089_;
goto v___jp_2012_;
}
}
v___jp_2090_:
{
lean_object* v_quotContext_2093_; lean_object* v_currMacroScope_2094_; lean_object* v_ref_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_quotContext_2093_ = lean_ctor_get(v_a_1995_, 1);
lean_inc(v_quotContext_2093_);
v_currMacroScope_2094_ = lean_ctor_get(v_a_1995_, 2);
lean_inc(v_currMacroScope_2094_);
v_ref_2095_ = lean_ctor_get(v_a_1995_, 5);
lean_inc(v_ref_2095_);
lean_dec_ref(v_a_1995_);
v___x_2096_ = 0;
v___x_2097_ = l_Lean_SourceInfo_fromRef(v_ref_2095_, v___x_2096_);
lean_dec(v_ref_2095_);
v___x_2098_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
v___x_2099_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
v___x_2100_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_2101_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
v___x_2102_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2103_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27);
if (lean_obj_tag(v___y_2092_) == 1)
{
lean_object* v_val_2104_; lean_object* v___x_2105_; 
v_val_2104_ = lean_ctor_get(v___y_2092_, 0);
lean_inc(v_val_2104_);
lean_dec_ref(v___y_2092_);
v___x_2105_ = l_Array_mkArray1___redArg(v_val_2104_);
v___y_2073_ = v___x_2101_;
v___y_2074_ = v___x_2100_;
v___y_2075_ = v___x_2102_;
v___y_2076_ = v___x_2099_;
v___y_2077_ = v___x_2103_;
v___y_2078_ = v_quotContext_2093_;
v___y_2079_ = v___y_2091_;
v___y_2080_ = v_currMacroScope_2094_;
v___y_2081_ = v___x_2098_;
v___y_2082_ = v___x_2097_;
v___y_2083_ = v___x_2105_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2106_; 
lean_dec(v___y_2092_);
v___x_2106_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
v___y_2073_ = v___x_2101_;
v___y_2074_ = v___x_2100_;
v___y_2075_ = v___x_2102_;
v___y_2076_ = v___x_2099_;
v___y_2077_ = v___x_2103_;
v___y_2078_ = v_quotContext_2093_;
v___y_2079_ = v___y_2091_;
v___y_2080_ = v_currMacroScope_2094_;
v___y_2081_ = v___x_2098_;
v___y_2082_ = v___x_2097_;
v___y_2083_ = v___x_2106_;
goto v___jp_2072_;
}
}
v___jp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_Syntax_getOptional_x3f(v___x_2003_);
lean_dec(v___x_2003_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_box(0);
v___y_2091_ = v___y_2108_;
v___y_2092_ = v___x_2110_;
goto v___jp_2090_;
}
else
{
lean_object* v_val_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_val_2111_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2109_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_val_2111_);
lean_dec(v___x_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_val_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
v___y_2091_ = v___y_2108_;
v___y_2092_ = v___x_2116_;
goto v___jp_2090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* v_x_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(v_x_2200_);
v___x_2204_ = l_Lean_Syntax_isOfKind(v_x_2200_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_a_2201_);
lean_dec(v_x_2200_);
v___x_2205_ = lean_box(1);
v___x_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_a_2202_);
return v___x_2206_;
}
else
{
lean_object* v_quotContext_2207_; lean_object* v_currMacroScope_2208_; lean_object* v_ref_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_name_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_quotContext_2207_ = lean_ctor_get(v_a_2201_, 1);
lean_inc(v_quotContext_2207_);
v_currMacroScope_2208_ = lean_ctor_get(v_a_2201_, 2);
lean_inc(v_currMacroScope_2208_);
v_ref_2209_ = lean_ctor_get(v_a_2201_, 5);
lean_inc(v_ref_2209_);
lean_dec_ref(v_a_2201_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = l_Lean_Syntax_getArg(v_x_2200_, v___x_2210_);
v___x_2212_ = lean_unsigned_to_nat(2u);
v_name_2213_ = l_Lean_Syntax_getArg(v_x_2200_, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(4u);
v___x_2215_ = l_Lean_Syntax_getArg(v_x_2200_, v___x_2214_);
v___x_2216_ = lean_unsigned_to_nat(6u);
v___x_2217_ = l_Lean_Syntax_getArg(v_x_2200_, v___x_2216_);
lean_dec(v_x_2200_);
v___x_2218_ = 0;
v___x_2219_ = l_Lean_SourceInfo_fromRef(v_ref_2209_, v___x_2218_);
lean_dec(v_ref_2209_);
v___x_2220_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
v___x_2221_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
v___x_2222_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
lean_inc(v___x_2219_);
v___x_2223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2219_);
lean_ctor_set(v___x_2223_, 1, v___x_2220_);
lean_inc(v___x_2219_);
v___x_2224_ = l_Lean_Syntax_node1(v___x_2219_, v___x_2222_, v___x_2223_);
v___x_2225_ = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
v___x_2226_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
v___x_2227_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
lean_inc(v___x_2219_);
v___x_2228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2219_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
v___x_2230_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
v___x_2231_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc(v_currMacroScope_2208_);
lean_inc(v_quotContext_2207_);
v___x_2232_ = l_Lean_addMacroScope(v_quotContext_2207_, v___x_2231_, v_currMacroScope_2208_);
v___x_2233_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
lean_inc(v___x_2219_);
v___x_2234_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2219_);
lean_ctor_set(v___x_2234_, 1, v___x_2230_);
lean_ctor_set(v___x_2234_, 2, v___x_2232_);
lean_ctor_set(v___x_2234_, 3, v___x_2233_);
lean_inc(v___x_2219_);
v___x_2235_ = l_Lean_Syntax_node1(v___x_2219_, v___x_2225_, v___x_2215_);
lean_inc(v___x_2219_);
v___x_2236_ = l_Lean_Syntax_node2(v___x_2219_, v___x_2229_, v___x_2234_, v___x_2235_);
lean_inc(v___x_2219_);
v___x_2237_ = l_Lean_Syntax_node2(v___x_2219_, v___x_2226_, v___x_2228_, v___x_2236_);
v___x_2238_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
lean_inc(v___x_2219_);
v___x_2239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2219_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
lean_inc(v_name_2213_);
lean_inc(v___x_2219_);
v___x_2240_ = l_Lean_Syntax_node3(v___x_2219_, v___x_2225_, v_name_2213_, v___x_2237_, v___x_2239_);
v___x_2241_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
v___x_2242_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4));
v___x_2243_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5));
v___x_2244_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
v___x_2245_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
v___x_2246_ = l_Lean_addMacroScope(v_quotContext_2207_, v___x_2245_, v_currMacroScope_2208_);
v___x_2247_ = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
lean_inc(v___x_2219_);
v___x_2248_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2219_);
lean_ctor_set(v___x_2248_, 1, v___x_2244_);
lean_ctor_set(v___x_2248_, 2, v___x_2246_);
lean_ctor_set(v___x_2248_, 3, v___x_2247_);
v___x_2249_ = l_Lean_TSyntax_getId(v_name_2213_);
lean_dec(v_name_2213_);
v___x_2250_ = l_Lean_instQuoteNameMkStr1___private__1(v___x_2249_);
lean_inc(v___x_2219_);
v___x_2251_ = l_Lean_Syntax_node2(v___x_2219_, v___x_2225_, v___x_2250_, v___x_2217_);
lean_inc(v___x_2219_);
v___x_2252_ = l_Lean_Syntax_node2(v___x_2219_, v___x_2229_, v___x_2248_, v___x_2251_);
lean_inc(v___x_2219_);
v___x_2253_ = l_Lean_Syntax_node1(v___x_2219_, v___x_2243_, v___x_2252_);
v___x_2254_ = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27);
lean_inc(v___x_2219_);
v___x_2255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2219_);
lean_ctor_set(v___x_2255_, 1, v___x_2225_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
lean_inc(v___x_2219_);
v___x_2256_ = l_Lean_Syntax_node2(v___x_2219_, v___x_2242_, v___x_2253_, v___x_2255_);
lean_inc(v___x_2219_);
v___x_2257_ = l_Lean_Syntax_node1(v___x_2219_, v___x_2225_, v___x_2256_);
lean_inc(v___x_2219_);
v___x_2258_ = l_Lean_Syntax_node1(v___x_2219_, v___x_2241_, v___x_2257_);
v___x_2259_ = l_Lean_Syntax_node4(v___x_2219_, v___x_2221_, v___x_2211_, v___x_2224_, v___x_2240_, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v_a_2202_);
return v___x_2260_;
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
