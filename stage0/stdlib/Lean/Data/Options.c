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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_data_value_to_string(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2_value;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Options_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Options_instToString___private__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Options_instToString___closed__0 = (const lean_object*)&l_Lean_Options_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Options_instToString = (const lean_object*)&l_Lean_Options_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqDataValue_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Options_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_insert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_insert___closed__0 = (const lean_object*)&l_Lean_Options_insert___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Options_insert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_insert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_insert___closed__1 = (const lean_object*)&l_Lean_Options_insert___closed__1_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
LEAN_EXPORT lean_object* l_Lean_Options_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_isPrefixOf___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Options_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_isPrefixOf___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Options_insert___closed__1_value)} };
static const lean_object* l_Lean_Options_erase___closed__0 = (const lean_object*)&l_Lean_Options_erase___closed__0_value;
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_OptionDecl_declName___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_OptionDecl_declName___autoParam___closed__4 = (const lean_object*)&l_Lean_OptionDecl_declName___autoParam___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l_Lean_OptionDecl_declName___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_OptionDecl_declName___autoParam___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedDataValue_default;
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptionDecls;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
static const lean_string_object l_Lean_registerOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "Failed to register option: Options can only be registered during initialization"};
static const lean_object* l_Lean_registerOption___closed__0 = (const lean_object*)&l_Lean_registerOption___closed__0_value;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_once_cell_t l_Lean_registerOption___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerOption___closed__1;
static const lean_string_object l_Lean_registerOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Invalid option declaration `"};
static const lean_object* l_Lean_registerOption___closed__2 = (const lean_object*)&l_Lean_registerOption___closed__2_value;
static const lean_string_object l_Lean_registerOption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "`: Option already exists"};
static const lean_object* l_Lean_registerOption___closed__3 = (const lean_object*)&l_Lean_registerOption___closed__3_value;
lean_object* l_Lean_initializing();
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDecls();
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_once_cell_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
static lean_once_cell_t l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
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
LEAN_EXPORT lean_object* lean_options_get_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Options_empty));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0));
x_8 = lean_string_append(x_1, x_7);
x_9 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1));
x_10 = 1;
x_11 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_5, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_12, x_7);
x_14 = lean_data_value_to_string(x_6);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_8, x_17);
lean_dec_ref(x_17);
x_1 = x_18;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Options_instToString___private__1_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1));
x_8 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1));
x_9 = 1;
x_10 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_5, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_data_value_to_string(x_6);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_7, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__2));
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint32_t x_37; lean_object* x_38; 
lean_inc(x_3);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = ((lean_object*)(l_List_toString___at___00Lean_Options_instToString___private__1_spec__1___closed__1));
x_25 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__1));
x_26 = 1;
x_27 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_22, x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__0));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_data_value_to_string(x_23);
x_32 = lean_string_append(x_30, x_31);
lean_dec_ref(x_31);
x_33 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1___closed__2));
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_24, x_34);
lean_dec_ref(x_34);
x_36 = l_List_foldl___at___00List_toString___at___00Lean_Options_instToString___private__1_spec__1_spec__1(x_35, x_3);
x_37 = 93;
x_38 = lean_string_push(x_36, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_instToString___private__1_spec__0(x_3, x_2);
x_5 = l_List_toString___at___00Lean_Options_instToString___private__1_spec__1(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instToString___private__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Options_instToString___private__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__0), 4, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(x_1, x_9, x_3, x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg___lam__1), 2, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___private__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Options_instForInProdNameDataValueOfMonad___private__1___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instForInProdNameDataValueOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Options_instForInProdNameDataValueOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_8 = lean_apply_2(x_1, x_3, x_4);
x_9 = lean_unbox(x_8);
switch (x_9) {
case 0:
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
case 1:
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_instBEqDataValue_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 4);
lean_inc(x_8);
lean_dec_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_9, 0);
lean_dec(x_26);
x_10 = x_9;
x_11 = x_25;
goto block_24;
}
else
{
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_box(0);
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_2, x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_15 = l_Option_instBEq_beq___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__3(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_18);
x_19 = x_10;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; 
lean_del_object(x_10);
x_22 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
x_3 = x_22;
x_4 = x_8;
goto _start;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_3);
return x_27;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_10; lean_object* x_11; lean_object* x_17; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_17 = x_21;
goto block_20;
}
else
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(0u);
x_17 = x_22;
goto block_20;
}
block_9:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
return x_8;
}
}
block_16:
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
x_14 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_3, x_13, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_4 = x_15;
goto block_9;
}
}
block_20:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_10 = x_17;
x_11 = x_18;
goto block_16;
}
else
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(0u);
x_10 = x_17;
x_11 = x_19;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_instBEq___private__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = ((lean_object*)(l_Lean_Options_instBEq___private__1___closed__0));
x_6 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_instBEq___private__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Options_instBEq___private__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_Const_beq___at___00Std_DTreeMap_Const_beq___at___00Std_TreeMap_beq___at___00Lean_Options_instBEq___private__1_spec__0_spec__0_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Options_find_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_find___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Options_find(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Options_get_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_1(x_6, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Options_get_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_6);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_1(x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Options_get___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_6, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec_ref(x_7);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_1(x_7, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Options_get(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getBool(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_getBool(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Options_contains(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_18; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_6 = x_1;
x_7 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_3, x_4);
if (x_5 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = ((lean_object*)(l_Lean_Options_insert___closed__1));
x_10 = l_Lean_Name_isPrefixOf(x_9, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_8);
x_11 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_8);
x_14 = x_6;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_5);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
x_8 = x_2;
x_9 = x_21;
goto block_20;
}
else
{
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_1(x_5, x_4);
lean_inc(x_3);
x_11 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_3, x_10, x_6);
if (x_7 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = ((lean_object*)(l_Lean_Options_insert___closed__1));
x_13 = l_Lean_Name_isPrefixOf(x_12, x_3);
lean_dec(x_3);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_14 = x_8;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
return x_14;
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_17 = x_8;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_7);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Options_set___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_KVMap_instValueBool;
x_5 = lean_box(x_3);
x_6 = l_Lean_Options_set___redArg(x_4, x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_setBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_setBool(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(x_1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_660; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_660 = !lean_is_exclusive(x_2);
if (x_660 == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_2, 0);
lean_dec(x_661);
x_7 = x_2;
x_8 = x_660;
goto block_659;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_660;
goto block_659;
}
block_659:
{
uint8_t x_9; 
x_9 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_9) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(x_1, x_5);
x_11 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_mul(x_18, x_12);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_21 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_22 = lean_nat_add(x_21, x_13);
lean_dec(x_21);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_22);
x_23 = x_7;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_6);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_89; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_6, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_6, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_6, 0);
lean_dec(x_94);
x_26 = x_6;
x_27 = x_89;
goto block_88;
}
else
{
lean_dec(x_6);
x_26 = lean_box(0);
x_27 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
x_32 = lean_ctor_get(x_16, 4);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_33);
x_36 = lean_nat_dec_lt(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_64; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_16, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_16, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 0);
lean_dec(x_69);
x_37 = x_16;
x_38 = x_64;
goto block_63;
}
else
{
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; 
x_39 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_40 = lean_nat_add(x_39, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_52 = x_61;
goto block_60;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_52 = x_62;
goto block_60;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_17);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_14);
lean_ctor_set(x_50, 2, x_15);
lean_ctor_set(x_50, 3, x_32);
lean_ctor_set(x_50, 4, x_17);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_45);
lean_ctor_set(x_26, 3, x_41);
lean_ctor_set(x_26, 2, x_30);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_40);
x_46 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_39, x_52);
lean_dec(x_52);
lean_dec(x_39);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_31);
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_53);
x_54 = x_7;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_3);
lean_ctor_set(x_59, 2, x_4);
lean_ctor_set(x_59, 3, x_10);
lean_ctor_set(x_59, 4, x_31);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
x_55 = lean_nat_add(x_11, x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
goto block_51;
}
else
{
lean_object* x_57; 
x_57 = lean_unsigned_to_nat(0u);
x_41 = x_54;
x_42 = x_55;
x_43 = x_57;
goto block_51;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_del_object(x_7);
x_70 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_71 = lean_nat_add(x_70, x_13);
lean_dec(x_13);
x_72 = lean_nat_add(x_70, x_28);
lean_dec(x_70);
lean_inc_ref(x_10);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 3, x_10);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 0, x_72);
x_73 = x_26;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_4);
lean_ctor_set(x_87, 3, x_10);
lean_ctor_set(x_87, 4, x_16);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_10, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_10, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_10, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_10, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_10, 0);
lean_dec(x_85);
x_74 = x_10;
x_75 = x_80;
goto block_79;
}
else
{
lean_dec(x_10);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_17);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 2, x_15);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 0, x_71);
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_14);
lean_ctor_set(x_78, 2, x_15);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_17);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
lean_inc(x_95);
x_96 = lean_nat_add(x_11, x_95);
lean_dec(x_95);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_96);
x_97 = x_7;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_4);
lean_ctor_set(x_99, 3, x_10);
lean_ctor_set(x_99, 4, x_6);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_6, 3);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_6, 4);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_117; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_117 = !lean_is_exclusive(x_6);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_6, 4);
lean_dec(x_118);
x_119 = lean_ctor_get(x_6, 3);
lean_dec(x_119);
x_105 = x_6;
x_106 = x_117;
goto block_116;
}
else
{
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_105 = lean_box(0);
x_106 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_100, 0);
x_108 = lean_nat_add(x_11, x_102);
lean_dec(x_102);
x_109 = lean_nat_add(x_11, x_107);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_100);
lean_ctor_set(x_105, 3, x_10);
lean_ctor_set(x_105, 2, x_4);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 0, x_109);
x_110 = x_105;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_4);
lean_ctor_set(x_115, 3, x_10);
lean_ctor_set(x_115, 4, x_100);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_101);
lean_ctor_set(x_7, 3, x_110);
lean_ctor_set(x_7, 2, x_104);
lean_ctor_set(x_7, 1, x_103);
lean_ctor_set(x_7, 0, x_108);
x_111 = x_7;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_104);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_101);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_144; 
x_120 = lean_ctor_get(x_6, 1);
x_121 = lean_ctor_get(x_6, 2);
x_144 = !lean_is_exclusive(x_6);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_6, 4);
lean_dec(x_145);
x_146 = lean_ctor_get(x_6, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_6, 0);
lean_dec(x_147);
x_122 = x_6;
x_123 = x_144;
goto block_143;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_122 = lean_box(0);
x_123 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_139; 
x_124 = lean_ctor_get(x_100, 1);
x_125 = lean_ctor_get(x_100, 2);
x_139 = !lean_is_exclusive(x_100);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_100, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_100, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_100, 0);
lean_dec(x_142);
x_126 = x_100;
x_127 = x_139;
goto block_138;
}
else
{
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_box(0);
x_127 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_unsigned_to_nat(3u);
if (x_127 == 0)
{
lean_ctor_set(x_126, 4, x_101);
lean_ctor_set(x_126, 3, x_101);
lean_ctor_set(x_126, 2, x_4);
lean_ctor_set(x_126, 1, x_3);
lean_ctor_set(x_126, 0, x_11);
x_129 = x_126;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_11);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_101);
lean_ctor_set(x_137, 4, x_101);
x_129 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_130; 
if (x_123 == 0)
{
lean_ctor_set(x_122, 3, x_101);
lean_ctor_set(x_122, 0, x_11);
x_130 = x_122;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_120);
lean_ctor_set(x_135, 2, x_121);
lean_ctor_set(x_135, 3, x_101);
lean_ctor_set(x_135, 4, x_101);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_130);
lean_ctor_set(x_7, 3, x_129);
lean_ctor_set(x_7, 2, x_125);
lean_ctor_set(x_7, 1, x_124);
lean_ctor_set(x_7, 0, x_128);
x_131 = x_7;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_125);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_6, 4);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_161; 
x_149 = lean_ctor_get(x_6, 1);
x_150 = lean_ctor_get(x_6, 2);
x_161 = !lean_is_exclusive(x_6);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_6, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_6, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_dec(x_164);
x_151 = x_6;
x_152 = x_161;
goto block_160;
}
else
{
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_6);
x_151 = lean_box(0);
x_152 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(3u);
if (x_152 == 0)
{
lean_ctor_set(x_151, 4, x_100);
lean_ctor_set(x_151, 2, x_4);
lean_ctor_set(x_151, 1, x_3);
lean_ctor_set(x_151, 0, x_11);
x_154 = x_151;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_11);
lean_ctor_set(x_159, 1, x_3);
lean_ctor_set(x_159, 2, x_4);
lean_ctor_set(x_159, 3, x_100);
lean_ctor_set(x_159, 4, x_100);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_148);
lean_ctor_set(x_7, 3, x_154);
lean_ctor_set(x_7, 2, x_150);
lean_ctor_set(x_7, 1, x_149);
lean_ctor_set(x_7, 0, x_153);
x_155 = x_7;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_154);
lean_ctor_set(x_157, 4, x_148);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_178; 
x_165 = lean_ctor_get(x_6, 0);
x_166 = lean_ctor_get(x_6, 1);
x_167 = lean_ctor_get(x_6, 2);
x_178 = !lean_is_exclusive(x_6);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_6, 4);
lean_dec(x_179);
x_180 = lean_ctor_get(x_6, 3);
lean_dec(x_180);
x_168 = x_6;
x_169 = x_178;
goto block_177;
}
else
{
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_6);
x_168 = lean_box(0);
x_169 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_170; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 3, x_148);
x_170 = x_168;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_176, 2, x_167);
lean_ctor_set(x_176, 3, x_148);
lean_ctor_set(x_176, 4, x_148);
x_170 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_170);
lean_ctor_set(x_7, 3, x_148);
lean_ctor_set(x_7, 0, x_171);
x_172 = x_7;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_3);
lean_ctor_set(x_174, 2, x_4);
lean_ctor_set(x_174, 3, x_148);
lean_ctor_set(x_174, 4, x_170);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
}
}
else
{
lean_object* x_181; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 0, x_11);
x_181 = x_7;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_11);
lean_ctor_set(x_183, 1, x_3);
lean_ctor_set(x_183, 2, x_4);
lean_ctor_set(x_183, 3, x_6);
lean_ctor_set(x_183, 4, x_6);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
case 1:
{
lean_del_object(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_184 = lean_ctor_get(x_5, 0);
x_185 = lean_ctor_get(x_5, 1);
x_186 = lean_ctor_get(x_5, 2);
x_187 = lean_ctor_get(x_5, 3);
x_188 = lean_ctor_get(x_5, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_6, 0);
x_190 = lean_ctor_get(x_6, 1);
x_191 = lean_ctor_get(x_6, 2);
x_192 = lean_ctor_get(x_6, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_6, 4);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_dec_lt(x_184, x_189);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; uint8_t x_331; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_331 = !lean_is_exclusive(x_5);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_5, 4);
lean_dec(x_332);
x_333 = lean_ctor_get(x_5, 3);
lean_dec(x_333);
x_334 = lean_ctor_get(x_5, 2);
lean_dec(x_334);
x_335 = lean_ctor_get(x_5, 1);
lean_dec(x_335);
x_336 = lean_ctor_get(x_5, 0);
lean_dec(x_336);
x_196 = x_5;
x_197 = x_331;
goto block_330;
}
else
{
lean_dec(x_5);
x_196 = lean_box(0);
x_197 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_185, x_186, x_187, x_188);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec_ref(x_198);
x_202 = lean_ctor_get(x_199, 0);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_mul(x_203, x_202);
x_205 = lean_nat_dec_lt(x_204, x_189);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_192);
x_206 = lean_nat_add(x_194, x_202);
x_207 = lean_nat_add(x_206, x_189);
lean_dec(x_206);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_6);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_207);
x_208 = x_196;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_200);
lean_ctor_set(x_210, 2, x_201);
lean_ctor_set(x_210, 3, x_199);
lean_ctor_set(x_210, 4, x_6);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
else
{
lean_object* x_211; uint8_t x_212; uint8_t x_265; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_265 = !lean_is_exclusive(x_6);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_6, 4);
lean_dec(x_266);
x_267 = lean_ctor_get(x_6, 3);
lean_dec(x_267);
x_268 = lean_ctor_get(x_6, 2);
lean_dec(x_268);
x_269 = lean_ctor_get(x_6, 1);
lean_dec(x_269);
x_270 = lean_ctor_get(x_6, 0);
lean_dec(x_270);
x_211 = x_6;
x_212 = x_265;
goto block_264;
}
else
{
lean_dec(x_6);
x_211 = lean_box(0);
x_212 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_213 = lean_ctor_get(x_192, 0);
x_214 = lean_ctor_get(x_192, 1);
x_215 = lean_ctor_get(x_192, 2);
x_216 = lean_ctor_get(x_192, 3);
x_217 = lean_ctor_get(x_192, 4);
x_218 = lean_ctor_get(x_193, 0);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_mul(x_219, x_218);
x_221 = lean_nat_dec_lt(x_213, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; uint8_t x_249; 
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_249 = !lean_is_exclusive(x_192);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_192, 4);
lean_dec(x_250);
x_251 = lean_ctor_get(x_192, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_192, 2);
lean_dec(x_252);
x_253 = lean_ctor_get(x_192, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_192, 0);
lean_dec(x_254);
x_222 = x_192;
x_223 = x_249;
goto block_248;
}
else
{
lean_dec(x_192);
x_222 = lean_box(0);
x_223 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_237; 
x_224 = lean_nat_add(x_194, x_202);
x_225 = lean_nat_add(x_224, x_189);
lean_dec(x_189);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_216, 0);
lean_inc(x_246);
x_237 = x_246;
goto block_245;
}
else
{
lean_object* x_247; 
x_247 = lean_unsigned_to_nat(0u);
x_237 = x_247;
goto block_245;
}
block_236:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_add(x_226, x_228);
lean_dec(x_228);
lean_dec(x_226);
if (x_223 == 0)
{
lean_ctor_set(x_222, 4, x_193);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 2, x_191);
lean_ctor_set(x_222, 1, x_190);
lean_ctor_set(x_222, 0, x_229);
x_230 = x_222;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_190);
lean_ctor_set(x_235, 2, x_191);
lean_ctor_set(x_235, 3, x_217);
lean_ctor_set(x_235, 4, x_193);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_230);
lean_ctor_set(x_211, 3, x_227);
lean_ctor_set(x_211, 2, x_215);
lean_ctor_set(x_211, 1, x_214);
lean_ctor_set(x_211, 0, x_225);
x_231 = x_211;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_214);
lean_ctor_set(x_233, 2, x_215);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set(x_233, 4, x_230);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_nat_add(x_224, x_237);
lean_dec(x_237);
lean_dec(x_224);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_216);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_238);
x_239 = x_196;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_200);
lean_ctor_set(x_244, 2, x_201);
lean_ctor_set(x_244, 3, x_199);
lean_ctor_set(x_244, 4, x_216);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
x_240 = lean_nat_add(x_194, x_218);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_217, 0);
lean_inc(x_241);
x_226 = x_240;
x_227 = x_239;
x_228 = x_241;
goto block_236;
}
else
{
lean_object* x_242; 
x_242 = lean_unsigned_to_nat(0u);
x_226 = x_240;
x_227 = x_239;
x_228 = x_242;
goto block_236;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_nat_add(x_194, x_202);
x_256 = lean_nat_add(x_255, x_189);
lean_dec(x_189);
x_257 = lean_nat_add(x_255, x_213);
lean_dec(x_255);
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_192);
lean_ctor_set(x_211, 3, x_199);
lean_ctor_set(x_211, 2, x_201);
lean_ctor_set(x_211, 1, x_200);
lean_ctor_set(x_211, 0, x_257);
x_258 = x_211;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_200);
lean_ctor_set(x_263, 2, x_201);
lean_ctor_set(x_263, 3, x_199);
lean_ctor_set(x_263, 4, x_192);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_258);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_256);
x_259 = x_196;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_190);
lean_ctor_set(x_261, 2, x_191);
lean_ctor_set(x_261, 3, x_258);
lean_ctor_set(x_261, 4, x_193);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
else
{
lean_object* x_271; uint8_t x_272; uint8_t x_324; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_324 = !lean_is_exclusive(x_6);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_6, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_6, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_6, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_6, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_6, 0);
lean_dec(x_329);
x_271 = x_6;
x_272 = x_324;
goto block_323;
}
else
{
lean_dec(x_6);
x_271 = lean_box(0);
x_272 = x_324;
goto block_323;
}
block_323:
{
if (lean_obj_tag(x_192) == 0)
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_198, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_198, 1);
lean_inc(x_274);
lean_dec_ref(x_198);
x_275 = lean_ctor_get(x_192, 0);
x_276 = lean_nat_add(x_194, x_189);
lean_dec(x_189);
x_277 = lean_nat_add(x_194, x_275);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 3, x_199);
lean_ctor_set(x_271, 2, x_274);
lean_ctor_set(x_271, 1, x_273);
lean_ctor_set(x_271, 0, x_277);
x_278 = x_271;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_274);
lean_ctor_set(x_283, 3, x_199);
lean_ctor_set(x_283, 4, x_192);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_278);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_276);
x_279 = x_196;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_190);
lean_ctor_set(x_281, 2, x_191);
lean_ctor_set(x_281, 3, x_278);
lean_ctor_set(x_281, 4, x_193);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_301; 
lean_dec(x_189);
x_284 = lean_ctor_get(x_198, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_198, 1);
lean_inc(x_285);
lean_dec_ref(x_198);
x_286 = lean_ctor_get(x_192, 1);
x_287 = lean_ctor_get(x_192, 2);
x_301 = !lean_is_exclusive(x_192);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_192, 4);
lean_dec(x_302);
x_303 = lean_ctor_get(x_192, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_192, 0);
lean_dec(x_304);
x_288 = x_192;
x_289 = x_301;
goto block_300;
}
else
{
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_192);
x_288 = lean_box(0);
x_289 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(3u);
if (x_289 == 0)
{
lean_ctor_set(x_288, 4, x_193);
lean_ctor_set(x_288, 3, x_193);
lean_ctor_set(x_288, 2, x_285);
lean_ctor_set(x_288, 1, x_284);
lean_ctor_set(x_288, 0, x_194);
x_291 = x_288;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_194);
lean_ctor_set(x_299, 1, x_284);
lean_ctor_set(x_299, 2, x_285);
lean_ctor_set(x_299, 3, x_193);
lean_ctor_set(x_299, 4, x_193);
x_291 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_292; 
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 0, x_194);
x_292 = x_271;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_194);
lean_ctor_set(x_297, 1, x_190);
lean_ctor_set(x_297, 2, x_191);
lean_ctor_set(x_297, 3, x_193);
lean_ctor_set(x_297, 4, x_193);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_292);
lean_ctor_set(x_196, 3, x_291);
lean_ctor_set(x_196, 2, x_287);
lean_ctor_set(x_196, 1, x_286);
lean_ctor_set(x_196, 0, x_290);
x_293 = x_196;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_286);
lean_ctor_set(x_295, 2, x_287);
lean_ctor_set(x_295, 3, x_291);
lean_ctor_set(x_295, 4, x_292);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_189);
x_305 = lean_ctor_get(x_198, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_198, 1);
lean_inc(x_306);
lean_dec_ref(x_198);
x_307 = lean_unsigned_to_nat(3u);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 2, x_306);
lean_ctor_set(x_271, 1, x_305);
lean_ctor_set(x_271, 0, x_194);
x_308 = x_271;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_194);
lean_ctor_set(x_313, 1, x_305);
lean_ctor_set(x_313, 2, x_306);
lean_ctor_set(x_313, 3, x_192);
lean_ctor_set(x_313, 4, x_192);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_308);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_307);
x_309 = x_196;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_190);
lean_ctor_set(x_311, 2, x_191);
lean_ctor_set(x_311, 3, x_308);
lean_ctor_set(x_311, 4, x_193);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_198, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_198, 1);
lean_inc(x_315);
lean_dec_ref(x_198);
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
x_316 = x_271;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_322, 0, x_189);
lean_ctor_set(x_322, 1, x_190);
lean_ctor_set(x_322, 2, x_191);
lean_ctor_set(x_322, 3, x_193);
lean_ctor_set(x_322, 4, x_193);
x_316 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_unsigned_to_nat(2u);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_316);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 2, x_315);
lean_ctor_set(x_196, 1, x_314);
lean_ctor_set(x_196, 0, x_317);
x_318 = x_196;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_314);
lean_ctor_set(x_320, 2, x_315);
lean_ctor_set(x_320, 3, x_193);
lean_ctor_set(x_320, 4, x_316);
x_318 = x_320;
goto block_319;
}
block_319:
{
return x_318;
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
lean_object* x_337; uint8_t x_338; uint8_t x_489; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
x_489 = !lean_is_exclusive(x_6);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = lean_ctor_get(x_6, 4);
lean_dec(x_490);
x_491 = lean_ctor_get(x_6, 3);
lean_dec(x_491);
x_492 = lean_ctor_get(x_6, 2);
lean_dec(x_492);
x_493 = lean_ctor_get(x_6, 1);
lean_dec(x_493);
x_494 = lean_ctor_get(x_6, 0);
lean_dec(x_494);
x_337 = x_6;
x_338 = x_489;
goto block_488;
}
else
{
lean_dec(x_6);
x_337 = lean_box(0);
x_338 = x_489;
goto block_488;
}
block_488:
{
lean_object* x_339; lean_object* x_340; 
x_339 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_190, x_191, x_192, x_193);
x_340 = lean_ctor_get(x_339, 2);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec_ref(x_339);
x_343 = lean_ctor_get(x_340, 0);
x_344 = lean_unsigned_to_nat(3u);
x_345 = lean_nat_mul(x_344, x_343);
x_346 = lean_nat_dec_lt(x_345, x_184);
lean_dec(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_188);
x_347 = lean_nat_add(x_194, x_184);
x_348 = lean_nat_add(x_347, x_343);
lean_dec(x_347);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_348);
x_349 = x_337;
goto block_350;
}
else
{
lean_object* x_351; 
x_351 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_341);
lean_ctor_set(x_351, 2, x_342);
lean_ctor_set(x_351, 3, x_5);
lean_ctor_set(x_351, 4, x_340);
x_349 = x_351;
goto block_350;
}
block_350:
{
return x_349;
}
}
else
{
lean_object* x_352; uint8_t x_353; uint8_t x_417; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_417 = !lean_is_exclusive(x_5);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_5, 4);
lean_dec(x_418);
x_419 = lean_ctor_get(x_5, 3);
lean_dec(x_419);
x_420 = lean_ctor_get(x_5, 2);
lean_dec(x_420);
x_421 = lean_ctor_get(x_5, 1);
lean_dec(x_421);
x_422 = lean_ctor_get(x_5, 0);
lean_dec(x_422);
x_352 = x_5;
x_353 = x_417;
goto block_416;
}
else
{
lean_dec(x_5);
x_352 = lean_box(0);
x_353 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_354 = lean_ctor_get(x_187, 0);
x_355 = lean_ctor_get(x_188, 0);
x_356 = lean_ctor_get(x_188, 1);
x_357 = lean_ctor_get(x_188, 2);
x_358 = lean_ctor_get(x_188, 3);
x_359 = lean_ctor_get(x_188, 4);
x_360 = lean_unsigned_to_nat(2u);
x_361 = lean_nat_mul(x_360, x_354);
x_362 = lean_nat_dec_lt(x_355, x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; uint8_t x_400; 
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_del_object(x_352);
x_400 = !lean_is_exclusive(x_188);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_188, 4);
lean_dec(x_401);
x_402 = lean_ctor_get(x_188, 3);
lean_dec(x_402);
x_403 = lean_ctor_get(x_188, 2);
lean_dec(x_403);
x_404 = lean_ctor_get(x_188, 1);
lean_dec(x_404);
x_405 = lean_ctor_get(x_188, 0);
lean_dec(x_405);
x_363 = x_188;
x_364 = x_400;
goto block_399;
}
else
{
lean_dec(x_188);
x_363 = lean_box(0);
x_364 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_387; lean_object* x_388; 
x_365 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_366 = lean_nat_add(x_365, x_343);
lean_dec(x_365);
x_387 = lean_nat_add(x_194, x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_358, 0);
lean_inc(x_397);
x_388 = x_397;
goto block_396;
}
else
{
lean_object* x_398; 
x_398 = lean_unsigned_to_nat(0u);
x_388 = x_398;
goto block_396;
}
block_386:
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_nat_add(x_367, x_369);
lean_dec(x_369);
lean_dec(x_367);
lean_inc_ref(x_340);
if (x_364 == 0)
{
lean_ctor_set(x_363, 4, x_340);
lean_ctor_set(x_363, 3, x_359);
lean_ctor_set(x_363, 2, x_342);
lean_ctor_set(x_363, 1, x_341);
lean_ctor_set(x_363, 0, x_370);
x_371 = x_363;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_370);
lean_ctor_set(x_385, 1, x_341);
lean_ctor_set(x_385, 2, x_342);
lean_ctor_set(x_385, 3, x_359);
lean_ctor_set(x_385, 4, x_340);
x_371 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_372; uint8_t x_373; uint8_t x_378; 
x_378 = !lean_is_exclusive(x_340);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_340, 4);
lean_dec(x_379);
x_380 = lean_ctor_get(x_340, 3);
lean_dec(x_380);
x_381 = lean_ctor_get(x_340, 2);
lean_dec(x_381);
x_382 = lean_ctor_get(x_340, 1);
lean_dec(x_382);
x_383 = lean_ctor_get(x_340, 0);
lean_dec(x_383);
x_372 = x_340;
x_373 = x_378;
goto block_377;
}
else
{
lean_dec(x_340);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
lean_ctor_set(x_372, 4, x_371);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set(x_372, 2, x_357);
lean_ctor_set(x_372, 1, x_356);
lean_ctor_set(x_372, 0, x_366);
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_356);
lean_ctor_set(x_376, 2, x_357);
lean_ctor_set(x_376, 3, x_368);
lean_ctor_set(x_376, 4, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
block_396:
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_nat_add(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_358);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_186);
lean_ctor_set(x_337, 1, x_185);
lean_ctor_set(x_337, 0, x_389);
x_390 = x_337;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_185);
lean_ctor_set(x_395, 2, x_186);
lean_ctor_set(x_395, 3, x_187);
lean_ctor_set(x_395, 4, x_358);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
x_391 = lean_nat_add(x_194, x_343);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_359, 0);
lean_inc(x_392);
x_367 = x_391;
x_368 = x_390;
x_369 = x_392;
goto block_386;
}
else
{
lean_object* x_393; 
x_393 = lean_unsigned_to_nat(0u);
x_367 = x_391;
x_368 = x_390;
x_369 = x_393;
goto block_386;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_407 = lean_nat_add(x_406, x_343);
lean_dec(x_406);
x_408 = lean_nat_add(x_194, x_343);
x_409 = lean_nat_add(x_408, x_355);
lean_dec(x_408);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_409);
x_410 = x_337;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_415, 0, x_409);
lean_ctor_set(x_415, 1, x_341);
lean_ctor_set(x_415, 2, x_342);
lean_ctor_set(x_415, 3, x_188);
lean_ctor_set(x_415, 4, x_340);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_353 == 0)
{
lean_ctor_set(x_352, 4, x_410);
lean_ctor_set(x_352, 0, x_407);
x_411 = x_352;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_185);
lean_ctor_set(x_413, 2, x_186);
lean_ctor_set(x_413, 3, x_187);
lean_ctor_set(x_413, 4, x_410);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_423; uint8_t x_424; uint8_t x_446; 
lean_inc_ref(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_446 = !lean_is_exclusive(x_5);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_5, 4);
lean_dec(x_447);
x_448 = lean_ctor_get(x_5, 3);
lean_dec(x_448);
x_449 = lean_ctor_get(x_5, 2);
lean_dec(x_449);
x_450 = lean_ctor_get(x_5, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_5, 0);
lean_dec(x_451);
x_423 = x_5;
x_424 = x_446;
goto block_445;
}
else
{
lean_dec(x_5);
x_423 = lean_box(0);
x_424 = x_446;
goto block_445;
}
block_445:
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = lean_ctor_get(x_339, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_339, 1);
lean_inc(x_426);
lean_dec_ref(x_339);
x_427 = lean_ctor_get(x_188, 0);
x_428 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_429 = lean_nat_add(x_194, x_427);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_426);
lean_ctor_set(x_337, 1, x_425);
lean_ctor_set(x_337, 0, x_429);
x_430 = x_337;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_429);
lean_ctor_set(x_435, 1, x_425);
lean_ctor_set(x_435, 2, x_426);
lean_ctor_set(x_435, 3, x_188);
lean_ctor_set(x_435, 4, x_340);
x_430 = x_435;
goto block_434;
}
block_434:
{
lean_object* x_431; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_430);
lean_ctor_set(x_423, 0, x_428);
x_431 = x_423;
goto block_432;
}
else
{
lean_object* x_433; 
x_433 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_185);
lean_ctor_set(x_433, 2, x_186);
lean_ctor_set(x_433, 3, x_187);
lean_ctor_set(x_433, 4, x_430);
x_431 = x_433;
goto block_432;
}
block_432:
{
return x_431;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_184);
x_436 = lean_ctor_get(x_339, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_339, 1);
lean_inc(x_437);
lean_dec_ref(x_339);
x_438 = lean_unsigned_to_nat(3u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_437);
lean_ctor_set(x_337, 1, x_436);
lean_ctor_set(x_337, 0, x_194);
x_439 = x_337;
goto block_443;
}
else
{
lean_object* x_444; 
x_444 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_444, 0, x_194);
lean_ctor_set(x_444, 1, x_436);
lean_ctor_set(x_444, 2, x_437);
lean_ctor_set(x_444, 3, x_188);
lean_ctor_set(x_444, 4, x_188);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_439);
lean_ctor_set(x_423, 0, x_438);
x_440 = x_423;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_185);
lean_ctor_set(x_442, 2, x_186);
lean_ctor_set(x_442, 3, x_187);
lean_ctor_set(x_442, 4, x_439);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
}
else
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_452; uint8_t x_453; uint8_t x_476; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_476 = !lean_is_exclusive(x_5);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_477 = lean_ctor_get(x_5, 4);
lean_dec(x_477);
x_478 = lean_ctor_get(x_5, 3);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 2);
lean_dec(x_479);
x_480 = lean_ctor_get(x_5, 1);
lean_dec(x_480);
x_481 = lean_ctor_get(x_5, 0);
lean_dec(x_481);
x_452 = x_5;
x_453 = x_476;
goto block_475;
}
else
{
lean_dec(x_5);
x_452 = lean_box(0);
x_453 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_471; 
x_454 = lean_ctor_get(x_339, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_339, 1);
lean_inc(x_455);
lean_dec_ref(x_339);
x_456 = lean_ctor_get(x_188, 1);
x_457 = lean_ctor_get(x_188, 2);
x_471 = !lean_is_exclusive(x_188);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_188, 4);
lean_dec(x_472);
x_473 = lean_ctor_get(x_188, 3);
lean_dec(x_473);
x_474 = lean_ctor_get(x_188, 0);
lean_dec(x_474);
x_458 = x_188;
x_459 = x_471;
goto block_470;
}
else
{
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_188);
x_458 = lean_box(0);
x_459 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_unsigned_to_nat(3u);
if (x_459 == 0)
{
lean_ctor_set(x_458, 4, x_187);
lean_ctor_set(x_458, 3, x_187);
lean_ctor_set(x_458, 2, x_186);
lean_ctor_set(x_458, 1, x_185);
lean_ctor_set(x_458, 0, x_194);
x_461 = x_458;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_469, 0, x_194);
lean_ctor_set(x_469, 1, x_185);
lean_ctor_set(x_469, 2, x_186);
lean_ctor_set(x_469, 3, x_187);
lean_ctor_set(x_469, 4, x_187);
x_461 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_462; 
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_187);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_455);
lean_ctor_set(x_337, 1, x_454);
lean_ctor_set(x_337, 0, x_194);
x_462 = x_337;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_467, 0, x_194);
lean_ctor_set(x_467, 1, x_454);
lean_ctor_set(x_467, 2, x_455);
lean_ctor_set(x_467, 3, x_187);
lean_ctor_set(x_467, 4, x_187);
x_462 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_463; 
if (x_453 == 0)
{
lean_ctor_set(x_452, 4, x_462);
lean_ctor_set(x_452, 3, x_461);
lean_ctor_set(x_452, 2, x_457);
lean_ctor_set(x_452, 1, x_456);
lean_ctor_set(x_452, 0, x_460);
x_463 = x_452;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_460);
lean_ctor_set(x_465, 1, x_456);
lean_ctor_set(x_465, 2, x_457);
lean_ctor_set(x_465, 3, x_461);
lean_ctor_set(x_465, 4, x_462);
x_463 = x_465;
goto block_464;
}
block_464:
{
return x_463;
}
}
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_339, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_339, 1);
lean_inc(x_483);
lean_dec_ref(x_339);
x_484 = lean_unsigned_to_nat(2u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_483);
lean_ctor_set(x_337, 1, x_482);
lean_ctor_set(x_337, 0, x_484);
x_485 = x_337;
goto block_486;
}
else
{
lean_object* x_487; 
x_487 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_482);
lean_ctor_set(x_487, 2, x_483);
lean_ctor_set(x_487, 3, x_5);
lean_ctor_set(x_487, 4, x_188);
x_485 = x_487;
goto block_486;
}
block_486:
{
return x_485;
}
}
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_495; lean_object* x_496; 
x_495 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(x_1, x_6);
x_496 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_495) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_5, 0);
x_499 = lean_ctor_get(x_5, 1);
x_500 = lean_ctor_get(x_5, 2);
x_501 = lean_ctor_get(x_5, 3);
x_502 = lean_ctor_get(x_5, 4);
lean_inc(x_502);
x_503 = lean_unsigned_to_nat(3u);
x_504 = lean_nat_mul(x_503, x_497);
x_505 = lean_nat_dec_lt(x_504, x_498);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_502);
x_506 = lean_nat_add(x_496, x_498);
x_507 = lean_nat_add(x_506, x_497);
lean_dec(x_497);
lean_dec(x_506);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_507);
x_508 = x_7;
goto block_509;
}
else
{
lean_object* x_510; 
x_510 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_3);
lean_ctor_set(x_510, 2, x_4);
lean_ctor_set(x_510, 3, x_5);
lean_ctor_set(x_510, 4, x_495);
x_508 = x_510;
goto block_509;
}
block_509:
{
return x_508;
}
}
else
{
lean_object* x_511; uint8_t x_512; uint8_t x_576; 
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
x_576 = !lean_is_exclusive(x_5);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_577 = lean_ctor_get(x_5, 4);
lean_dec(x_577);
x_578 = lean_ctor_get(x_5, 3);
lean_dec(x_578);
x_579 = lean_ctor_get(x_5, 2);
lean_dec(x_579);
x_580 = lean_ctor_get(x_5, 1);
lean_dec(x_580);
x_581 = lean_ctor_get(x_5, 0);
lean_dec(x_581);
x_511 = x_5;
x_512 = x_576;
goto block_575;
}
else
{
lean_dec(x_5);
x_511 = lean_box(0);
x_512 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_513 = lean_ctor_get(x_501, 0);
x_514 = lean_ctor_get(x_502, 0);
x_515 = lean_ctor_get(x_502, 1);
x_516 = lean_ctor_get(x_502, 2);
x_517 = lean_ctor_get(x_502, 3);
x_518 = lean_ctor_get(x_502, 4);
x_519 = lean_unsigned_to_nat(2u);
x_520 = lean_nat_mul(x_519, x_513);
x_521 = lean_nat_dec_lt(x_514, x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; uint8_t x_523; uint8_t x_550; 
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
x_550 = !lean_is_exclusive(x_502);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_551 = lean_ctor_get(x_502, 4);
lean_dec(x_551);
x_552 = lean_ctor_get(x_502, 3);
lean_dec(x_552);
x_553 = lean_ctor_get(x_502, 2);
lean_dec(x_553);
x_554 = lean_ctor_get(x_502, 1);
lean_dec(x_554);
x_555 = lean_ctor_get(x_502, 0);
lean_dec(x_555);
x_522 = x_502;
x_523 = x_550;
goto block_549;
}
else
{
lean_dec(x_502);
x_522 = lean_box(0);
x_523 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_537; lean_object* x_538; 
x_524 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_525 = lean_nat_add(x_524, x_497);
lean_dec(x_524);
x_537 = lean_nat_add(x_496, x_513);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_517, 0);
lean_inc(x_547);
x_538 = x_547;
goto block_546;
}
else
{
lean_object* x_548; 
x_548 = lean_unsigned_to_nat(0u);
x_538 = x_548;
goto block_546;
}
block_536:
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_nat_add(x_526, x_528);
lean_dec(x_528);
lean_dec(x_526);
if (x_523 == 0)
{
lean_ctor_set(x_522, 4, x_495);
lean_ctor_set(x_522, 3, x_518);
lean_ctor_set(x_522, 2, x_4);
lean_ctor_set(x_522, 1, x_3);
lean_ctor_set(x_522, 0, x_529);
x_530 = x_522;
goto block_534;
}
else
{
lean_object* x_535; 
x_535 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_535, 0, x_529);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set(x_535, 4, x_495);
x_530 = x_535;
goto block_534;
}
block_534:
{
lean_object* x_531; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_530);
lean_ctor_set(x_511, 3, x_527);
lean_ctor_set(x_511, 2, x_516);
lean_ctor_set(x_511, 1, x_515);
lean_ctor_set(x_511, 0, x_525);
x_531 = x_511;
goto block_532;
}
else
{
lean_object* x_533; 
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_525);
lean_ctor_set(x_533, 1, x_515);
lean_ctor_set(x_533, 2, x_516);
lean_ctor_set(x_533, 3, x_527);
lean_ctor_set(x_533, 4, x_530);
x_531 = x_533;
goto block_532;
}
block_532:
{
return x_531;
}
}
}
block_546:
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_nat_add(x_537, x_538);
lean_dec(x_538);
lean_dec(x_537);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_517);
lean_ctor_set(x_7, 3, x_501);
lean_ctor_set(x_7, 2, x_500);
lean_ctor_set(x_7, 1, x_499);
lean_ctor_set(x_7, 0, x_539);
x_540 = x_7;
goto block_544;
}
else
{
lean_object* x_545; 
x_545 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_545, 0, x_539);
lean_ctor_set(x_545, 1, x_499);
lean_ctor_set(x_545, 2, x_500);
lean_ctor_set(x_545, 3, x_501);
lean_ctor_set(x_545, 4, x_517);
x_540 = x_545;
goto block_544;
}
block_544:
{
lean_object* x_541; 
x_541 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_518, 0);
lean_inc(x_542);
x_526 = x_541;
x_527 = x_540;
x_528 = x_542;
goto block_536;
}
else
{
lean_object* x_543; 
x_543 = lean_unsigned_to_nat(0u);
x_526 = x_541;
x_527 = x_540;
x_528 = x_543;
goto block_536;
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_del_object(x_7);
x_556 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_557 = lean_nat_add(x_556, x_497);
lean_dec(x_556);
x_558 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
x_559 = lean_nat_add(x_558, x_514);
lean_dec(x_558);
lean_inc_ref(x_495);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_495);
lean_ctor_set(x_511, 3, x_502);
lean_ctor_set(x_511, 2, x_4);
lean_ctor_set(x_511, 1, x_3);
lean_ctor_set(x_511, 0, x_559);
x_560 = x_511;
goto block_573;
}
else
{
lean_object* x_574; 
x_574 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_574, 0, x_559);
lean_ctor_set(x_574, 1, x_3);
lean_ctor_set(x_574, 2, x_4);
lean_ctor_set(x_574, 3, x_502);
lean_ctor_set(x_574, 4, x_495);
x_560 = x_574;
goto block_573;
}
block_573:
{
lean_object* x_561; uint8_t x_562; uint8_t x_567; 
x_567 = !lean_is_exclusive(x_495);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_495, 4);
lean_dec(x_568);
x_569 = lean_ctor_get(x_495, 3);
lean_dec(x_569);
x_570 = lean_ctor_get(x_495, 2);
lean_dec(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_dec(x_571);
x_572 = lean_ctor_get(x_495, 0);
lean_dec(x_572);
x_561 = x_495;
x_562 = x_567;
goto block_566;
}
else
{
lean_dec(x_495);
x_561 = lean_box(0);
x_562 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_563; 
if (x_562 == 0)
{
lean_ctor_set(x_561, 4, x_560);
lean_ctor_set(x_561, 3, x_501);
lean_ctor_set(x_561, 2, x_500);
lean_ctor_set(x_561, 1, x_499);
lean_ctor_set(x_561, 0, x_557);
x_563 = x_561;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_565, 0, x_557);
lean_ctor_set(x_565, 1, x_499);
lean_ctor_set(x_565, 2, x_500);
lean_ctor_set(x_565, 3, x_501);
lean_ctor_set(x_565, 4, x_560);
x_563 = x_565;
goto block_564;
}
block_564:
{
return x_563;
}
}
}
}
}
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_495, 0);
lean_inc(x_582);
x_583 = lean_nat_add(x_496, x_582);
lean_dec(x_582);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_583);
x_584 = x_7;
goto block_585;
}
else
{
lean_object* x_586; 
x_586 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_3);
lean_ctor_set(x_586, 2, x_4);
lean_ctor_set(x_586, 3, x_5);
lean_ctor_set(x_586, 4, x_495);
x_584 = x_586;
goto block_585;
}
block_585:
{
return x_584;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_587; 
x_587 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
lean_inc_ref(x_587);
x_588 = lean_ctor_get(x_5, 4);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; uint8_t x_604; 
x_589 = lean_ctor_get(x_5, 0);
x_590 = lean_ctor_get(x_5, 1);
x_591 = lean_ctor_get(x_5, 2);
x_604 = !lean_is_exclusive(x_5);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_5, 4);
lean_dec(x_605);
x_606 = lean_ctor_get(x_5, 3);
lean_dec(x_606);
x_592 = x_5;
x_593 = x_604;
goto block_603;
}
else
{
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_5);
x_592 = lean_box(0);
x_593 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_588, 0);
x_595 = lean_nat_add(x_496, x_589);
lean_dec(x_589);
x_596 = lean_nat_add(x_496, x_594);
if (x_593 == 0)
{
lean_ctor_set(x_592, 4, x_495);
lean_ctor_set(x_592, 3, x_588);
lean_ctor_set(x_592, 2, x_4);
lean_ctor_set(x_592, 1, x_3);
lean_ctor_set(x_592, 0, x_596);
x_597 = x_592;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_3);
lean_ctor_set(x_602, 2, x_4);
lean_ctor_set(x_602, 3, x_588);
lean_ctor_set(x_602, 4, x_495);
x_597 = x_602;
goto block_601;
}
block_601:
{
lean_object* x_598; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_597);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_591);
lean_ctor_set(x_7, 1, x_590);
lean_ctor_set(x_7, 0, x_595);
x_598 = x_7;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_600, 0, x_595);
lean_ctor_set(x_600, 1, x_590);
lean_ctor_set(x_600, 2, x_591);
lean_ctor_set(x_600, 3, x_587);
lean_ctor_set(x_600, 4, x_597);
x_598 = x_600;
goto block_599;
}
block_599:
{
return x_598;
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; uint8_t x_619; 
x_607 = lean_ctor_get(x_5, 1);
x_608 = lean_ctor_get(x_5, 2);
x_619 = !lean_is_exclusive(x_5);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_5, 4);
lean_dec(x_620);
x_621 = lean_ctor_get(x_5, 3);
lean_dec(x_621);
x_622 = lean_ctor_get(x_5, 0);
lean_dec(x_622);
x_609 = x_5;
x_610 = x_619;
goto block_618;
}
else
{
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_5);
x_609 = lean_box(0);
x_610 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_unsigned_to_nat(3u);
if (x_610 == 0)
{
lean_ctor_set(x_609, 3, x_588);
lean_ctor_set(x_609, 2, x_4);
lean_ctor_set(x_609, 1, x_3);
lean_ctor_set(x_609, 0, x_496);
x_612 = x_609;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_617, 0, x_496);
lean_ctor_set(x_617, 1, x_3);
lean_ctor_set(x_617, 2, x_4);
lean_ctor_set(x_617, 3, x_588);
lean_ctor_set(x_617, 4, x_588);
x_612 = x_617;
goto block_616;
}
block_616:
{
lean_object* x_613; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_612);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_608);
lean_ctor_set(x_7, 1, x_607);
lean_ctor_set(x_7, 0, x_611);
x_613 = x_7;
goto block_614;
}
else
{
lean_object* x_615; 
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_611);
lean_ctor_set(x_615, 1, x_607);
lean_ctor_set(x_615, 2, x_608);
lean_ctor_set(x_615, 3, x_587);
lean_ctor_set(x_615, 4, x_612);
x_613 = x_615;
goto block_614;
}
block_614:
{
return x_613;
}
}
}
}
}
else
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_5, 4);
lean_inc(x_623);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; uint8_t x_648; 
lean_inc(x_587);
x_624 = lean_ctor_get(x_5, 1);
x_625 = lean_ctor_get(x_5, 2);
x_648 = !lean_is_exclusive(x_5);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_5, 4);
lean_dec(x_649);
x_650 = lean_ctor_get(x_5, 3);
lean_dec(x_650);
x_651 = lean_ctor_get(x_5, 0);
lean_dec(x_651);
x_626 = x_5;
x_627 = x_648;
goto block_647;
}
else
{
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_5);
x_626 = lean_box(0);
x_627 = x_648;
goto block_647;
}
block_647:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_643; 
x_628 = lean_ctor_get(x_623, 1);
x_629 = lean_ctor_get(x_623, 2);
x_643 = !lean_is_exclusive(x_623);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_623, 4);
lean_dec(x_644);
x_645 = lean_ctor_get(x_623, 3);
lean_dec(x_645);
x_646 = lean_ctor_get(x_623, 0);
lean_dec(x_646);
x_630 = x_623;
x_631 = x_643;
goto block_642;
}
else
{
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_623);
x_630 = lean_box(0);
x_631 = x_643;
goto block_642;
}
block_642:
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_unsigned_to_nat(3u);
if (x_631 == 0)
{
lean_ctor_set(x_630, 4, x_587);
lean_ctor_set(x_630, 3, x_587);
lean_ctor_set(x_630, 2, x_625);
lean_ctor_set(x_630, 1, x_624);
lean_ctor_set(x_630, 0, x_496);
x_633 = x_630;
goto block_640;
}
else
{
lean_object* x_641; 
x_641 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_641, 0, x_496);
lean_ctor_set(x_641, 1, x_624);
lean_ctor_set(x_641, 2, x_625);
lean_ctor_set(x_641, 3, x_587);
lean_ctor_set(x_641, 4, x_587);
x_633 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_634; 
if (x_627 == 0)
{
lean_ctor_set(x_626, 4, x_587);
lean_ctor_set(x_626, 2, x_4);
lean_ctor_set(x_626, 1, x_3);
lean_ctor_set(x_626, 0, x_496);
x_634 = x_626;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_639, 0, x_496);
lean_ctor_set(x_639, 1, x_3);
lean_ctor_set(x_639, 2, x_4);
lean_ctor_set(x_639, 3, x_587);
lean_ctor_set(x_639, 4, x_587);
x_634 = x_639;
goto block_638;
}
block_638:
{
lean_object* x_635; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_634);
lean_ctor_set(x_7, 3, x_633);
lean_ctor_set(x_7, 2, x_629);
lean_ctor_set(x_7, 1, x_628);
lean_ctor_set(x_7, 0, x_632);
x_635 = x_7;
goto block_636;
}
else
{
lean_object* x_637; 
x_637 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_637, 0, x_632);
lean_ctor_set(x_637, 1, x_628);
lean_ctor_set(x_637, 2, x_629);
lean_ctor_set(x_637, 3, x_633);
lean_ctor_set(x_637, 4, x_634);
x_635 = x_637;
goto block_636;
}
block_636:
{
return x_635;
}
}
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_623);
lean_ctor_set(x_7, 0, x_652);
x_653 = x_7;
goto block_654;
}
else
{
lean_object* x_655; 
x_655 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_3);
lean_ctor_set(x_655, 2, x_4);
lean_ctor_set(x_655, 3, x_5);
lean_ctor_set(x_655, 4, x_623);
x_653 = x_655;
goto block_654;
}
block_654:
{
return x_653;
}
}
}
}
else
{
lean_object* x_656; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 0, x_496);
x_656 = x_7;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_658, 0, x_496);
lean_ctor_set(x_658, 1, x_3);
lean_ctor_set(x_658, 2, x_4);
lean_ctor_set(x_658, 3, x_5);
lean_ctor_set(x_658, 4, x_5);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
x_4 = x_1;
x_5 = x_15;
goto block_14;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_3);
x_6 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(x_2, x_3);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Options_erase_spec__1(x_7, x_3);
lean_dec(x_3);
x_9 = ((lean_object*)(l_Lean_Options_erase___closed__0));
x_10 = l_List_any___redArg(x_8, x_9);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_6);
x_11 = x_4;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_6);
x_11 = x_13;
goto block_12;
}
block_12:
{
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_erase___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Options_erase(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Options_erase_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
x_7 = x_4;
x_8 = x_14;
goto block_13;
}
else
{
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_3(x_2, x_3, x_6, x_1);
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_25; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
x_11 = x_5;
x_12 = x_25;
goto block_24;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_25;
goto block_24;
}
block_24:
{
uint8_t x_13; 
x_13 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_4, x_7);
switch (x_13) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_del_object(x_11);
lean_dec(x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(x_1, x_2, x_3, x_4, x_9);
x_15 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_7, x_8, x_14, x_10);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_8);
x_17 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(x_1, x_2, x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (x_12 == 0)
{
lean_ctor_set(x_11, 2, x_18);
lean_ctor_set(x_11, 1, x_4);
x_19 = x_11;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_9);
lean_ctor_set(x_21, 4, x_10);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; 
lean_del_object(x_11);
lean_dec(x_6);
x_22 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(x_1, x_2, x_3, x_4, x_10);
x_23 = l_Std_DTreeMap_Internal_Impl_balance___redArg(x_7, x_8, x_9, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_box(0);
x_27 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg___lam__0(x_1, x_2, x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_5);
lean_ctor_set(x_30, 4, x_5);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(x_1, x_2, x_6);
lean_inc(x_4);
lean_inc_ref(x_1);
x_9 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(x_5, x_1, x_4, x_4, x_8);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_mergeBy(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_18; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_8 = x_3;
x_9 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_10; 
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(x_1, x_4, x_6);
if (x_5 == 0)
{
lean_object* x_11; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_7);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_14 = x_8;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_10);
x_14 = x_16;
goto block_15;
}
block_15:
{
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_5);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Options_mergeBy_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Options_mergeBy_spec__1_spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__12, &l_Lean_OptionDecl_declName___autoParam___closed__12_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__12);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__17));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__18, &l_Lean_OptionDecl_declName___autoParam___closed__18_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__18);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__19, &l_Lean_OptionDecl_declName___autoParam___closed__19_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__19);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__16));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__20, &l_Lean_OptionDecl_declName___autoParam___closed__20_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__20);
x_2 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__13, &l_Lean_OptionDecl_declName___autoParam___closed__13_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__21, &l_Lean_OptionDecl_declName___autoParam___closed__21_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__21);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__22, &l_Lean_OptionDecl_declName___autoParam___closed__22_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__22);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__23, &l_Lean_OptionDecl_declName___autoParam___closed__23_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__23);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__24, &l_Lean_OptionDecl_declName___autoParam___closed__24_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__24);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__25, &l_Lean_OptionDecl_declName___autoParam___closed__25_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__25);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__26, &l_Lean_OptionDecl_declName___autoParam___closed__26_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__26);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__27, &l_Lean_OptionDecl_declName___autoParam___closed__27_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__27);
x_2 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_instInhabitedOptionDecl_default___closed__0));
x_2 = l_Lean_instInhabitedDataValue_default;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instInhabitedOptionDecl_default___closed__1, &l_Lean_instInhabitedOptionDecl_default___closed__1_once, _init_l_Lean_instInhabitedOptionDecl_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedOptionDecl_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_OptionDecl_fullDescr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__2));
x_9 = l_Lean_Name_isPrefixOf(x_8, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_string_utf8_byte_size(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__3));
x_14 = lean_string_append(x_7, x_13);
x_2 = x_14;
goto block_5;
}
else
{
x_2 = x_7;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Lean_OptionDecl_fullDescr___closed__0));
x_4 = lean_string_append(x_2, x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(1);
x_3 = lean_st_mk_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l_Lean_registerOption___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_registerOption___closed__0));
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initializing();
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_31; 
x_5 = lean_ctor_get(x_4, 0);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
x_6 = x_4;
x_7 = x_31;
goto block_30;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_31;
goto block_30;
}
block_30:
{
uint8_t x_8; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_9 = lean_obj_once(&l_Lean_registerOption___closed__1, &l_Lean_registerOption___closed__1_once, _init_l_Lean_registerOption___closed__1);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
x_10 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_14 = lean_st_ref_get(x_13);
x_15 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_14);
x_17 = lean_st_ref_set(x_13, x_16);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_17);
x_18 = x_6;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec_ref(x_2);
x_21 = ((lean_object*)(l_Lean_registerOption___closed__2));
x_22 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_15);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lean_registerOption___closed__3));
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_mk_io_user_error(x_25);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_26);
x_27 = x_6;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_4, 0);
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
x_33 = x_4;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_register_option(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_3 = lean_st_ref_get(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getOptionDecls();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_12; 
x_2 = l_Lean_getOptionDecls();
x_3 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_4 = x_2;
x_5 = x_12;
goto block_11;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_getOptionDeclsArray___closed__0));
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(x_6, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_ctor_set(x_4, 0, x_7);
x_8 = x_4;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDeclsArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_option_decls_array();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getOptionDeclsArray_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_23; 
x_3 = l_Lean_getOptionDecls();
x_4 = lean_ctor_get(x_3, 0);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_5 = x_3;
x_6 = x_23;
goto block_22;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_1);
lean_dec(x_4);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_12 = ((lean_object*)(l_Lean_getOptionDecl___closed__0));
x_13 = 1;
x_14 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_Lean_getOptionDecl___closed__1));
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_mk_io_user_error(x_17);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_18);
x_19 = x_5;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_4 = lean_ctor_get(x_3, 0);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
x_5 = x_3;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_14 = x_3;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDefaultValue(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_4 = lean_ctor_get(x_3, 0);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
x_5 = x_3;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_7);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_14 = x_3;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDescr(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_3);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get_uint8(x_9, 0);
lean_dec_ref(x_9);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_box(x_3);
x_14 = lean_apply_2(x_2, lean_box(0), x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_getBoolOption___redArg___lam__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_getBoolOption___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getBoolOption___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_getBoolOption(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_apply_2(x_2, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 3)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_apply_2(x_2, lean_box(0), x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getNatOption___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getNatOption___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_3(x_2, lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
x_4 = 1;
x_5 = lean_box(x_4);
x_6 = l_Lean_Options_set___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_withInPattern___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_KVMap_instValueBool;
x_2 = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_obj_once(&l_Lean_withInPattern___redArg___closed__0, &l_Lean_withInPattern___redArg___closed__0_once, _init_l_Lean_withInPattern___redArg___closed__0);
x_4 = lean_apply_3(x_1, lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_withInPattern___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = ((lean_object*)(l_Lean_withInPattern___redArg___lam__0___closed__1));
x_4 = 0;
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Options_getInPattern(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedOption_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedOption_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedOption_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_1(x_6, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_get_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get_x3f(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_6, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec_ref(x_7);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_1(x_7, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_get___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t lean_options_get_bool(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_2);
lean_dec(x_2);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_getBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = lean_options_get_bool(x_1, x_2, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Option_get___redArg(x_1, x_4, x_2);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_getM___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Option_getM___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Option_getM___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_Options_set___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Option_set___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_6 = x_1;
x_7 = x_19;
goto block_18;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_8, 0, x_3);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_8, x_4);
if (x_5 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = ((lean_object*)(l_Lean_Options_insert___closed__1));
x_11 = l_Lean_Name_isPrefixOf(x_10, x_2);
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_9);
x_15 = x_6;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_5);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_options_update_bool(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Options_set___at___00__private_Lean_Data_Options_0__Lean_Option_updateBool_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_Option_updateBool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = lean_options_update_bool(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Option_set___redArg(x_1, x_2, x_3, x_4);
return x_8;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Option_setIfNotSet___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Option_register___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_OptionDecl_declName___autoParam___closed__28, &l_Lean_OptionDecl_declName___autoParam___closed__28_once, _init_l_Lean_OptionDecl_declName___autoParam___closed__28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_34; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
x_9 = x_3;
x_10 = x_34;
goto block_33;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_11 = lean_apply_1(x_6, x_7);
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_8);
lean_inc(x_2);
x_13 = lean_register_option(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_13, 0);
lean_dec(x_24);
x_14 = x_13;
x_15 = x_23;
goto block_22;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_16; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_2);
x_16 = x_9;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_7);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_del_object(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_25 = lean_ctor_get(x_13, 0);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
x_26 = x_13;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Option_register___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Option_register___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Option_register(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__5));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__16));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__0));
x_5 = ((lean_object*)(l_Lean_Option_registerBuiltinOption___closed__2));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_97; lean_object* x_98; lean_object* x_114; lean_object* x_126; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(7u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_126 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_box(0);
x_114 = x_127;
goto block_125;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_135; 
x_128 = lean_ctor_get(x_126, 0);
x_135 = !lean_is_exclusive(x_126);
if (x_135 == 0)
{
x_129 = x_126;
x_130 = x_135;
goto block_134;
}
else
{
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_128);
x_131 = x_133;
goto block_132;
}
block_132:
{
x_114 = x_131;
goto block_125;
}
}
}
block_78:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_31 = l_Array_append___redArg(x_22, x_30);
lean_dec_ref(x_30);
lean_inc(x_21);
lean_inc(x_26);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_31);
lean_inc_n(x_20, 5);
lean_inc(x_26);
x_33 = l_Lean_Syntax_node7(x_26, x_19, x_23, x_20, x_32, x_20, x_20, x_20, x_20);
x_34 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__0));
lean_inc_ref(x_27);
x_35 = l_Lean_Name_mkStr4(x_4, x_27, x_24, x_34);
x_36 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__1));
lean_inc(x_26);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_26);
x_38 = l_Lean_Syntax_node1(x_26, x_35, x_37);
x_39 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__14));
x_40 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__2));
lean_inc_ref(x_27);
x_41 = l_Lean_Name_mkStr4(x_4, x_27, x_39, x_40);
x_42 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
lean_inc(x_26);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_42);
x_44 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__4));
lean_inc_ref(x_27);
x_45 = l_Lean_Name_mkStr4(x_4, x_27, x_39, x_44);
x_46 = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
x_47 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc(x_28);
lean_inc(x_25);
x_48 = l_Lean_addMacroScope(x_25, x_47, x_28);
x_49 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
lean_inc(x_26);
x_50 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
lean_inc(x_21);
lean_inc(x_26);
x_51 = l_Lean_Syntax_node1(x_26, x_21, x_16);
lean_inc(x_45);
lean_inc(x_26);
x_52 = l_Lean_Syntax_node2(x_26, x_45, x_50, x_51);
lean_inc(x_26);
x_53 = l_Lean_Syntax_node2(x_26, x_41, x_43, x_52);
x_54 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
lean_inc(x_26);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_14);
lean_inc(x_21);
lean_inc(x_26);
x_56 = l_Lean_Syntax_node3(x_26, x_21, x_14, x_53, x_55);
x_57 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__13));
lean_inc_ref(x_27);
x_58 = l_Lean_Name_mkStr4(x_4, x_27, x_39, x_57);
x_59 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__14));
lean_inc_ref(x_27);
x_60 = l_Lean_Name_mkStr4(x_4, x_27, x_39, x_59);
x_61 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__15));
x_62 = l_Lean_Name_mkStr4(x_4, x_27, x_39, x_61);
x_63 = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
x_64 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
x_65 = l_Lean_addMacroScope(x_25, x_64, x_28);
x_66 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
lean_inc(x_26);
x_67 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_67, 0, x_26);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
x_68 = l_Lean_TSyntax_getId(x_14);
lean_dec(x_14);
x_69 = l_Lean_instQuoteNameMkStr1___private__1(x_68);
lean_inc(x_21);
lean_inc(x_26);
x_70 = l_Lean_Syntax_node2(x_26, x_21, x_69, x_18);
lean_inc(x_26);
x_71 = l_Lean_Syntax_node2(x_26, x_45, x_67, x_70);
lean_inc(x_26);
x_72 = l_Lean_Syntax_node1(x_26, x_62, x_71);
lean_inc(x_26);
x_73 = l_Lean_Syntax_node2(x_26, x_60, x_72, x_20);
lean_inc(x_26);
x_74 = l_Lean_Syntax_node1(x_26, x_21, x_73);
lean_inc(x_26);
x_75 = l_Lean_Syntax_node1(x_26, x_58, x_74);
x_76 = l_Lean_Syntax_node4(x_26, x_29, x_33, x_38, x_56, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_3);
return x_77;
}
block_96:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_inc_ref(x_82);
x_90 = l_Array_append___redArg(x_82, x_89);
lean_dec_ref(x_89);
lean_inc(x_81);
lean_inc(x_85);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_90);
lean_inc_ref(x_82);
lean_inc(x_81);
lean_inc(x_85);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_81);
lean_ctor_set(x_92, 2, x_82);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
lean_dec_ref(x_80);
x_94 = l_Array_mkArray1___redArg(x_93);
x_19 = x_79;
x_20 = x_92;
x_21 = x_81;
x_22 = x_82;
x_23 = x_91;
x_24 = x_83;
x_25 = x_84;
x_26 = x_85;
x_27 = x_86;
x_28 = x_87;
x_29 = x_88;
x_30 = x_94;
goto block_78;
}
else
{
lean_object* x_95; 
lean_dec(x_80);
x_95 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_19 = x_79;
x_20 = x_92;
x_21 = x_81;
x_22 = x_82;
x_23 = x_91;
x_24 = x_83;
x_25 = x_84;
x_26 = x_85;
x_27 = x_86;
x_28 = x_87;
x_29 = x_88;
x_30 = x_95;
goto block_78;
}
}
block_113:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 5);
lean_inc(x_101);
lean_dec_ref(x_2);
x_102 = 0;
x_103 = l_Lean_SourceInfo_fromRef(x_101, x_102);
lean_dec(x_101);
x_104 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__1));
x_105 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__22));
x_106 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
x_107 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__26));
x_108 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
x_109 = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_98, 0);
lean_inc(x_110);
lean_dec_ref(x_98);
x_111 = l_Array_mkArray1___redArg(x_110);
x_79 = x_107;
x_80 = x_97;
x_81 = x_108;
x_82 = x_109;
x_83 = x_105;
x_84 = x_99;
x_85 = x_103;
x_86 = x_104;
x_87 = x_100;
x_88 = x_106;
x_89 = x_111;
goto block_96;
}
else
{
lean_object* x_112; 
lean_dec(x_98);
x_112 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__5));
x_79 = x_107;
x_80 = x_97;
x_81 = x_108;
x_82 = x_109;
x_83 = x_105;
x_84 = x_99;
x_85 = x_103;
x_86 = x_104;
x_87 = x_100;
x_88 = x_106;
x_89 = x_112;
goto block_96;
}
}
block_125:
{
lean_object* x_115; 
x_115 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
x_97 = x_114;
x_98 = x_116;
goto block_113;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_124 = !lean_is_exclusive(x_115);
if (x_124 == 0)
{
x_118 = x_115;
x_119 = x_124;
goto block_123;
}
else
{
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_box(0);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_119 == 0)
{
x_120 = x_118;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_117);
x_120 = x_122;
goto block_121;
}
block_121:
{
x_97 = x_114;
x_98 = x_120;
goto block_113;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Option_registerOption___closed__1));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(6u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_10, x_19);
lean_dec(x_10);
x_21 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__23));
x_22 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__24));
x_23 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__0));
lean_inc(x_20);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_inc(x_20);
x_25 = l_Lean_Syntax_node1(x_20, x_23, x_24);
x_26 = ((lean_object*)(l_Lean_OptionDecl_declName___autoParam___closed__9));
x_27 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__1));
x_28 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__3));
lean_inc(x_20);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__2));
x_31 = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__6);
x_32 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__7));
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_addMacroScope(x_8, x_32, x_9);
x_34 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__11));
lean_inc(x_20);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_inc(x_20);
x_36 = l_Lean_Syntax_node1(x_20, x_26, x_16);
lean_inc(x_20);
x_37 = l_Lean_Syntax_node2(x_20, x_30, x_35, x_36);
lean_inc(x_20);
x_38 = l_Lean_Syntax_node2(x_20, x_27, x_29, x_37);
x_39 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__12));
lean_inc(x_20);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_14);
lean_inc(x_20);
x_41 = l_Lean_Syntax_node3(x_20, x_26, x_14, x_38, x_40);
x_42 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__3));
x_43 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__4));
x_44 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1___closed__5));
x_45 = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__17);
x_46 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__19));
x_47 = l_Lean_addMacroScope(x_8, x_46, x_9);
x_48 = ((lean_object*)(l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__21));
lean_inc(x_20);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_20);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Lean_TSyntax_getId(x_14);
lean_dec(x_14);
x_51 = l_Lean_instQuoteNameMkStr1___private__1(x_50);
lean_inc(x_20);
x_52 = l_Lean_Syntax_node2(x_20, x_26, x_51, x_18);
lean_inc(x_20);
x_53 = l_Lean_Syntax_node2(x_20, x_30, x_49, x_52);
lean_inc(x_20);
x_54 = l_Lean_Syntax_node1(x_20, x_44, x_53);
x_55 = lean_obj_once(&l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27, &l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27_once, _init_l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1___closed__27);
lean_inc(x_20);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_20);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_20);
x_57 = l_Lean_Syntax_node2(x_20, x_43, x_54, x_56);
lean_inc(x_20);
x_58 = l_Lean_Syntax_node1(x_20, x_26, x_57);
lean_inc(x_20);
x_59 = l_Lean_Syntax_node1(x_20, x_42, x_58);
x_60 = l_Lean_Syntax_node4(x_20, x_22, x_12, x_25, x_41, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
return x_61;
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
res = runtime_initialize_Lean_ImportingFlag(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_KVMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedOptionDecl_default = _init_l_Lean_instInhabitedOptionDecl_default();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl_default);
l_Lean_instInhabitedOptionDecl = _init_l_Lean_instInhabitedOptionDecl();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl);
l_Lean_instInhabitedOptionDecls = _init_l_Lean_instInhabitedOptionDecls();
lean_mark_persistent(l_Lean_instInhabitedOptionDecls);
res = l___private_Lean_Data_Options_0__Lean_initFn_00___x40_Lean_Data_Options_2861175937____hygCtx___hyg_2_()
;
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
res = initialize_Lean_ImportingFlag(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Options(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Options(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Options(builtin);
}
#ifdef __cplusplus
}
#endif
