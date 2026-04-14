// Lean compiler output
// Module: Lean.Data.NameTrie
// Imports: public import Lean.Data.PrefixTree import Init.Data.Ord.String
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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqNamePart_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqNamePart_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqNamePart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqNamePart_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqNamePart___closed__0 = (const lean_object*)&l_Lean_instBEqNamePart___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqNamePart = (const lean_object*)&l_Lean_instBEqNamePart___closed__0_value;
static const lean_string_object l_Lean_instInhabitedNamePart_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedNamePart_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedNamePart_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedNamePart_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedNamePart_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedNamePart_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedNamePart_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNamePart_default = (const lean_object*)&l_Lean_instInhabitedNamePart_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedNamePart = (const lean_object*)&l_Lean_instInhabitedNamePart_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instToStringNamePart___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToStringNamePart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToStringNamePart___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringNamePart___closed__0 = (const lean_object*)&l_Lean_instToStringNamePart___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringNamePart = (const lean_object*)&l_Lean_instToStringNamePart___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_NamePart_cmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_cmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NamePart_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameTrie_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NamePart_cmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameTrie_empty___closed__0 = (const lean_object*)&l_Lean_NameTrie_empty___closed__0_value;
static lean_once_cell_t l_Lean_NameTrie_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameTrie_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedNameTrie___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedNameTrie___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_NameTrie_foldM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameTrie_foldM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_NameTrie_matchingToArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_NameTrie_matchingToArray___redArg___closed__0 = (const lean_object*)&l_Lean_NameTrie_matchingToArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_NamePart_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_s_8_; lean_object* v___x_9_; 
v_s_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_s_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_s_8_);
return v___x_9_;
}
else
{
lean_object* v_n_10_; lean_object* v___x_11_; 
v_n_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_n_10_);
lean_dec_ref(v_t_6_);
v___x_11_ = lean_apply_1(v_k_7_, v_n_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_NamePart_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_NamePart_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_str_elim___redArg(lean_object* v_t_24_, lean_object* v_str_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_NamePart_ctorElim___redArg(v_t_24_, v_str_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_str_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_str_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_NamePart_ctorElim___redArg(v_t_28_, v_str_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_num_elim___redArg(lean_object* v_t_32_, lean_object* v_num_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_NamePart_ctorElim___redArg(v_t_32_, v_num_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_num_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_num_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_NamePart_ctorElim___redArg(v_t_36_, v_num_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqNamePart_beq(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_object* v_s_42_; lean_object* v_s_43_; uint8_t v___x_44_; 
v_s_42_ = lean_ctor_get(v_x_40_, 0);
v_s_43_ = lean_ctor_get(v_x_41_, 0);
v___x_44_ = lean_string_dec_eq(v_s_42_, v_s_43_);
return v___x_44_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
}
else
{
if (lean_obj_tag(v_x_41_) == 1)
{
lean_object* v_n_46_; lean_object* v_n_47_; uint8_t v___x_48_; 
v_n_46_ = lean_ctor_get(v_x_40_, 0);
v_n_47_ = lean_ctor_get(v_x_41_, 0);
v___x_48_ = lean_nat_dec_eq(v_n_46_, v_n_47_);
return v___x_48_;
}
else
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqNamePart_beq___boxed(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_instBEqNamePart_beq(v_x_50_, v_x_51_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringNamePart___lam__0(lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 0)
{
lean_object* v_s_62_; 
v_s_62_ = lean_ctor_get(v_x_61_, 0);
lean_inc_ref(v_s_62_);
lean_dec_ref(v_x_61_);
return v_s_62_;
}
else
{
lean_object* v_n_63_; lean_object* v___x_64_; 
v_n_63_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_n_63_);
lean_dec_ref(v_x_61_);
v___x_64_ = l_Nat_reprFast(v_n_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NamePart_cmp(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
if (lean_obj_tag(v_x_68_) == 0)
{
lean_object* v_s_69_; lean_object* v_s_70_; uint8_t v___x_71_; 
v_s_69_ = lean_ctor_get(v_x_67_, 0);
v_s_70_ = lean_ctor_get(v_x_68_, 0);
v___x_71_ = lean_string_dec_lt(v_s_69_, v_s_70_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; 
v___x_72_ = lean_string_dec_eq(v_s_69_, v_s_70_);
if (v___x_72_ == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 2;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 2;
return v___x_76_;
}
}
else
{
if (lean_obj_tag(v_x_68_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
else
{
lean_object* v_n_78_; lean_object* v_n_79_; uint8_t v___x_80_; 
v_n_78_ = lean_ctor_get(v_x_67_, 0);
v_n_79_ = lean_ctor_get(v_x_68_, 0);
v___x_80_ = lean_nat_dec_lt(v_n_78_, v_n_79_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = lean_nat_dec_eq(v_n_78_, v_n_79_);
if (v___x_81_ == 0)
{
uint8_t v___x_82_; 
v___x_82_ = 2;
return v___x_82_;
}
else
{
uint8_t v___x_83_; 
v___x_83_ = 1;
return v___x_83_;
}
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_cmp___boxed(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_NamePart_cmp(v_x_85_, v_x_86_);
lean_dec_ref(v_x_86_);
lean_dec_ref(v_x_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint8_t l_Lean_NamePart_lt(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v_s_91_; lean_object* v_s_92_; uint8_t v___x_93_; 
v_s_91_ = lean_ctor_get(v_x_89_, 0);
v_s_92_ = lean_ctor_get(v_x_90_, 0);
v___x_93_ = lean_string_dec_lt(v_s_91_, v_s_92_);
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
else
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 1;
return v___x_95_;
}
else
{
lean_object* v_n_96_; lean_object* v_n_97_; uint8_t v___x_98_; 
v_n_96_ = lean_ctor_get(v_x_89_, 0);
v_n_97_ = lean_ctor_get(v_x_90_, 0);
v___x_98_ = lean_nat_dec_lt(v_n_96_, v_n_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_lt___boxed(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lean_NamePart_lt(v_x_99_, v_x_100_);
lean_dec_ref(v_x_100_);
lean_dec_ref(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
switch(lean_obj_tag(v_x_103_))
{
case 0:
{
return v_x_104_;
}
case 1:
{
lean_object* v_pre_105_; lean_object* v_str_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_pre_105_ = lean_ctor_get(v_x_103_, 0);
v_str_106_ = lean_ctor_get(v_x_103_, 1);
lean_inc_ref(v_str_106_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v_str_106_);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_x_104_);
v_x_103_ = v_pre_105_;
v_x_104_ = v___x_108_;
goto _start;
}
default: 
{
lean_object* v_pre_110_; lean_object* v_i_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_pre_110_ = lean_ctor_get(v_x_103_, 0);
v_i_111_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_i_111_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_i_111_);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_x_104_);
v_x_103_ = v_pre_110_;
v_x_104_ = v___x_113_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_x_115_, v_x_116_);
lean_dec(v_x_115_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey(lean_object* v_n_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_box(0);
v___x_120_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_n_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(lean_object* v_n_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_121_);
lean_dec(v_n_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(lean_object* v_t_123_, lean_object* v_k_124_){
_start:
{
if (lean_obj_tag(v_t_123_) == 0)
{
lean_object* v_k_125_; lean_object* v_v_126_; lean_object* v_l_127_; lean_object* v_r_128_; uint8_t v___x_129_; 
v_k_125_ = lean_ctor_get(v_t_123_, 1);
v_v_126_ = lean_ctor_get(v_t_123_, 2);
v_l_127_ = lean_ctor_get(v_t_123_, 3);
v_r_128_ = lean_ctor_get(v_t_123_, 4);
v___x_129_ = l_Lean_NamePart_cmp(v_k_124_, v_k_125_);
switch(v___x_129_)
{
case 0:
{
v_t_123_ = v_l_127_;
goto _start;
}
case 1:
{
lean_object* v___x_131_; 
lean_inc(v_v_126_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_v_126_);
return v___x_131_;
}
default: 
{
v_t_123_ = v_r_128_;
goto _start;
}
}
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_box(0);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(lean_object* v_t_134_, lean_object* v_k_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_134_, v_k_135_);
lean_dec_ref(v_k_135_);
lean_dec(v_t_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_box(1);
v___x_139_ = lean_panic_fn_borrowed(v___x_138_, v_msg_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_143_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_144_ = lean_unsigned_to_nat(35u);
v___x_145_ = lean_unsigned_to_nat(182u);
v___x_146_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_148_ = l_mkPanicMessageWithDecl(v___x_147_, v___x_146_, v___x_145_, v___x_144_, v___x_143_);
return v___x_148_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_149_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_150_ = lean_unsigned_to_nat(21u);
v___x_151_ = lean_unsigned_to_nat(183u);
v___x_152_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_153_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_154_ = l_mkPanicMessageWithDecl(v___x_153_, v___x_152_, v___x_151_, v___x_150_, v___x_149_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_157_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_158_ = lean_unsigned_to_nat(35u);
v___x_159_ = lean_unsigned_to_nat(276u);
v___x_160_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_161_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_162_ = l_mkPanicMessageWithDecl(v___x_161_, v___x_160_, v___x_159_, v___x_158_, v___x_157_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_163_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_164_ = lean_unsigned_to_nat(21u);
v___x_165_ = lean_unsigned_to_nat(277u);
v___x_166_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_167_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_168_ = l_mkPanicMessageWithDecl(v___x_167_, v___x_166_, v___x_165_, v___x_164_, v___x_163_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(lean_object* v_k_169_, lean_object* v_v_170_, lean_object* v_t_171_){
_start:
{
if (lean_obj_tag(v_t_171_) == 0)
{
lean_object* v_size_172_; lean_object* v_k_173_; lean_object* v_v_174_; lean_object* v_l_175_; lean_object* v_r_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_532_; 
v_size_172_ = lean_ctor_get(v_t_171_, 0);
v_k_173_ = lean_ctor_get(v_t_171_, 1);
v_v_174_ = lean_ctor_get(v_t_171_, 2);
v_l_175_ = lean_ctor_get(v_t_171_, 3);
v_r_176_ = lean_ctor_get(v_t_171_, 4);
v_isSharedCheck_532_ = !lean_is_exclusive(v_t_171_);
if (v_isSharedCheck_532_ == 0)
{
v___x_178_ = v_t_171_;
v_isShared_179_ = v_isSharedCheck_532_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_r_176_);
lean_inc(v_l_175_);
lean_inc(v_v_174_);
lean_inc(v_k_173_);
lean_inc(v_size_172_);
lean_dec(v_t_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_532_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
uint8_t v___x_180_; 
v___x_180_ = l_Lean_NamePart_cmp(v_k_169_, v_k_173_);
switch(v___x_180_)
{
case 0:
{
lean_object* v___x_181_; 
lean_dec(v_size_172_);
v___x_181_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_169_, v_v_170_, v_l_175_);
if (lean_obj_tag(v_r_176_) == 0)
{
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_size_182_; lean_object* v_size_183_; lean_object* v_k_184_; lean_object* v_v_185_; lean_object* v_l_186_; lean_object* v_r_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_size_182_ = lean_ctor_get(v_r_176_, 0);
v_size_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_size_183_);
v_k_184_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_k_184_);
v_v_185_ = lean_ctor_get(v___x_181_, 2);
lean_inc(v_v_185_);
v_l_186_ = lean_ctor_get(v___x_181_, 3);
lean_inc(v_l_186_);
v_r_187_ = lean_ctor_get(v___x_181_, 4);
lean_inc(v_r_187_);
v___x_188_ = lean_unsigned_to_nat(3u);
v___x_189_ = lean_nat_mul(v___x_188_, v_size_182_);
v___x_190_ = lean_nat_dec_lt(v___x_189_, v_size_183_);
lean_dec(v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
lean_dec(v_r_187_);
lean_dec(v_l_186_);
lean_dec(v_v_185_);
lean_dec(v_k_184_);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = lean_nat_add(v___x_191_, v_size_183_);
lean_dec(v_size_183_);
v___x_193_ = lean_nat_add(v___x_192_, v_size_182_);
lean_dec(v___x_192_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 3, v___x_181_);
lean_ctor_set(v___x_178_, 0, v___x_193_);
v___x_195_ = v___x_178_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_r_176_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_268_; 
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; lean_object* v_unused_273_; 
v_unused_269_ = lean_ctor_get(v___x_181_, 4);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v___x_181_, 3);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v___x_181_, 2);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v___x_181_, 1);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v___x_181_, 0);
lean_dec(v_unused_273_);
v___x_198_ = v___x_181_;
v_isShared_199_ = v_isSharedCheck_268_;
goto v_resetjp_197_;
}
else
{
lean_dec(v___x_181_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_268_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
if (lean_obj_tag(v_l_186_) == 0)
{
if (lean_obj_tag(v_r_187_) == 0)
{
lean_object* v_size_200_; lean_object* v_size_201_; lean_object* v_k_202_; lean_object* v_v_203_; lean_object* v_l_204_; lean_object* v_r_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_size_200_ = lean_ctor_get(v_l_186_, 0);
v_size_201_ = lean_ctor_get(v_r_187_, 0);
v_k_202_ = lean_ctor_get(v_r_187_, 1);
v_v_203_ = lean_ctor_get(v_r_187_, 2);
v_l_204_ = lean_ctor_get(v_r_187_, 3);
v_r_205_ = lean_ctor_get(v_r_187_, 4);
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = lean_nat_mul(v___x_206_, v_size_200_);
v___x_208_ = lean_nat_dec_lt(v_size_201_, v___x_207_);
lean_dec(v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_238_; 
lean_inc(v_r_205_);
lean_inc(v_l_204_);
lean_inc(v_v_203_);
lean_inc(v_k_202_);
v_isSharedCheck_238_ = !lean_is_exclusive(v_r_187_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; lean_object* v_unused_242_; lean_object* v_unused_243_; 
v_unused_239_ = lean_ctor_get(v_r_187_, 4);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_r_187_, 3);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_r_187_, 2);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_r_187_, 1);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_r_187_, 0);
lean_dec(v_unused_243_);
v___x_210_ = v_r_187_;
v_isShared_211_ = v_isSharedCheck_238_;
goto v_resetjp_209_;
}
else
{
lean_dec(v_r_187_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_238_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___x_226_; lean_object* v___y_228_; 
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v___x_212_, v_size_183_);
lean_dec(v_size_183_);
v___x_214_ = lean_nat_add(v___x_213_, v_size_182_);
lean_dec(v___x_213_);
v___x_226_ = lean_nat_add(v___x_212_, v_size_200_);
if (lean_obj_tag(v_l_204_) == 0)
{
lean_object* v_size_236_; 
v_size_236_ = lean_ctor_get(v_l_204_, 0);
lean_inc(v_size_236_);
v___y_228_ = v_size_236_;
goto v___jp_227_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___y_228_ = v___x_237_;
goto v___jp_227_;
}
v___jp_215_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_nat_add(v___y_216_, v___y_218_);
lean_dec(v___y_218_);
lean_dec(v___y_216_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 4, v_r_176_);
lean_ctor_set(v___x_210_, 3, v_r_205_);
lean_ctor_set(v___x_210_, 2, v_v_174_);
lean_ctor_set(v___x_210_, 1, v_k_173_);
lean_ctor_set(v___x_210_, 0, v___x_219_);
v___x_221_ = v___x_210_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_r_205_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_r_176_);
v___x_221_ = v_reuseFailAlloc_225_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v___x_221_);
lean_ctor_set(v___x_198_, 3, v___y_217_);
lean_ctor_set(v___x_198_, 2, v_v_203_);
lean_ctor_set(v___x_198_, 1, v_k_202_);
lean_ctor_set(v___x_198_, 0, v___x_214_);
v___x_223_ = v___x_198_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_202_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_203_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v___y_217_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_nat_add(v___x_226_, v___y_228_);
lean_dec(v___y_228_);
lean_dec(v___x_226_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_l_204_);
lean_ctor_set(v___x_178_, 3, v_l_186_);
lean_ctor_set(v___x_178_, 2, v_v_185_);
lean_ctor_set(v___x_178_, 1, v_k_184_);
lean_ctor_set(v___x_178_, 0, v___x_229_);
v___x_231_ = v___x_178_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_k_184_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_v_185_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_l_204_);
v___x_231_ = v_reuseFailAlloc_235_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_nat_add(v___x_212_, v_size_182_);
if (lean_obj_tag(v_r_205_) == 0)
{
lean_object* v_size_233_; 
v_size_233_ = lean_ctor_get(v_r_205_, 0);
lean_inc(v_size_233_);
v___y_216_ = v___x_232_;
v___y_217_ = v___x_231_;
v___y_218_ = v_size_233_;
goto v___jp_215_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
v___y_216_ = v___x_232_;
v___y_217_ = v___x_231_;
v___y_218_ = v___x_234_;
goto v___jp_215_;
}
}
}
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
lean_del_object(v___x_178_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v___x_244_, v_size_183_);
lean_dec(v_size_183_);
v___x_246_ = lean_nat_add(v___x_245_, v_size_182_);
lean_dec(v___x_245_);
v___x_247_ = lean_nat_add(v___x_244_, v_size_182_);
v___x_248_ = lean_nat_add(v___x_247_, v_size_201_);
lean_dec(v___x_247_);
lean_inc_ref(v_r_176_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 4, v_r_176_);
lean_ctor_set(v___x_198_, 3, v_r_187_);
lean_ctor_set(v___x_198_, 2, v_v_174_);
lean_ctor_set(v___x_198_, 1, v_k_173_);
lean_ctor_set(v___x_198_, 0, v___x_248_);
v___x_250_ = v___x_198_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v_r_187_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v_r_176_);
v___x_250_ = v_reuseFailAlloc_263_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_isSharedCheck_257_ = !lean_is_exclusive(v_r_176_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_258_ = lean_ctor_get(v_r_176_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_r_176_, 3);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_r_176_, 2);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_r_176_, 1);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_r_176_, 0);
lean_dec(v_unused_262_);
v___x_252_ = v_r_176_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_r_176_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v___x_250_);
lean_ctor_set(v___x_252_, 3, v_l_186_);
lean_ctor_set(v___x_252_, 2, v_v_185_);
lean_ctor_set(v___x_252_, 1, v_k_184_);
lean_ctor_set(v___x_252_, 0, v___x_246_);
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_k_184_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_v_185_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_l_186_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v___x_250_);
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
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref(v_l_186_);
lean_del_object(v___x_198_);
lean_dec(v_v_185_);
lean_dec(v_k_184_);
lean_dec(v_size_183_);
lean_dec_ref(v_r_176_);
lean_del_object(v___x_178_);
lean_dec(v_v_174_);
lean_dec(v_k_173_);
v___x_264_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3);
v___x_265_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_264_);
return v___x_265_;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_del_object(v___x_198_);
lean_dec(v_r_187_);
lean_dec(v_v_185_);
lean_dec(v_k_184_);
lean_dec(v_size_183_);
lean_dec_ref(v_r_176_);
lean_del_object(v___x_178_);
lean_dec(v_v_174_);
lean_dec(v_k_173_);
v___x_266_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4);
v___x_267_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_266_);
return v___x_267_;
}
}
}
}
else
{
lean_object* v_size_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_size_274_ = lean_ctor_get(v_r_176_, 0);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v___x_275_, v_size_274_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 3, v___x_181_);
lean_ctor_set(v___x_178_, 0, v___x_276_);
v___x_278_ = v___x_178_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_r_176_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
else
{
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_l_280_; 
v_l_280_ = lean_ctor_get(v___x_181_, 3);
lean_inc(v_l_280_);
if (lean_obj_tag(v_l_280_) == 0)
{
lean_object* v_r_281_; 
v_r_281_ = lean_ctor_get(v___x_181_, 4);
lean_inc(v_r_281_);
if (lean_obj_tag(v_r_281_) == 0)
{
lean_object* v_size_282_; lean_object* v_k_283_; lean_object* v_v_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_298_; 
v_size_282_ = lean_ctor_get(v___x_181_, 0);
v_k_283_ = lean_ctor_get(v___x_181_, 1);
v_v_284_ = lean_ctor_get(v___x_181_, 2);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_299_ = lean_ctor_get(v___x_181_, 4);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v___x_181_, 3);
lean_dec(v_unused_300_);
v___x_286_ = v___x_181_;
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_v_284_);
lean_inc(v_k_283_);
lean_inc(v_size_282_);
lean_dec(v___x_181_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_298_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_size_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v_size_288_ = lean_ctor_get(v_r_281_, 0);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v___x_289_, v_size_282_);
lean_dec(v_size_282_);
v___x_291_ = lean_nat_add(v___x_289_, v_size_288_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 4, v_r_176_);
lean_ctor_set(v___x_286_, 3, v_r_281_);
lean_ctor_set(v___x_286_, 2, v_v_174_);
lean_ctor_set(v___x_286_, 1, v_k_173_);
lean_ctor_set(v___x_286_, 0, v___x_291_);
v___x_293_ = v___x_286_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_r_281_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_r_176_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_293_);
lean_ctor_set(v___x_178_, 3, v_l_280_);
lean_ctor_set(v___x_178_, 2, v_v_284_);
lean_ctor_set(v___x_178_, 1, v_k_283_);
lean_ctor_set(v___x_178_, 0, v___x_290_);
v___x_295_ = v___x_178_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_k_283_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_v_284_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_l_280_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_k_301_; lean_object* v_v_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v_k_301_ = lean_ctor_get(v___x_181_, 1);
v_v_302_ = lean_ctor_get(v___x_181_, 2);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_315_ = lean_ctor_get(v___x_181_, 4);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v___x_181_, 3);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v___x_181_, 0);
lean_dec(v_unused_317_);
v___x_304_ = v___x_181_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_v_302_);
lean_inc(v_k_301_);
lean_dec(v___x_181_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = lean_unsigned_to_nat(3u);
v___x_307_ = lean_unsigned_to_nat(1u);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 3, v_r_281_);
lean_ctor_set(v___x_304_, 2, v_v_174_);
lean_ctor_set(v___x_304_, 1, v_k_173_);
lean_ctor_set(v___x_304_, 0, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_r_281_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_r_281_);
v___x_309_ = v_reuseFailAlloc_313_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_309_);
lean_ctor_set(v___x_178_, 3, v_l_280_);
lean_ctor_set(v___x_178_, 2, v_v_302_);
lean_ctor_set(v___x_178_, 1, v_k_301_);
lean_ctor_set(v___x_178_, 0, v___x_306_);
v___x_311_ = v___x_178_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_301_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_302_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_l_280_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_r_318_; 
v_r_318_ = lean_ctor_get(v___x_181_, 4);
lean_inc(v_r_318_);
if (lean_obj_tag(v_r_318_) == 0)
{
lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_344_; 
v_k_319_ = lean_ctor_get(v___x_181_, 1);
v_v_320_ = lean_ctor_get(v___x_181_, 2);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_345_ = lean_ctor_get(v___x_181_, 4);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v___x_181_, 3);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v___x_181_, 0);
lean_dec(v_unused_347_);
v___x_322_ = v___x_181_;
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_v_320_);
lean_inc(v_k_319_);
lean_dec(v___x_181_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_k_324_; lean_object* v_v_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_340_; 
v_k_324_ = lean_ctor_get(v_r_318_, 1);
v_v_325_ = lean_ctor_get(v_r_318_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_r_318_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_341_ = lean_ctor_get(v_r_318_, 4);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_r_318_, 3);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_r_318_, 0);
lean_dec(v_unused_343_);
v___x_327_ = v_r_318_;
v_isShared_328_ = v_isSharedCheck_340_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_v_325_);
lean_inc(v_k_324_);
lean_dec(v_r_318_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_340_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = lean_unsigned_to_nat(1u);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 4, v_l_280_);
lean_ctor_set(v___x_327_, 3, v_l_280_);
lean_ctor_set(v___x_327_, 2, v_v_320_);
lean_ctor_set(v___x_327_, 1, v_k_319_);
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_l_280_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v_l_280_);
v___x_332_ = v_reuseFailAlloc_339_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 4, v_l_280_);
lean_ctor_set(v___x_322_, 2, v_v_174_);
lean_ctor_set(v___x_322_, 1, v_k_173_);
lean_ctor_set(v___x_322_, 0, v___x_330_);
v___x_334_ = v___x_322_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_l_280_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_l_280_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_334_);
lean_ctor_set(v___x_178_, 3, v___x_332_);
lean_ctor_set(v___x_178_, 2, v_v_325_);
lean_ctor_set(v___x_178_, 1, v_k_324_);
lean_ctor_set(v___x_178_, 0, v___x_329_);
v___x_336_ = v___x_178_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_unsigned_to_nat(2u);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_r_318_);
lean_ctor_set(v___x_178_, 3, v___x_181_);
lean_ctor_set(v___x_178_, 0, v___x_348_);
v___x_350_ = v___x_178_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_r_318_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(1u);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_181_);
lean_ctor_set(v___x_178_, 3, v___x_181_);
lean_ctor_set(v___x_178_, 0, v___x_352_);
v___x_354_ = v___x_178_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v___x_181_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
case 1:
{
lean_object* v___x_357_; 
lean_dec(v_v_174_);
lean_dec(v_k_173_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 2, v_v_170_);
lean_ctor_set(v___x_178_, 1, v_k_169_);
v___x_357_ = v___x_178_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_size_172_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_358_, 3, v_l_175_);
lean_ctor_set(v_reuseFailAlloc_358_, 4, v_r_176_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
default: 
{
lean_object* v___x_359_; 
lean_dec(v_size_172_);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_169_, v_v_170_, v_r_176_);
if (lean_obj_tag(v_l_175_) == 0)
{
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_size_360_; lean_object* v_size_361_; lean_object* v_k_362_; lean_object* v_v_363_; lean_object* v_l_364_; lean_object* v_r_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_size_360_ = lean_ctor_get(v_l_175_, 0);
v_size_361_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_size_361_);
v_k_362_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_k_362_);
v_v_363_ = lean_ctor_get(v___x_359_, 2);
lean_inc(v_v_363_);
v_l_364_ = lean_ctor_get(v___x_359_, 3);
lean_inc(v_l_364_);
v_r_365_ = lean_ctor_get(v___x_359_, 4);
lean_inc(v_r_365_);
v___x_366_ = lean_unsigned_to_nat(3u);
v___x_367_ = lean_nat_mul(v___x_366_, v_size_360_);
v___x_368_ = lean_nat_dec_lt(v___x_367_, v_size_361_);
lean_dec(v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec(v_r_365_);
lean_dec(v_l_364_);
lean_dec(v_v_363_);
lean_dec(v_k_362_);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v___x_369_, v_size_360_);
v___x_371_ = lean_nat_add(v___x_370_, v_size_361_);
lean_dec(v_size_361_);
lean_dec(v___x_370_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_359_);
lean_ctor_set(v___x_178_, 0, v___x_371_);
v___x_373_ = v___x_178_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_l_175_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v___x_359_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
else
{
lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_444_; 
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_445_ = lean_ctor_get(v___x_359_, 4);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v___x_359_, 3);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v___x_359_, 2);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v___x_359_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_449_);
v___x_376_ = v___x_359_;
v_isShared_377_ = v_isSharedCheck_444_;
goto v_resetjp_375_;
}
else
{
lean_dec(v___x_359_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_444_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
if (lean_obj_tag(v_l_364_) == 0)
{
if (lean_obj_tag(v_r_365_) == 0)
{
lean_object* v_size_378_; lean_object* v_k_379_; lean_object* v_v_380_; lean_object* v_l_381_; lean_object* v_r_382_; lean_object* v_size_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_size_378_ = lean_ctor_get(v_l_364_, 0);
v_k_379_ = lean_ctor_get(v_l_364_, 1);
v_v_380_ = lean_ctor_get(v_l_364_, 2);
v_l_381_ = lean_ctor_get(v_l_364_, 3);
v_r_382_ = lean_ctor_get(v_l_364_, 4);
v_size_383_ = lean_ctor_get(v_r_365_, 0);
v___x_384_ = lean_unsigned_to_nat(2u);
v___x_385_ = lean_nat_mul(v___x_384_, v_size_383_);
v___x_386_ = lean_nat_dec_lt(v_size_378_, v___x_385_);
lean_dec(v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_415_; 
lean_inc(v_r_382_);
lean_inc(v_l_381_);
lean_inc(v_v_380_);
lean_inc(v_k_379_);
v_isSharedCheck_415_ = !lean_is_exclusive(v_l_364_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; lean_object* v_unused_418_; lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_416_ = lean_ctor_get(v_l_364_, 4);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_l_364_, 3);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_l_364_, 2);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_l_364_, 1);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_l_364_, 0);
lean_dec(v_unused_420_);
v___x_388_ = v_l_364_;
v_isShared_389_ = v_isSharedCheck_415_;
goto v_resetjp_387_;
}
else
{
lean_dec(v_l_364_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_415_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_405_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v___x_390_, v_size_360_);
v___x_392_ = lean_nat_add(v___x_391_, v_size_361_);
lean_dec(v_size_361_);
if (lean_obj_tag(v_l_381_) == 0)
{
lean_object* v_size_413_; 
v_size_413_ = lean_ctor_get(v_l_381_, 0);
lean_inc(v_size_413_);
v___y_405_ = v_size_413_;
goto v___jp_404_;
}
else
{
lean_object* v___x_414_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___y_405_ = v___x_414_;
goto v___jp_404_;
}
v___jp_393_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_nat_add(v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 4, v_r_365_);
lean_ctor_set(v___x_388_, 3, v_r_382_);
lean_ctor_set(v___x_388_, 2, v_v_363_);
lean_ctor_set(v___x_388_, 1, v_k_362_);
lean_ctor_set(v___x_388_, 0, v___x_397_);
v___x_399_ = v___x_388_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_r_382_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_r_365_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 4, v___x_399_);
lean_ctor_set(v___x_376_, 3, v___y_394_);
lean_ctor_set(v___x_376_, 2, v_v_380_);
lean_ctor_set(v___x_376_, 1, v_k_379_);
lean_ctor_set(v___x_376_, 0, v___x_392_);
v___x_401_ = v___x_376_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_379_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_v_380_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v___y_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_nat_add(v___x_391_, v___y_405_);
lean_dec(v___y_405_);
lean_dec(v___x_391_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_l_381_);
lean_ctor_set(v___x_178_, 0, v___x_406_);
v___x_408_ = v___x_178_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_l_175_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_l_381_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_nat_add(v___x_390_, v_size_383_);
if (lean_obj_tag(v_r_382_) == 0)
{
lean_object* v_size_410_; 
v_size_410_ = lean_ctor_get(v_r_382_, 0);
lean_inc(v_size_410_);
v___y_394_ = v___x_408_;
v___y_395_ = v___x_409_;
v___y_396_ = v_size_410_;
goto v___jp_393_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___y_394_ = v___x_408_;
v___y_395_ = v___x_409_;
v___y_396_ = v___x_411_;
goto v___jp_393_;
}
}
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_del_object(v___x_178_);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v___x_421_, v_size_360_);
v___x_423_ = lean_nat_add(v___x_422_, v_size_361_);
lean_dec(v_size_361_);
v___x_424_ = lean_nat_add(v___x_422_, v_size_378_);
lean_dec(v___x_422_);
lean_inc_ref(v_l_175_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 4, v_l_364_);
lean_ctor_set(v___x_376_, 3, v_l_175_);
lean_ctor_set(v___x_376_, 2, v_v_174_);
lean_ctor_set(v___x_376_, 1, v_k_173_);
lean_ctor_set(v___x_376_, 0, v___x_424_);
v___x_426_ = v___x_376_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_l_175_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_l_364_);
v___x_426_ = v_reuseFailAlloc_439_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_isSharedCheck_433_ = !lean_is_exclusive(v_l_175_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; lean_object* v_unused_437_; lean_object* v_unused_438_; 
v_unused_434_ = lean_ctor_get(v_l_175_, 4);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_l_175_, 3);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_l_175_, 2);
lean_dec(v_unused_436_);
v_unused_437_ = lean_ctor_get(v_l_175_, 1);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_l_175_, 0);
lean_dec(v_unused_438_);
v___x_428_ = v_l_175_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_dec(v_l_175_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v_r_365_);
lean_ctor_set(v___x_428_, 3, v___x_426_);
lean_ctor_set(v___x_428_, 2, v_v_363_);
lean_ctor_set(v___x_428_, 1, v_k_362_);
lean_ctor_set(v___x_428_, 0, v___x_423_);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_r_365_);
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
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref(v_l_364_);
lean_del_object(v___x_376_);
lean_dec(v_v_363_);
lean_dec(v_k_362_);
lean_dec(v_size_361_);
lean_dec_ref(v_l_175_);
lean_del_object(v___x_178_);
lean_dec(v_v_174_);
lean_dec(v_k_173_);
v___x_440_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7);
v___x_441_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_440_);
return v___x_441_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_del_object(v___x_376_);
lean_dec(v_r_365_);
lean_dec(v_v_363_);
lean_dec(v_k_362_);
lean_dec(v_size_361_);
lean_dec_ref(v_l_175_);
lean_del_object(v___x_178_);
lean_dec(v_v_174_);
lean_dec(v_k_173_);
v___x_442_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8);
v___x_443_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_442_);
return v___x_443_;
}
}
}
}
else
{
lean_object* v_size_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v_size_450_ = lean_ctor_get(v_l_175_, 0);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v___x_451_, v_size_450_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_359_);
lean_ctor_set(v___x_178_, 0, v___x_452_);
v___x_454_ = v___x_178_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_l_175_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v___x_359_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_l_456_; 
v_l_456_ = lean_ctor_get(v___x_359_, 3);
lean_inc(v_l_456_);
if (lean_obj_tag(v_l_456_) == 0)
{
lean_object* v_r_457_; 
v_r_457_ = lean_ctor_get(v___x_359_, 4);
lean_inc(v_r_457_);
if (lean_obj_tag(v_r_457_) == 0)
{
lean_object* v_size_458_; lean_object* v_k_459_; lean_object* v_v_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_474_; 
v_size_458_ = lean_ctor_get(v___x_359_, 0);
v_k_459_ = lean_ctor_get(v___x_359_, 1);
v_v_460_ = lean_ctor_get(v___x_359_, 2);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; 
v_unused_475_ = lean_ctor_get(v___x_359_, 4);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v___x_359_, 3);
lean_dec(v_unused_476_);
v___x_462_ = v___x_359_;
v_isShared_463_ = v_isSharedCheck_474_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_v_460_);
lean_inc(v_k_459_);
lean_inc(v_size_458_);
lean_dec(v___x_359_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_474_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_size_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v_size_464_ = lean_ctor_get(v_l_456_, 0);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v___x_465_, v_size_458_);
lean_dec(v_size_458_);
v___x_467_ = lean_nat_add(v___x_465_, v_size_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 4, v_l_456_);
lean_ctor_set(v___x_462_, 3, v_l_175_);
lean_ctor_set(v___x_462_, 2, v_v_174_);
lean_ctor_set(v___x_462_, 1, v_k_173_);
lean_ctor_set(v___x_462_, 0, v___x_467_);
v___x_469_ = v___x_462_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_l_175_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_l_456_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_r_457_);
lean_ctor_set(v___x_178_, 3, v___x_469_);
lean_ctor_set(v___x_178_, 2, v_v_460_);
lean_ctor_set(v___x_178_, 1, v_k_459_);
lean_ctor_set(v___x_178_, 0, v___x_466_);
v___x_471_ = v___x_178_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_k_459_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_v_460_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v_r_457_);
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
lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_502_; 
v_k_477_ = lean_ctor_get(v___x_359_, 1);
v_v_478_ = lean_ctor_get(v___x_359_, 2);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; 
v_unused_503_ = lean_ctor_get(v___x_359_, 4);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v___x_359_, 3);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_505_);
v___x_480_ = v___x_359_;
v_isShared_481_ = v_isSharedCheck_502_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_v_478_);
lean_inc(v_k_477_);
lean_dec(v___x_359_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_502_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_k_482_; lean_object* v_v_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_498_; 
v_k_482_ = lean_ctor_get(v_l_456_, 1);
v_v_483_ = lean_ctor_get(v_l_456_, 2);
v_isSharedCheck_498_ = !lean_is_exclusive(v_l_456_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; 
v_unused_499_ = lean_ctor_get(v_l_456_, 4);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_l_456_, 3);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_l_456_, 0);
lean_dec(v_unused_501_);
v___x_485_ = v_l_456_;
v_isShared_486_ = v_isSharedCheck_498_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_v_483_);
lean_inc(v_k_482_);
lean_dec(v_l_456_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_498_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = lean_unsigned_to_nat(3u);
v___x_488_ = lean_unsigned_to_nat(1u);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 4, v_r_457_);
lean_ctor_set(v___x_485_, 3, v_r_457_);
lean_ctor_set(v___x_485_, 2, v_v_174_);
lean_ctor_set(v___x_485_, 1, v_k_173_);
lean_ctor_set(v___x_485_, 0, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_r_457_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_r_457_);
v___x_490_ = v_reuseFailAlloc_497_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 3, v_r_457_);
lean_ctor_set(v___x_480_, 0, v___x_488_);
v___x_492_ = v___x_480_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_r_457_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_r_457_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_492_);
lean_ctor_set(v___x_178_, 3, v___x_490_);
lean_ctor_set(v___x_178_, 2, v_v_483_);
lean_ctor_set(v___x_178_, 1, v_k_482_);
lean_ctor_set(v___x_178_, 0, v___x_487_);
v___x_494_ = v___x_178_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_k_482_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_v_483_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_506_; 
v_r_506_ = lean_ctor_get(v___x_359_, 4);
lean_inc(v_r_506_);
if (lean_obj_tag(v_r_506_) == 0)
{
lean_object* v_k_507_; lean_object* v_v_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_520_; 
v_k_507_ = lean_ctor_get(v___x_359_, 1);
v_v_508_ = lean_ctor_get(v___x_359_, 2);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; lean_object* v_unused_522_; lean_object* v_unused_523_; 
v_unused_521_ = lean_ctor_get(v___x_359_, 4);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v___x_359_, 3);
lean_dec(v_unused_522_);
v_unused_523_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_523_);
v___x_510_ = v___x_359_;
v_isShared_511_ = v_isSharedCheck_520_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_v_508_);
lean_inc(v_k_507_);
lean_dec(v___x_359_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_520_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = lean_unsigned_to_nat(3u);
v___x_513_ = lean_unsigned_to_nat(1u);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_l_456_);
lean_ctor_set(v___x_510_, 2, v_v_174_);
lean_ctor_set(v___x_510_, 1, v_k_173_);
lean_ctor_set(v___x_510_, 0, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_l_456_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_l_456_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v_r_506_);
lean_ctor_set(v___x_178_, 3, v___x_515_);
lean_ctor_set(v___x_178_, 2, v_v_508_);
lean_ctor_set(v___x_178_, 1, v_k_507_);
lean_ctor_set(v___x_178_, 0, v___x_512_);
v___x_517_ = v___x_178_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_k_507_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_v_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_r_506_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_unsigned_to_nat(2u);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_359_);
lean_ctor_set(v___x_178_, 3, v_r_506_);
lean_ctor_set(v___x_178_, 0, v___x_524_);
v___x_526_ = v___x_178_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_r_506_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v___x_359_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_unsigned_to_nat(1u);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 4, v___x_359_);
lean_ctor_set(v___x_178_, 3, v___x_359_);
lean_ctor_set(v___x_178_, 0, v___x_528_);
v___x_530_ = v___x_178_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_k_173_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_v_174_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v___x_359_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v_k_169_);
lean_ctor_set(v___x_534_, 2, v_v_170_);
lean_ctor_set(v___x_534_, 3, v_t_171_);
lean_ctor_set(v___x_534_, 4, v_t_171_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(lean_object* v_val_535_, lean_object* v_k_536_){
_start:
{
if (lean_obj_tag(v_k_536_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v_val_535_);
v___x_538_ = lean_box(1);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
return v___x_539_;
}
else
{
lean_object* v_head_540_; lean_object* v_tail_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_552_; 
v_head_540_ = lean_ctor_get(v_k_536_, 0);
v_tail_541_ = lean_ctor_get(v_k_536_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_k_536_);
if (v_isSharedCheck_552_ == 0)
{
v___x_543_ = v_k_536_;
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_tail_541_);
lean_inc(v_head_540_);
lean_dec(v_k_536_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v_t_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v_t_545_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_535_, v_tail_541_);
v___x_546_ = lean_box(0);
v___x_547_ = lean_box(1);
v___x_548_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_540_, v_t_545_, v___x_547_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
lean_ctor_set(v___x_543_, 1, v___x_548_);
lean_ctor_set(v___x_543_, 0, v___x_546_);
v___x_550_ = v___x_543_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(lean_object* v_val_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
v_a_556_ = lean_ctor_get(v_x_554_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_x_554_, 0);
lean_dec(v_unused_565_);
v___x_558_ = v_x_554_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v_x_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_val_553_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_a_556_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
else
{
lean_object* v_a_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_583_; 
v_a_566_ = lean_ctor_get(v_x_554_, 0);
v_a_567_ = lean_ctor_get(v_x_554_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_583_ == 0)
{
v___x_569_ = v_x_554_;
v_isShared_570_ = v_isSharedCheck_583_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_inc(v_a_566_);
lean_dec(v_x_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_583_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_head_571_; lean_object* v_tail_572_; lean_object* v___y_574_; lean_object* v___x_579_; 
v_head_571_ = lean_ctor_get(v_x_555_, 0);
lean_inc(v_head_571_);
v_tail_572_ = lean_ctor_get(v_x_555_, 1);
lean_inc(v_tail_572_);
lean_dec_ref(v_x_555_);
v___x_579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_567_, v_head_571_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_553_, v_tail_572_);
v___y_574_ = v___x_580_;
goto v___jp_573_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_582_; 
v_val_581_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v___x_579_);
v___x_582_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_553_, v_val_581_, v_tail_572_);
v___y_574_ = v___x_582_;
goto v___jp_573_;
}
v___jp_573_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_571_, v___y_574_, v_a_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_575_);
v___x_577_ = v___x_569_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_566_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg(lean_object* v_t_584_, lean_object* v_n_585_, lean_object* v_b_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_585_);
v___x_588_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_b_586_, v_t_584_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg___boxed(lean_object* v_t_589_, lean_object* v_n_590_, lean_object* v_b_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_NameTrie_insert___redArg(v_t_589_, v_n_590_, v_b_591_);
lean_dec(v_n_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert(lean_object* v_00_u03b2_593_, lean_object* v_t_594_, lean_object* v_n_595_, lean_object* v_b_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_NameTrie_insert___redArg(v_t_594_, v_n_595_, v_b_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___boxed(lean_object* v_00_u03b2_598_, lean_object* v_t_599_, lean_object* v_n_600_, lean_object* v_b_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_NameTrie_insert(v_00_u03b2_598_, v_t_599_, v_n_600_, v_b_601_);
lean_dec(v_n_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(lean_object* v_00_u03b2_603_, lean_object* v_val_604_, lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_604_, v_x_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_608_, lean_object* v_msg_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v_msg_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(lean_object* v_00_u03b2_611_, lean_object* v_k_612_, lean_object* v_v_613_, lean_object* v_t_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_612_, v_v_613_, v_t_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(lean_object* v_00_u03b4_616_, lean_object* v_t_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_617_, v_k_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b4_620_, lean_object* v_t_621_, lean_object* v_k_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(v_00_u03b4_620_, v_t_621_, v_k_622_);
lean_dec_ref(v_k_622_);
lean_dec(v_t_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(lean_object* v_00_u03b2_624_, lean_object* v_val_625_, lean_object* v_k_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_625_, v_k_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_NameTrie_empty___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_630_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty(lean_object* v_00_u03b2_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_NameTrie_empty___closed__1, &l_Lean_NameTrie_empty___closed__1_once, _init_l_Lean_NameTrie_empty___closed__1);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_instInhabitedNameTrie___closed__0(void){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_NameTrie_empty(lean_box(0));
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie(lean_object* v_00_u03b2_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_instInhabitedNameTrie___closed__0, &l_Lean_instInhabitedNameTrie___closed__0_once, _init_l_Lean_instInhabitedNameTrie___closed__0);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie(lean_object* v_00_u03b2_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_instInhabitedNameTrie___closed__0, &l_Lean_instInhabitedNameTrie___closed__0_once, _init_l_Lean_instInhabitedNameTrie___closed__0);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v_x_638_);
return v_a_640_;
}
else
{
lean_object* v_a_641_; lean_object* v_head_642_; lean_object* v_tail_643_; lean_object* v___x_644_; 
v_a_641_ = lean_ctor_get(v_x_638_, 1);
lean_inc(v_a_641_);
lean_dec_ref(v_x_638_);
v_head_642_ = lean_ctor_get(v_x_639_, 0);
v_tail_643_ = lean_ctor_get(v_x_639_, 1);
v___x_644_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_641_, v_head_642_);
lean_dec(v_a_641_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(0);
return v___x_645_;
}
else
{
lean_object* v_val_646_; 
v_val_646_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_val_646_);
lean_dec_ref(v___x_644_);
v_x_638_ = v_val_646_;
v_x_639_ = v_tail_643_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_648_, v_x_649_);
lean_dec(v_x_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object* v_t_651_, lean_object* v_k_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_652_);
v___x_654_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_t_651_, v___x_653_);
lean_dec(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg___boxed(lean_object* v_t_655_, lean_object* v_k_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_NameTrie_find_x3f___redArg(v_t_655_, v_k_656_);
lean_dec(v_k_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f(lean_object* v_00_u03b2_658_, lean_object* v_t_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_NameTrie_find_x3f___redArg(v_t_659_, v_k_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___boxed(lean_object* v_00_u03b2_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_NameTrie_find_x3f(v_00_u03b2_662_, v_t_663_, v_k_664_);
lean_dec(v_k_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(lean_object* v_00_u03b2_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(v_00_u03b2_670_, v_x_671_, v_x_672_);
lean_dec(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg(lean_object* v_t_674_, lean_object* v_k_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_677_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_675_);
v___x_678_ = lean_box(0);
v___x_679_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_676_, v___x_678_, v_t_674_, v___x_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(lean_object* v_t_680_, lean_object* v_k_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_NameTrie_findLongestPrefix_x3f___redArg(v_t_680_, v_k_681_);
lean_dec(v_k_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f(lean_object* v_00_u03b2_683_, lean_object* v_t_684_, lean_object* v_k_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_687_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_685_);
v___x_688_ = lean_box(0);
v___x_689_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_686_, v___x_688_, v_t_684_, v___x_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___boxed(lean_object* v_00_u03b2_690_, lean_object* v_t_691_, lean_object* v_k_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_NameTrie_findLongestPrefix_x3f(v_00_u03b2_690_, v_t_691_, v_k_692_);
lean_dec(v_k_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg(lean_object* v_inst_694_, lean_object* v_t_695_, lean_object* v_k_696_, lean_object* v_init_697_, lean_object* v_f_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_700_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_696_);
lean_inc(v_init_697_);
v___x_701_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_694_, v___x_699_, v_init_697_, v_f_698_, v___x_700_, v_t_695_, v_init_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg___boxed(lean_object* v_inst_702_, lean_object* v_t_703_, lean_object* v_k_704_, lean_object* v_init_705_, lean_object* v_f_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_NameTrie_foldMatchingM___redArg(v_inst_702_, v_t_703_, v_k_704_, v_init_705_, v_f_706_);
lean_dec(v_k_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM(lean_object* v_m_708_, lean_object* v_00_u03b2_709_, lean_object* v_00_u03c3_710_, lean_object* v_inst_711_, lean_object* v_t_712_, lean_object* v_k_713_, lean_object* v_init_714_, lean_object* v_f_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_717_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_713_);
lean_inc(v_init_714_);
v___x_718_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_711_, v___x_716_, v_init_714_, v_f_715_, v___x_717_, v_t_712_, v_init_714_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___boxed(lean_object* v_m_719_, lean_object* v_00_u03b2_720_, lean_object* v_00_u03c3_721_, lean_object* v_inst_722_, lean_object* v_t_723_, lean_object* v_k_724_, lean_object* v_init_725_, lean_object* v_f_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_NameTrie_foldMatchingM(v_m_719_, v_00_u03b2_720_, v_00_u03c3_721_, v_inst_722_, v_t_723_, v_k_724_, v_init_725_, v_f_726_);
lean_dec(v_k_724_);
return v_res_727_;
}
}
static lean_object* _init_l_Lean_NameTrie_foldM___redArg___closed__0(void){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_box(0);
v___x_729_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM___redArg(lean_object* v_inst_730_, lean_object* v_t_731_, lean_object* v_init_732_, lean_object* v_f_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_735_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_732_);
v___x_736_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v___x_734_, v_init_732_, v_f_733_, v___x_735_, v_t_731_, v_init_732_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM(lean_object* v_m_737_, lean_object* v_00_u03b2_738_, lean_object* v_00_u03c3_739_, lean_object* v_inst_740_, lean_object* v_t_741_, lean_object* v_init_742_, lean_object* v_f_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_745_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_742_);
v___x_746_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_740_, v___x_744_, v_init_742_, v_f_743_, v___x_745_, v_t_741_, v_init_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___lam__0(lean_object* v_f_747_, lean_object* v_b_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_apply_1(v_f_747_, v_b_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg(lean_object* v_inst_751_, lean_object* v_t_752_, lean_object* v_k_753_, lean_object* v_f_754_){
_start:
{
lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___f_755_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_755_, 0, v_f_754_);
v___x_756_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_757_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_753_);
v___x_758_ = lean_box(0);
v___x_759_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_751_, v___x_756_, v___x_758_, v___f_755_, v___x_757_, v_t_752_, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___boxed(lean_object* v_inst_760_, lean_object* v_t_761_, lean_object* v_k_762_, lean_object* v_f_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_NameTrie_forMatchingM___redArg(v_inst_760_, v_t_761_, v_k_762_, v_f_763_);
lean_dec(v_k_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM(lean_object* v_m_765_, lean_object* v_00_u03b2_766_, lean_object* v_inst_767_, lean_object* v_t_768_, lean_object* v_k_769_, lean_object* v_f_770_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___f_771_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_771_, 0, v_f_770_);
v___x_772_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_773_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_769_);
v___x_774_ = lean_box(0);
v___x_775_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_767_, v___x_772_, v___x_774_, v___f_771_, v___x_773_, v_t_768_, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___boxed(lean_object* v_m_776_, lean_object* v_00_u03b2_777_, lean_object* v_inst_778_, lean_object* v_t_779_, lean_object* v_k_780_, lean_object* v_f_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_NameTrie_forMatchingM(v_m_776_, v_00_u03b2_777_, v_inst_778_, v_t_779_, v_k_780_, v_f_781_);
lean_dec(v_k_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM___redArg(lean_object* v_inst_783_, lean_object* v_t_784_, lean_object* v_f_785_){
_start:
{
lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___f_786_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_786_, 0, v_f_785_);
v___x_787_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_788_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_789_ = lean_box(0);
v___x_790_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_783_, v___x_787_, v___x_789_, v___f_786_, v___x_788_, v_t_784_, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM(lean_object* v_m_791_, lean_object* v_00_u03b2_792_, lean_object* v_inst_793_, lean_object* v_t_794_, lean_object* v_f_795_){
_start:
{
lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___f_796_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_796_, 0, v_f_795_);
v___x_797_ = ((lean_object*)(l_Lean_NameTrie_empty___closed__0));
v___x_798_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_799_ = lean_box(0);
v___x_800_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_793_, v___x_797_, v___x_799_, v___f_796_, v___x_798_, v_t_794_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v_a_801_, 0);
if (lean_obj_tag(v_a_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v_a_801_, 1);
lean_inc(v_a_804_);
lean_dec_ref(v_a_801_);
v___x_805_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_a_802_, v_a_804_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; lean_object* v_val_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc_ref(v_a_803_);
v_a_806_ = lean_ctor_get(v_a_801_, 1);
lean_inc(v_a_806_);
lean_dec_ref(v_a_801_);
v_val_807_ = lean_ctor_get(v_a_803_, 0);
lean_inc(v_val_807_);
lean_dec_ref(v_a_803_);
v___x_808_ = lean_array_push(v_a_802_, v_val_807_);
v___x_809_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v___x_808_, v_a_806_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(lean_object* v_init_810_, lean_object* v_x_811_){
_start:
{
if (lean_obj_tag(v_x_811_) == 0)
{
lean_object* v_v_812_; lean_object* v_l_813_; lean_object* v_r_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v_v_812_ = lean_ctor_get(v_x_811_, 2);
lean_inc(v_v_812_);
v_l_813_ = lean_ctor_get(v_x_811_, 3);
lean_inc(v_l_813_);
v_r_814_ = lean_ctor_get(v_x_811_, 4);
lean_inc(v_r_814_);
lean_dec_ref(v_x_811_);
v___x_815_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_810_, v_l_813_);
v___x_816_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_v_812_, v___x_815_);
v_init_810_ = v___x_816_;
v_x_811_ = v_r_814_;
goto _start;
}
else
{
return v_init_810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(lean_object* v_init_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
if (lean_obj_tag(v_a_819_) == 0)
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_820_, v_a_821_);
return v___x_822_;
}
else
{
lean_object* v_head_823_; lean_object* v_tail_824_; lean_object* v_a_825_; lean_object* v___x_826_; 
v_head_823_ = lean_ctor_get(v_a_819_, 0);
v_tail_824_ = lean_ctor_get(v_a_819_, 1);
v_a_825_ = lean_ctor_get(v_a_820_, 1);
lean_inc(v_a_825_);
lean_dec_ref(v_a_820_);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_825_, v_head_823_);
lean_dec(v_a_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_dec_ref(v_a_821_);
lean_inc_ref(v_init_818_);
return v_init_818_;
}
else
{
lean_object* v_val_827_; 
v_val_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v___x_826_);
v_a_819_ = v_tail_824_;
v_a_820_ = v_val_827_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg___boxed(lean_object* v_init_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_830_);
lean_dec_ref(v_init_829_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object* v_t_836_, lean_object* v_k_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_839_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_837_);
v___x_840_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_838_, v___x_839_, v_t_836_, v___x_838_);
lean_dec(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg___boxed(lean_object* v_t_841_, lean_object* v_k_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_841_, v_k_842_);
lean_dec(v_k_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray(lean_object* v_00_u03b2_844_, lean_object* v_t_845_, lean_object* v_k_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_845_, v_k_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___boxed(lean_object* v_00_u03b2_848_, lean_object* v_t_849_, lean_object* v_k_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_NameTrie_matchingToArray(v_00_u03b2_848_, v_t_849_, v_k_850_);
lean_dec(v_k_850_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_init_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(lean_object* v_00_u03b2_858_, lean_object* v_init_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(v_00_u03b2_858_, v_init_859_, v_a_860_, v_a_861_, v_a_862_);
lean_dec(v_a_860_);
lean_dec_ref(v_init_859_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(lean_object* v_00_u03b2_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_865_, v_a_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_868_, lean_object* v_init_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray___redArg(lean_object* v_t_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_874_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_875_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_873_, v___x_874_, v_t_872_, v___x_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray(lean_object* v_00_u03b2_876_, lean_object* v_t_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_NameTrie_toArray___redArg(v_t_877_);
return v___x_878_;
}
}
lean_object* runtime_initialize_Lean_Data_PrefixTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_NameTrie(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_PrefixTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_NameTrie(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_PrefixTree(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_PrefixTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_NameTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_NameTrie(builtin);
}
#ifdef __cplusplus
}
#endif
