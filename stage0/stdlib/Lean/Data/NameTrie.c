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
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrefixTreeNode_empty___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_NameTrie_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameTrie_empty___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NamePart_cmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0_value;
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
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_s_8_);
return v___x_9_;
}
else
{
lean_object* v_n_10_; lean_object* v___x_11_; 
v_n_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_n_10_);
lean_dec_ref_known(v_t_6_, 1);
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
lean_dec_ref_known(v_x_61_, 1);
return v_s_62_;
}
else
{
lean_object* v_n_63_; lean_object* v___x_64_; 
v_n_63_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_n_63_);
lean_dec_ref_known(v_x_61_, 1);
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
v___x_71_ = lean_string_compare(v_s_69_, v_s_70_);
return v___x_71_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 2;
return v___x_72_;
}
}
else
{
if (lean_obj_tag(v_x_68_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
else
{
lean_object* v_n_74_; lean_object* v_n_75_; uint8_t v___x_76_; 
v_n_74_ = lean_ctor_get(v_x_67_, 0);
v_n_75_ = lean_ctor_get(v_x_68_, 0);
v___x_76_ = lean_nat_dec_lt(v_n_74_, v_n_75_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; 
v___x_77_ = lean_nat_dec_eq(v_n_74_, v_n_75_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; 
v___x_78_ = 2;
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_cmp___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_NamePart_cmp(v_x_81_, v_x_82_);
lean_dec_ref(v_x_82_);
lean_dec_ref(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_NamePart_lt(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_s_87_; lean_object* v_s_88_; uint8_t v___x_89_; 
v_s_87_ = lean_ctor_get(v_x_85_, 0);
v_s_88_ = lean_ctor_get(v_x_86_, 0);
v___x_89_ = lean_string_dec_lt(v_s_87_, v_s_88_);
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
else
{
if (lean_obj_tag(v_x_86_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
lean_object* v_n_92_; lean_object* v_n_93_; uint8_t v___x_94_; 
v_n_92_ = lean_ctor_get(v_x_85_, 0);
v_n_93_ = lean_ctor_get(v_x_86_, 0);
v___x_94_ = lean_nat_dec_lt(v_n_92_, v_n_93_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_lt___boxed(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_NamePart_lt(v_x_95_, v_x_96_);
lean_dec_ref(v_x_96_);
lean_dec_ref(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
switch(lean_obj_tag(v_x_99_))
{
case 0:
{
return v_x_100_;
}
case 1:
{
lean_object* v_pre_101_; lean_object* v_str_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_pre_101_ = lean_ctor_get(v_x_99_, 0);
v_str_102_ = lean_ctor_get(v_x_99_, 1);
lean_inc_ref(v_str_102_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v_str_102_);
v___x_104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_x_100_);
v_x_99_ = v_pre_101_;
v_x_100_ = v___x_104_;
goto _start;
}
default: 
{
lean_object* v_pre_106_; lean_object* v_i_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_pre_106_ = lean_ctor_get(v_x_99_, 0);
v_i_107_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_i_107_);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v_i_107_);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_x_100_);
v_x_99_ = v_pre_106_;
v_x_100_ = v___x_109_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop___boxed(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_x_111_, v_x_112_);
lean_dec(v_x_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey(lean_object* v_n_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_box(0);
v___x_116_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_n_114_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(lean_object* v_n_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_117_);
lean_dec(v_n_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(lean_object* v_t_119_, lean_object* v_k_120_){
_start:
{
if (lean_obj_tag(v_t_119_) == 0)
{
lean_object* v_k_121_; lean_object* v_v_122_; lean_object* v_l_123_; lean_object* v_r_124_; uint8_t v___x_125_; 
v_k_121_ = lean_ctor_get(v_t_119_, 1);
v_v_122_ = lean_ctor_get(v_t_119_, 2);
v_l_123_ = lean_ctor_get(v_t_119_, 3);
v_r_124_ = lean_ctor_get(v_t_119_, 4);
v___x_125_ = l_Lean_NamePart_cmp(v_k_120_, v_k_121_);
switch(v___x_125_)
{
case 0:
{
v_t_119_ = v_l_123_;
goto _start;
}
case 1:
{
lean_object* v___x_127_; 
lean_inc(v_v_122_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_v_122_);
return v___x_127_;
}
default: 
{
v_t_119_ = v_r_124_;
goto _start;
}
}
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(lean_object* v_t_130_, lean_object* v_k_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_130_, v_k_131_);
lean_dec_ref(v_k_131_);
lean_dec(v_t_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_box(1);
v___x_135_ = lean_panic_fn_borrowed(v___x_134_, v_msg_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_140_ = lean_unsigned_to_nat(35u);
v___x_141_ = lean_unsigned_to_nat(182u);
v___x_142_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_143_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_144_ = l_mkPanicMessageWithDecl(v___x_143_, v___x_142_, v___x_141_, v___x_140_, v___x_139_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_145_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_146_ = lean_unsigned_to_nat(21u);
v___x_147_ = lean_unsigned_to_nat(183u);
v___x_148_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_149_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_150_ = l_mkPanicMessageWithDecl(v___x_149_, v___x_148_, v___x_147_, v___x_146_, v___x_145_);
return v___x_150_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_153_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_154_ = lean_unsigned_to_nat(35u);
v___x_155_ = lean_unsigned_to_nat(276u);
v___x_156_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_157_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_158_ = l_mkPanicMessageWithDecl(v___x_157_, v___x_156_, v___x_155_, v___x_154_, v___x_153_);
return v___x_158_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_159_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_160_ = lean_unsigned_to_nat(21u);
v___x_161_ = lean_unsigned_to_nat(277u);
v___x_162_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_163_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_164_ = l_mkPanicMessageWithDecl(v___x_163_, v___x_162_, v___x_161_, v___x_160_, v___x_159_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(lean_object* v_k_165_, lean_object* v_v_166_, lean_object* v_t_167_){
_start:
{
if (lean_obj_tag(v_t_167_) == 0)
{
lean_object* v_size_168_; lean_object* v_k_169_; lean_object* v_v_170_; lean_object* v_l_171_; lean_object* v_r_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_528_; 
v_size_168_ = lean_ctor_get(v_t_167_, 0);
v_k_169_ = lean_ctor_get(v_t_167_, 1);
v_v_170_ = lean_ctor_get(v_t_167_, 2);
v_l_171_ = lean_ctor_get(v_t_167_, 3);
v_r_172_ = lean_ctor_get(v_t_167_, 4);
v_isSharedCheck_528_ = !lean_is_exclusive(v_t_167_);
if (v_isSharedCheck_528_ == 0)
{
v___x_174_ = v_t_167_;
v_isShared_175_ = v_isSharedCheck_528_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_r_172_);
lean_inc(v_l_171_);
lean_inc(v_v_170_);
lean_inc(v_k_169_);
lean_inc(v_size_168_);
lean_dec(v_t_167_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_528_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_NamePart_cmp(v_k_165_, v_k_169_);
switch(v___x_176_)
{
case 0:
{
lean_object* v___x_177_; 
lean_dec(v_size_168_);
v___x_177_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_165_, v_v_166_, v_l_171_);
if (lean_obj_tag(v_r_172_) == 0)
{
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_size_178_; lean_object* v_size_179_; lean_object* v_k_180_; lean_object* v_v_181_; lean_object* v_l_182_; lean_object* v_r_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_size_178_ = lean_ctor_get(v_r_172_, 0);
v_size_179_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_size_179_);
v_k_180_ = lean_ctor_get(v___x_177_, 1);
lean_inc(v_k_180_);
v_v_181_ = lean_ctor_get(v___x_177_, 2);
lean_inc(v_v_181_);
v_l_182_ = lean_ctor_get(v___x_177_, 3);
lean_inc(v_l_182_);
v_r_183_ = lean_ctor_get(v___x_177_, 4);
lean_inc(v_r_183_);
v___x_184_ = lean_unsigned_to_nat(3u);
v___x_185_ = lean_nat_mul(v___x_184_, v_size_178_);
v___x_186_ = lean_nat_dec_lt(v___x_185_, v_size_179_);
lean_dec(v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
lean_dec(v_r_183_);
lean_dec(v_l_182_);
lean_dec(v_v_181_);
lean_dec(v_k_180_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v___x_187_, v_size_179_);
lean_dec(v_size_179_);
v___x_189_ = lean_nat_add(v___x_188_, v_size_178_);
lean_dec(v___x_188_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 3, v___x_177_);
lean_ctor_set(v___x_174_, 0, v___x_189_);
v___x_191_ = v___x_174_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_r_172_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_264_; 
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; 
v_unused_265_ = lean_ctor_get(v___x_177_, 4);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v___x_177_, 3);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v___x_177_, 2);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v___x_177_, 1);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v___x_177_, 0);
lean_dec(v_unused_269_);
v___x_194_ = v___x_177_;
v_isShared_195_ = v_isSharedCheck_264_;
goto v_resetjp_193_;
}
else
{
lean_dec(v___x_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_264_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
if (lean_obj_tag(v_l_182_) == 0)
{
if (lean_obj_tag(v_r_183_) == 0)
{
lean_object* v_size_196_; lean_object* v_size_197_; lean_object* v_k_198_; lean_object* v_v_199_; lean_object* v_l_200_; lean_object* v_r_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_size_196_ = lean_ctor_get(v_l_182_, 0);
v_size_197_ = lean_ctor_get(v_r_183_, 0);
v_k_198_ = lean_ctor_get(v_r_183_, 1);
v_v_199_ = lean_ctor_get(v_r_183_, 2);
v_l_200_ = lean_ctor_get(v_r_183_, 3);
v_r_201_ = lean_ctor_get(v_r_183_, 4);
v___x_202_ = lean_unsigned_to_nat(2u);
v___x_203_ = lean_nat_mul(v___x_202_, v_size_196_);
v___x_204_ = lean_nat_dec_lt(v_size_197_, v___x_203_);
lean_dec(v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_234_; 
lean_inc(v_r_201_);
lean_inc(v_l_200_);
lean_inc(v_v_199_);
lean_inc(v_k_198_);
v_isSharedCheck_234_ = !lean_is_exclusive(v_r_183_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; 
v_unused_235_ = lean_ctor_get(v_r_183_, 4);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_r_183_, 3);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_r_183_, 2);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_r_183_, 1);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_r_183_, 0);
lean_dec(v_unused_239_);
v___x_206_ = v_r_183_;
v_isShared_207_ = v_isSharedCheck_234_;
goto v_resetjp_205_;
}
else
{
lean_dec(v_r_183_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_234_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___x_222_; lean_object* v___y_224_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v___x_208_, v_size_179_);
lean_dec(v_size_179_);
v___x_210_ = lean_nat_add(v___x_209_, v_size_178_);
lean_dec(v___x_209_);
v___x_222_ = lean_nat_add(v___x_208_, v_size_196_);
if (lean_obj_tag(v_l_200_) == 0)
{
lean_object* v_size_232_; 
v_size_232_ = lean_ctor_get(v_l_200_, 0);
lean_inc(v_size_232_);
v___y_224_ = v_size_232_;
goto v___jp_223_;
}
else
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___y_224_ = v___x_233_;
goto v___jp_223_;
}
v___jp_211_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_nat_add(v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec(v___y_213_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 4, v_r_172_);
lean_ctor_set(v___x_206_, 3, v_r_201_);
lean_ctor_set(v___x_206_, 2, v_v_170_);
lean_ctor_set(v___x_206_, 1, v_k_169_);
lean_ctor_set(v___x_206_, 0, v___x_215_);
v___x_217_ = v___x_206_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_221_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_221_, 3, v_r_201_);
lean_ctor_set(v_reuseFailAlloc_221_, 4, v_r_172_);
v___x_217_ = v_reuseFailAlloc_221_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 4, v___x_217_);
lean_ctor_set(v___x_194_, 3, v___y_212_);
lean_ctor_set(v___x_194_, 2, v_v_199_);
lean_ctor_set(v___x_194_, 1, v_k_198_);
lean_ctor_set(v___x_194_, 0, v___x_210_);
v___x_219_ = v___x_194_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_k_198_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_v_199_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v___y_212_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_nat_add(v___x_222_, v___y_224_);
lean_dec(v___y_224_);
lean_dec(v___x_222_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_l_200_);
lean_ctor_set(v___x_174_, 3, v_l_182_);
lean_ctor_set(v___x_174_, 2, v_v_181_);
lean_ctor_set(v___x_174_, 1, v_k_180_);
lean_ctor_set(v___x_174_, 0, v___x_225_);
v___x_227_ = v___x_174_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_180_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_181_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_l_200_);
v___x_227_ = v_reuseFailAlloc_231_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
v___x_228_ = lean_nat_add(v___x_208_, v_size_178_);
if (lean_obj_tag(v_r_201_) == 0)
{
lean_object* v_size_229_; 
v_size_229_ = lean_ctor_get(v_r_201_, 0);
lean_inc(v_size_229_);
v___y_212_ = v___x_227_;
v___y_213_ = v___x_228_;
v___y_214_ = v_size_229_;
goto v___jp_211_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___y_212_ = v___x_227_;
v___y_213_ = v___x_228_;
v___y_214_ = v___x_230_;
goto v___jp_211_;
}
}
}
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_del_object(v___x_174_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v___x_240_, v_size_179_);
lean_dec(v_size_179_);
v___x_242_ = lean_nat_add(v___x_241_, v_size_178_);
lean_dec(v___x_241_);
v___x_243_ = lean_nat_add(v___x_240_, v_size_178_);
v___x_244_ = lean_nat_add(v___x_243_, v_size_197_);
lean_dec(v___x_243_);
lean_inc_ref(v_r_172_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 4, v_r_172_);
lean_ctor_set(v___x_194_, 3, v_r_183_);
lean_ctor_set(v___x_194_, 2, v_v_170_);
lean_ctor_set(v___x_194_, 1, v_k_169_);
lean_ctor_set(v___x_194_, 0, v___x_244_);
v___x_246_ = v___x_194_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_r_183_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_r_172_);
v___x_246_ = v_reuseFailAlloc_259_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
v_isSharedCheck_253_ = !lean_is_exclusive(v_r_172_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; 
v_unused_254_ = lean_ctor_get(v_r_172_, 4);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_r_172_, 3);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_r_172_, 2);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_r_172_, 1);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_r_172_, 0);
lean_dec(v_unused_258_);
v___x_248_ = v_r_172_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_r_172_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v___x_246_);
lean_ctor_set(v___x_248_, 3, v_l_182_);
lean_ctor_set(v___x_248_, 2, v_v_181_);
lean_ctor_set(v___x_248_, 1, v_k_180_);
lean_ctor_set(v___x_248_, 0, v___x_242_);
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_k_180_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_v_181_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v___x_246_);
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
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref_known(v_l_182_, 5);
lean_del_object(v___x_194_);
lean_dec(v_v_181_);
lean_dec(v_k_180_);
lean_dec(v_size_179_);
lean_dec_ref_known(v_r_172_, 5);
lean_del_object(v___x_174_);
lean_dec(v_v_170_);
lean_dec(v_k_169_);
v___x_260_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3);
v___x_261_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_260_);
return v___x_261_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_del_object(v___x_194_);
lean_dec(v_r_183_);
lean_dec(v_v_181_);
lean_dec(v_k_180_);
lean_dec(v_size_179_);
lean_dec_ref_known(v_r_172_, 5);
lean_del_object(v___x_174_);
lean_dec(v_v_170_);
lean_dec(v_k_169_);
v___x_262_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4);
v___x_263_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_262_);
return v___x_263_;
}
}
}
}
else
{
lean_object* v_size_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v_size_270_ = lean_ctor_get(v_r_172_, 0);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v___x_271_, v_size_270_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 3, v___x_177_);
lean_ctor_set(v___x_174_, 0, v___x_272_);
v___x_274_ = v___x_174_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_r_172_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_l_276_; 
v_l_276_ = lean_ctor_get(v___x_177_, 3);
lean_inc(v_l_276_);
if (lean_obj_tag(v_l_276_) == 0)
{
lean_object* v_r_277_; 
v_r_277_ = lean_ctor_get(v___x_177_, 4);
lean_inc(v_r_277_);
if (lean_obj_tag(v_r_277_) == 0)
{
lean_object* v_size_278_; lean_object* v_k_279_; lean_object* v_v_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_294_; 
v_size_278_ = lean_ctor_get(v___x_177_, 0);
v_k_279_ = lean_ctor_get(v___x_177_, 1);
v_v_280_ = lean_ctor_get(v___x_177_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; lean_object* v_unused_296_; 
v_unused_295_ = lean_ctor_get(v___x_177_, 4);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v___x_177_, 3);
lean_dec(v_unused_296_);
v___x_282_ = v___x_177_;
v_isShared_283_ = v_isSharedCheck_294_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_v_280_);
lean_inc(v_k_279_);
lean_inc(v_size_278_);
lean_dec(v___x_177_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_294_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_size_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v_size_284_ = lean_ctor_get(v_r_277_, 0);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v___x_285_, v_size_278_);
lean_dec(v_size_278_);
v___x_287_ = lean_nat_add(v___x_285_, v_size_284_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_r_172_);
lean_ctor_set(v___x_282_, 3, v_r_277_);
lean_ctor_set(v___x_282_, 2, v_v_170_);
lean_ctor_set(v___x_282_, 1, v_k_169_);
lean_ctor_set(v___x_282_, 0, v___x_287_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_r_277_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_r_172_);
v___x_289_ = v_reuseFailAlloc_293_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_291_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_289_);
lean_ctor_set(v___x_174_, 3, v_l_276_);
lean_ctor_set(v___x_174_, 2, v_v_280_);
lean_ctor_set(v___x_174_, 1, v_k_279_);
lean_ctor_set(v___x_174_, 0, v___x_286_);
v___x_291_ = v___x_174_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_279_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_280_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_l_276_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_k_297_; lean_object* v_v_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_310_; 
v_k_297_ = lean_ctor_get(v___x_177_, 1);
v_v_298_ = lean_ctor_get(v___x_177_, 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_311_ = lean_ctor_get(v___x_177_, 4);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v___x_177_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v___x_177_, 0);
lean_dec(v_unused_313_);
v___x_300_ = v___x_177_;
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_v_298_);
lean_inc(v_k_297_);
lean_dec(v___x_177_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = lean_unsigned_to_nat(3u);
v___x_303_ = lean_unsigned_to_nat(1u);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 3, v_r_277_);
lean_ctor_set(v___x_300_, 2, v_v_170_);
lean_ctor_set(v___x_300_, 1, v_k_169_);
lean_ctor_set(v___x_300_, 0, v___x_303_);
v___x_305_ = v___x_300_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_r_277_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_r_277_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_305_);
lean_ctor_set(v___x_174_, 3, v_l_276_);
lean_ctor_set(v___x_174_, 2, v_v_298_);
lean_ctor_set(v___x_174_, 1, v_k_297_);
lean_ctor_set(v___x_174_, 0, v___x_302_);
v___x_307_ = v___x_174_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_k_297_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_v_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_l_276_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_r_314_; 
v_r_314_ = lean_ctor_get(v___x_177_, 4);
lean_inc(v_r_314_);
if (lean_obj_tag(v_r_314_) == 0)
{
lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_340_; 
v_k_315_ = lean_ctor_get(v___x_177_, 1);
v_v_316_ = lean_ctor_get(v___x_177_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_341_ = lean_ctor_get(v___x_177_, 4);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v___x_177_, 3);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v___x_177_, 0);
lean_dec(v_unused_343_);
v___x_318_ = v___x_177_;
v_isShared_319_ = v_isSharedCheck_340_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_v_316_);
lean_inc(v_k_315_);
lean_dec(v___x_177_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_340_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_k_320_; lean_object* v_v_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_336_; 
v_k_320_ = lean_ctor_get(v_r_314_, 1);
v_v_321_ = lean_ctor_get(v_r_314_, 2);
v_isSharedCheck_336_ = !lean_is_exclusive(v_r_314_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; lean_object* v_unused_338_; lean_object* v_unused_339_; 
v_unused_337_ = lean_ctor_get(v_r_314_, 4);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_r_314_, 3);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_r_314_, 0);
lean_dec(v_unused_339_);
v___x_323_ = v_r_314_;
v_isShared_324_ = v_isSharedCheck_336_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_v_321_);
lean_inc(v_k_320_);
lean_dec(v_r_314_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_336_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = lean_unsigned_to_nat(1u);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 4, v_l_276_);
lean_ctor_set(v___x_323_, 3, v_l_276_);
lean_ctor_set(v___x_323_, 2, v_v_316_);
lean_ctor_set(v___x_323_, 1, v_k_315_);
lean_ctor_set(v___x_323_, 0, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_k_315_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_v_316_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_l_276_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_l_276_);
v___x_328_ = v_reuseFailAlloc_335_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 4, v_l_276_);
lean_ctor_set(v___x_318_, 2, v_v_170_);
lean_ctor_set(v___x_318_, 1, v_k_169_);
lean_ctor_set(v___x_318_, 0, v___x_326_);
v___x_330_ = v___x_318_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_l_276_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_l_276_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_330_);
lean_ctor_set(v___x_174_, 3, v___x_328_);
lean_ctor_set(v___x_174_, 2, v_v_321_);
lean_ctor_set(v___x_174_, 1, v_k_320_);
lean_ctor_set(v___x_174_, 0, v___x_325_);
v___x_332_ = v___x_174_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_k_320_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_v_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_unsigned_to_nat(2u);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_r_314_);
lean_ctor_set(v___x_174_, 3, v___x_177_);
lean_ctor_set(v___x_174_, 0, v___x_344_);
v___x_346_ = v___x_174_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_r_314_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_unsigned_to_nat(1u);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_177_);
lean_ctor_set(v___x_174_, 3, v___x_177_);
lean_ctor_set(v___x_174_, 0, v___x_348_);
v___x_350_ = v___x_174_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v___x_177_);
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
case 1:
{
lean_object* v___x_353_; 
lean_dec(v_v_170_);
lean_dec(v_k_169_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 2, v_v_166_);
lean_ctor_set(v___x_174_, 1, v_k_165_);
v___x_353_ = v___x_174_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_size_168_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_k_165_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_v_166_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_l_171_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_r_172_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
default: 
{
lean_object* v___x_355_; 
lean_dec(v_size_168_);
v___x_355_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_165_, v_v_166_, v_r_172_);
if (lean_obj_tag(v_l_171_) == 0)
{
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_size_356_; lean_object* v_size_357_; lean_object* v_k_358_; lean_object* v_v_359_; lean_object* v_l_360_; lean_object* v_r_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_size_356_ = lean_ctor_get(v_l_171_, 0);
v_size_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_size_357_);
v_k_358_ = lean_ctor_get(v___x_355_, 1);
lean_inc(v_k_358_);
v_v_359_ = lean_ctor_get(v___x_355_, 2);
lean_inc(v_v_359_);
v_l_360_ = lean_ctor_get(v___x_355_, 3);
lean_inc(v_l_360_);
v_r_361_ = lean_ctor_get(v___x_355_, 4);
lean_inc(v_r_361_);
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_nat_mul(v___x_362_, v_size_356_);
v___x_364_ = lean_nat_dec_lt(v___x_363_, v_size_357_);
lean_dec(v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_dec(v_r_361_);
lean_dec(v_l_360_);
lean_dec(v_v_359_);
lean_dec(v_k_358_);
v___x_365_ = lean_unsigned_to_nat(1u);
v___x_366_ = lean_nat_add(v___x_365_, v_size_356_);
v___x_367_ = lean_nat_add(v___x_366_, v_size_357_);
lean_dec(v_size_357_);
lean_dec(v___x_366_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_355_);
lean_ctor_set(v___x_174_, 0, v___x_367_);
v___x_369_ = v___x_174_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_l_171_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v___x_355_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
else
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_440_; 
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_441_ = lean_ctor_get(v___x_355_, 4);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v___x_355_, 3);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v___x_355_, 2);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v___x_355_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v___x_355_, 0);
lean_dec(v_unused_445_);
v___x_372_ = v___x_355_;
v_isShared_373_ = v_isSharedCheck_440_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_355_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_440_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
if (lean_obj_tag(v_l_360_) == 0)
{
if (lean_obj_tag(v_r_361_) == 0)
{
lean_object* v_size_374_; lean_object* v_k_375_; lean_object* v_v_376_; lean_object* v_l_377_; lean_object* v_r_378_; lean_object* v_size_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_size_374_ = lean_ctor_get(v_l_360_, 0);
v_k_375_ = lean_ctor_get(v_l_360_, 1);
v_v_376_ = lean_ctor_get(v_l_360_, 2);
v_l_377_ = lean_ctor_get(v_l_360_, 3);
v_r_378_ = lean_ctor_get(v_l_360_, 4);
v_size_379_ = lean_ctor_get(v_r_361_, 0);
v___x_380_ = lean_unsigned_to_nat(2u);
v___x_381_ = lean_nat_mul(v___x_380_, v_size_379_);
v___x_382_ = lean_nat_dec_lt(v_size_374_, v___x_381_);
lean_dec(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_411_; 
lean_inc(v_r_378_);
lean_inc(v_l_377_);
lean_inc(v_v_376_);
lean_inc(v_k_375_);
v_isSharedCheck_411_ = !lean_is_exclusive(v_l_360_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_412_ = lean_ctor_get(v_l_360_, 4);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_l_360_, 3);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_l_360_, 2);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_l_360_, 1);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_l_360_, 0);
lean_dec(v_unused_416_);
v___x_384_ = v_l_360_;
v_isShared_385_ = v_isSharedCheck_411_;
goto v_resetjp_383_;
}
else
{
lean_dec(v_l_360_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_411_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_401_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v___x_386_, v_size_356_);
v___x_388_ = lean_nat_add(v___x_387_, v_size_357_);
lean_dec(v_size_357_);
if (lean_obj_tag(v_l_377_) == 0)
{
lean_object* v_size_409_; 
v_size_409_ = lean_ctor_get(v_l_377_, 0);
lean_inc(v_size_409_);
v___y_401_ = v_size_409_;
goto v___jp_400_;
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___y_401_ = v___x_410_;
goto v___jp_400_;
}
v___jp_389_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_nat_add(v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec(v___y_391_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 4, v_r_361_);
lean_ctor_set(v___x_384_, 3, v_r_378_);
lean_ctor_set(v___x_384_, 2, v_v_359_);
lean_ctor_set(v___x_384_, 1, v_k_358_);
lean_ctor_set(v___x_384_, 0, v___x_393_);
v___x_395_ = v___x_384_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_k_358_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_v_359_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_r_378_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_r_361_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_397_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v___x_395_);
lean_ctor_set(v___x_372_, 3, v___y_390_);
lean_ctor_set(v___x_372_, 2, v_v_376_);
lean_ctor_set(v___x_372_, 1, v_k_375_);
lean_ctor_set(v___x_372_, 0, v___x_388_);
v___x_397_ = v___x_372_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_375_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_376_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v___y_390_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_nat_add(v___x_387_, v___y_401_);
lean_dec(v___y_401_);
lean_dec(v___x_387_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_l_377_);
lean_ctor_set(v___x_174_, 0, v___x_402_);
v___x_404_ = v___x_174_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_l_171_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_l_377_);
v___x_404_ = v_reuseFailAlloc_408_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_nat_add(v___x_386_, v_size_379_);
if (lean_obj_tag(v_r_378_) == 0)
{
lean_object* v_size_406_; 
v_size_406_ = lean_ctor_get(v_r_378_, 0);
lean_inc(v_size_406_);
v___y_390_ = v___x_404_;
v___y_391_ = v___x_405_;
v___y_392_ = v_size_406_;
goto v___jp_389_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___y_390_ = v___x_404_;
v___y_391_ = v___x_405_;
v___y_392_ = v___x_407_;
goto v___jp_389_;
}
}
}
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
lean_del_object(v___x_174_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_add(v___x_417_, v_size_356_);
v___x_419_ = lean_nat_add(v___x_418_, v_size_357_);
lean_dec(v_size_357_);
v___x_420_ = lean_nat_add(v___x_418_, v_size_374_);
lean_dec(v___x_418_);
lean_inc_ref(v_l_171_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 4, v_l_360_);
lean_ctor_set(v___x_372_, 3, v_l_171_);
lean_ctor_set(v___x_372_, 2, v_v_170_);
lean_ctor_set(v___x_372_, 1, v_k_169_);
lean_ctor_set(v___x_372_, 0, v___x_420_);
v___x_422_ = v___x_372_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_l_171_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_l_360_);
v___x_422_ = v_reuseFailAlloc_435_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_isSharedCheck_429_ = !lean_is_exclusive(v_l_171_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_430_ = lean_ctor_get(v_l_171_, 4);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_l_171_, 3);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_l_171_, 2);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_l_171_, 1);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_l_171_, 0);
lean_dec(v_unused_434_);
v___x_424_ = v_l_171_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_l_171_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 4, v_r_361_);
lean_ctor_set(v___x_424_, 3, v___x_422_);
lean_ctor_set(v___x_424_, 2, v_v_359_);
lean_ctor_set(v___x_424_, 1, v_k_358_);
lean_ctor_set(v___x_424_, 0, v___x_419_);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_358_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_359_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_r_361_);
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
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref_known(v_l_360_, 5);
lean_del_object(v___x_372_);
lean_dec(v_v_359_);
lean_dec(v_k_358_);
lean_dec(v_size_357_);
lean_dec_ref_known(v_l_171_, 5);
lean_del_object(v___x_174_);
lean_dec(v_v_170_);
lean_dec(v_k_169_);
v___x_436_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7);
v___x_437_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_436_);
return v___x_437_;
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_del_object(v___x_372_);
lean_dec(v_r_361_);
lean_dec(v_v_359_);
lean_dec(v_k_358_);
lean_dec(v_size_357_);
lean_dec_ref_known(v_l_171_, 5);
lean_del_object(v___x_174_);
lean_dec(v_v_170_);
lean_dec(v_k_169_);
v___x_438_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8);
v___x_439_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_438_);
return v___x_439_;
}
}
}
}
else
{
lean_object* v_size_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v_size_446_ = lean_ctor_get(v_l_171_, 0);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v___x_447_, v_size_446_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_355_);
lean_ctor_set(v___x_174_, 0, v___x_448_);
v___x_450_ = v___x_174_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_l_171_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v___x_355_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
else
{
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_l_452_; 
v_l_452_ = lean_ctor_get(v___x_355_, 3);
lean_inc(v_l_452_);
if (lean_obj_tag(v_l_452_) == 0)
{
lean_object* v_r_453_; 
v_r_453_ = lean_ctor_get(v___x_355_, 4);
lean_inc(v_r_453_);
if (lean_obj_tag(v_r_453_) == 0)
{
lean_object* v_size_454_; lean_object* v_k_455_; lean_object* v_v_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_470_; 
v_size_454_ = lean_ctor_get(v___x_355_, 0);
v_k_455_ = lean_ctor_get(v___x_355_, 1);
v_v_456_ = lean_ctor_get(v___x_355_, 2);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; 
v_unused_471_ = lean_ctor_get(v___x_355_, 4);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v___x_355_, 3);
lean_dec(v_unused_472_);
v___x_458_ = v___x_355_;
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_v_456_);
lean_inc(v_k_455_);
lean_inc(v_size_454_);
lean_dec(v___x_355_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_470_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_size_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v_size_460_ = lean_ctor_get(v_l_452_, 0);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_add(v___x_461_, v_size_454_);
lean_dec(v_size_454_);
v___x_463_ = lean_nat_add(v___x_461_, v_size_460_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 4, v_l_452_);
lean_ctor_set(v___x_458_, 3, v_l_171_);
lean_ctor_set(v___x_458_, 2, v_v_170_);
lean_ctor_set(v___x_458_, 1, v_k_169_);
lean_ctor_set(v___x_458_, 0, v___x_463_);
v___x_465_ = v___x_458_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_l_171_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_l_452_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_r_453_);
lean_ctor_set(v___x_174_, 3, v___x_465_);
lean_ctor_set(v___x_174_, 2, v_v_456_);
lean_ctor_set(v___x_174_, 1, v_k_455_);
lean_ctor_set(v___x_174_, 0, v___x_462_);
v___x_467_ = v___x_174_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_k_455_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_v_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_r_453_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_k_473_; lean_object* v_v_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_498_; 
v_k_473_ = lean_ctor_get(v___x_355_, 1);
v_v_474_ = lean_ctor_get(v___x_355_, 2);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; 
v_unused_499_ = lean_ctor_get(v___x_355_, 4);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v___x_355_, 3);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v___x_355_, 0);
lean_dec(v_unused_501_);
v___x_476_ = v___x_355_;
v_isShared_477_ = v_isSharedCheck_498_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_v_474_);
lean_inc(v_k_473_);
lean_dec(v___x_355_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_498_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_k_478_; lean_object* v_v_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_494_; 
v_k_478_ = lean_ctor_get(v_l_452_, 1);
v_v_479_ = lean_ctor_get(v_l_452_, 2);
v_isSharedCheck_494_ = !lean_is_exclusive(v_l_452_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_495_ = lean_ctor_get(v_l_452_, 4);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_l_452_, 3);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_l_452_, 0);
lean_dec(v_unused_497_);
v___x_481_ = v_l_452_;
v_isShared_482_ = v_isSharedCheck_494_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_v_479_);
lean_inc(v_k_478_);
lean_dec(v_l_452_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_494_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = lean_unsigned_to_nat(3u);
v___x_484_ = lean_unsigned_to_nat(1u);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 4, v_r_453_);
lean_ctor_set(v___x_481_, 3, v_r_453_);
lean_ctor_set(v___x_481_, 2, v_v_170_);
lean_ctor_set(v___x_481_, 1, v_k_169_);
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_r_453_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_r_453_);
v___x_486_ = v_reuseFailAlloc_493_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 3, v_r_453_);
lean_ctor_set(v___x_476_, 0, v___x_484_);
v___x_488_ = v___x_476_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_k_473_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_v_474_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_r_453_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_r_453_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_488_);
lean_ctor_set(v___x_174_, 3, v___x_486_);
lean_ctor_set(v___x_174_, 2, v_v_479_);
lean_ctor_set(v___x_174_, 1, v_k_478_);
lean_ctor_set(v___x_174_, 0, v___x_483_);
v___x_490_ = v___x_174_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_478_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_502_; 
v_r_502_ = lean_ctor_get(v___x_355_, 4);
lean_inc(v_r_502_);
if (lean_obj_tag(v_r_502_) == 0)
{
lean_object* v_k_503_; lean_object* v_v_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_516_; 
v_k_503_ = lean_ctor_get(v___x_355_, 1);
v_v_504_ = lean_ctor_get(v___x_355_, 2);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_517_ = lean_ctor_get(v___x_355_, 4);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v___x_355_, 3);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v___x_355_, 0);
lean_dec(v_unused_519_);
v___x_506_ = v___x_355_;
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_v_504_);
lean_inc(v_k_503_);
lean_dec(v___x_355_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(3u);
v___x_509_ = lean_unsigned_to_nat(1u);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 4, v_l_452_);
lean_ctor_set(v___x_506_, 2, v_v_170_);
lean_ctor_set(v___x_506_, 1, v_k_169_);
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_l_452_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_l_452_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v_r_502_);
lean_ctor_set(v___x_174_, 3, v___x_511_);
lean_ctor_set(v___x_174_, 2, v_v_504_);
lean_ctor_set(v___x_174_, 1, v_k_503_);
lean_ctor_set(v___x_174_, 0, v___x_508_);
v___x_513_ = v___x_174_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_r_502_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = lean_unsigned_to_nat(2u);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_355_);
lean_ctor_set(v___x_174_, 3, v_r_502_);
lean_ctor_set(v___x_174_, 0, v___x_520_);
v___x_522_ = v___x_174_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_r_502_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v___x_355_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_unsigned_to_nat(1u);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 4, v___x_355_);
lean_ctor_set(v___x_174_, 3, v___x_355_);
lean_ctor_set(v___x_174_, 0, v___x_524_);
v___x_526_ = v___x_174_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_169_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v___x_355_);
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
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v_k_165_);
lean_ctor_set(v___x_530_, 2, v_v_166_);
lean_ctor_set(v___x_530_, 3, v_t_167_);
lean_ctor_set(v___x_530_, 4, v_t_167_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(lean_object* v_val_531_, lean_object* v_k_532_){
_start:
{
if (lean_obj_tag(v_k_532_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_val_531_);
v___x_534_ = lean_box(1);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
else
{
lean_object* v_head_536_; lean_object* v_tail_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v_head_536_ = lean_ctor_get(v_k_532_, 0);
v_tail_537_ = lean_ctor_get(v_k_532_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_k_532_);
if (v_isSharedCheck_548_ == 0)
{
v___x_539_ = v_k_532_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_tail_537_);
lean_inc(v_head_536_);
lean_dec(v_k_532_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_t_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v_t_541_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_531_, v_tail_537_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_box(1);
v___x_544_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_536_, v_t_541_, v___x_543_);
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 0);
lean_ctor_set(v___x_539_, 1, v___x_544_);
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_546_ = v___x_539_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(lean_object* v_val_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_a_552_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_x_550_, 0);
lean_dec(v_unused_561_);
v___x_554_ = v_x_550_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v_x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_val_549_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_a_552_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_579_; 
v_a_562_ = lean_ctor_get(v_x_550_, 0);
v_a_563_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_579_ == 0)
{
v___x_565_ = v_x_550_;
v_isShared_566_ = v_isSharedCheck_579_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_inc(v_a_562_);
lean_dec(v_x_550_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_579_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_head_567_; lean_object* v_tail_568_; lean_object* v___y_570_; lean_object* v___x_575_; 
v_head_567_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_head_567_);
v_tail_568_ = lean_ctor_get(v_x_551_, 1);
lean_inc(v_tail_568_);
lean_dec_ref_known(v_x_551_, 2);
v___x_575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_563_, v_head_567_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_549_, v_tail_568_);
v___y_570_ = v___x_576_;
goto v___jp_569_;
}
else
{
lean_object* v_val_577_; lean_object* v___x_578_; 
v_val_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_575_, 1);
v___x_578_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_549_, v_val_577_, v_tail_568_);
v___y_570_ = v___x_578_;
goto v___jp_569_;
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_567_, v___y_570_, v_a_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v___x_571_);
v___x_573_ = v___x_565_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_562_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg(lean_object* v_t_580_, lean_object* v_n_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_581_);
v___x_584_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_b_582_, v_t_580_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg___boxed(lean_object* v_t_585_, lean_object* v_n_586_, lean_object* v_b_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_NameTrie_insert___redArg(v_t_585_, v_n_586_, v_b_587_);
lean_dec(v_n_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert(lean_object* v_00_u03b2_589_, lean_object* v_t_590_, lean_object* v_n_591_, lean_object* v_b_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_NameTrie_insert___redArg(v_t_590_, v_n_591_, v_b_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___boxed(lean_object* v_00_u03b2_594_, lean_object* v_t_595_, lean_object* v_n_596_, lean_object* v_b_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_NameTrie_insert(v_00_u03b2_594_, v_t_595_, v_n_596_, v_b_597_);
lean_dec(v_n_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(lean_object* v_00_u03b2_599_, lean_object* v_val_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_600_, v_x_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_604_, lean_object* v_msg_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v_msg_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(lean_object* v_00_u03b2_607_, lean_object* v_k_608_, lean_object* v_v_609_, lean_object* v_t_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_608_, v_v_609_, v_t_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(lean_object* v_00_u03b4_612_, lean_object* v_t_613_, lean_object* v_k_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_613_, v_k_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b4_616_, lean_object* v_t_617_, lean_object* v_k_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(v_00_u03b4_616_, v_t_617_, v_k_618_);
lean_dec_ref(v_k_618_);
lean_dec(v_t_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(lean_object* v_00_u03b2_620_, lean_object* v_val_621_, lean_object* v_k_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_621_, v_k_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_NameTrie_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_PrefixTreeNode_empty___redArg();
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg(){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg___boxed(lean_object* v___dummy_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_NameTrie_empty___redArg();
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty(lean_object* v_00_u03b2_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg(){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg___boxed(lean_object* v___dummy_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_instInhabitedNameTrie___redArg();
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie(lean_object* v_00_u03b2_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg(){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg___boxed(lean_object* v___dummy_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_instEmptyCollectionNameTrie___redArg();
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie(lean_object* v_00_u03b2_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v_x_643_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v_x_643_);
return v_a_645_;
}
else
{
lean_object* v_a_646_; lean_object* v_head_647_; lean_object* v_tail_648_; lean_object* v___x_649_; 
v_a_646_ = lean_ctor_get(v_x_643_, 1);
lean_inc(v_a_646_);
lean_dec_ref(v_x_643_);
v_head_647_ = lean_ctor_get(v_x_644_, 0);
v_tail_648_ = lean_ctor_get(v_x_644_, 1);
v___x_649_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_646_, v_head_647_);
lean_dec(v_a_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = lean_box(0);
return v___x_650_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_649_, 1);
v_x_643_ = v_val_651_;
v_x_644_ = v_tail_648_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_653_, v_x_654_);
lean_dec(v_x_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object* v_t_656_, lean_object* v_k_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_657_);
v___x_659_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_t_656_, v___x_658_);
lean_dec(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg___boxed(lean_object* v_t_660_, lean_object* v_k_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_NameTrie_find_x3f___redArg(v_t_660_, v_k_661_);
lean_dec(v_k_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f(lean_object* v_00_u03b2_663_, lean_object* v_t_664_, lean_object* v_k_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_NameTrie_find_x3f___redArg(v_t_664_, v_k_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___boxed(lean_object* v_00_u03b2_667_, lean_object* v_t_668_, lean_object* v_k_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_NameTrie_find_x3f(v_00_u03b2_667_, v_t_668_, v_k_669_);
lean_dec(v_k_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(lean_object* v_00_u03b2_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(v_00_u03b2_675_, v_x_676_, v_x_677_);
lean_dec(v_x_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg(lean_object* v_t_680_, lean_object* v_k_681_){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_683_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_681_);
v___x_684_ = lean_box(0);
v___x_685_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_682_, v___x_684_, v_t_680_, v___x_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(lean_object* v_t_686_, lean_object* v_k_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_NameTrie_findLongestPrefix_x3f___redArg(v_t_686_, v_k_687_);
lean_dec(v_k_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f(lean_object* v_00_u03b2_689_, lean_object* v_t_690_, lean_object* v_k_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_693_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_691_);
v___x_694_ = lean_box(0);
v___x_695_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_692_, v___x_694_, v_t_690_, v___x_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___boxed(lean_object* v_00_u03b2_696_, lean_object* v_t_697_, lean_object* v_k_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_NameTrie_findLongestPrefix_x3f(v_00_u03b2_696_, v_t_697_, v_k_698_);
lean_dec(v_k_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg(lean_object* v_inst_700_, lean_object* v_t_701_, lean_object* v_k_702_, lean_object* v_init_703_, lean_object* v_f_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_706_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_702_);
lean_inc(v_init_703_);
v___x_707_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_700_, v___x_705_, v_init_703_, v_f_704_, v___x_706_, v_t_701_, v_init_703_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg___boxed(lean_object* v_inst_708_, lean_object* v_t_709_, lean_object* v_k_710_, lean_object* v_init_711_, lean_object* v_f_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_NameTrie_foldMatchingM___redArg(v_inst_708_, v_t_709_, v_k_710_, v_init_711_, v_f_712_);
lean_dec(v_k_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM(lean_object* v_m_714_, lean_object* v_00_u03b2_715_, lean_object* v_00_u03c3_716_, lean_object* v_inst_717_, lean_object* v_t_718_, lean_object* v_k_719_, lean_object* v_init_720_, lean_object* v_f_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_722_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_723_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_719_);
lean_inc(v_init_720_);
v___x_724_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_717_, v___x_722_, v_init_720_, v_f_721_, v___x_723_, v_t_718_, v_init_720_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___boxed(lean_object* v_m_725_, lean_object* v_00_u03b2_726_, lean_object* v_00_u03c3_727_, lean_object* v_inst_728_, lean_object* v_t_729_, lean_object* v_k_730_, lean_object* v_init_731_, lean_object* v_f_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_NameTrie_foldMatchingM(v_m_725_, v_00_u03b2_726_, v_00_u03c3_727_, v_inst_728_, v_t_729_, v_k_730_, v_init_731_, v_f_732_);
lean_dec(v_k_730_);
return v_res_733_;
}
}
static lean_object* _init_l_Lean_NameTrie_foldM___redArg___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM___redArg(lean_object* v_inst_736_, lean_object* v_t_737_, lean_object* v_init_738_, lean_object* v_f_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_741_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_738_);
v___x_742_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_736_, v___x_740_, v_init_738_, v_f_739_, v___x_741_, v_t_737_, v_init_738_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM(lean_object* v_m_743_, lean_object* v_00_u03b2_744_, lean_object* v_00_u03c3_745_, lean_object* v_inst_746_, lean_object* v_t_747_, lean_object* v_init_748_, lean_object* v_f_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_751_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_748_);
v___x_752_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_746_, v___x_750_, v_init_748_, v_f_749_, v___x_751_, v_t_747_, v_init_748_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___lam__0(lean_object* v_f_753_, lean_object* v_b_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_apply_1(v_f_753_, v_b_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg(lean_object* v_inst_757_, lean_object* v_t_758_, lean_object* v_k_759_, lean_object* v_f_760_){
_start:
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___f_761_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_761_, 0, v_f_760_);
v___x_762_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_763_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_759_);
v___x_764_ = lean_box(0);
v___x_765_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v___x_762_, v___x_764_, v___f_761_, v___x_763_, v_t_758_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___boxed(lean_object* v_inst_766_, lean_object* v_t_767_, lean_object* v_k_768_, lean_object* v_f_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_NameTrie_forMatchingM___redArg(v_inst_766_, v_t_767_, v_k_768_, v_f_769_);
lean_dec(v_k_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM(lean_object* v_m_771_, lean_object* v_00_u03b2_772_, lean_object* v_inst_773_, lean_object* v_t_774_, lean_object* v_k_775_, lean_object* v_f_776_){
_start:
{
lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___f_777_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_777_, 0, v_f_776_);
v___x_778_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_779_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_775_);
v___x_780_ = lean_box(0);
v___x_781_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_773_, v___x_778_, v___x_780_, v___f_777_, v___x_779_, v_t_774_, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___boxed(lean_object* v_m_782_, lean_object* v_00_u03b2_783_, lean_object* v_inst_784_, lean_object* v_t_785_, lean_object* v_k_786_, lean_object* v_f_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_NameTrie_forMatchingM(v_m_782_, v_00_u03b2_783_, v_inst_784_, v_t_785_, v_k_786_, v_f_787_);
lean_dec(v_k_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM___redArg(lean_object* v_inst_789_, lean_object* v_t_790_, lean_object* v_f_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___f_792_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_792_, 0, v_f_791_);
v___x_793_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_794_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_795_ = lean_box(0);
v___x_796_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_789_, v___x_793_, v___x_795_, v___f_792_, v___x_794_, v_t_790_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM(lean_object* v_m_797_, lean_object* v_00_u03b2_798_, lean_object* v_inst_799_, lean_object* v_t_800_, lean_object* v_f_801_){
_start:
{
lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___f_802_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_802_, 0, v_f_801_);
v___x_803_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_804_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_805_ = lean_box(0);
v___x_806_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_799_, v___x_803_, v___x_805_, v___f_802_, v___x_804_, v_t_800_, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v_a_807_, 0);
if (lean_obj_tag(v_a_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; 
v_a_810_ = lean_ctor_get(v_a_807_, 1);
lean_inc(v_a_810_);
lean_dec_ref(v_a_807_);
v___x_811_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_a_808_, v_a_810_);
return v___x_811_;
}
else
{
lean_object* v_a_812_; lean_object* v_val_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_inc_ref(v_a_809_);
v_a_812_ = lean_ctor_get(v_a_807_, 1);
lean_inc(v_a_812_);
lean_dec_ref(v_a_807_);
v_val_813_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_a_809_, 1);
v___x_814_ = lean_array_push(v_a_808_, v_val_813_);
v___x_815_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v___x_814_, v_a_812_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(lean_object* v_init_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_817_) == 0)
{
lean_object* v_v_818_; lean_object* v_l_819_; lean_object* v_r_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_v_818_ = lean_ctor_get(v_x_817_, 2);
lean_inc(v_v_818_);
v_l_819_ = lean_ctor_get(v_x_817_, 3);
lean_inc(v_l_819_);
v_r_820_ = lean_ctor_get(v_x_817_, 4);
lean_inc(v_r_820_);
lean_dec_ref_known(v_x_817_, 5);
v___x_821_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_816_, v_l_819_);
v___x_822_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_v_818_, v___x_821_);
v_init_816_ = v___x_822_;
v_x_817_ = v_r_820_;
goto _start;
}
else
{
return v_init_816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(lean_object* v_init_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_826_, v_a_827_);
return v___x_828_;
}
else
{
lean_object* v_head_829_; lean_object* v_tail_830_; lean_object* v_a_831_; lean_object* v___x_832_; 
v_head_829_ = lean_ctor_get(v_a_825_, 0);
v_tail_830_ = lean_ctor_get(v_a_825_, 1);
v_a_831_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_a_831_);
lean_dec_ref(v_a_826_);
v___x_832_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_831_, v_head_829_);
lean_dec(v_a_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref(v_a_827_);
lean_inc_ref(v_init_824_);
return v_init_824_;
}
else
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_832_, 1);
v_a_825_ = v_tail_830_;
v_a_826_ = v_val_833_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg___boxed(lean_object* v_init_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_836_);
lean_dec_ref(v_init_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object* v_t_842_, lean_object* v_k_843_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_845_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_843_);
v___x_846_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_844_, v___x_845_, v_t_842_, v___x_844_);
lean_dec(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg___boxed(lean_object* v_t_847_, lean_object* v_k_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_847_, v_k_848_);
lean_dec(v_k_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray(lean_object* v_00_u03b2_850_, lean_object* v_t_851_, lean_object* v_k_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_851_, v_k_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___boxed(lean_object* v_00_u03b2_854_, lean_object* v_t_855_, lean_object* v_k_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_NameTrie_matchingToArray(v_00_u03b2_854_, v_t_855_, v_k_856_);
lean_dec(v_k_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(lean_object* v_00_u03b2_858_, lean_object* v_init_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_859_, v_a_860_, v_a_861_, v_a_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(lean_object* v_00_u03b2_864_, lean_object* v_init_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(v_00_u03b2_864_, v_init_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_866_);
lean_dec_ref(v_init_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(lean_object* v_00_u03b2_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_871_, v_a_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_874_, lean_object* v_init_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_875_, v_x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray___redArg(lean_object* v_t_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_880_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_881_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_879_, v___x_880_, v_t_878_, v___x_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray(lean_object* v_00_u03b2_882_, lean_object* v_t_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_NameTrie_toArray___redArg(v_t_883_);
return v___x_884_;
}
}
lean_object* runtime_initialize_Lean_Data_PrefixTree(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_NameTrie(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
