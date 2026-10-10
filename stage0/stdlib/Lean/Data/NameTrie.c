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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_NamePart_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_s_7_; lean_object* v___x_8_; 
v_s_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_s_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_s_7_);
return v___x_8_;
}
else
{
lean_object* v_n_9_; lean_object* v___x_10_; 
v_n_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_n_9_);
lean_dec_ref_known(v_t_5_, 1);
v___x_10_ = lean_apply_1(v_k_6_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_NamePart_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_NamePart_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_str_elim___redArg(lean_object* v_t_23_, lean_object* v_str_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_NamePart_ctorElim___redArg(v_t_23_, v_str_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_str_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_str_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_NamePart_ctorElim___redArg(v_t_27_, v_str_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_num_elim___redArg(lean_object* v_t_31_, lean_object* v_num_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_NamePart_ctorElim___redArg(v_t_31_, v_num_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_num_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_num_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_NamePart_ctorElim___redArg(v_t_35_, v_num_37_);
return v___x_38_;
}
}
uint8_t l_Lean_instBEqNamePart_beq(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v_s_41_; lean_object* v_s_42_; uint8_t v___x_43_; 
v_s_41_ = lean_ctor_get(v_x_39_, 0);
v_s_42_ = lean_ctor_get(v_x_40_, 0);
v___x_43_ = lean_string_dec_eq(v_s_41_, v_s_42_);
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
else
{
if (lean_obj_tag(v_x_40_) == 1)
{
lean_object* v_n_45_; lean_object* v_n_46_; uint8_t v___x_47_; 
v_n_45_ = lean_ctor_get(v_x_39_, 0);
v_n_46_ = lean_ctor_get(v_x_40_, 0);
v___x_47_ = lean_nat_dec_eq(v_n_45_, v_n_46_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqNamePart_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_39_ = stack[0].m_obj;
lean_object* v_x_40_ = stack[1].m_obj;
uint8_t v_res_49_;
v_res_49_ = l_Lean_instBEqNamePart_beq(v_x_39_, v_x_40_);
stack->m_num = v_res_49_;
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
uint8_t l_Lean_NamePart_cmp(lean_object* v_x_67_, lean_object* v_x_68_){
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
LEAN_EXPORT void l_Lean_NamePart_cmp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_67_ = stack[0].m_obj;
lean_object* v_x_68_ = stack[1].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Lean_NamePart_cmp(v_x_67_, v_x_68_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_NamePart_cmp___boxed(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Lean_NamePart_cmp(v_x_82_, v_x_83_);
lean_dec_ref(v_x_83_);
lean_dec_ref(v_x_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
uint8_t l_Lean_NamePart_lt(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_object* v_s_88_; lean_object* v_s_89_; uint8_t v___x_90_; 
v_s_88_ = lean_ctor_get(v_x_86_, 0);
v_s_89_ = lean_ctor_get(v_x_87_, 0);
v___x_90_ = lean_string_dec_lt(v_s_88_, v_s_89_);
return v___x_90_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
else
{
if (lean_obj_tag(v_x_87_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
lean_object* v_n_93_; lean_object* v_n_94_; uint8_t v___x_95_; 
v_n_93_ = lean_ctor_get(v_x_86_, 0);
v_n_94_ = lean_ctor_get(v_x_87_, 0);
v___x_95_ = lean_nat_dec_lt(v_n_93_, v_n_94_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT void l_Lean_NamePart_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_86_ = stack[0].m_obj;
lean_object* v_x_87_ = stack[1].m_obj;
uint8_t v_res_96_;
v_res_96_ = l_Lean_NamePart_lt(v_x_86_, v_x_87_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_NamePart_lt___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_Lean_NamePart_lt(v_x_97_, v_x_98_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_x_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
switch(lean_obj_tag(v_x_101_))
{
case 0:
{
return v_x_102_;
}
case 1:
{
lean_object* v_pre_103_; lean_object* v_str_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_pre_103_ = lean_ctor_get(v_x_101_, 0);
v_str_104_ = lean_ctor_get(v_x_101_, 1);
lean_inc_ref(v_str_104_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v_str_104_);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_x_102_);
v_x_101_ = v_pre_103_;
v_x_102_ = v___x_106_;
goto _start;
}
default: 
{
lean_object* v_pre_108_; lean_object* v_i_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_pre_108_ = lean_ctor_get(v_x_101_, 0);
v_i_109_ = lean_ctor_get(v_x_101_, 1);
lean_inc(v_i_109_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_i_109_);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_x_102_);
v_x_101_ = v_pre_108_;
v_x_102_ = v___x_111_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop___boxed(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_x_113_, v_x_114_);
lean_dec(v_x_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey(lean_object* v_n_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_box(0);
v___x_118_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_n_116_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(lean_object* v_n_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_119_);
lean_dec(v_n_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(lean_object* v_t_121_, lean_object* v_k_122_){
_start:
{
if (lean_obj_tag(v_t_121_) == 0)
{
lean_object* v_k_123_; lean_object* v_v_124_; lean_object* v_l_125_; lean_object* v_r_126_; uint8_t v___x_127_; 
v_k_123_ = lean_ctor_get(v_t_121_, 1);
v_v_124_ = lean_ctor_get(v_t_121_, 2);
v_l_125_ = lean_ctor_get(v_t_121_, 3);
v_r_126_ = lean_ctor_get(v_t_121_, 4);
v___x_127_ = l_Lean_NamePart_cmp(v_k_122_, v_k_123_);
switch(v___x_127_)
{
case 0:
{
v_t_121_ = v_l_125_;
goto _start;
}
case 1:
{
lean_object* v___x_129_; 
lean_inc(v_v_124_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_v_124_);
return v___x_129_;
}
default: 
{
v_t_121_ = v_r_126_;
goto _start;
}
}
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_132_, v_k_133_);
lean_dec_ref(v_k_133_);
lean_dec(v_t_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(1);
v___x_137_ = lean_panic_fn_borrowed(v___x_136_, v_msg_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_142_ = lean_unsigned_to_nat(35u);
v___x_143_ = lean_unsigned_to_nat(182u);
v___x_144_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_145_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_146_ = l_mkPanicMessageWithDecl(v___x_145_, v___x_144_, v___x_143_, v___x_142_, v___x_141_);
return v___x_146_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_148_ = lean_unsigned_to_nat(21u);
v___x_149_ = lean_unsigned_to_nat(183u);
v___x_150_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_151_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_152_ = l_mkPanicMessageWithDecl(v___x_151_, v___x_150_, v___x_149_, v___x_148_, v___x_147_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_156_ = lean_unsigned_to_nat(35u);
v___x_157_ = lean_unsigned_to_nat(276u);
v___x_158_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_159_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_160_ = l_mkPanicMessageWithDecl(v___x_159_, v___x_158_, v___x_157_, v___x_156_, v___x_155_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_161_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_162_ = lean_unsigned_to_nat(21u);
v___x_163_ = lean_unsigned_to_nat(277u);
v___x_164_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_166_ = l_mkPanicMessageWithDecl(v___x_165_, v___x_164_, v___x_163_, v___x_162_, v___x_161_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(lean_object* v_k_167_, lean_object* v_v_168_, lean_object* v_t_169_){
_start:
{
if (lean_obj_tag(v_t_169_) == 0)
{
lean_object* v_size_170_; lean_object* v_k_171_; lean_object* v_v_172_; lean_object* v_l_173_; lean_object* v_r_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_530_; 
v_size_170_ = lean_ctor_get(v_t_169_, 0);
v_k_171_ = lean_ctor_get(v_t_169_, 1);
v_v_172_ = lean_ctor_get(v_t_169_, 2);
v_l_173_ = lean_ctor_get(v_t_169_, 3);
v_r_174_ = lean_ctor_get(v_t_169_, 4);
v_isSharedCheck_530_ = !lean_is_exclusive(v_t_169_);
if (v_isSharedCheck_530_ == 0)
{
v___x_176_ = v_t_169_;
v_isShared_177_ = v_isSharedCheck_530_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_r_174_);
lean_inc(v_l_173_);
lean_inc(v_v_172_);
lean_inc(v_k_171_);
lean_inc(v_size_170_);
lean_dec(v_t_169_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_530_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
uint8_t v___x_178_; 
v___x_178_ = l_Lean_NamePart_cmp(v_k_167_, v_k_171_);
switch(v___x_178_)
{
case 0:
{
lean_object* v___x_179_; 
lean_dec(v_size_170_);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_167_, v_v_168_, v_l_173_);
if (lean_obj_tag(v_r_174_) == 0)
{
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_size_180_; lean_object* v_size_181_; lean_object* v_k_182_; lean_object* v_v_183_; lean_object* v_l_184_; lean_object* v_r_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v_size_180_ = lean_ctor_get(v_r_174_, 0);
v_size_181_ = lean_ctor_get(v___x_179_, 0);
v_k_182_ = lean_ctor_get(v___x_179_, 1);
v_v_183_ = lean_ctor_get(v___x_179_, 2);
v_l_184_ = lean_ctor_get(v___x_179_, 3);
v_r_185_ = lean_ctor_get(v___x_179_, 4);
lean_inc(v_r_185_);
v___x_186_ = lean_unsigned_to_nat(3u);
v___x_187_ = lean_nat_mul(v___x_186_, v_size_180_);
v___x_188_ = lean_nat_dec_lt(v___x_187_, v_size_181_);
lean_dec(v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec(v_r_185_);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_add(v___x_189_, v_size_181_);
v___x_191_ = lean_nat_add(v___x_190_, v_size_180_);
lean_dec(v___x_190_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 3, v___x_179_);
lean_ctor_set(v___x_176_, 0, v___x_191_);
v___x_193_ = v___x_176_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v_r_174_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_266_; 
lean_inc(v_l_184_);
lean_inc(v_v_183_);
lean_inc(v_k_182_);
lean_inc(v_size_181_);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_267_ = lean_ctor_get(v___x_179_, 4);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v___x_179_, 3);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v___x_179_, 2);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v___x_179_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v___x_179_, 0);
lean_dec(v_unused_271_);
v___x_196_ = v___x_179_;
v_isShared_197_ = v_isSharedCheck_266_;
goto v_resetjp_195_;
}
else
{
lean_dec(v___x_179_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_266_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
if (lean_obj_tag(v_l_184_) == 0)
{
if (lean_obj_tag(v_r_185_) == 0)
{
lean_object* v_size_198_; lean_object* v_size_199_; lean_object* v_k_200_; lean_object* v_v_201_; lean_object* v_l_202_; lean_object* v_r_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_size_198_ = lean_ctor_get(v_l_184_, 0);
v_size_199_ = lean_ctor_get(v_r_185_, 0);
v_k_200_ = lean_ctor_get(v_r_185_, 1);
v_v_201_ = lean_ctor_get(v_r_185_, 2);
v_l_202_ = lean_ctor_get(v_r_185_, 3);
v_r_203_ = lean_ctor_get(v_r_185_, 4);
v___x_204_ = lean_unsigned_to_nat(2u);
v___x_205_ = lean_nat_mul(v___x_204_, v_size_198_);
v___x_206_ = lean_nat_dec_lt(v_size_199_, v___x_205_);
lean_dec(v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_236_; 
lean_inc(v_r_203_);
lean_inc(v_l_202_);
lean_inc(v_v_201_);
lean_inc(v_k_200_);
v_isSharedCheck_236_ = !lean_is_exclusive(v_r_185_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; lean_object* v_unused_240_; lean_object* v_unused_241_; 
v_unused_237_ = lean_ctor_get(v_r_185_, 4);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_r_185_, 3);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_r_185_, 2);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_r_185_, 1);
lean_dec(v_unused_240_);
v_unused_241_ = lean_ctor_get(v_r_185_, 0);
lean_dec(v_unused_241_);
v___x_208_ = v_r_185_;
v_isShared_209_ = v_isSharedCheck_236_;
goto v_resetjp_207_;
}
else
{
lean_dec(v_r_185_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_236_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___x_224_; lean_object* v___y_226_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v___x_210_, v_size_181_);
lean_dec(v_size_181_);
v___x_212_ = lean_nat_add(v___x_211_, v_size_180_);
lean_dec(v___x_211_);
v___x_224_ = lean_nat_add(v___x_210_, v_size_198_);
if (lean_obj_tag(v_l_202_) == 0)
{
lean_object* v_size_234_; 
v_size_234_ = lean_ctor_get(v_l_202_, 0);
lean_inc(v_size_234_);
v___y_226_ = v_size_234_;
goto v___jp_225_;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___y_226_ = v___x_235_;
goto v___jp_225_;
}
v___jp_213_:
{
lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_217_ = lean_nat_add(v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec(v___y_215_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 4, v_r_174_);
lean_ctor_set(v___x_208_, 3, v_r_203_);
lean_ctor_set(v___x_208_, 2, v_v_172_);
lean_ctor_set(v___x_208_, 1, v_k_171_);
lean_ctor_set(v___x_208_, 0, v___x_217_);
v___x_219_ = v___x_208_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v_r_203_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v_r_174_);
v___x_219_ = v_reuseFailAlloc_223_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 4, v___x_219_);
lean_ctor_set(v___x_196_, 3, v___y_214_);
lean_ctor_set(v___x_196_, 2, v_v_201_);
lean_ctor_set(v___x_196_, 1, v_k_200_);
lean_ctor_set(v___x_196_, 0, v___x_212_);
v___x_221_ = v___x_196_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_k_200_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_v_201_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v___y_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_nat_add(v___x_224_, v___y_226_);
lean_dec(v___y_226_);
lean_dec(v___x_224_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v_l_202_);
lean_ctor_set(v___x_176_, 3, v_l_184_);
lean_ctor_set(v___x_176_, 2, v_v_183_);
lean_ctor_set(v___x_176_, 1, v_k_182_);
lean_ctor_set(v___x_176_, 0, v___x_227_);
v___x_229_ = v___x_176_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_k_182_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_v_183_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_l_184_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_l_202_);
v___x_229_ = v_reuseFailAlloc_233_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_nat_add(v___x_210_, v_size_180_);
if (lean_obj_tag(v_r_203_) == 0)
{
lean_object* v_size_231_; 
v_size_231_ = lean_ctor_get(v_r_203_, 0);
lean_inc(v_size_231_);
v___y_214_ = v___x_229_;
v___y_215_ = v___x_230_;
v___y_216_ = v_size_231_;
goto v___jp_213_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___y_214_ = v___x_229_;
v___y_215_ = v___x_230_;
v___y_216_ = v___x_232_;
goto v___jp_213_;
}
}
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
lean_del_object(v___x_176_);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v___x_242_, v_size_181_);
lean_dec(v_size_181_);
v___x_244_ = lean_nat_add(v___x_243_, v_size_180_);
lean_dec(v___x_243_);
v___x_245_ = lean_nat_add(v___x_242_, v_size_180_);
v___x_246_ = lean_nat_add(v___x_245_, v_size_199_);
lean_dec(v___x_245_);
lean_inc_ref(v_r_174_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 4, v_r_174_);
lean_ctor_set(v___x_196_, 3, v_r_185_);
lean_ctor_set(v___x_196_, 2, v_v_172_);
lean_ctor_set(v___x_196_, 1, v_k_171_);
lean_ctor_set(v___x_196_, 0, v___x_246_);
v___x_248_ = v___x_196_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_r_185_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_r_174_);
v___x_248_ = v_reuseFailAlloc_261_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_isSharedCheck_255_ = !lean_is_exclusive(v_r_174_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; lean_object* v_unused_258_; lean_object* v_unused_259_; lean_object* v_unused_260_; 
v_unused_256_ = lean_ctor_get(v_r_174_, 4);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_r_174_, 3);
lean_dec(v_unused_257_);
v_unused_258_ = lean_ctor_get(v_r_174_, 2);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_r_174_, 1);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_r_174_, 0);
lean_dec(v_unused_260_);
v___x_250_ = v_r_174_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_dec(v_r_174_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 4, v___x_248_);
lean_ctor_set(v___x_250_, 3, v_l_184_);
lean_ctor_set(v___x_250_, 2, v_v_183_);
lean_ctor_set(v___x_250_, 1, v_k_182_);
lean_ctor_set(v___x_250_, 0, v___x_244_);
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_k_182_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_v_183_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v_l_184_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v___x_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref_known(v_l_184_, 5);
lean_del_object(v___x_196_);
lean_dec(v_v_183_);
lean_dec(v_k_182_);
lean_dec(v_size_181_);
lean_dec_ref_known(v_r_174_, 5);
lean_del_object(v___x_176_);
lean_dec(v_v_172_);
lean_dec(v_k_171_);
v___x_262_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3);
v___x_263_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_262_);
return v___x_263_;
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_del_object(v___x_196_);
lean_dec(v_r_185_);
lean_dec(v_v_183_);
lean_dec(v_k_182_);
lean_dec(v_size_181_);
lean_dec_ref_known(v_r_174_, 5);
lean_del_object(v___x_176_);
lean_dec(v_v_172_);
lean_dec(v_k_171_);
v___x_264_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4);
v___x_265_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_264_);
return v___x_265_;
}
}
}
}
else
{
lean_object* v_size_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v_size_272_ = lean_ctor_get(v_r_174_, 0);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v___x_273_, v_size_272_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 3, v___x_179_);
lean_ctor_set(v___x_176_, 0, v___x_274_);
v___x_276_ = v___x_176_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v_r_174_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_l_278_; 
v_l_278_ = lean_ctor_get(v___x_179_, 3);
if (lean_obj_tag(v_l_278_) == 0)
{
lean_object* v_r_279_; 
lean_inc_ref(v_l_278_);
v_r_279_ = lean_ctor_get(v___x_179_, 4);
lean_inc(v_r_279_);
if (lean_obj_tag(v_r_279_) == 0)
{
lean_object* v_size_280_; lean_object* v_k_281_; lean_object* v_v_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_296_; 
v_size_280_ = lean_ctor_get(v___x_179_, 0);
v_k_281_ = lean_ctor_get(v___x_179_, 1);
v_v_282_ = lean_ctor_get(v___x_179_, 2);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_297_ = lean_ctor_get(v___x_179_, 4);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v___x_179_, 3);
lean_dec(v_unused_298_);
v___x_284_ = v___x_179_;
v_isShared_285_ = v_isSharedCheck_296_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_v_282_);
lean_inc(v_k_281_);
lean_inc(v_size_280_);
lean_dec(v___x_179_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_296_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_size_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v_size_286_ = lean_ctor_get(v_r_279_, 0);
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v___x_287_, v_size_280_);
lean_dec(v_size_280_);
v___x_289_ = lean_nat_add(v___x_287_, v_size_286_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 4, v_r_174_);
lean_ctor_set(v___x_284_, 3, v_r_279_);
lean_ctor_set(v___x_284_, 2, v_v_172_);
lean_ctor_set(v___x_284_, 1, v_k_171_);
lean_ctor_set(v___x_284_, 0, v___x_289_);
v___x_291_ = v___x_284_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_r_279_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_r_174_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_291_);
lean_ctor_set(v___x_176_, 3, v_l_278_);
lean_ctor_set(v___x_176_, 2, v_v_282_);
lean_ctor_set(v___x_176_, 1, v_k_281_);
lean_ctor_set(v___x_176_, 0, v___x_288_);
v___x_293_ = v___x_176_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_k_281_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_v_282_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_l_278_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_k_299_; lean_object* v_v_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_312_; 
v_k_299_ = lean_ctor_get(v___x_179_, 1);
v_v_300_ = lean_ctor_get(v___x_179_, 2);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_313_ = lean_ctor_get(v___x_179_, 4);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v___x_179_, 3);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v___x_179_, 0);
lean_dec(v_unused_315_);
v___x_302_ = v___x_179_;
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_v_300_);
lean_inc(v_k_299_);
lean_dec(v___x_179_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_312_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(3u);
v___x_305_ = lean_unsigned_to_nat(1u);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v_r_279_);
lean_ctor_set(v___x_302_, 2, v_v_172_);
lean_ctor_set(v___x_302_, 1, v_k_171_);
lean_ctor_set(v___x_302_, 0, v___x_305_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_r_279_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_r_279_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_309_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_307_);
lean_ctor_set(v___x_176_, 3, v_l_278_);
lean_ctor_set(v___x_176_, 2, v_v_300_);
lean_ctor_set(v___x_176_, 1, v_k_299_);
lean_ctor_set(v___x_176_, 0, v___x_304_);
v___x_309_ = v___x_176_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_k_299_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_v_300_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v_l_278_);
lean_ctor_set(v_reuseFailAlloc_310_, 4, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
else
{
lean_object* v_r_316_; 
v_r_316_ = lean_ctor_get(v___x_179_, 4);
lean_inc(v_r_316_);
if (lean_obj_tag(v_r_316_) == 0)
{
lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_342_; 
lean_inc(v_l_278_);
v_k_317_ = lean_ctor_get(v___x_179_, 1);
v_v_318_ = lean_ctor_get(v___x_179_, 2);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_343_ = lean_ctor_get(v___x_179_, 4);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v___x_179_, 3);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v___x_179_, 0);
lean_dec(v_unused_345_);
v___x_320_ = v___x_179_;
v_isShared_321_ = v_isSharedCheck_342_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_v_318_);
lean_inc(v_k_317_);
lean_dec(v___x_179_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_342_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_k_322_; lean_object* v_v_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_338_; 
v_k_322_ = lean_ctor_get(v_r_316_, 1);
v_v_323_ = lean_ctor_get(v_r_316_, 2);
v_isSharedCheck_338_ = !lean_is_exclusive(v_r_316_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; lean_object* v_unused_341_; 
v_unused_339_ = lean_ctor_get(v_r_316_, 4);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_r_316_, 3);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_r_316_, 0);
lean_dec(v_unused_341_);
v___x_325_ = v_r_316_;
v_isShared_326_ = v_isSharedCheck_338_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_v_323_);
lean_inc(v_k_322_);
lean_dec(v_r_316_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_338_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(3u);
v___x_328_ = lean_unsigned_to_nat(1u);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 4, v_l_278_);
lean_ctor_set(v___x_325_, 3, v_l_278_);
lean_ctor_set(v___x_325_, 2, v_v_318_);
lean_ctor_set(v___x_325_, 1, v_k_317_);
lean_ctor_set(v___x_325_, 0, v___x_328_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_l_278_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_l_278_);
v___x_330_ = v_reuseFailAlloc_337_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v_l_278_);
lean_ctor_set(v___x_320_, 2, v_v_172_);
lean_ctor_set(v___x_320_, 1, v_k_171_);
lean_ctor_set(v___x_320_, 0, v___x_328_);
v___x_332_ = v___x_320_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_l_278_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_l_278_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_332_);
lean_ctor_set(v___x_176_, 3, v___x_330_);
lean_ctor_set(v___x_176_, 2, v_v_323_);
lean_ctor_set(v___x_176_, 1, v_k_322_);
lean_ctor_set(v___x_176_, 0, v___x_327_);
v___x_334_ = v___x_176_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_k_322_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_v_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_unsigned_to_nat(2u);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v_r_316_);
lean_ctor_set(v___x_176_, 3, v___x_179_);
lean_ctor_set(v___x_176_, 0, v___x_346_);
v___x_348_ = v___x_176_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_r_316_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_unsigned_to_nat(1u);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_179_);
lean_ctor_set(v___x_176_, 3, v___x_179_);
lean_ctor_set(v___x_176_, 0, v___x_350_);
v___x_352_ = v___x_176_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v___x_179_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
case 1:
{
lean_object* v___x_355_; 
lean_dec(v_v_172_);
lean_dec(v_k_171_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 2, v_v_168_);
lean_ctor_set(v___x_176_, 1, v_k_167_);
v___x_355_ = v___x_176_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_size_170_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_k_167_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_v_168_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_l_173_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_r_174_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
default: 
{
lean_object* v___x_357_; 
lean_dec(v_size_170_);
v___x_357_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_167_, v_v_168_, v_r_174_);
if (lean_obj_tag(v_l_173_) == 0)
{
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_size_358_; lean_object* v_size_359_; lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v_l_362_; lean_object* v_r_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_size_358_ = lean_ctor_get(v_l_173_, 0);
v_size_359_ = lean_ctor_get(v___x_357_, 0);
v_k_360_ = lean_ctor_get(v___x_357_, 1);
v_v_361_ = lean_ctor_get(v___x_357_, 2);
v_l_362_ = lean_ctor_get(v___x_357_, 3);
lean_inc(v_l_362_);
v_r_363_ = lean_ctor_get(v___x_357_, 4);
v___x_364_ = lean_unsigned_to_nat(3u);
v___x_365_ = lean_nat_mul(v___x_364_, v_size_358_);
v___x_366_ = lean_nat_dec_lt(v___x_365_, v_size_359_);
lean_dec(v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec(v_l_362_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_add(v___x_367_, v_size_358_);
v___x_369_ = lean_nat_add(v___x_368_, v_size_359_);
lean_dec(v___x_368_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_357_);
lean_ctor_set(v___x_176_, 0, v___x_369_);
v___x_371_ = v___x_176_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_l_173_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_357_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_442_; 
lean_inc(v_r_363_);
lean_inc(v_v_361_);
lean_inc(v_k_360_);
lean_inc(v_size_359_);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; 
v_unused_443_ = lean_ctor_get(v___x_357_, 4);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v___x_357_, 3);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v___x_357_, 2);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v___x_357_, 1);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_447_);
v___x_374_ = v___x_357_;
v_isShared_375_ = v_isSharedCheck_442_;
goto v_resetjp_373_;
}
else
{
lean_dec(v___x_357_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_442_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
if (lean_obj_tag(v_l_362_) == 0)
{
if (lean_obj_tag(v_r_363_) == 0)
{
lean_object* v_size_376_; lean_object* v_k_377_; lean_object* v_v_378_; lean_object* v_l_379_; lean_object* v_r_380_; lean_object* v_size_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_size_376_ = lean_ctor_get(v_l_362_, 0);
v_k_377_ = lean_ctor_get(v_l_362_, 1);
v_v_378_ = lean_ctor_get(v_l_362_, 2);
v_l_379_ = lean_ctor_get(v_l_362_, 3);
v_r_380_ = lean_ctor_get(v_l_362_, 4);
v_size_381_ = lean_ctor_get(v_r_363_, 0);
v___x_382_ = lean_unsigned_to_nat(2u);
v___x_383_ = lean_nat_mul(v___x_382_, v_size_381_);
v___x_384_ = lean_nat_dec_lt(v_size_376_, v___x_383_);
lean_dec(v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_413_; 
lean_inc(v_r_380_);
lean_inc(v_l_379_);
lean_inc(v_v_378_);
lean_inc(v_k_377_);
v_isSharedCheck_413_ = !lean_is_exclusive(v_l_362_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; lean_object* v_unused_417_; lean_object* v_unused_418_; 
v_unused_414_ = lean_ctor_get(v_l_362_, 4);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_l_362_, 3);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_l_362_, 2);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_l_362_, 1);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_l_362_, 0);
lean_dec(v_unused_418_);
v___x_386_ = v_l_362_;
v_isShared_387_ = v_isSharedCheck_413_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_l_362_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_413_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_403_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_nat_add(v___x_388_, v_size_358_);
v___x_390_ = lean_nat_add(v___x_389_, v_size_359_);
lean_dec(v_size_359_);
if (lean_obj_tag(v_l_379_) == 0)
{
lean_object* v_size_411_; 
v_size_411_ = lean_ctor_get(v_l_379_, 0);
lean_inc(v_size_411_);
v___y_403_ = v_size_411_;
goto v___jp_402_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___y_403_ = v___x_412_;
goto v___jp_402_;
}
v___jp_391_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_nat_add(v___y_392_, v___y_394_);
lean_dec(v___y_394_);
lean_dec(v___y_392_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v_r_363_);
lean_ctor_set(v___x_386_, 3, v_r_380_);
lean_ctor_set(v___x_386_, 2, v_v_361_);
lean_ctor_set(v___x_386_, 1, v_k_360_);
lean_ctor_set(v___x_386_, 0, v___x_395_);
v___x_397_ = v___x_386_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_r_380_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v_r_363_);
v___x_397_ = v_reuseFailAlloc_401_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_399_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 4, v___x_397_);
lean_ctor_set(v___x_374_, 3, v___y_393_);
lean_ctor_set(v___x_374_, 2, v_v_378_);
lean_ctor_set(v___x_374_, 1, v_k_377_);
lean_ctor_set(v___x_374_, 0, v___x_390_);
v___x_399_ = v___x_374_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_377_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_378_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v___y_393_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_nat_add(v___x_389_, v___y_403_);
lean_dec(v___y_403_);
lean_dec(v___x_389_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v_l_379_);
lean_ctor_set(v___x_176_, 0, v___x_404_);
v___x_406_ = v___x_176_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_l_173_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_l_379_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_nat_add(v___x_388_, v_size_381_);
if (lean_obj_tag(v_r_380_) == 0)
{
lean_object* v_size_408_; 
v_size_408_ = lean_ctor_get(v_r_380_, 0);
lean_inc(v_size_408_);
v___y_392_ = v___x_407_;
v___y_393_ = v___x_406_;
v___y_394_ = v_size_408_;
goto v___jp_391_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___y_392_ = v___x_407_;
v___y_393_ = v___x_406_;
v___y_394_ = v___x_409_;
goto v___jp_391_;
}
}
}
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_del_object(v___x_176_);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_add(v___x_419_, v_size_358_);
v___x_421_ = lean_nat_add(v___x_420_, v_size_359_);
lean_dec(v_size_359_);
v___x_422_ = lean_nat_add(v___x_420_, v_size_376_);
lean_dec(v___x_420_);
lean_inc_ref(v_l_173_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 4, v_l_362_);
lean_ctor_set(v___x_374_, 3, v_l_173_);
lean_ctor_set(v___x_374_, 2, v_v_172_);
lean_ctor_set(v___x_374_, 1, v_k_171_);
lean_ctor_set(v___x_374_, 0, v___x_422_);
v___x_424_ = v___x_374_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_l_173_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_l_362_);
v___x_424_ = v_reuseFailAlloc_437_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_isSharedCheck_431_ = !lean_is_exclusive(v_l_173_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; 
v_unused_432_ = lean_ctor_get(v_l_173_, 4);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_l_173_, 3);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_l_173_, 2);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_l_173_, 1);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_l_173_, 0);
lean_dec(v_unused_436_);
v___x_426_ = v_l_173_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_dec(v_l_173_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 4, v_r_363_);
lean_ctor_set(v___x_426_, 3, v___x_424_);
lean_ctor_set(v___x_426_, 2, v_v_361_);
lean_ctor_set(v___x_426_, 1, v_k_360_);
lean_ctor_set(v___x_426_, 0, v___x_421_);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_r_363_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_dec_ref_known(v_l_362_, 5);
lean_del_object(v___x_374_);
lean_dec(v_v_361_);
lean_dec(v_k_360_);
lean_dec(v_size_359_);
lean_dec_ref_known(v_l_173_, 5);
lean_del_object(v___x_176_);
lean_dec(v_v_172_);
lean_dec(v_k_171_);
v___x_438_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7);
v___x_439_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_438_);
return v___x_439_;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_del_object(v___x_374_);
lean_dec(v_r_363_);
lean_dec(v_v_361_);
lean_dec(v_k_360_);
lean_dec(v_size_359_);
lean_dec_ref_known(v_l_173_, 5);
lean_del_object(v___x_176_);
lean_dec(v_v_172_);
lean_dec(v_k_171_);
v___x_440_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8);
v___x_441_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_440_);
return v___x_441_;
}
}
}
}
else
{
lean_object* v_size_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v_size_448_ = lean_ctor_get(v_l_173_, 0);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v___x_449_, v_size_448_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_357_);
lean_ctor_set(v___x_176_, 0, v___x_450_);
v___x_452_ = v___x_176_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_l_173_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v___x_357_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_l_454_; 
v_l_454_ = lean_ctor_get(v___x_357_, 3);
lean_inc(v_l_454_);
if (lean_obj_tag(v_l_454_) == 0)
{
lean_object* v_r_455_; 
v_r_455_ = lean_ctor_get(v___x_357_, 4);
lean_inc(v_r_455_);
if (lean_obj_tag(v_r_455_) == 0)
{
lean_object* v_size_456_; lean_object* v_k_457_; lean_object* v_v_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_472_; 
v_size_456_ = lean_ctor_get(v___x_357_, 0);
v_k_457_ = lean_ctor_get(v___x_357_, 1);
v_v_458_ = lean_ctor_get(v___x_357_, 2);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_473_ = lean_ctor_get(v___x_357_, 4);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v___x_357_, 3);
lean_dec(v_unused_474_);
v___x_460_ = v___x_357_;
v_isShared_461_ = v_isSharedCheck_472_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_v_458_);
lean_inc(v_k_457_);
lean_inc(v_size_456_);
lean_dec(v___x_357_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_472_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_size_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v_size_462_ = lean_ctor_get(v_l_454_, 0);
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_add(v___x_463_, v_size_456_);
lean_dec(v_size_456_);
v___x_465_ = lean_nat_add(v___x_463_, v_size_462_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 4, v_l_454_);
lean_ctor_set(v___x_460_, 3, v_l_173_);
lean_ctor_set(v___x_460_, 2, v_v_172_);
lean_ctor_set(v___x_460_, 1, v_k_171_);
lean_ctor_set(v___x_460_, 0, v___x_465_);
v___x_467_ = v___x_460_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_l_173_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_l_454_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_469_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v_r_455_);
lean_ctor_set(v___x_176_, 3, v___x_467_);
lean_ctor_set(v___x_176_, 2, v_v_458_);
lean_ctor_set(v___x_176_, 1, v_k_457_);
lean_ctor_set(v___x_176_, 0, v___x_464_);
v___x_469_ = v___x_176_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_k_457_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_v_458_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_r_455_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_k_475_; lean_object* v_v_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_500_; 
v_k_475_ = lean_ctor_get(v___x_357_, 1);
v_v_476_ = lean_ctor_get(v___x_357_, 2);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_501_ = lean_ctor_get(v___x_357_, 4);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v___x_357_, 3);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_503_);
v___x_478_ = v___x_357_;
v_isShared_479_ = v_isSharedCheck_500_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_v_476_);
lean_inc(v_k_475_);
lean_dec(v___x_357_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_500_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_k_480_; lean_object* v_v_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_496_; 
v_k_480_ = lean_ctor_get(v_l_454_, 1);
v_v_481_ = lean_ctor_get(v_l_454_, 2);
v_isSharedCheck_496_ = !lean_is_exclusive(v_l_454_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_497_ = lean_ctor_get(v_l_454_, 4);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_l_454_, 3);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_l_454_, 0);
lean_dec(v_unused_499_);
v___x_483_ = v_l_454_;
v_isShared_484_ = v_isSharedCheck_496_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_v_481_);
lean_inc(v_k_480_);
lean_dec(v_l_454_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_496_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = lean_unsigned_to_nat(1u);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 4, v_r_455_);
lean_ctor_set(v___x_483_, 3, v_r_455_);
lean_ctor_set(v___x_483_, 2, v_v_172_);
lean_ctor_set(v___x_483_, 1, v_k_171_);
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_r_455_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_r_455_);
v___x_488_ = v_reuseFailAlloc_495_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 3, v_r_455_);
lean_ctor_set(v___x_478_, 0, v___x_486_);
v___x_490_ = v___x_478_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_k_475_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_v_476_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_r_455_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_r_455_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_490_);
lean_ctor_set(v___x_176_, 3, v___x_488_);
lean_ctor_set(v___x_176_, 2, v_v_481_);
lean_ctor_set(v___x_176_, 1, v_k_480_);
lean_ctor_set(v___x_176_, 0, v___x_485_);
v___x_492_ = v___x_176_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_k_480_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_v_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v___x_490_);
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
}
else
{
lean_object* v_r_504_; 
v_r_504_ = lean_ctor_get(v___x_357_, 4);
lean_inc(v_r_504_);
if (lean_obj_tag(v_r_504_) == 0)
{
lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_518_; 
v_k_505_ = lean_ctor_get(v___x_357_, 1);
v_v_506_ = lean_ctor_get(v___x_357_, 2);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; lean_object* v_unused_520_; lean_object* v_unused_521_; 
v_unused_519_ = lean_ctor_get(v___x_357_, 4);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v___x_357_, 3);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_521_);
v___x_508_ = v___x_357_;
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_v_506_);
lean_inc(v_k_505_);
lean_dec(v___x_357_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_unsigned_to_nat(3u);
v___x_511_ = lean_unsigned_to_nat(1u);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v_l_454_);
lean_ctor_set(v___x_508_, 2, v_v_172_);
lean_ctor_set(v___x_508_, 1, v_k_171_);
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_l_454_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_l_454_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v_r_504_);
lean_ctor_set(v___x_176_, 3, v___x_513_);
lean_ctor_set(v___x_176_, 2, v_v_506_);
lean_ctor_set(v___x_176_, 1, v_k_505_);
lean_ctor_set(v___x_176_, 0, v___x_510_);
v___x_515_ = v___x_176_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_k_505_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_v_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 4, v_r_504_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_unsigned_to_nat(2u);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_357_);
lean_ctor_set(v___x_176_, 3, v_r_504_);
lean_ctor_set(v___x_176_, 0, v___x_522_);
v___x_524_ = v___x_176_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_r_504_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v___x_357_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(1u);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 4, v___x_357_);
lean_ctor_set(v___x_176_, 3, v___x_357_);
lean_ctor_set(v___x_176_, 0, v___x_526_);
v___x_528_ = v___x_176_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_k_171_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_v_172_);
lean_ctor_set(v_reuseFailAlloc_529_, 3, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_529_, 4, v___x_357_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_k_167_);
lean_ctor_set(v___x_532_, 2, v_v_168_);
lean_ctor_set(v___x_532_, 3, v_t_169_);
lean_ctor_set(v___x_532_, 4, v_t_169_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(lean_object* v_val_533_, lean_object* v_k_534_){
_start:
{
if (lean_obj_tag(v_k_534_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_val_533_);
v___x_536_ = lean_box(1);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
else
{
lean_object* v_head_538_; lean_object* v_tail_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_550_; 
v_head_538_ = lean_ctor_get(v_k_534_, 0);
v_tail_539_ = lean_ctor_get(v_k_534_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_k_534_);
if (v_isSharedCheck_550_ == 0)
{
v___x_541_ = v_k_534_;
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_tail_539_);
lean_inc(v_head_538_);
lean_dec(v_k_534_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_t_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v_t_543_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_533_, v_tail_539_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_box(1);
v___x_546_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_538_, v_t_543_, v___x_545_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 0);
lean_ctor_set(v___x_541_, 1, v___x_546_);
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_548_ = v___x_541_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(lean_object* v_val_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_562_; 
v_a_554_ = lean_ctor_get(v_x_552_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_x_552_, 0);
lean_dec(v_unused_563_);
v___x_556_ = v_x_552_;
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v_x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_562_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v_val_551_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_a_554_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_581_; 
v_a_564_ = lean_ctor_get(v_x_552_, 0);
v_a_565_ = lean_ctor_get(v_x_552_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_581_ == 0)
{
v___x_567_ = v_x_552_;
v_isShared_568_ = v_isSharedCheck_581_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_inc(v_a_564_);
lean_dec(v_x_552_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_581_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_head_569_; lean_object* v_tail_570_; lean_object* v___y_572_; lean_object* v___x_577_; 
v_head_569_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_head_569_);
v_tail_570_ = lean_ctor_get(v_x_553_, 1);
lean_inc(v_tail_570_);
lean_dec_ref_known(v_x_553_, 2);
v___x_577_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_565_, v_head_569_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_551_, v_tail_570_);
v___y_572_ = v___x_578_;
goto v___jp_571_;
}
else
{
lean_object* v_val_579_; lean_object* v___x_580_; 
v_val_579_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_577_, 1);
v___x_580_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_551_, v_val_579_, v_tail_570_);
v___y_572_ = v___x_580_;
goto v___jp_571_;
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_569_, v___y_572_, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_573_);
v___x_575_ = v___x_567_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_564_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg(lean_object* v_t_582_, lean_object* v_n_583_, lean_object* v_b_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_583_);
v___x_586_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_b_584_, v_t_582_, v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg___boxed(lean_object* v_t_587_, lean_object* v_n_588_, lean_object* v_b_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_NameTrie_insert___redArg(v_t_587_, v_n_588_, v_b_589_);
lean_dec(v_n_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert(lean_object* v_00_u03b2_591_, lean_object* v_t_592_, lean_object* v_n_593_, lean_object* v_b_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_NameTrie_insert___redArg(v_t_592_, v_n_593_, v_b_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___boxed(lean_object* v_00_u03b2_596_, lean_object* v_t_597_, lean_object* v_n_598_, lean_object* v_b_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_NameTrie_insert(v_00_u03b2_596_, v_t_597_, v_n_598_, v_b_599_);
lean_dec(v_n_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(lean_object* v_00_u03b2_601_, lean_object* v_val_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_602_, v_x_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_606_, lean_object* v_msg_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v_msg_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(lean_object* v_00_u03b2_609_, lean_object* v_k_610_, lean_object* v_v_611_, lean_object* v_t_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_610_, v_v_611_, v_t_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(lean_object* v_00_u03b4_614_, lean_object* v_t_615_, lean_object* v_k_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_615_, v_k_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b4_618_, lean_object* v_t_619_, lean_object* v_k_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(v_00_u03b4_618_, v_t_619_, v_k_620_);
lean_dec_ref(v_k_620_);
lean_dec(v_t_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(lean_object* v_00_u03b2_622_, lean_object* v_val_623_, lean_object* v_k_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_623_, v_k_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_NameTrie_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_PrefixTreeNode_empty___redArg();
return v___x_626_;
}
}
lean_object* l_Lean_NameTrie_empty___redArg(){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_628_;
}
}
LEAN_EXPORT void l_Lean_NameTrie_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_629_;
v_res_629_ = l_Lean_NameTrie_empty___redArg();
stack->m_obj
 = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg___boxed(lean_object* v___dummy_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_NameTrie_empty___redArg();
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty(lean_object* v_00_u03b2_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_633_;
}
}
lean_object* l_Lean_instInhabitedNameTrie___redArg(){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_635_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedNameTrie___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_636_;
v_res_636_ = l_Lean_instInhabitedNameTrie___redArg();
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg___boxed(lean_object* v___dummy_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_instInhabitedNameTrie___redArg();
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie(lean_object* v_00_u03b2_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_640_;
}
}
lean_object* l_Lean_instEmptyCollectionNameTrie___redArg(){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_642_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionNameTrie___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_643_;
v_res_643_ = l_Lean_instEmptyCollectionNameTrie___redArg();
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg___boxed(lean_object* v___dummy_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_instEmptyCollectionNameTrie___redArg();
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie(lean_object* v_00_u03b2_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v_a_650_; 
v_a_650_ = lean_ctor_get(v_x_648_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v_x_648_);
return v_a_650_;
}
else
{
lean_object* v_a_651_; lean_object* v_head_652_; lean_object* v_tail_653_; lean_object* v___x_654_; 
v_a_651_ = lean_ctor_get(v_x_648_, 1);
lean_inc(v_a_651_);
lean_dec_ref(v_x_648_);
v_head_652_ = lean_ctor_get(v_x_649_, 0);
v_tail_653_ = lean_ctor_get(v_x_649_, 1);
v___x_654_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_651_, v_head_652_);
lean_dec(v_a_651_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v_val_656_; 
v_val_656_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v___x_654_, 1);
v_x_648_ = v_val_656_;
v_x_649_ = v_tail_653_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_658_, v_x_659_);
lean_dec(v_x_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object* v_t_661_, lean_object* v_k_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_662_);
v___x_664_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_t_661_, v___x_663_);
lean_dec(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg___boxed(lean_object* v_t_665_, lean_object* v_k_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_NameTrie_find_x3f___redArg(v_t_665_, v_k_666_);
lean_dec(v_k_666_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f(lean_object* v_00_u03b2_668_, lean_object* v_t_669_, lean_object* v_k_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_NameTrie_find_x3f___redArg(v_t_669_, v_k_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___boxed(lean_object* v_00_u03b2_672_, lean_object* v_t_673_, lean_object* v_k_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_NameTrie_find_x3f(v_00_u03b2_672_, v_t_673_, v_k_674_);
lean_dec(v_k_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(v_00_u03b2_680_, v_x_681_, v_x_682_);
lean_dec(v_x_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg(lean_object* v_t_685_, lean_object* v_k_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_688_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_686_);
v___x_689_ = lean_box(0);
v___x_690_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_687_, v___x_689_, v_t_685_, v___x_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(lean_object* v_t_691_, lean_object* v_k_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_NameTrie_findLongestPrefix_x3f___redArg(v_t_691_, v_k_692_);
lean_dec(v_k_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f(lean_object* v_00_u03b2_694_, lean_object* v_t_695_, lean_object* v_k_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_698_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_696_);
v___x_699_ = lean_box(0);
v___x_700_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_697_, v___x_699_, v_t_695_, v___x_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___boxed(lean_object* v_00_u03b2_701_, lean_object* v_t_702_, lean_object* v_k_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_NameTrie_findLongestPrefix_x3f(v_00_u03b2_701_, v_t_702_, v_k_703_);
lean_dec(v_k_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg(lean_object* v_inst_705_, lean_object* v_t_706_, lean_object* v_k_707_, lean_object* v_init_708_, lean_object* v_f_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_711_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_707_);
lean_inc(v_init_708_);
v___x_712_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_705_, v___x_710_, v_init_708_, v_f_709_, v___x_711_, v_t_706_, v_init_708_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg___boxed(lean_object* v_inst_713_, lean_object* v_t_714_, lean_object* v_k_715_, lean_object* v_init_716_, lean_object* v_f_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_NameTrie_foldMatchingM___redArg(v_inst_713_, v_t_714_, v_k_715_, v_init_716_, v_f_717_);
lean_dec(v_k_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM(lean_object* v_m_719_, lean_object* v_00_u03b2_720_, lean_object* v_00_u03c3_721_, lean_object* v_inst_722_, lean_object* v_t_723_, lean_object* v_k_724_, lean_object* v_init_725_, lean_object* v_f_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_728_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_724_);
lean_inc(v_init_725_);
v___x_729_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_722_, v___x_727_, v_init_725_, v_f_726_, v___x_728_, v_t_723_, v_init_725_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___boxed(lean_object* v_m_730_, lean_object* v_00_u03b2_731_, lean_object* v_00_u03c3_732_, lean_object* v_inst_733_, lean_object* v_t_734_, lean_object* v_k_735_, lean_object* v_init_736_, lean_object* v_f_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_NameTrie_foldMatchingM(v_m_730_, v_00_u03b2_731_, v_00_u03c3_732_, v_inst_733_, v_t_734_, v_k_735_, v_init_736_, v_f_737_);
lean_dec(v_k_735_);
return v_res_738_;
}
}
static lean_object* _init_l_Lean_NameTrie_foldM___redArg___closed__0(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_box(0);
v___x_740_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM___redArg(lean_object* v_inst_741_, lean_object* v_t_742_, lean_object* v_init_743_, lean_object* v_f_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_746_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_743_);
v___x_747_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_741_, v___x_745_, v_init_743_, v_f_744_, v___x_746_, v_t_742_, v_init_743_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM(lean_object* v_m_748_, lean_object* v_00_u03b2_749_, lean_object* v_00_u03c3_750_, lean_object* v_inst_751_, lean_object* v_t_752_, lean_object* v_init_753_, lean_object* v_f_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_756_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_753_);
v___x_757_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_751_, v___x_755_, v_init_753_, v_f_754_, v___x_756_, v_t_752_, v_init_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___lam__0(lean_object* v_f_758_, lean_object* v_b_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_apply_1(v_f_758_, v_b_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg(lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_k_764_, lean_object* v_f_765_){
_start:
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___f_766_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_766_, 0, v_f_765_);
v___x_767_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_768_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_764_);
v___x_769_ = lean_box(0);
v___x_770_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_762_, v___x_767_, v___x_769_, v___f_766_, v___x_768_, v_t_763_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___boxed(lean_object* v_inst_771_, lean_object* v_t_772_, lean_object* v_k_773_, lean_object* v_f_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_NameTrie_forMatchingM___redArg(v_inst_771_, v_t_772_, v_k_773_, v_f_774_);
lean_dec(v_k_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM(lean_object* v_m_776_, lean_object* v_00_u03b2_777_, lean_object* v_inst_778_, lean_object* v_t_779_, lean_object* v_k_780_, lean_object* v_f_781_){
_start:
{
lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___f_782_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_782_, 0, v_f_781_);
v___x_783_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_784_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_780_);
v___x_785_ = lean_box(0);
v___x_786_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_778_, v___x_783_, v___x_785_, v___f_782_, v___x_784_, v_t_779_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___boxed(lean_object* v_m_787_, lean_object* v_00_u03b2_788_, lean_object* v_inst_789_, lean_object* v_t_790_, lean_object* v_k_791_, lean_object* v_f_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_NameTrie_forMatchingM(v_m_787_, v_00_u03b2_788_, v_inst_789_, v_t_790_, v_k_791_, v_f_792_);
lean_dec(v_k_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM___redArg(lean_object* v_inst_794_, lean_object* v_t_795_, lean_object* v_f_796_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___f_797_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_797_, 0, v_f_796_);
v___x_798_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_799_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_800_ = lean_box(0);
v___x_801_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_794_, v___x_798_, v___x_800_, v___f_797_, v___x_799_, v_t_795_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM(lean_object* v_m_802_, lean_object* v_00_u03b2_803_, lean_object* v_inst_804_, lean_object* v_t_805_, lean_object* v_f_806_){
_start:
{
lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___f_807_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_807_, 0, v_f_806_);
v___x_808_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_809_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_810_ = lean_box(0);
v___x_811_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_804_, v___x_808_, v___x_810_, v___f_807_, v___x_809_, v_t_805_, v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v_a_812_, 0);
if (lean_obj_tag(v_a_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; 
v_a_815_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_a_815_);
lean_dec_ref(v_a_812_);
v___x_816_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_a_813_, v_a_815_);
return v___x_816_;
}
else
{
lean_object* v_a_817_; lean_object* v_val_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_inc_ref(v_a_814_);
v_a_817_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_a_817_);
lean_dec_ref(v_a_812_);
v_val_818_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_a_814_, 1);
v___x_819_ = lean_array_push(v_a_813_, v_val_818_);
v___x_820_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v___x_819_, v_a_817_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(lean_object* v_init_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v_v_823_; lean_object* v_l_824_; lean_object* v_r_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_v_823_ = lean_ctor_get(v_x_822_, 2);
lean_inc(v_v_823_);
v_l_824_ = lean_ctor_get(v_x_822_, 3);
lean_inc(v_l_824_);
v_r_825_ = lean_ctor_get(v_x_822_, 4);
lean_inc(v_r_825_);
lean_dec_ref_known(v_x_822_, 5);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_821_, v_l_824_);
v___x_827_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_v_823_, v___x_826_);
v_init_821_ = v___x_827_;
v_x_822_ = v_r_825_;
goto _start;
}
else
{
return v_init_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(lean_object* v_init_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
if (lean_obj_tag(v_a_830_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_831_, v_a_832_);
return v___x_833_;
}
else
{
lean_object* v_head_834_; lean_object* v_tail_835_; lean_object* v_a_836_; lean_object* v___x_837_; 
v_head_834_ = lean_ctor_get(v_a_830_, 0);
v_tail_835_ = lean_ctor_get(v_a_830_, 1);
v_a_836_ = lean_ctor_get(v_a_831_, 1);
lean_inc(v_a_836_);
lean_dec_ref(v_a_831_);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_836_, v_head_834_);
lean_dec(v_a_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_dec_ref(v_a_832_);
lean_inc_ref(v_init_829_);
return v_init_829_;
}
else
{
lean_object* v_val_838_; 
v_val_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v___x_837_, 1);
v_a_830_ = v_tail_835_;
v_a_831_ = v_val_838_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg___boxed(lean_object* v_init_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_841_);
lean_dec_ref(v_init_840_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object* v_t_847_, lean_object* v_k_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_850_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_848_);
v___x_851_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_849_, v___x_850_, v_t_847_, v___x_849_);
lean_dec(v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg___boxed(lean_object* v_t_852_, lean_object* v_k_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_852_, v_k_853_);
lean_dec(v_k_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray(lean_object* v_00_u03b2_855_, lean_object* v_t_856_, lean_object* v_k_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_856_, v_k_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___boxed(lean_object* v_00_u03b2_859_, lean_object* v_t_860_, lean_object* v_k_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_NameTrie_matchingToArray(v_00_u03b2_859_, v_t_860_, v_k_861_);
lean_dec(v_k_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(lean_object* v_00_u03b2_863_, lean_object* v_init_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_864_, v_a_865_, v_a_866_, v_a_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(lean_object* v_00_u03b2_869_, lean_object* v_init_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(v_00_u03b2_869_, v_init_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_871_);
lean_dec_ref(v_init_870_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(lean_object* v_00_u03b2_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_876_, v_a_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_879_, lean_object* v_init_880_, lean_object* v_x_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_880_, v_x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray___redArg(lean_object* v_t_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_885_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_886_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_884_, v___x_885_, v_t_883_, v___x_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray(lean_object* v_00_u03b2_887_, lean_object* v_t_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_NameTrie_toArray___redArg(v_t_888_);
return v___x_889_;
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
