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
LEAN_EXPORT uint8_t l_Lean_instBEqNamePart_beq(lean_object* v_x_39_, lean_object* v_x_40_){
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
LEAN_EXPORT lean_object* l_Lean_instBEqNamePart_beq___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_instBEqNamePart_beq(v_x_49_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringNamePart___lam__0(lean_object* v_x_60_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_s_61_; 
v_s_61_ = lean_ctor_get(v_x_60_, 0);
lean_inc_ref(v_s_61_);
lean_dec_ref_known(v_x_60_, 1);
return v_s_61_;
}
else
{
lean_object* v_n_62_; lean_object* v___x_63_; 
v_n_62_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_n_62_);
lean_dec_ref_known(v_x_60_, 1);
v___x_63_ = l_Nat_reprFast(v_n_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NamePart_cmp(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v_s_68_; lean_object* v_s_69_; uint8_t v___x_70_; 
v_s_68_ = lean_ctor_get(v_x_66_, 0);
v_s_69_ = lean_ctor_get(v_x_67_, 0);
v___x_70_ = lean_string_compare(v_s_68_, v_s_69_);
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 2;
return v___x_71_;
}
}
else
{
if (lean_obj_tag(v_x_67_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
else
{
lean_object* v_n_73_; lean_object* v_n_74_; uint8_t v___x_75_; 
v_n_73_ = lean_ctor_get(v_x_66_, 0);
v_n_74_ = lean_ctor_get(v_x_67_, 0);
v___x_75_ = lean_nat_dec_lt(v_n_73_, v_n_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = lean_nat_dec_eq(v_n_73_, v_n_74_);
if (v___x_76_ == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 2;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
}
else
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_cmp___boxed(lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Lean_NamePart_cmp(v_x_80_, v_x_81_);
lean_dec_ref(v_x_81_);
lean_dec_ref(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l_Lean_NamePart_lt(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_s_86_; lean_object* v_s_87_; uint8_t v___x_88_; 
v_s_86_ = lean_ctor_get(v_x_84_, 0);
v_s_87_ = lean_ctor_get(v_x_85_, 0);
v___x_88_ = lean_string_dec_lt(v_s_86_, v_s_87_);
return v___x_88_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
else
{
if (lean_obj_tag(v_x_85_) == 0)
{
uint8_t v___x_90_; 
v___x_90_ = 1;
return v___x_90_;
}
else
{
lean_object* v_n_91_; lean_object* v_n_92_; uint8_t v___x_93_; 
v_n_91_ = lean_ctor_get(v_x_84_, 0);
v_n_92_ = lean_ctor_get(v_x_85_, 0);
v___x_93_ = lean_nat_dec_lt(v_n_91_, v_n_92_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NamePart_lt___boxed(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Lean_NamePart_lt(v_x_94_, v_x_95_);
lean_dec_ref(v_x_95_);
lean_dec_ref(v_x_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
return v_x_99_;
}
case 1:
{
lean_object* v_pre_100_; lean_object* v_str_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_pre_100_ = lean_ctor_get(v_x_98_, 0);
v_str_101_ = lean_ctor_get(v_x_98_, 1);
lean_inc_ref(v_str_101_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v_str_101_);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_x_99_);
v_x_98_ = v_pre_100_;
v_x_99_ = v___x_103_;
goto _start;
}
default: 
{
lean_object* v_pre_105_; lean_object* v_i_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_pre_105_ = lean_ctor_get(v_x_98_, 0);
v_i_106_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_i_106_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_i_106_);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_x_99_);
v_x_98_ = v_pre_105_;
v_x_99_ = v___x_108_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey_loop___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_x_110_, v_x_111_);
lean_dec(v_x_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey(lean_object* v_n_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_box(0);
v___x_115_ = l___private_Lean_Data_NameTrie_0__Lean_toKey_loop(v_n_113_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_NameTrie_0__Lean_toKey___boxed(lean_object* v_n_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_116_);
lean_dec(v_n_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(lean_object* v_t_118_, lean_object* v_k_119_){
_start:
{
if (lean_obj_tag(v_t_118_) == 0)
{
lean_object* v_k_120_; lean_object* v_v_121_; lean_object* v_l_122_; lean_object* v_r_123_; uint8_t v___x_124_; 
v_k_120_ = lean_ctor_get(v_t_118_, 1);
v_v_121_ = lean_ctor_get(v_t_118_, 2);
v_l_122_ = lean_ctor_get(v_t_118_, 3);
v_r_123_ = lean_ctor_get(v_t_118_, 4);
v___x_124_ = l_Lean_NamePart_cmp(v_k_119_, v_k_120_);
switch(v___x_124_)
{
case 0:
{
v_t_118_ = v_l_122_;
goto _start;
}
case 1:
{
lean_object* v___x_126_; 
lean_inc(v_v_121_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v_v_121_);
return v___x_126_;
}
default: 
{
v_t_118_ = v_r_123_;
goto _start;
}
}
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg___boxed(lean_object* v_t_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_129_, v_k_130_);
lean_dec_ref(v_k_130_);
lean_dec(v_t_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_box(1);
v___x_134_ = lean_panic_fn_borrowed(v___x_133_, v_msg_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_139_ = lean_unsigned_to_nat(35u);
v___x_140_ = lean_unsigned_to_nat(182u);
v___x_141_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_142_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_143_ = l_mkPanicMessageWithDecl(v___x_142_, v___x_141_, v___x_140_, v___x_139_, v___x_138_);
return v___x_143_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_144_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__2));
v___x_145_ = lean_unsigned_to_nat(21u);
v___x_146_ = lean_unsigned_to_nat(183u);
v___x_147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__1));
v___x_148_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_149_ = l_mkPanicMessageWithDecl(v___x_148_, v___x_147_, v___x_146_, v___x_145_, v___x_144_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_152_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_153_ = lean_unsigned_to_nat(35u);
v___x_154_ = lean_unsigned_to_nat(276u);
v___x_155_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_156_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_157_ = l_mkPanicMessageWithDecl(v___x_156_, v___x_155_, v___x_154_, v___x_153_, v___x_152_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__6));
v___x_159_ = lean_unsigned_to_nat(21u);
v___x_160_ = lean_unsigned_to_nat(277u);
v___x_161_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__5));
v___x_162_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__0));
v___x_163_ = l_mkPanicMessageWithDecl(v___x_162_, v___x_161_, v___x_160_, v___x_159_, v___x_158_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(lean_object* v_k_164_, lean_object* v_v_165_, lean_object* v_t_166_){
_start:
{
if (lean_obj_tag(v_t_166_) == 0)
{
lean_object* v_size_167_; lean_object* v_k_168_; lean_object* v_v_169_; lean_object* v_l_170_; lean_object* v_r_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_527_; 
v_size_167_ = lean_ctor_get(v_t_166_, 0);
v_k_168_ = lean_ctor_get(v_t_166_, 1);
v_v_169_ = lean_ctor_get(v_t_166_, 2);
v_l_170_ = lean_ctor_get(v_t_166_, 3);
v_r_171_ = lean_ctor_get(v_t_166_, 4);
v_isSharedCheck_527_ = !lean_is_exclusive(v_t_166_);
if (v_isSharedCheck_527_ == 0)
{
v___x_173_ = v_t_166_;
v_isShared_174_ = v_isSharedCheck_527_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_r_171_);
lean_inc(v_l_170_);
lean_inc(v_v_169_);
lean_inc(v_k_168_);
lean_inc(v_size_167_);
lean_dec(v_t_166_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_527_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
uint8_t v___x_175_; 
v___x_175_ = l_Lean_NamePart_cmp(v_k_164_, v_k_168_);
switch(v___x_175_)
{
case 0:
{
lean_object* v___x_176_; 
lean_dec(v_size_167_);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_164_, v_v_165_, v_l_170_);
if (lean_obj_tag(v_r_171_) == 0)
{
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_size_177_; lean_object* v_size_178_; lean_object* v_k_179_; lean_object* v_v_180_; lean_object* v_l_181_; lean_object* v_r_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_size_177_ = lean_ctor_get(v_r_171_, 0);
v_size_178_ = lean_ctor_get(v___x_176_, 0);
v_k_179_ = lean_ctor_get(v___x_176_, 1);
v_v_180_ = lean_ctor_get(v___x_176_, 2);
v_l_181_ = lean_ctor_get(v___x_176_, 3);
v_r_182_ = lean_ctor_get(v___x_176_, 4);
lean_inc(v_r_182_);
v___x_183_ = lean_unsigned_to_nat(3u);
v___x_184_ = lean_nat_mul(v___x_183_, v_size_177_);
v___x_185_ = lean_nat_dec_lt(v___x_184_, v_size_178_);
lean_dec(v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec(v_r_182_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v___x_186_, v_size_178_);
v___x_188_ = lean_nat_add(v___x_187_, v_size_177_);
lean_dec(v___x_187_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 3, v___x_176_);
lean_ctor_set(v___x_173_, 0, v___x_188_);
v___x_190_ = v___x_173_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_r_171_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
else
{
lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_263_; 
lean_inc(v_l_181_);
lean_inc(v_v_180_);
lean_inc(v_k_179_);
lean_inc(v_size_178_);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; 
v_unused_264_ = lean_ctor_get(v___x_176_, 4);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v___x_176_, 3);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v___x_176_, 2);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v___x_176_, 1);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v___x_176_, 0);
lean_dec(v_unused_268_);
v___x_193_ = v___x_176_;
v_isShared_194_ = v_isSharedCheck_263_;
goto v_resetjp_192_;
}
else
{
lean_dec(v___x_176_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_263_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
if (lean_obj_tag(v_l_181_) == 0)
{
if (lean_obj_tag(v_r_182_) == 0)
{
lean_object* v_size_195_; lean_object* v_size_196_; lean_object* v_k_197_; lean_object* v_v_198_; lean_object* v_l_199_; lean_object* v_r_200_; lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_size_195_ = lean_ctor_get(v_l_181_, 0);
v_size_196_ = lean_ctor_get(v_r_182_, 0);
v_k_197_ = lean_ctor_get(v_r_182_, 1);
v_v_198_ = lean_ctor_get(v_r_182_, 2);
v_l_199_ = lean_ctor_get(v_r_182_, 3);
v_r_200_ = lean_ctor_get(v_r_182_, 4);
v___x_201_ = lean_unsigned_to_nat(2u);
v___x_202_ = lean_nat_mul(v___x_201_, v_size_195_);
v___x_203_ = lean_nat_dec_lt(v_size_196_, v___x_202_);
lean_dec(v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_233_; 
lean_inc(v_r_200_);
lean_inc(v_l_199_);
lean_inc(v_v_198_);
lean_inc(v_k_197_);
v_isSharedCheck_233_ = !lean_is_exclusive(v_r_182_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_234_ = lean_ctor_get(v_r_182_, 4);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_r_182_, 3);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_r_182_, 2);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_r_182_, 1);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_r_182_, 0);
lean_dec(v_unused_238_);
v___x_205_ = v_r_182_;
v_isShared_206_ = v_isSharedCheck_233_;
goto v_resetjp_204_;
}
else
{
lean_dec(v_r_182_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_233_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___x_221_; lean_object* v___y_223_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v___x_207_, v_size_178_);
lean_dec(v_size_178_);
v___x_209_ = lean_nat_add(v___x_208_, v_size_177_);
lean_dec(v___x_208_);
v___x_221_ = lean_nat_add(v___x_207_, v_size_195_);
if (lean_obj_tag(v_l_199_) == 0)
{
lean_object* v_size_231_; 
v_size_231_ = lean_ctor_get(v_l_199_, 0);
lean_inc(v_size_231_);
v___y_223_ = v_size_231_;
goto v___jp_222_;
}
else
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___y_223_ = v___x_232_;
goto v___jp_222_;
}
v___jp_210_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_nat_add(v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec(v___y_212_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 4, v_r_171_);
lean_ctor_set(v___x_205_, 3, v_r_200_);
lean_ctor_set(v___x_205_, 2, v_v_169_);
lean_ctor_set(v___x_205_, 1, v_k_168_);
lean_ctor_set(v___x_205_, 0, v___x_214_);
v___x_216_ = v___x_205_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_r_200_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_r_171_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_218_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 4, v___x_216_);
lean_ctor_set(v___x_193_, 3, v___y_211_);
lean_ctor_set(v___x_193_, 2, v_v_198_);
lean_ctor_set(v___x_193_, 1, v_k_197_);
lean_ctor_set(v___x_193_, 0, v___x_209_);
v___x_218_ = v___x_193_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_197_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_198_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v___y_211_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_nat_add(v___x_221_, v___y_223_);
lean_dec(v___y_223_);
lean_dec(v___x_221_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_l_199_);
lean_ctor_set(v___x_173_, 3, v_l_181_);
lean_ctor_set(v___x_173_, 2, v_v_180_);
lean_ctor_set(v___x_173_, 1, v_k_179_);
lean_ctor_set(v___x_173_, 0, v___x_224_);
v___x_226_ = v___x_173_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_179_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_180_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_l_181_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_l_199_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_nat_add(v___x_207_, v_size_177_);
if (lean_obj_tag(v_r_200_) == 0)
{
lean_object* v_size_228_; 
v_size_228_ = lean_ctor_get(v_r_200_, 0);
lean_inc(v_size_228_);
v___y_211_ = v___x_226_;
v___y_212_ = v___x_227_;
v___y_213_ = v_size_228_;
goto v___jp_210_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___y_211_ = v___x_226_;
v___y_212_ = v___x_227_;
v___y_213_ = v___x_229_;
goto v___jp_210_;
}
}
}
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
lean_del_object(v___x_173_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v___x_239_, v_size_178_);
lean_dec(v_size_178_);
v___x_241_ = lean_nat_add(v___x_240_, v_size_177_);
lean_dec(v___x_240_);
v___x_242_ = lean_nat_add(v___x_239_, v_size_177_);
v___x_243_ = lean_nat_add(v___x_242_, v_size_196_);
lean_dec(v___x_242_);
lean_inc_ref(v_r_171_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 4, v_r_171_);
lean_ctor_set(v___x_193_, 3, v_r_182_);
lean_ctor_set(v___x_193_, 2, v_v_169_);
lean_ctor_set(v___x_193_, 1, v_k_168_);
lean_ctor_set(v___x_193_, 0, v___x_243_);
v___x_245_ = v___x_193_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_r_182_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_r_171_);
v___x_245_ = v_reuseFailAlloc_258_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_isSharedCheck_252_ = !lean_is_exclusive(v_r_171_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; lean_object* v_unused_254_; lean_object* v_unused_255_; lean_object* v_unused_256_; lean_object* v_unused_257_; 
v_unused_253_ = lean_ctor_get(v_r_171_, 4);
lean_dec(v_unused_253_);
v_unused_254_ = lean_ctor_get(v_r_171_, 3);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_r_171_, 2);
lean_dec(v_unused_255_);
v_unused_256_ = lean_ctor_get(v_r_171_, 1);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_r_171_, 0);
lean_dec(v_unused_257_);
v___x_247_ = v_r_171_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_dec(v_r_171_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 4, v___x_245_);
lean_ctor_set(v___x_247_, 3, v_l_181_);
lean_ctor_set(v___x_247_, 2, v_v_180_);
lean_ctor_set(v___x_247_, 1, v_k_179_);
lean_ctor_set(v___x_247_, 0, v___x_241_);
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_k_179_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_v_180_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_l_181_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v___x_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref_known(v_l_181_, 5);
lean_del_object(v___x_193_);
lean_dec(v_v_180_);
lean_dec(v_k_179_);
lean_dec(v_size_178_);
lean_dec_ref_known(v_r_171_, 5);
lean_del_object(v___x_173_);
lean_dec(v_v_169_);
lean_dec(v_k_168_);
v___x_259_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__3);
v___x_260_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_259_);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_del_object(v___x_193_);
lean_dec(v_r_182_);
lean_dec(v_v_180_);
lean_dec(v_k_179_);
lean_dec(v_size_178_);
lean_dec_ref_known(v_r_171_, 5);
lean_del_object(v___x_173_);
lean_dec(v_v_169_);
lean_dec(v_k_168_);
v___x_261_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__4);
v___x_262_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_261_);
return v___x_262_;
}
}
}
}
else
{
lean_object* v_size_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v_size_269_ = lean_ctor_get(v_r_171_, 0);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v___x_270_, v_size_269_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 3, v___x_176_);
lean_ctor_set(v___x_173_, 0, v___x_271_);
v___x_273_ = v___x_173_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_r_171_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_l_275_; 
v_l_275_ = lean_ctor_get(v___x_176_, 3);
if (lean_obj_tag(v_l_275_) == 0)
{
lean_object* v_r_276_; 
lean_inc_ref(v_l_275_);
v_r_276_ = lean_ctor_get(v___x_176_, 4);
lean_inc(v_r_276_);
if (lean_obj_tag(v_r_276_) == 0)
{
lean_object* v_size_277_; lean_object* v_k_278_; lean_object* v_v_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_293_; 
v_size_277_ = lean_ctor_get(v___x_176_, 0);
v_k_278_ = lean_ctor_get(v___x_176_, 1);
v_v_279_ = lean_ctor_get(v___x_176_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; 
v_unused_294_ = lean_ctor_get(v___x_176_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v___x_176_, 3);
lean_dec(v_unused_295_);
v___x_281_ = v___x_176_;
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_v_279_);
lean_inc(v_k_278_);
lean_inc(v_size_277_);
lean_dec(v___x_176_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_size_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v_size_283_ = lean_ctor_get(v_r_276_, 0);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v___x_284_, v_size_277_);
lean_dec(v_size_277_);
v___x_286_ = lean_nat_add(v___x_284_, v_size_283_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 4, v_r_171_);
lean_ctor_set(v___x_281_, 3, v_r_276_);
lean_ctor_set(v___x_281_, 2, v_v_169_);
lean_ctor_set(v___x_281_, 1, v_k_168_);
lean_ctor_set(v___x_281_, 0, v___x_286_);
v___x_288_ = v___x_281_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_r_276_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_r_171_);
v___x_288_ = v_reuseFailAlloc_292_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_290_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_288_);
lean_ctor_set(v___x_173_, 3, v_l_275_);
lean_ctor_set(v___x_173_, 2, v_v_279_);
lean_ctor_set(v___x_173_, 1, v_k_278_);
lean_ctor_set(v___x_173_, 0, v___x_285_);
v___x_290_ = v___x_173_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_278_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_279_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_l_275_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_k_296_; lean_object* v_v_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_309_; 
v_k_296_ = lean_ctor_get(v___x_176_, 1);
v_v_297_ = lean_ctor_get(v___x_176_, 2);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_309_ == 0)
{
lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_310_ = lean_ctor_get(v___x_176_, 4);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v___x_176_, 3);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v___x_176_, 0);
lean_dec(v_unused_312_);
v___x_299_ = v___x_176_;
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_v_297_);
lean_inc(v_k_296_);
lean_dec(v___x_176_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_309_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_301_ = lean_unsigned_to_nat(3u);
v___x_302_ = lean_unsigned_to_nat(1u);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 3, v_r_276_);
lean_ctor_set(v___x_299_, 2, v_v_169_);
lean_ctor_set(v___x_299_, 1, v_k_168_);
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_r_276_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_r_276_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_304_);
lean_ctor_set(v___x_173_, 3, v_l_275_);
lean_ctor_set(v___x_173_, 2, v_v_297_);
lean_ctor_set(v___x_173_, 1, v_k_296_);
lean_ctor_set(v___x_173_, 0, v___x_301_);
v___x_306_ = v___x_173_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_k_296_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_v_297_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_l_275_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
else
{
lean_object* v_r_313_; 
v_r_313_ = lean_ctor_get(v___x_176_, 4);
lean_inc(v_r_313_);
if (lean_obj_tag(v_r_313_) == 0)
{
lean_object* v_k_314_; lean_object* v_v_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_339_; 
lean_inc(v_l_275_);
v_k_314_ = lean_ctor_get(v___x_176_, 1);
v_v_315_ = lean_ctor_get(v___x_176_, 2);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; lean_object* v_unused_341_; lean_object* v_unused_342_; 
v_unused_340_ = lean_ctor_get(v___x_176_, 4);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v___x_176_, 3);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v___x_176_, 0);
lean_dec(v_unused_342_);
v___x_317_ = v___x_176_;
v_isShared_318_ = v_isSharedCheck_339_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_v_315_);
lean_inc(v_k_314_);
lean_dec(v___x_176_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_339_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_335_; 
v_k_319_ = lean_ctor_get(v_r_313_, 1);
v_v_320_ = lean_ctor_get(v_r_313_, 2);
v_isSharedCheck_335_ = !lean_is_exclusive(v_r_313_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; lean_object* v_unused_337_; lean_object* v_unused_338_; 
v_unused_336_ = lean_ctor_get(v_r_313_, 4);
lean_dec(v_unused_336_);
v_unused_337_ = lean_ctor_get(v_r_313_, 3);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_r_313_, 0);
lean_dec(v_unused_338_);
v___x_322_ = v_r_313_;
v_isShared_323_ = v_isSharedCheck_335_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_v_320_);
lean_inc(v_k_319_);
lean_dec(v_r_313_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_335_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_unsigned_to_nat(1u);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 4, v_l_275_);
lean_ctor_set(v___x_322_, 3, v_l_275_);
lean_ctor_set(v___x_322_, 2, v_v_315_);
lean_ctor_set(v___x_322_, 1, v_k_314_);
lean_ctor_set(v___x_322_, 0, v___x_325_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_k_314_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_v_315_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_l_275_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_l_275_);
v___x_327_ = v_reuseFailAlloc_334_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 4, v_l_275_);
lean_ctor_set(v___x_317_, 2, v_v_169_);
lean_ctor_set(v___x_317_, 1, v_k_168_);
lean_ctor_set(v___x_317_, 0, v___x_325_);
v___x_329_ = v___x_317_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_l_275_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_l_275_);
v___x_329_ = v_reuseFailAlloc_333_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_329_);
lean_ctor_set(v___x_173_, 3, v___x_327_);
lean_ctor_set(v___x_173_, 2, v_v_320_);
lean_ctor_set(v___x_173_, 1, v_k_319_);
lean_ctor_set(v___x_173_, 0, v___x_324_);
v___x_331_ = v___x_173_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_k_319_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_v_320_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(2u);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_r_313_);
lean_ctor_set(v___x_173_, 3, v___x_176_);
lean_ctor_set(v___x_173_, 0, v___x_343_);
v___x_345_ = v___x_173_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_r_313_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_unsigned_to_nat(1u);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_176_);
lean_ctor_set(v___x_173_, 3, v___x_176_);
lean_ctor_set(v___x_173_, 0, v___x_347_);
v___x_349_ = v___x_173_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v___x_176_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
case 1:
{
lean_object* v___x_352_; 
lean_dec(v_v_169_);
lean_dec(v_k_168_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 2, v_v_165_);
lean_ctor_set(v___x_173_, 1, v_k_164_);
v___x_352_ = v___x_173_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_size_167_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_k_164_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_v_165_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_l_170_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_r_171_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
default: 
{
lean_object* v___x_354_; 
lean_dec(v_size_167_);
v___x_354_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_164_, v_v_165_, v_r_171_);
if (lean_obj_tag(v_l_170_) == 0)
{
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_size_355_; lean_object* v_size_356_; lean_object* v_k_357_; lean_object* v_v_358_; lean_object* v_l_359_; lean_object* v_r_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_size_355_ = lean_ctor_get(v_l_170_, 0);
v_size_356_ = lean_ctor_get(v___x_354_, 0);
v_k_357_ = lean_ctor_get(v___x_354_, 1);
v_v_358_ = lean_ctor_get(v___x_354_, 2);
v_l_359_ = lean_ctor_get(v___x_354_, 3);
lean_inc(v_l_359_);
v_r_360_ = lean_ctor_get(v___x_354_, 4);
v___x_361_ = lean_unsigned_to_nat(3u);
v___x_362_ = lean_nat_mul(v___x_361_, v_size_355_);
v___x_363_ = lean_nat_dec_lt(v___x_362_, v_size_356_);
lean_dec(v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
lean_dec(v_l_359_);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_add(v___x_364_, v_size_355_);
v___x_366_ = lean_nat_add(v___x_365_, v_size_356_);
lean_dec(v___x_365_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_354_);
lean_ctor_set(v___x_173_, 0, v___x_366_);
v___x_368_ = v___x_173_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_l_170_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v___x_354_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_439_; 
lean_inc(v_r_360_);
lean_inc(v_v_358_);
lean_inc(v_k_357_);
lean_inc(v_size_356_);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; 
v_unused_440_ = lean_ctor_get(v___x_354_, 4);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v___x_354_, 3);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v___x_354_, 2);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v___x_354_, 1);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v___x_354_, 0);
lean_dec(v_unused_444_);
v___x_371_ = v___x_354_;
v_isShared_372_ = v_isSharedCheck_439_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_354_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_439_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
if (lean_obj_tag(v_l_359_) == 0)
{
if (lean_obj_tag(v_r_360_) == 0)
{
lean_object* v_size_373_; lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_l_376_; lean_object* v_r_377_; lean_object* v_size_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_size_373_ = lean_ctor_get(v_l_359_, 0);
v_k_374_ = lean_ctor_get(v_l_359_, 1);
v_v_375_ = lean_ctor_get(v_l_359_, 2);
v_l_376_ = lean_ctor_get(v_l_359_, 3);
v_r_377_ = lean_ctor_get(v_l_359_, 4);
v_size_378_ = lean_ctor_get(v_r_360_, 0);
v___x_379_ = lean_unsigned_to_nat(2u);
v___x_380_ = lean_nat_mul(v___x_379_, v_size_378_);
v___x_381_ = lean_nat_dec_lt(v_size_373_, v___x_380_);
lean_dec(v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_410_; 
lean_inc(v_r_377_);
lean_inc(v_l_376_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
v_isSharedCheck_410_ = !lean_is_exclusive(v_l_359_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; lean_object* v_unused_412_; lean_object* v_unused_413_; lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_411_ = lean_ctor_get(v_l_359_, 4);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_l_359_, 3);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_l_359_, 2);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_l_359_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_l_359_, 0);
lean_dec(v_unused_415_);
v___x_383_ = v_l_359_;
v_isShared_384_ = v_isSharedCheck_410_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_l_359_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_410_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_400_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v___x_385_, v_size_355_);
v___x_387_ = lean_nat_add(v___x_386_, v_size_356_);
lean_dec(v_size_356_);
if (lean_obj_tag(v_l_376_) == 0)
{
lean_object* v_size_408_; 
v_size_408_ = lean_ctor_get(v_l_376_, 0);
lean_inc(v_size_408_);
v___y_400_ = v_size_408_;
goto v___jp_399_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___y_400_ = v___x_409_;
goto v___jp_399_;
}
v___jp_388_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_nat_add(v___y_389_, v___y_391_);
lean_dec(v___y_391_);
lean_dec(v___y_389_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 4, v_r_360_);
lean_ctor_set(v___x_383_, 3, v_r_377_);
lean_ctor_set(v___x_383_, 2, v_v_358_);
lean_ctor_set(v___x_383_, 1, v_k_357_);
lean_ctor_set(v___x_383_, 0, v___x_392_);
v___x_394_ = v___x_383_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_k_357_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_v_358_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_r_377_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_r_360_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_394_);
lean_ctor_set(v___x_371_, 3, v___y_390_);
lean_ctor_set(v___x_371_, 2, v_v_375_);
lean_ctor_set(v___x_371_, 1, v_k_374_);
lean_ctor_set(v___x_371_, 0, v___x_387_);
v___x_396_ = v___x_371_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_374_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_375_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v___y_390_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_nat_add(v___x_386_, v___y_400_);
lean_dec(v___y_400_);
lean_dec(v___x_386_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_l_376_);
lean_ctor_set(v___x_173_, 0, v___x_401_);
v___x_403_ = v___x_173_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_l_170_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_l_376_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = lean_nat_add(v___x_385_, v_size_378_);
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_size_405_; 
v_size_405_ = lean_ctor_get(v_r_377_, 0);
lean_inc(v_size_405_);
v___y_389_ = v___x_404_;
v___y_390_ = v___x_403_;
v___y_391_ = v_size_405_;
goto v___jp_388_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v___y_389_ = v___x_404_;
v___y_390_ = v___x_403_;
v___y_391_ = v___x_406_;
goto v___jp_388_;
}
}
}
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
lean_del_object(v___x_173_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v___x_416_, v_size_355_);
v___x_418_ = lean_nat_add(v___x_417_, v_size_356_);
lean_dec(v_size_356_);
v___x_419_ = lean_nat_add(v___x_417_, v_size_373_);
lean_dec(v___x_417_);
lean_inc_ref(v_l_170_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v_l_359_);
lean_ctor_set(v___x_371_, 3, v_l_170_);
lean_ctor_set(v___x_371_, 2, v_v_169_);
lean_ctor_set(v___x_371_, 1, v_k_168_);
lean_ctor_set(v___x_371_, 0, v___x_419_);
v___x_421_ = v___x_371_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_l_170_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v_l_359_);
v___x_421_ = v_reuseFailAlloc_434_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_isSharedCheck_428_ = !lean_is_exclusive(v_l_170_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; lean_object* v_unused_430_; lean_object* v_unused_431_; lean_object* v_unused_432_; lean_object* v_unused_433_; 
v_unused_429_ = lean_ctor_get(v_l_170_, 4);
lean_dec(v_unused_429_);
v_unused_430_ = lean_ctor_get(v_l_170_, 3);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_l_170_, 2);
lean_dec(v_unused_431_);
v_unused_432_ = lean_ctor_get(v_l_170_, 1);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_l_170_, 0);
lean_dec(v_unused_433_);
v___x_423_ = v_l_170_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_l_170_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_r_360_);
lean_ctor_set(v___x_423_, 3, v___x_421_);
lean_ctor_set(v___x_423_, 2, v_v_358_);
lean_ctor_set(v___x_423_, 1, v_k_357_);
lean_ctor_set(v___x_423_, 0, v___x_418_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_k_357_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_v_358_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v___x_421_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_r_360_);
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
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref_known(v_l_359_, 5);
lean_del_object(v___x_371_);
lean_dec(v_v_358_);
lean_dec(v_k_357_);
lean_dec(v_size_356_);
lean_dec_ref_known(v_l_170_, 5);
lean_del_object(v___x_173_);
lean_dec(v_v_169_);
lean_dec(v_k_168_);
v___x_435_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__7);
v___x_436_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_435_);
return v___x_436_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_del_object(v___x_371_);
lean_dec(v_r_360_);
lean_dec(v_v_358_);
lean_dec(v_k_357_);
lean_dec(v_size_356_);
lean_dec_ref_known(v_l_170_, 5);
lean_del_object(v___x_173_);
lean_dec(v_v_169_);
lean_dec(v_k_168_);
v___x_437_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg___closed__8);
v___x_438_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v___x_437_);
return v___x_438_;
}
}
}
}
else
{
lean_object* v_size_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v_size_445_ = lean_ctor_get(v_l_170_, 0);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v___x_446_, v_size_445_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_354_);
lean_ctor_set(v___x_173_, 0, v___x_447_);
v___x_449_ = v___x_173_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_l_170_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v___x_354_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_l_451_; 
v_l_451_ = lean_ctor_get(v___x_354_, 3);
lean_inc(v_l_451_);
if (lean_obj_tag(v_l_451_) == 0)
{
lean_object* v_r_452_; 
v_r_452_ = lean_ctor_get(v___x_354_, 4);
lean_inc(v_r_452_);
if (lean_obj_tag(v_r_452_) == 0)
{
lean_object* v_size_453_; lean_object* v_k_454_; lean_object* v_v_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_469_; 
v_size_453_ = lean_ctor_get(v___x_354_, 0);
v_k_454_ = lean_ctor_get(v___x_354_, 1);
v_v_455_ = lean_ctor_get(v___x_354_, 2);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; 
v_unused_470_ = lean_ctor_get(v___x_354_, 4);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v___x_354_, 3);
lean_dec(v_unused_471_);
v___x_457_ = v___x_354_;
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_v_455_);
lean_inc(v_k_454_);
lean_inc(v_size_453_);
lean_dec(v___x_354_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_469_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_size_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v_size_459_ = lean_ctor_get(v_l_451_, 0);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v___x_460_, v_size_453_);
lean_dec(v_size_453_);
v___x_462_ = lean_nat_add(v___x_460_, v_size_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 4, v_l_451_);
lean_ctor_set(v___x_457_, 3, v_l_170_);
lean_ctor_set(v___x_457_, 2, v_v_169_);
lean_ctor_set(v___x_457_, 1, v_k_168_);
lean_ctor_set(v___x_457_, 0, v___x_462_);
v___x_464_ = v___x_457_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_l_170_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_l_451_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_466_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_r_452_);
lean_ctor_set(v___x_173_, 3, v___x_464_);
lean_ctor_set(v___x_173_, 2, v_v_455_);
lean_ctor_set(v___x_173_, 1, v_k_454_);
lean_ctor_set(v___x_173_, 0, v___x_461_);
v___x_466_ = v___x_173_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_k_454_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_v_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_r_452_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_k_472_; lean_object* v_v_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_497_; 
v_k_472_ = lean_ctor_get(v___x_354_, 1);
v_v_473_ = lean_ctor_get(v___x_354_, 2);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; lean_object* v_unused_500_; 
v_unused_498_ = lean_ctor_get(v___x_354_, 4);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v___x_354_, 3);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v___x_354_, 0);
lean_dec(v_unused_500_);
v___x_475_ = v___x_354_;
v_isShared_476_ = v_isSharedCheck_497_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_v_473_);
lean_inc(v_k_472_);
lean_dec(v___x_354_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_497_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_493_; 
v_k_477_ = lean_ctor_get(v_l_451_, 1);
v_v_478_ = lean_ctor_get(v_l_451_, 2);
v_isSharedCheck_493_ = !lean_is_exclusive(v_l_451_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; 
v_unused_494_ = lean_ctor_get(v_l_451_, 4);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_l_451_, 3);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_l_451_, 0);
lean_dec(v_unused_496_);
v___x_480_ = v_l_451_;
v_isShared_481_ = v_isSharedCheck_493_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_v_478_);
lean_inc(v_k_477_);
lean_dec(v_l_451_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_493_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_482_ = lean_unsigned_to_nat(3u);
v___x_483_ = lean_unsigned_to_nat(1u);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v_r_452_);
lean_ctor_set(v___x_480_, 3, v_r_452_);
lean_ctor_set(v___x_480_, 2, v_v_169_);
lean_ctor_set(v___x_480_, 1, v_k_168_);
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_r_452_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_r_452_);
v___x_485_ = v_reuseFailAlloc_492_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v_r_452_);
lean_ctor_set(v___x_475_, 0, v___x_483_);
v___x_487_ = v___x_475_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_472_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_473_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_r_452_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_r_452_);
v___x_487_ = v_reuseFailAlloc_491_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_487_);
lean_ctor_set(v___x_173_, 3, v___x_485_);
lean_ctor_set(v___x_173_, 2, v_v_478_);
lean_ctor_set(v___x_173_, 1, v_k_477_);
lean_ctor_set(v___x_173_, 0, v___x_482_);
v___x_489_ = v___x_173_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_501_; 
v_r_501_ = lean_ctor_get(v___x_354_, 4);
lean_inc(v_r_501_);
if (lean_obj_tag(v_r_501_) == 0)
{
lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_515_; 
v_k_502_ = lean_ctor_get(v___x_354_, 1);
v_v_503_ = lean_ctor_get(v___x_354_, 2);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; lean_object* v_unused_517_; lean_object* v_unused_518_; 
v_unused_516_ = lean_ctor_get(v___x_354_, 4);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v___x_354_, 3);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v___x_354_, 0);
lean_dec(v_unused_518_);
v___x_505_ = v___x_354_;
v_isShared_506_ = v_isSharedCheck_515_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_v_503_);
lean_inc(v_k_502_);
lean_dec(v___x_354_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_515_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_507_ = lean_unsigned_to_nat(3u);
v___x_508_ = lean_unsigned_to_nat(1u);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 4, v_l_451_);
lean_ctor_set(v___x_505_, 2, v_v_169_);
lean_ctor_set(v___x_505_, 1, v_k_168_);
lean_ctor_set(v___x_505_, 0, v___x_508_);
v___x_510_ = v___x_505_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_l_451_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_l_451_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v_r_501_);
lean_ctor_set(v___x_173_, 3, v___x_510_);
lean_ctor_set(v___x_173_, 2, v_v_503_);
lean_ctor_set(v___x_173_, 1, v_k_502_);
lean_ctor_set(v___x_173_, 0, v___x_507_);
v___x_512_ = v___x_173_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 4, v_r_501_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_unsigned_to_nat(2u);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_354_);
lean_ctor_set(v___x_173_, 3, v_r_501_);
lean_ctor_set(v___x_173_, 0, v___x_519_);
v___x_521_ = v___x_173_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_r_501_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v___x_354_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_unsigned_to_nat(1u);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 4, v___x_354_);
lean_ctor_set(v___x_173_, 3, v___x_354_);
lean_ctor_set(v___x_173_, 0, v___x_523_);
v___x_525_ = v___x_173_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_k_168_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v___x_354_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_k_164_);
lean_ctor_set(v___x_529_, 2, v_v_165_);
lean_ctor_set(v___x_529_, 3, v_t_166_);
lean_ctor_set(v___x_529_, 4, v_t_166_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(lean_object* v_val_530_, lean_object* v_k_531_){
_start:
{
if (lean_obj_tag(v_k_531_) == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v_val_530_);
v___x_533_ = lean_box(1);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_547_; 
v_head_535_ = lean_ctor_get(v_k_531_, 0);
v_tail_536_ = lean_ctor_get(v_k_531_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_k_531_);
if (v_isSharedCheck_547_ == 0)
{
v___x_538_ = v_k_531_;
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_tail_536_);
lean_inc(v_head_535_);
lean_dec(v_k_531_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_t_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v_t_540_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_530_, v_tail_536_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_box(1);
v___x_543_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_535_, v_t_540_, v___x_542_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 0);
lean_ctor_set(v___x_538_, 1, v___x_543_);
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_545_ = v___x_538_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(lean_object* v_val_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_a_551_ = lean_ctor_get(v_x_549_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v_x_549_, 0);
lean_dec(v_unused_560_);
v___x_553_ = v_x_549_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v_x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v_val_548_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_a_551_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_578_; 
v_a_561_ = lean_ctor_get(v_x_549_, 0);
v_a_562_ = lean_ctor_get(v_x_549_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_578_ == 0)
{
v___x_564_ = v_x_549_;
v_isShared_565_ = v_isSharedCheck_578_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_inc(v_a_561_);
lean_dec(v_x_549_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_578_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_head_566_; lean_object* v_tail_567_; lean_object* v___y_569_; lean_object* v___x_574_; 
v_head_566_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_head_566_);
v_tail_567_ = lean_ctor_get(v_x_550_, 1);
lean_inc(v_tail_567_);
lean_dec_ref_known(v_x_550_, 2);
v___x_574_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_562_, v_head_566_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; 
v___x_575_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_548_, v_tail_567_);
v___y_569_ = v___x_575_;
goto v___jp_568_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_577_; 
v_val_576_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v___x_574_, 1);
v___x_577_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_548_, v_val_576_, v_tail_567_);
v___y_569_ = v___x_577_;
goto v___jp_568_;
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_head_566_, v___y_569_, v_a_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_570_);
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg(lean_object* v_t_579_, lean_object* v_n_580_, lean_object* v_b_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_n_580_);
v___x_583_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_b_581_, v_t_579_, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___redArg___boxed(lean_object* v_t_584_, lean_object* v_n_585_, lean_object* v_b_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_NameTrie_insert___redArg(v_t_584_, v_n_585_, v_b_586_);
lean_dec(v_n_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert(lean_object* v_00_u03b2_588_, lean_object* v_t_589_, lean_object* v_n_590_, lean_object* v_b_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_NameTrie_insert___redArg(v_t_589_, v_n_590_, v_b_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_insert___boxed(lean_object* v_00_u03b2_593_, lean_object* v_t_594_, lean_object* v_n_595_, lean_object* v_b_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_NameTrie_insert(v_00_u03b2_593_, v_t_594_, v_n_595_, v_b_596_);
lean_dec(v_n_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0(lean_object* v_00_u03b2_598_, lean_object* v_val_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0___redArg(v_val_599_, v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_603_, lean_object* v_msg_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0_spec__1___redArg(v_msg_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0(lean_object* v_00_u03b2_606_, lean_object* v_k_607_, lean_object* v_v_608_, lean_object* v_t_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__0___redArg(v_k_607_, v_v_608_, v_t_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(lean_object* v_00_u03b4_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_t_612_, v_k_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___boxed(lean_object* v_00_u03b4_615_, lean_object* v_t_616_, lean_object* v_k_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1(v_00_u03b4_615_, v_t_616_, v_k_617_);
lean_dec_ref(v_k_617_);
lean_dec(v_t_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2(lean_object* v_00_u03b2_619_, lean_object* v_val_620_, lean_object* v_k_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__2___redArg(v_val_620_, v_k_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_NameTrie_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PrefixTreeNode_empty___redArg();
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg(){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty___redArg___boxed(lean_object* v___dummy_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_NameTrie_empty___redArg();
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_empty(lean_object* v_00_u03b2_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg(){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie___redArg___boxed(lean_object* v___dummy_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_instInhabitedNameTrie___redArg();
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameTrie(lean_object* v_00_u03b2_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg(){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie___redArg___boxed(lean_object* v___dummy_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_instEmptyCollectionNameTrie___redArg();
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionNameTrie(lean_object* v_00_u03b2_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_NameTrie_empty___redArg___closed__0, &l_Lean_NameTrie_empty___redArg___closed__0_once, _init_l_Lean_NameTrie_empty___redArg___closed__0);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v_a_644_; 
v_a_644_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v_x_642_);
return v_a_644_;
}
else
{
lean_object* v_a_645_; lean_object* v_head_646_; lean_object* v_tail_647_; lean_object* v___x_648_; 
v_a_645_ = lean_ctor_get(v_x_642_, 1);
lean_inc(v_a_645_);
lean_dec_ref(v_x_642_);
v_head_646_ = lean_ctor_get(v_x_643_, 0);
v_tail_647_ = lean_ctor_get(v_x_643_, 1);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_645_, v_head_646_);
lean_dec(v_a_645_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
else
{
lean_object* v_val_650_; 
v_val_650_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_648_, 1);
v_x_642_ = v_val_650_;
v_x_643_ = v_tail_647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg___boxed(lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_652_, v_x_653_);
lean_dec(v_x_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg(lean_object* v_t_655_, lean_object* v_k_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_656_);
v___x_658_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_t_655_, v___x_657_);
lean_dec(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___redArg___boxed(lean_object* v_t_659_, lean_object* v_k_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_NameTrie_find_x3f___redArg(v_t_659_, v_k_660_);
lean_dec(v_k_660_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f(lean_object* v_00_u03b2_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_NameTrie_find_x3f___redArg(v_t_663_, v_k_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_find_x3f___boxed(lean_object* v_00_u03b2_666_, lean_object* v_t_667_, lean_object* v_k_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_NameTrie_find_x3f(v_00_u03b2_666_, v_t_667_, v_k_668_);
lean_dec(v_k_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___redArg(v_x_671_, v_x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___at___00Lean_NameTrie_find_x3f_spec__0(v_00_u03b2_674_, v_x_675_, v_x_676_);
lean_dec(v_x_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg(lean_object* v_t_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_682_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_680_);
v___x_683_ = lean_box(0);
v___x_684_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_681_, v___x_683_, v_t_679_, v___x_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___redArg___boxed(lean_object* v_t_685_, lean_object* v_k_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_NameTrie_findLongestPrefix_x3f___redArg(v_t_685_, v_k_686_);
lean_dec(v_k_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f(lean_object* v_00_u03b2_688_, lean_object* v_t_689_, lean_object* v_k_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_692_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_690_);
v___x_693_ = lean_box(0);
v___x_694_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(lean_box(0), lean_box(0), v___x_691_, v___x_693_, v_t_689_, v___x_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_findLongestPrefix_x3f___boxed(lean_object* v_00_u03b2_695_, lean_object* v_t_696_, lean_object* v_k_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_NameTrie_findLongestPrefix_x3f(v_00_u03b2_695_, v_t_696_, v_k_697_);
lean_dec(v_k_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg(lean_object* v_inst_699_, lean_object* v_t_700_, lean_object* v_k_701_, lean_object* v_init_702_, lean_object* v_f_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_705_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_701_);
lean_inc(v_init_702_);
v___x_706_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_699_, v___x_704_, v_init_702_, v_f_703_, v___x_705_, v_t_700_, v_init_702_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___redArg___boxed(lean_object* v_inst_707_, lean_object* v_t_708_, lean_object* v_k_709_, lean_object* v_init_710_, lean_object* v_f_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_NameTrie_foldMatchingM___redArg(v_inst_707_, v_t_708_, v_k_709_, v_init_710_, v_f_711_);
lean_dec(v_k_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM(lean_object* v_m_713_, lean_object* v_00_u03b2_714_, lean_object* v_00_u03c3_715_, lean_object* v_inst_716_, lean_object* v_t_717_, lean_object* v_k_718_, lean_object* v_init_719_, lean_object* v_f_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_722_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_718_);
lean_inc(v_init_719_);
v___x_723_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_716_, v___x_721_, v_init_719_, v_f_720_, v___x_722_, v_t_717_, v_init_719_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldMatchingM___boxed(lean_object* v_m_724_, lean_object* v_00_u03b2_725_, lean_object* v_00_u03c3_726_, lean_object* v_inst_727_, lean_object* v_t_728_, lean_object* v_k_729_, lean_object* v_init_730_, lean_object* v_f_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_NameTrie_foldMatchingM(v_m_724_, v_00_u03b2_725_, v_00_u03c3_726_, v_inst_727_, v_t_728_, v_k_729_, v_init_730_, v_f_731_);
lean_dec(v_k_729_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_NameTrie_foldM___redArg___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_box(0);
v___x_734_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM___redArg(lean_object* v_inst_735_, lean_object* v_t_736_, lean_object* v_init_737_, lean_object* v_f_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_740_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_737_);
v___x_741_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_735_, v___x_739_, v_init_737_, v_f_738_, v___x_740_, v_t_736_, v_init_737_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_foldM(lean_object* v_m_742_, lean_object* v_00_u03b2_743_, lean_object* v_00_u03c3_744_, lean_object* v_inst_745_, lean_object* v_t_746_, lean_object* v_init_747_, lean_object* v_f_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_750_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
lean_inc(v_init_747_);
v___x_751_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_745_, v___x_749_, v_init_747_, v_f_748_, v___x_750_, v_t_746_, v_init_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___lam__0(lean_object* v_f_752_, lean_object* v_b_753_, lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_1(v_f_752_, v_b_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg(lean_object* v_inst_756_, lean_object* v_t_757_, lean_object* v_k_758_, lean_object* v_f_759_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___f_760_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_760_, 0, v_f_759_);
v___x_761_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_762_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_758_);
v___x_763_ = lean_box(0);
v___x_764_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_756_, v___x_761_, v___x_763_, v___f_760_, v___x_762_, v_t_757_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___redArg___boxed(lean_object* v_inst_765_, lean_object* v_t_766_, lean_object* v_k_767_, lean_object* v_f_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_NameTrie_forMatchingM___redArg(v_inst_765_, v_t_766_, v_k_767_, v_f_768_);
lean_dec(v_k_767_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM(lean_object* v_m_770_, lean_object* v_00_u03b2_771_, lean_object* v_inst_772_, lean_object* v_t_773_, lean_object* v_k_774_, lean_object* v_f_775_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___f_776_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_776_, 0, v_f_775_);
v___x_777_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_778_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_774_);
v___x_779_ = lean_box(0);
v___x_780_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_772_, v___x_777_, v___x_779_, v___f_776_, v___x_778_, v_t_773_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forMatchingM___boxed(lean_object* v_m_781_, lean_object* v_00_u03b2_782_, lean_object* v_inst_783_, lean_object* v_t_784_, lean_object* v_k_785_, lean_object* v_f_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_NameTrie_forMatchingM(v_m_781_, v_00_u03b2_782_, v_inst_783_, v_t_784_, v_k_785_, v_f_786_);
lean_dec(v_k_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM___redArg(lean_object* v_inst_788_, lean_object* v_t_789_, lean_object* v_f_790_){
_start:
{
lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___f_791_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_791_, 0, v_f_790_);
v___x_792_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_793_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_794_ = lean_box(0);
v___x_795_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_788_, v___x_792_, v___x_794_, v___f_791_, v___x_793_, v_t_789_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_forM(lean_object* v_m_796_, lean_object* v_00_u03b2_797_, lean_object* v_inst_798_, lean_object* v_t_799_, lean_object* v_f_800_){
_start:
{
lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___f_801_ = lean_alloc_closure((void*)(l_Lean_NameTrie_forMatchingM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_801_, 0, v_f_800_);
v___x_802_ = ((lean_object*)(l_Lean_NameTrie_findLongestPrefix_x3f___redArg___closed__0));
v___x_803_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_804_ = lean_box(0);
v___x_805_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_798_, v___x_802_, v___x_804_, v___f_801_, v___x_803_, v_t_799_, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v_a_806_, 0);
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_ctor_get(v_a_806_, 1);
lean_inc(v_a_809_);
lean_dec_ref(v_a_806_);
v___x_810_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_a_807_, v_a_809_);
return v___x_810_;
}
else
{
lean_object* v_a_811_; lean_object* v_val_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref(v_a_808_);
v_a_811_ = lean_ctor_get(v_a_806_, 1);
lean_inc(v_a_811_);
lean_dec_ref(v_a_806_);
v_val_812_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v_a_808_, 1);
v___x_813_ = lean_array_push(v_a_807_, v_val_812_);
v___x_814_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v___x_813_, v_a_811_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(lean_object* v_init_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
lean_object* v_v_817_; lean_object* v_l_818_; lean_object* v_r_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_v_817_ = lean_ctor_get(v_x_816_, 2);
lean_inc(v_v_817_);
v_l_818_ = lean_ctor_get(v_x_816_, 3);
lean_inc(v_l_818_);
v_r_819_ = lean_ctor_get(v_x_816_, 4);
lean_inc(v_r_819_);
lean_dec_ref_known(v_x_816_, 5);
v___x_820_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_815_, v_l_818_);
v___x_821_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_v_817_, v___x_820_);
v_init_815_ = v___x_821_;
v_x_816_ = v_r_819_;
goto _start;
}
else
{
return v_init_815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(lean_object* v_init_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_825_, v_a_826_);
return v___x_827_;
}
else
{
lean_object* v_head_828_; lean_object* v_tail_829_; lean_object* v_a_830_; lean_object* v___x_831_; 
v_head_828_ = lean_ctor_get(v_a_824_, 0);
v_tail_829_ = lean_ctor_get(v_a_824_, 1);
v_a_830_ = lean_ctor_get(v_a_825_, 1);
lean_inc(v_a_830_);
lean_dec_ref(v_a_825_);
v___x_831_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___at___00Lean_NameTrie_insert_spec__0_spec__1___redArg(v_a_830_, v_head_828_);
lean_dec(v_a_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref(v_a_826_);
lean_inc_ref(v_init_823_);
return v_init_823_;
}
else
{
lean_object* v_val_832_; 
v_val_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v___x_831_, 1);
v_a_824_ = v_tail_829_;
v_a_825_ = v_val_832_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg___boxed(lean_object* v_init_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_835_);
lean_dec_ref(v_init_834_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg(lean_object* v_t_841_, lean_object* v_k_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_844_ = l___private_Lean_Data_NameTrie_0__Lean_toKey(v_k_842_);
v___x_845_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_843_, v___x_844_, v_t_841_, v___x_843_);
lean_dec(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___redArg___boxed(lean_object* v_t_846_, lean_object* v_k_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_846_, v_k_847_);
lean_dec(v_k_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray(lean_object* v_00_u03b2_849_, lean_object* v_t_850_, lean_object* v_k_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_NameTrie_matchingToArray___redArg(v_t_850_, v_k_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_matchingToArray___boxed(lean_object* v_00_u03b2_853_, lean_object* v_t_854_, lean_object* v_k_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_NameTrie_matchingToArray(v_00_u03b2_853_, v_t_854_, v_k_855_);
lean_dec(v_k_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(lean_object* v_00_u03b2_857_, lean_object* v_init_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v_init_858_, v_a_859_, v_a_860_, v_a_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___boxed(lean_object* v_00_u03b2_863_, lean_object* v_init_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0(v_00_u03b2_863_, v_init_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_865_);
lean_dec_ref(v_init_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0(lean_object* v_00_u03b2_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0___redArg(v_a_870_, v_a_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_873_, lean_object* v_init_874_, lean_object* v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___at___00__private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0_spec__0_spec__1___redArg(v_init_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray___redArg(lean_object* v_t_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((lean_object*)(l_Lean_NameTrie_matchingToArray___redArg___closed__0));
v___x_879_ = lean_obj_once(&l_Lean_NameTrie_foldM___redArg___closed__0, &l_Lean_NameTrie_foldM___redArg___closed__0_once, _init_l_Lean_NameTrie_foldM___redArg___closed__0);
v___x_880_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___at___00Lean_NameTrie_matchingToArray_spec__0___redArg(v___x_878_, v___x_879_, v_t_877_, v___x_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameTrie_toArray(lean_object* v_00_u03b2_881_, lean_object* v_t_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_NameTrie_toArray___redArg(v_t_882_);
return v___x_883_;
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
