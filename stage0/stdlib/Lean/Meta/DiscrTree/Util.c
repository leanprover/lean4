// Lean compiler output
// Module: Lean.Meta.DiscrTree.Util
// Imports: public import Lean.Meta.DiscrTree.Basic
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_hasChildren___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_hasChildren___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_hasChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_hasChildren___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_starChild_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_starChild_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldChildrenM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldChildrenM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldChildrenM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_values___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_values___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_values___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_values___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value),((lean_object*)&l_Lean_Meta_DiscrTree_values___redArg___closed__0_value)} };
static const lean_object* l_Lean_Meta_DiscrTree_values___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_values___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_toArray___redArg___closed__0_value;
static const lean_array_object l_Lean_Meta_DiscrTree_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_toArray___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_toArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_toArray___redArg___lam__1, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value),((lean_object*)&l_Lean_Meta_DiscrTree_toArray___redArg___closed__0_value)} };
static const lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_toArray___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_size___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_size___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_size___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1_value)} };
static const lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object* v_vs_1_, lean_object* v_cs_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_array_get_size(v_vs_1_);
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_nat_dec_eq(v___x_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6_, 0, v_vs_1_);
lean_ctor_set(v___x_6_, 1, v_cs_2_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = lean_array_get_size(v_cs_2_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_dec_eq(v___x_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v_vs_1_);
lean_ctor_set(v___x_10_, 1, v_cs_2_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v_fst_12_; lean_object* v_snd_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_20_; 
lean_dec_ref(v_vs_1_);
v___x_11_ = lean_array_fget(v_cs_2_, v___x_4_);
lean_dec_ref(v_cs_2_);
v_fst_12_ = lean_ctor_get(v___x_11_, 0);
v_snd_13_ = lean_ctor_get(v___x_11_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_20_ == 0)
{
v___x_15_ = v___x_11_;
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_snd_13_);
lean_inc(v_fst_12_);
lean_dec(v___x_11_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_20_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_fst_12_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_snd_13_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object* v_00_u03b1_21_, lean_object* v_vs_22_, lean_object* v_cs_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_24_ = lean_array_get_size(v_vs_22_);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_nat_dec_eq(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v_vs_22_);
lean_ctor_set(v___x_27_, 1, v_cs_23_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_28_ = lean_array_get_size(v_cs_23_);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_dec_eq(v___x_28_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; 
v___x_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_31_, 0, v_vs_22_);
lean_ctor_set(v___x_31_, 1, v_cs_23_);
return v___x_31_;
}
else
{
lean_object* v___x_32_; lean_object* v_fst_33_; lean_object* v_snd_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_dec_ref(v_vs_22_);
v___x_32_ = lean_array_fget(v_cs_23_, v___x_25_);
lean_dec_ref(v_cs_23_);
v_fst_33_ = lean_ctor_get(v___x_32_, 0);
v_snd_34_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_32_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_snd_34_);
lean_inc(v_fst_33_);
lean_dec(v___x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_fst_33_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_snd_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object* v_t_44_){
_start:
{
lean_object* v_val_46_; 
switch(lean_obj_tag(v_t_44_))
{
case 2:
{
lean_object* v___x_70_; 
v___x_70_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_44_);
v_val_46_ = v___x_70_;
goto v___jp_45_;
}
case 3:
{
lean_object* v___x_71_; 
v___x_71_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_44_);
v_val_46_ = v___x_71_;
goto v___jp_45_;
}
default: 
{
v_val_46_ = v_t_44_;
goto v___jp_45_;
}
}
v___jp_45_:
{
if (lean_obj_tag(v_val_46_) == 0)
{
lean_object* v_key_47_; lean_object* v_child_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_60_; 
v_key_47_ = lean_ctor_get(v_val_46_, 0);
v_child_48_ = lean_ctor_get(v_val_46_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v_val_46_);
if (v_isSharedCheck_60_ == 0)
{
v___x_50_ = v_val_46_;
v_isShared_51_ = v_isSharedCheck_60_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_child_48_);
lean_inc(v_key_47_);
lean_dec(v_val_46_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_60_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_51_ == 0)
{
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_key_47_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_child_48_);
v___x_54_ = v_reuseFailAlloc_59_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_57_ = lean_array_push(v___x_56_, v___x_54_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_52_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
return v___x_58_;
}
}
}
else
{
lean_object* v_vs_61_; lean_object* v_children_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_vs_61_ = lean_ctor_get(v_val_46_, 0);
v_children_62_ = lean_ctor_get(v_val_46_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_val_46_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v_val_46_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_children_62_);
lean_inc(v_vs_61_);
lean_dec(v_val_46_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 0);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_vs_61_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_children_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object* v_00_u03b1_72_, lean_object* v_t_73_){
_start:
{
lean_object* v_val_75_; 
switch(lean_obj_tag(v_t_73_))
{
case 2:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_73_);
v_val_75_ = v___x_99_;
goto v___jp_74_;
}
case 3:
{
lean_object* v___x_100_; 
v___x_100_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_73_);
v_val_75_ = v___x_100_;
goto v___jp_74_;
}
default: 
{
v_val_75_ = v_t_73_;
goto v___jp_74_;
}
}
v___jp_74_:
{
if (lean_obj_tag(v_val_75_) == 0)
{
lean_object* v_key_76_; lean_object* v_child_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_89_; 
v_key_76_ = lean_ctor_get(v_val_75_, 0);
v_child_77_ = lean_ctor_get(v_val_75_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_val_75_);
if (v_isSharedCheck_89_ == 0)
{
v___x_79_ = v_val_75_;
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_child_77_);
lean_inc(v_key_76_);
lean_dec(v_val_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_80_ == 0)
{
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_key_76_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_child_77_);
v___x_83_ = v_reuseFailAlloc_88_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_array_push(v___x_85_, v___x_83_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_81_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
return v___x_87_;
}
}
}
else
{
lean_object* v_vs_90_; lean_object* v_children_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_vs_90_ = lean_ctor_get(v_val_75_, 0);
v_children_91_ = lean_ctor_get(v_val_75_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_val_75_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v_val_75_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_children_91_);
lean_inc(v_vs_90_);
lean_dec(v_val_75_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 0);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_vs_90_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_children_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object* v_t_101_){
_start:
{
lean_object* v_val_103_; 
switch(lean_obj_tag(v_t_101_))
{
case 2:
{
lean_object* v___x_106_; 
v___x_106_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_101_);
v_val_103_ = v___x_106_;
goto v___jp_102_;
}
case 3:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_101_);
v_val_103_ = v___x_107_;
goto v___jp_102_;
}
default: 
{
v_val_103_ = v_t_101_;
goto v___jp_102_;
}
}
v___jp_102_:
{
if (lean_obj_tag(v_val_103_) == 0)
{
lean_object* v___x_104_; 
lean_dec_ref_known(v_val_103_, 2);
v___x_104_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_104_;
}
else
{
lean_object* v_vs_105_; 
v_vs_105_ = lean_ctor_get(v_val_103_, 0);
lean_inc_ref(v_vs_105_);
lean_dec_ref_known(v_val_103_, 2);
return v_vs_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object* v_00_u03b1_108_, lean_object* v_t_109_){
_start:
{
lean_object* v_val_111_; 
switch(lean_obj_tag(v_t_109_))
{
case 2:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_109_);
v_val_111_ = v___x_114_;
goto v___jp_110_;
}
case 3:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_109_);
v_val_111_ = v___x_115_;
goto v___jp_110_;
}
default: 
{
v_val_111_ = v_t_109_;
goto v___jp_110_;
}
}
v___jp_110_:
{
if (lean_obj_tag(v_val_111_) == 0)
{
lean_object* v___x_112_; 
lean_dec_ref_known(v_val_111_, 2);
v___x_112_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_112_;
}
else
{
lean_object* v_vs_113_; 
v_vs_113_ = lean_ctor_get(v_val_111_, 0);
lean_inc_ref(v_vs_113_);
lean_dec_ref_known(v_val_111_, 2);
return v_vs_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object* v_t_116_){
_start:
{
lean_object* v_val_118_; 
switch(lean_obj_tag(v_t_116_))
{
case 2:
{
lean_object* v___x_132_; 
v___x_132_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_116_);
v_val_118_ = v___x_132_;
goto v___jp_117_;
}
case 3:
{
lean_object* v___x_133_; 
v___x_133_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_116_);
v_val_118_ = v___x_133_;
goto v___jp_117_;
}
default: 
{
v_val_118_ = v_t_116_;
goto v___jp_117_;
}
}
v___jp_117_:
{
if (lean_obj_tag(v_val_118_) == 0)
{
lean_object* v_key_119_; lean_object* v_child_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_key_119_ = lean_ctor_get(v_val_118_, 0);
v_child_120_ = lean_ctor_get(v_val_118_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_val_118_);
if (v_isSharedCheck_130_ == 0)
{
v___x_122_ = v_val_118_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_child_120_);
lean_inc(v_key_119_);
lean_dec(v_val_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_key_119_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_child_120_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_mk_empty_array_with_capacity(v___x_126_);
v___x_128_ = lean_array_push(v___x_127_, v___x_125_);
return v___x_128_;
}
}
}
else
{
lean_object* v_children_131_; 
v_children_131_ = lean_ctor_get(v_val_118_, 1);
lean_inc_ref(v_children_131_);
lean_dec_ref_known(v_val_118_, 2);
return v_children_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object* v_00_u03b1_134_, lean_object* v_t_135_){
_start:
{
lean_object* v_val_137_; 
switch(lean_obj_tag(v_t_135_))
{
case 2:
{
lean_object* v___x_151_; 
v___x_151_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_135_);
v_val_137_ = v___x_151_;
goto v___jp_136_;
}
case 3:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_135_);
v_val_137_ = v___x_152_;
goto v___jp_136_;
}
default: 
{
v_val_137_ = v_t_135_;
goto v___jp_136_;
}
}
v___jp_136_:
{
if (lean_obj_tag(v_val_137_) == 0)
{
lean_object* v_key_138_; lean_object* v_child_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_149_; 
v_key_138_ = lean_ctor_get(v_val_137_, 0);
v_child_139_ = lean_ctor_get(v_val_137_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_val_137_);
if (v_isSharedCheck_149_ == 0)
{
v___x_141_ = v_val_137_;
v_isShared_142_ = v_isSharedCheck_149_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_child_139_);
lean_inc(v_key_138_);
lean_dec(v_val_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_149_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_key_138_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_child_139_);
v___x_144_ = v_reuseFailAlloc_148_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_array_push(v___x_146_, v___x_144_);
return v___x_147_;
}
}
}
else
{
lean_object* v_children_150_; 
v_children_150_ = lean_ctor_get(v_val_137_, 1);
lean_inc_ref(v_children_150_);
lean_dec_ref_known(v_val_137_, 2);
return v_children_150_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_hasChildren___redArg(lean_object* v_t_153_){
_start:
{
lean_object* v_val_155_; 
switch(lean_obj_tag(v_t_153_))
{
case 2:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_153_);
v_val_155_ = v___x_163_;
goto v___jp_154_;
}
case 3:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_153_);
v_val_155_ = v___x_164_;
goto v___jp_154_;
}
default: 
{
v_val_155_ = v_t_153_;
goto v___jp_154_;
}
}
v___jp_154_:
{
if (lean_obj_tag(v_val_155_) == 0)
{
uint8_t v___x_156_; 
lean_dec_ref_known(v_val_155_, 2);
v___x_156_ = 1;
return v___x_156_;
}
else
{
lean_object* v_children_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_children_157_ = lean_ctor_get(v_val_155_, 1);
lean_inc_ref(v_children_157_);
lean_dec_ref_known(v_val_155_, 2);
v___x_158_ = lean_array_get_size(v_children_157_);
lean_dec_ref(v_children_157_);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_nat_dec_eq(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
uint8_t v___x_161_; 
v___x_161_ = 1;
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_hasChildren___redArg___boxed(lean_object* v_t_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lean_Meta_DiscrTree_Trie_hasChildren___redArg(v_t_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_hasChildren(lean_object* v_00_u03b1_168_, lean_object* v_t_169_){
_start:
{
lean_object* v_val_171_; 
switch(lean_obj_tag(v_t_169_))
{
case 2:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_169_);
v_val_171_ = v___x_179_;
goto v___jp_170_;
}
case 3:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_169_);
v_val_171_ = v___x_180_;
goto v___jp_170_;
}
default: 
{
v_val_171_ = v_t_169_;
goto v___jp_170_;
}
}
v___jp_170_:
{
if (lean_obj_tag(v_val_171_) == 0)
{
uint8_t v___x_172_; 
lean_dec_ref_known(v_val_171_, 2);
v___x_172_ = 1;
return v___x_172_;
}
else
{
lean_object* v_children_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_children_173_ = lean_ctor_get(v_val_171_, 1);
lean_inc_ref(v_children_173_);
lean_dec_ref_known(v_val_171_, 2);
v___x_174_ = lean_array_get_size(v_children_173_);
lean_dec_ref(v_children_173_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_nat_dec_eq(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = 1;
return v___x_177_;
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_hasChildren___boxed(lean_object* v_00_u03b1_181_, lean_object* v_t_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Lean_Meta_DiscrTree_Trie_hasChildren(v_00_u03b1_181_, v_t_182_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_starChild_x3f___redArg(lean_object* v_t_185_){
_start:
{
lean_object* v_val_187_; 
switch(lean_obj_tag(v_t_185_))
{
case 2:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_185_);
v_val_187_ = v___x_206_;
goto v___jp_186_;
}
case 3:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_185_);
v_val_187_ = v___x_207_;
goto v___jp_186_;
}
default: 
{
v_val_187_ = v_t_185_;
goto v___jp_186_;
}
}
v___jp_186_:
{
if (lean_obj_tag(v_val_187_) == 0)
{
lean_object* v_key_188_; lean_object* v_child_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_key_188_ = lean_ctor_get(v_val_187_, 0);
lean_inc(v_key_188_);
v_child_189_ = lean_ctor_get(v_val_187_, 1);
lean_inc_ref(v_child_189_);
lean_dec_ref_known(v_val_187_, 2);
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_188_, v___x_190_);
lean_dec(v_key_188_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
lean_dec_ref(v_child_189_);
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_child_189_);
return v___x_193_;
}
}
else
{
lean_object* v_children_194_; lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_children_194_ = lean_ctor_get(v_val_187_, 1);
lean_inc_ref(v_children_194_);
lean_dec_ref_known(v_val_187_, 2);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_array_get_size(v_children_194_);
v___x_197_ = lean_nat_dec_lt(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_dec_ref(v_children_194_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___x_199_; lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_199_ = lean_array_fget(v_children_194_, v___x_195_);
lean_dec_ref(v_children_194_);
v_fst_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_fst_200_);
v_snd_201_ = lean_ctor_get(v___x_199_, 1);
lean_inc(v_snd_201_);
lean_dec(v___x_199_);
v___x_202_ = lean_box(0);
v___x_203_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_200_, v___x_202_);
lean_dec(v_fst_200_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_snd_201_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_snd_201_);
return v___x_205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_starChild_x3f(lean_object* v_00_u03b1_208_, lean_object* v_t_209_){
_start:
{
lean_object* v_val_211_; 
switch(lean_obj_tag(v_t_209_))
{
case 2:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_209_);
v_val_211_ = v___x_230_;
goto v___jp_210_;
}
case 3:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_209_);
v_val_211_ = v___x_231_;
goto v___jp_210_;
}
default: 
{
v_val_211_ = v_t_209_;
goto v___jp_210_;
}
}
v___jp_210_:
{
if (lean_obj_tag(v_val_211_) == 0)
{
lean_object* v_key_212_; lean_object* v_child_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_key_212_ = lean_ctor_get(v_val_211_, 0);
lean_inc(v_key_212_);
v_child_213_ = lean_ctor_get(v_val_211_, 1);
lean_inc_ref(v_child_213_);
lean_dec_ref_known(v_val_211_, 2);
v___x_214_ = lean_box(0);
v___x_215_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_212_, v___x_214_);
lean_dec(v_key_212_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
lean_dec_ref(v_child_213_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_child_213_);
return v___x_217_;
}
}
else
{
lean_object* v_children_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_children_218_ = lean_ctor_get(v_val_211_, 1);
lean_inc_ref(v_children_218_);
lean_dec_ref_known(v_val_211_, 2);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_array_get_size(v_children_218_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec_ref(v_children_218_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_223_ = lean_array_fget(v_children_218_, v___x_219_);
lean_dec_ref(v_children_218_);
v_fst_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v___x_223_, 1);
lean_inc(v_snd_225_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v___x_227_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_224_, v___x_226_);
lean_dec(v_fst_224_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v_snd_225_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v_snd_225_);
return v___x_229_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___lam__0(lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v_fst_234_; lean_object* v_fst_235_; uint8_t v___x_236_; 
v_fst_234_ = lean_ctor_get(v_a_232_, 0);
v_fst_235_ = lean_ctor_get(v_b_233_, 0);
v___x_236_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_234_, v_fst_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___lam__0___boxed(lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___lam__0(v_a_237_, v_b_238_);
lean_dec_ref(v_b_238_);
lean_dec_ref(v_a_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg(lean_object* v_t_245_, lean_object* v_k_246_){
_start:
{
lean_object* v___f_247_; lean_object* v_val_249_; 
v___f_247_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__0));
switch(lean_obj_tag(v_t_245_))
{
case 2:
{
lean_object* v___x_285_; 
v___x_285_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_245_);
v_val_249_ = v___x_285_;
goto v___jp_248_;
}
case 3:
{
lean_object* v___x_286_; 
v___x_286_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_245_);
v_val_249_ = v___x_286_;
goto v___jp_248_;
}
default: 
{
v_val_249_ = v_t_245_;
goto v___jp_248_;
}
}
v___jp_248_:
{
if (lean_obj_tag(v_val_249_) == 0)
{
lean_object* v_key_250_; lean_object* v_child_251_; uint8_t v___x_252_; 
v_key_250_ = lean_ctor_get(v_val_249_, 0);
lean_inc(v_key_250_);
v_child_251_ = lean_ctor_get(v_val_249_, 1);
lean_inc_ref(v_child_251_);
lean_dec_ref_known(v_val_249_, 2);
v___x_252_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_250_, v_k_246_);
lean_dec(v_k_246_);
lean_dec(v_key_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v_child_251_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_child_251_);
return v___x_254_;
}
}
else
{
lean_object* v_children_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_283_; 
v_children_255_ = lean_ctor_get(v_val_249_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_val_249_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_val_249_, 0);
lean_dec(v_unused_284_);
v___x_257_ = v_val_249_;
v_isShared_258_ = v_isSharedCheck_283_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_children_255_);
lean_dec(v_val_249_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_283_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_array_get_size(v_children_255_);
v___x_261_ = lean_nat_dec_lt(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_del_object(v___x_257_);
lean_dec_ref(v_children_255_);
lean_dec(v_k_246_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_sub(v___x_260_, v___x_263_);
v___x_265_ = lean_nat_dec_le(v___x_259_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
lean_dec(v___x_264_);
lean_del_object(v___x_257_);
lean_dec_ref(v_children_255_);
lean_dec(v_k_246_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__1));
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 0);
lean_ctor_set(v___x_257_, 1, v___x_267_);
lean_ctor_set(v___x_257_, 0, v_k_246_);
v___x_269_ = v___x_257_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_k_246_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_267_);
v___x_269_ = v_reuseFailAlloc_282_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__2));
v___x_271_ = l_Array_binSearchAux___redArg(v___f_247_, v___x_270_, v_children_255_, v___x_269_, v___x_259_, v___x_264_);
lean_dec_ref(v_children_255_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
else
{
lean_object* v_val_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_val_273_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_281_ == 0)
{
v___x_275_ = v___x_271_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_val_273_);
lean_dec(v___x_271_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v_snd_277_; lean_object* v___x_279_; 
v_snd_277_ = lean_ctor_get(v_val_273_, 1);
lean_inc(v_snd_277_);
lean_dec(v_val_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_snd_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_snd_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_findChild_x3f(lean_object* v_00_u03b1_287_, lean_object* v_t_288_, lean_object* v_k_289_){
_start:
{
lean_object* v___f_290_; lean_object* v_val_292_; 
v___f_290_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__0));
switch(lean_obj_tag(v_t_288_))
{
case 2:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_288_);
v_val_292_ = v___x_328_;
goto v___jp_291_;
}
case 3:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_288_);
v_val_292_ = v___x_329_;
goto v___jp_291_;
}
default: 
{
v_val_292_ = v_t_288_;
goto v___jp_291_;
}
}
v___jp_291_:
{
if (lean_obj_tag(v_val_292_) == 0)
{
lean_object* v_key_293_; lean_object* v_child_294_; uint8_t v___x_295_; 
v_key_293_ = lean_ctor_get(v_val_292_, 0);
lean_inc(v_key_293_);
v_child_294_ = lean_ctor_get(v_val_292_, 1);
lean_inc_ref(v_child_294_);
lean_dec_ref_known(v_val_292_, 2);
v___x_295_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_293_, v_k_289_);
lean_dec(v_k_289_);
lean_dec(v_key_293_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v_child_294_);
v___x_296_ = lean_box(0);
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_child_294_);
return v___x_297_;
}
}
else
{
lean_object* v_children_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_326_; 
v_children_298_ = lean_ctor_get(v_val_292_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_val_292_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v_val_292_, 0);
lean_dec(v_unused_327_);
v___x_300_ = v_val_292_;
v_isShared_301_ = v_isSharedCheck_326_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_children_298_);
lean_dec(v_val_292_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_326_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_get_size(v_children_298_);
v___x_304_ = lean_nat_dec_lt(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_del_object(v___x_300_);
lean_dec_ref(v_children_298_);
lean_dec(v_k_289_);
v___x_305_ = lean_box(0);
return v___x_305_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_sub(v___x_303_, v___x_306_);
v___x_308_ = lean_nat_dec_le(v___x_302_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v___x_307_);
lean_del_object(v___x_300_);
lean_dec_ref(v_children_298_);
lean_dec(v_k_289_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__1));
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 0);
lean_ctor_set(v___x_300_, 1, v___x_310_);
lean_ctor_set(v___x_300_, 0, v_k_289_);
v___x_312_ = v___x_300_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_k_289_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_325_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__2));
v___x_314_ = l_Array_binSearchAux___redArg(v___f_290_, v___x_313_, v_children_298_, v___x_312_, v___x_302_, v___x_307_);
lean_dec_ref(v_children_298_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
return v___x_315_;
}
else
{
lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_val_316_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_314_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_dec(v___x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_snd_320_; lean_object* v___x_322_; 
v_snd_320_ = lean_ctor_get(v_val_316_, 1);
lean_inc(v_snd_320_);
lean_dec(v_val_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_snd_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_snd_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldChildrenM___redArg___lam__0(lean_object* v_f_330_, lean_object* v_s_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_335_; 
v_fst_333_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v_x_332_, 1);
lean_inc(v_snd_334_);
lean_dec_ref(v_x_332_);
v___x_335_ = lean_apply_3(v_f_330_, v_s_331_, v_fst_333_, v_snd_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldChildrenM___redArg(lean_object* v_inst_336_, lean_object* v_f_337_, lean_object* v_init_338_, lean_object* v_t_339_){
_start:
{
lean_object* v___f_340_; lean_object* v_val_342_; 
lean_inc(v_f_337_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldChildrenM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_340_, 0, v_f_337_);
switch(lean_obj_tag(v_t_339_))
{
case 2:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_339_);
v_val_342_ = v___x_356_;
goto v___jp_341_;
}
case 3:
{
lean_object* v___x_357_; 
v___x_357_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_339_);
v_val_342_ = v___x_357_;
goto v___jp_341_;
}
default: 
{
v_val_342_ = v_t_339_;
goto v___jp_341_;
}
}
v___jp_341_:
{
if (lean_obj_tag(v_val_342_) == 0)
{
lean_object* v_key_343_; lean_object* v_child_344_; lean_object* v___x_345_; 
lean_dec_ref(v___f_340_);
lean_dec_ref(v_inst_336_);
v_key_343_ = lean_ctor_get(v_val_342_, 0);
lean_inc(v_key_343_);
v_child_344_ = lean_ctor_get(v_val_342_, 1);
lean_inc_ref(v_child_344_);
lean_dec_ref_known(v_val_342_, 2);
v___x_345_ = lean_apply_3(v_f_337_, v_init_338_, v_key_343_, v_child_344_);
return v___x_345_;
}
else
{
lean_object* v_toApplicative_346_; lean_object* v_children_347_; lean_object* v_toPure_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
lean_dec(v_f_337_);
v_toApplicative_346_ = lean_ctor_get(v_inst_336_, 0);
v_children_347_ = lean_ctor_get(v_val_342_, 1);
lean_inc_ref(v_children_347_);
lean_dec_ref_known(v_val_342_, 2);
v_toPure_348_ = lean_ctor_get(v_toApplicative_346_, 1);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_array_get_size(v_children_347_);
v___x_351_ = lean_nat_dec_lt(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_inc(v_toPure_348_);
lean_dec_ref(v_children_347_);
lean_dec_ref(v___f_340_);
lean_dec_ref(v_inst_336_);
v___x_352_ = lean_apply_2(v_toPure_348_, lean_box(0), v_init_338_);
return v___x_352_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_350_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_336_, v___f_340_, v_children_347_, v___x_353_, v___x_354_, v_init_338_);
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldChildrenM(lean_object* v_m_358_, lean_object* v_00_u03c3_359_, lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_f_362_, lean_object* v_init_363_, lean_object* v_t_364_){
_start:
{
lean_object* v___f_365_; lean_object* v_val_367_; 
lean_inc(v_f_362_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldChildrenM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_365_, 0, v_f_362_);
switch(lean_obj_tag(v_t_364_))
{
case 2:
{
lean_object* v___x_381_; 
v___x_381_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_364_);
v_val_367_ = v___x_381_;
goto v___jp_366_;
}
case 3:
{
lean_object* v___x_382_; 
v___x_382_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_364_);
v_val_367_ = v___x_382_;
goto v___jp_366_;
}
default: 
{
v_val_367_ = v_t_364_;
goto v___jp_366_;
}
}
v___jp_366_:
{
if (lean_obj_tag(v_val_367_) == 0)
{
lean_object* v_key_368_; lean_object* v_child_369_; lean_object* v___x_370_; 
lean_dec_ref(v___f_365_);
lean_dec_ref(v_inst_361_);
v_key_368_ = lean_ctor_get(v_val_367_, 0);
lean_inc(v_key_368_);
v_child_369_ = lean_ctor_get(v_val_367_, 1);
lean_inc_ref(v_child_369_);
lean_dec_ref_known(v_val_367_, 2);
v___x_370_ = lean_apply_3(v_f_362_, v_init_363_, v_key_368_, v_child_369_);
return v___x_370_;
}
else
{
lean_object* v_toApplicative_371_; lean_object* v_children_372_; lean_object* v_toPure_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
lean_dec(v_f_362_);
v_toApplicative_371_ = lean_ctor_get(v_inst_361_, 0);
v_children_372_ = lean_ctor_get(v_val_367_, 1);
lean_inc_ref(v_children_372_);
lean_dec_ref_known(v_val_367_, 2);
v_toPure_373_ = lean_ctor_get(v_toApplicative_371_, 1);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_array_get_size(v_children_372_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_inc(v_toPure_373_);
lean_dec_ref(v_children_372_);
lean_dec_ref(v___f_365_);
lean_dec_ref(v_inst_361_);
v___x_377_ = lean_apply_2(v_toPure_373_, lean_box(0), v_init_363_);
return v___x_377_;
}
else
{
size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; 
v___x_378_ = ((size_t)0ULL);
v___x_379_ = lean_usize_of_nat(v___x_375_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_361_, v___f_365_, v_children_372_, v___x_378_, v___x_379_, v_init_363_);
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0___boxed(lean_object* v___x_383_, lean_object* v_toPure_384_, lean_object* v_i_385_, lean_object* v___x_386_, lean_object* v_inst_387_, lean_object* v_next_388_, lean_object* v_ks_389_, lean_object* v_____x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0(v___x_383_, v_toPure_384_, v_i_385_, v___x_386_, v_inst_387_, v_next_388_, v_ks_389_, v_____x_390_);
lean_dec(v___x_386_);
lean_dec(v_i_385_);
lean_dec(v___x_383_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(lean_object* v_inst_392_, lean_object* v_next_393_, lean_object* v_todo_394_, lean_object* v_ks_395_, lean_object* v_i_396_){
_start:
{
lean_object* v_toApplicative_397_; lean_object* v_toBind_398_; lean_object* v_toPure_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_toApplicative_397_ = lean_ctor_get(v_inst_392_, 0);
v_toBind_398_ = lean_ctor_get(v_inst_392_, 1);
v_toPure_399_ = lean_ctor_get(v_toApplicative_397_, 1);
v___x_400_ = lean_array_get_size(v_ks_395_);
v___x_401_ = lean_nat_dec_lt(v_i_396_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_inc(v_toPure_399_);
lean_dec(v_i_396_);
lean_dec_ref(v_ks_395_);
lean_dec(v_next_393_);
lean_dec_ref(v_inst_392_);
v___x_402_ = lean_array_get_size(v_todo_394_);
lean_dec_ref(v_todo_394_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_nat_dec_eq(v___x_402_, v___x_403_);
v___x_405_ = lean_box(v___x_404_);
v___x_406_ = lean_apply_2(v_toPure_399_, lean_box(0), v___x_405_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_array_get_size(v_todo_394_);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_nat_dec_eq(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_e_413_; lean_object* v_todo_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_410_ = l_Lean_instInhabitedExpr;
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_sub(v___x_407_, v___x_411_);
v_e_413_ = lean_array_get(v___x_410_, v_todo_394_, v___x_412_);
lean_dec(v___x_412_);
v_todo_414_ = lean_array_pop(v_todo_394_);
v___x_415_ = lean_array_fget_borrowed(v_ks_395_, v_i_396_);
v___x_416_ = lean_box(0);
v___x_417_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc(v___x_415_);
lean_inc(v_toPure_399_);
lean_inc(v_toBind_398_);
lean_inc(v_next_393_);
v___f_418_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_418_, 0, v___x_415_);
lean_closure_set(v___f_418_, 1, v_toPure_399_);
lean_closure_set(v___f_418_, 2, v_i_396_);
lean_closure_set(v___f_418_, 3, v___x_411_);
lean_closure_set(v___f_418_, 4, v_inst_392_);
lean_closure_set(v___f_418_, 5, v_next_393_);
lean_closure_set(v___f_418_, 6, v_ks_395_);
v___x_419_ = lean_apply_2(v_next_393_, v_e_413_, v_todo_414_);
v___x_420_ = lean_apply_4(v_toBind_398_, lean_box(0), lean_box(0), v___x_419_, v___f_418_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; 
lean_dec(v_e_413_);
v___x_421_ = lean_nat_add(v_i_396_, v___x_411_);
lean_dec(v_i_396_);
v_todo_394_ = v_todo_414_;
v_i_396_ = v___x_421_;
goto _start;
}
}
else
{
uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_inc(v_toPure_399_);
lean_dec(v_i_396_);
lean_dec_ref(v_ks_395_);
lean_dec_ref(v_todo_394_);
lean_dec(v_next_393_);
lean_dec_ref(v_inst_392_);
v___x_423_ = 0;
v___x_424_ = lean_box(v___x_423_);
v___x_425_ = lean_apply_2(v_toPure_399_, lean_box(0), v___x_424_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0(lean_object* v___x_426_, lean_object* v_toPure_427_, lean_object* v_i_428_, lean_object* v___x_429_, lean_object* v_inst_430_, lean_object* v_next_431_, lean_object* v_ks_432_, lean_object* v_____x_433_){
_start:
{
lean_object* v_fst_434_; lean_object* v_snd_435_; uint8_t v___x_436_; 
v_fst_434_ = lean_ctor_get(v_____x_433_, 0);
lean_inc(v_fst_434_);
v_snd_435_ = lean_ctor_get(v_____x_433_, 1);
lean_inc(v_snd_435_);
lean_dec_ref(v_____x_433_);
v___x_436_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_426_, v_fst_434_);
lean_dec(v_fst_434_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_snd_435_);
lean_dec_ref(v_ks_432_);
lean_dec(v_next_431_);
lean_dec_ref(v_inst_430_);
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_apply_2(v_toPure_427_, lean_box(0), v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_toPure_427_);
v___x_439_ = lean_nat_add(v_i_428_, v___x_429_);
v___x_440_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(v_inst_430_, v_next_431_, v_snd_435_, v_ks_432_, v___x_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix(lean_object* v_m_441_, lean_object* v_inst_442_, lean_object* v_next_443_, lean_object* v_todo_444_, lean_object* v_ks_445_, lean_object* v_i_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(v_inst_442_, v_next_443_, v_todo_444_, v_ks_445_, v_i_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter___redArg(lean_object* v_x_448_, lean_object* v_h__1_449_){
_start:
{
lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_452_; 
v_fst_450_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_fst_450_);
v_snd_451_ = lean_ctor_get(v_x_448_, 1);
lean_inc(v_snd_451_);
lean_dec_ref(v_x_448_);
v___x_452_ = lean_apply_2(v_h__1_449_, v_fst_450_, v_snd_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter(lean_object* v_motive_453_, lean_object* v_x_454_, lean_object* v_h__1_455_){
_start:
{
lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_458_; 
v_fst_456_ = lean_ctor_get(v_x_454_, 0);
lean_inc(v_fst_456_);
v_snd_457_ = lean_ctor_get(v_x_454_, 1);
lean_inc(v_snd_457_);
lean_dec_ref(v_x_454_);
v___x_458_ = lean_apply_2(v_h__1_455_, v_fst_456_, v_snd_457_);
return v___x_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_t_459_){
_start:
{
lean_object* v_val_461_; 
switch(lean_obj_tag(v_t_459_))
{
case 2:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_459_);
v_val_461_ = v___x_470_;
goto v___jp_460_;
}
case 3:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_459_);
v_val_461_ = v___x_471_;
goto v___jp_460_;
}
default: 
{
v_val_461_ = v_t_459_;
goto v___jp_460_;
}
}
v___jp_460_:
{
if (lean_obj_tag(v_val_461_) == 0)
{
uint8_t v___x_462_; 
lean_dec_ref_known(v_val_461_, 2);
v___x_462_ = 0;
return v___x_462_;
}
else
{
lean_object* v_vs_463_; lean_object* v_children_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_vs_463_ = lean_ctor_get(v_val_461_, 0);
lean_inc_ref(v_vs_463_);
v_children_464_ = lean_ctor_get(v_val_461_, 1);
lean_inc_ref(v_children_464_);
lean_dec_ref_known(v_val_461_, 2);
v___x_465_ = lean_array_get_size(v_vs_463_);
lean_dec_ref(v_vs_463_);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_nat_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_dec_ref(v_children_464_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_array_get_size(v_children_464_);
lean_dec_ref(v_children_464_);
v___x_469_ = lean_nat_dec_eq(v___x_468_, v___x_466_);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_t_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_t_472_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_475_, lean_object* v_t_476_){
_start:
{
lean_object* v_val_478_; 
switch(lean_obj_tag(v_t_476_))
{
case 2:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_476_);
v_val_478_ = v___x_487_;
goto v___jp_477_;
}
case 3:
{
lean_object* v___x_488_; 
v___x_488_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_476_);
v_val_478_ = v___x_488_;
goto v___jp_477_;
}
default: 
{
v_val_478_ = v_t_476_;
goto v___jp_477_;
}
}
v___jp_477_:
{
if (lean_obj_tag(v_val_478_) == 0)
{
uint8_t v___x_479_; 
lean_dec_ref_known(v_val_478_, 2);
v___x_479_ = 0;
return v___x_479_;
}
else
{
lean_object* v_vs_480_; lean_object* v_children_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_vs_480_ = lean_ctor_get(v_val_478_, 0);
lean_inc_ref(v_vs_480_);
v_children_481_ = lean_ctor_get(v_val_478_, 1);
lean_inc_ref(v_children_481_);
lean_dec_ref_known(v_val_478_, 2);
v___x_482_ = lean_array_get_size(v_vs_480_);
lean_dec_ref(v_vs_480_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_dec_ref(v_children_481_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_array_get_size(v_children_481_);
lean_dec_ref(v_children_481_);
v___x_486_ = lean_nat_dec_eq(v___x_485_, v___x_483_);
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_489_, lean_object* v_t_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_489_, v_t_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__3(lean_object* v_f_493_, lean_object* v_initialKeys_494_, lean_object* v_s_495_, lean_object* v_v_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_apply_3(v_f_493_, v_s_495_, v_initialKeys_494_, v_v_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(lean_object* v___f_498_, lean_object* v_s_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_503_; 
v_fst_501_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_fst_501_);
v_snd_502_ = lean_ctor_get(v_x_500_, 1);
lean_inc(v_snd_502_);
lean_dec_ref(v_x_500_);
v___x_503_ = lean_apply_3(v___f_498_, v_s_499_, v_fst_501_, v_snd_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object* v___f_504_, lean_object* v_toApplicative_505_, lean_object* v_inst_506_, lean_object* v___f_507_, lean_object* v_t_508_, lean_object* v_s_509_){
_start:
{
lean_object* v_val_511_; 
switch(lean_obj_tag(v_t_508_))
{
case 2:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_508_);
v_val_511_ = v___x_524_;
goto v___jp_510_;
}
case 3:
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_508_);
v_val_511_ = v___x_525_;
goto v___jp_510_;
}
default: 
{
v_val_511_ = v_t_508_;
goto v___jp_510_;
}
}
v___jp_510_:
{
if (lean_obj_tag(v_val_511_) == 0)
{
lean_object* v_key_512_; lean_object* v_child_513_; lean_object* v___x_514_; 
lean_dec(v___f_507_);
lean_dec_ref(v_inst_506_);
lean_dec_ref(v_toApplicative_505_);
v_key_512_ = lean_ctor_get(v_val_511_, 0);
lean_inc(v_key_512_);
v_child_513_ = lean_ctor_get(v_val_511_, 1);
lean_inc_ref(v_child_513_);
lean_dec_ref_known(v_val_511_, 2);
v___x_514_ = lean_apply_3(v___f_504_, v_s_509_, v_key_512_, v_child_513_);
return v___x_514_;
}
else
{
lean_object* v_children_515_; lean_object* v_toPure_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
lean_dec(v___f_504_);
v_children_515_ = lean_ctor_get(v_val_511_, 1);
lean_inc_ref(v_children_515_);
lean_dec_ref_known(v_val_511_, 2);
v_toPure_516_ = lean_ctor_get(v_toApplicative_505_, 1);
lean_inc(v_toPure_516_);
lean_dec_ref(v_toApplicative_505_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = lean_array_get_size(v_children_515_);
v___x_519_ = lean_nat_dec_lt(v___x_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_dec_ref(v_children_515_);
lean_dec(v___f_507_);
lean_dec_ref(v_inst_506_);
v___x_520_ = lean_apply_2(v_toPure_516_, lean_box(0), v_s_509_);
return v___x_520_;
}
else
{
size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
lean_dec(v_toPure_516_);
v___x_521_ = ((size_t)0ULL);
v___x_522_ = lean_usize_of_nat(v___x_518_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_506_, v___f_507_, v_children_515_, v___x_521_, v___x_522_, v_s_509_);
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object* v_inst_526_, lean_object* v_initialKeys_527_, lean_object* v_f_528_, lean_object* v_init_529_, lean_object* v_t_530_){
_start:
{
if (lean_obj_tag(v_t_530_) == 3)
{
lean_object* v_keys_531_; lean_object* v_i_532_; lean_object* v_v_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v_inst_526_);
v_keys_531_ = lean_ctor_get(v_t_530_, 0);
lean_inc_ref(v_keys_531_);
v_i_532_ = lean_ctor_get(v_t_530_, 1);
lean_inc(v_i_532_);
v_v_533_ = lean_ctor_get(v_t_530_, 2);
lean_inc(v_v_533_);
lean_dec_ref_known(v_t_530_, 3);
v___x_534_ = lean_array_get_size(v_keys_531_);
v___x_535_ = l_Array_extract___redArg(v_keys_531_, v_i_532_, v___x_534_);
lean_dec_ref(v_keys_531_);
v___x_536_ = l_Array_append___redArg(v_initialKeys_527_, v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = lean_apply_3(v_f_528_, v_init_529_, v___x_536_, v_v_533_);
return v___x_537_;
}
else
{
lean_object* v_toApplicative_538_; lean_object* v_toBind_539_; lean_object* v___f_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___f_543_; lean_object* v___y_545_; lean_object* v_val_557_; 
v_toApplicative_538_ = lean_ctor_get(v_inst_526_, 0);
v_toBind_539_ = lean_ctor_get(v_inst_526_, 1);
lean_inc(v_toBind_539_);
lean_inc(v_f_528_);
lean_inc_ref_n(v_inst_526_, 2);
lean_inc_ref(v_initialKeys_527_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0), 6, 3);
lean_closure_set(v___f_540_, 0, v_initialKeys_527_);
lean_closure_set(v___f_540_, 1, v_inst_526_);
lean_closure_set(v___f_540_, 2, v_f_528_);
lean_inc_ref(v___f_540_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1), 3, 1);
lean_closure_set(v___f_541_, 0, v___f_540_);
lean_inc_ref(v_t_530_);
lean_inc_ref(v_toApplicative_538_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_542_, 0, v___f_540_);
lean_closure_set(v___f_542_, 1, v_toApplicative_538_);
lean_closure_set(v___f_542_, 2, v_inst_526_);
lean_closure_set(v___f_542_, 3, v___f_541_);
lean_closure_set(v___f_542_, 4, v_t_530_);
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_543_, 0, v_f_528_);
lean_closure_set(v___f_543_, 1, v_initialKeys_527_);
switch(lean_obj_tag(v_t_530_))
{
case 2:
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_530_);
v_val_557_ = v___x_560_;
goto v___jp_556_;
}
case 3:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_530_);
v_val_557_ = v___x_561_;
goto v___jp_556_;
}
default: 
{
v_val_557_ = v_t_530_;
goto v___jp_556_;
}
}
v___jp_544_:
{
lean_object* v_toPure_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_toPure_546_ = lean_ctor_get(v_toApplicative_538_, 1);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v___y_545_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_inc(v_toPure_546_);
lean_dec_ref(v___y_545_);
lean_dec_ref(v___f_543_);
lean_dec_ref(v_inst_526_);
v___x_550_ = lean_apply_2(v_toPure_546_, lean_box(0), v_init_529_);
v___x_551_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_550_, v___f_542_);
return v___x_551_;
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_548_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_526_, v___f_543_, v___y_545_, v___x_552_, v___x_553_, v_init_529_);
v___x_555_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_554_, v___f_542_);
return v___x_555_;
}
}
v___jp_556_:
{
if (lean_obj_tag(v_val_557_) == 0)
{
lean_object* v___x_558_; 
lean_dec_ref_known(v_val_557_, 2);
v___x_558_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_545_ = v___x_558_;
goto v___jp_544_;
}
else
{
lean_object* v_vs_559_; 
v_vs_559_ = lean_ctor_get(v_val_557_, 0);
lean_inc_ref(v_vs_559_);
lean_dec_ref_known(v_val_557_, 2);
v___y_545_ = v_vs_559_;
goto v___jp_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object* v_initialKeys_562_, lean_object* v_inst_563_, lean_object* v_f_564_, lean_object* v_s_565_, lean_object* v_k_566_, lean_object* v_c_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_array_push(v_initialKeys_562_, v_k_566_);
v___x_569_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_563_, v___x_568_, v_f_564_, v_s_565_, v_c_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object* v_m_570_, lean_object* v_00_u03c3_571_, lean_object* v_00_u03b1_572_, lean_object* v_inst_573_, lean_object* v_initialKeys_574_, lean_object* v_f_575_, lean_object* v_init_576_, lean_object* v_t_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_573_, v_initialKeys_574_, v_f_575_, v_init_576_, v_t_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object* v_f_579_, lean_object* v_s_580_, lean_object* v_k_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_apply_3(v_f_579_, v_s_580_, v_k_581_, v_a_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object* v_initialKeys_603_, lean_object* v_f_604_, lean_object* v_init_605_, lean_object* v_t_606_){
_start:
{
lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___f_607_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_607_, 0, v_f_604_);
v___x_608_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_609_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_608_, v_initialKeys_603_, v___f_607_, v_init_605_, v_t_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object* v_00_u03c3_610_, lean_object* v_00_u03b1_611_, lean_object* v_initialKeys_612_, lean_object* v_f_613_, lean_object* v_init_614_, lean_object* v_t_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___f_616_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_616_, 0, v_f_613_);
v___x_617_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_618_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_617_, v_initialKeys_612_, v___f_616_, v_init_614_, v_t_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__1(lean_object* v_inst_619_, lean_object* v_f_620_, lean_object* v_toApplicative_621_, lean_object* v___f_622_, lean_object* v_t_623_, lean_object* v_s_624_){
_start:
{
lean_object* v_val_626_; 
switch(lean_obj_tag(v_t_623_))
{
case 2:
{
lean_object* v___x_638_; 
v___x_638_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_623_);
v_val_626_ = v___x_638_;
goto v___jp_625_;
}
case 3:
{
lean_object* v___x_639_; 
v___x_639_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_623_);
v_val_626_ = v___x_639_;
goto v___jp_625_;
}
default: 
{
v_val_626_ = v_t_623_;
goto v___jp_625_;
}
}
v___jp_625_:
{
if (lean_obj_tag(v_val_626_) == 0)
{
lean_object* v_child_627_; lean_object* v___x_628_; 
lean_dec(v___f_622_);
lean_dec_ref(v_toApplicative_621_);
v_child_627_ = lean_ctor_get(v_val_626_, 1);
lean_inc_ref(v_child_627_);
lean_dec_ref_known(v_val_626_, 2);
v___x_628_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_619_, v_f_620_, v_s_624_, v_child_627_);
return v___x_628_;
}
else
{
lean_object* v_children_629_; lean_object* v_toPure_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
lean_dec(v_f_620_);
v_children_629_ = lean_ctor_get(v_val_626_, 1);
lean_inc_ref(v_children_629_);
lean_dec_ref_known(v_val_626_, 2);
v_toPure_630_ = lean_ctor_get(v_toApplicative_621_, 1);
lean_inc(v_toPure_630_);
lean_dec_ref(v_toApplicative_621_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_array_get_size(v_children_629_);
v___x_633_ = lean_nat_dec_lt(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec_ref(v_children_629_);
lean_dec(v___f_622_);
lean_dec_ref(v_inst_619_);
v___x_634_ = lean_apply_2(v_toPure_630_, lean_box(0), v_s_624_);
return v___x_634_;
}
else
{
size_t v___x_635_; size_t v___x_636_; lean_object* v___x_637_; 
lean_dec(v_toPure_630_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = lean_usize_of_nat(v___x_632_);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_619_, v___f_622_, v_children_629_, v___x_635_, v___x_636_, v_s_624_);
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object* v_inst_640_, lean_object* v_f_641_, lean_object* v_init_642_, lean_object* v_t_643_){
_start:
{
if (lean_obj_tag(v_t_643_) == 3)
{
lean_object* v_v_644_; lean_object* v___x_645_; 
lean_dec_ref(v_inst_640_);
v_v_644_ = lean_ctor_get(v_t_643_, 2);
lean_inc(v_v_644_);
lean_dec_ref_known(v_t_643_, 3);
v___x_645_ = lean_apply_2(v_f_641_, v_init_642_, v_v_644_);
return v___x_645_;
}
else
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v___f_648_; lean_object* v___f_649_; lean_object* v___y_651_; lean_object* v_val_663_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_640_, 0);
v_toBind_647_ = lean_ctor_get(v_inst_640_, 1);
lean_inc(v_toBind_647_);
lean_inc_n(v_f_641_, 2);
lean_inc_ref_n(v_inst_640_, 2);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_648_, 0, v_inst_640_);
lean_closure_set(v___f_648_, 1, v_f_641_);
lean_inc_ref(v_t_643_);
lean_inc_ref(v_toApplicative_646_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_649_, 0, v_inst_640_);
lean_closure_set(v___f_649_, 1, v_f_641_);
lean_closure_set(v___f_649_, 2, v_toApplicative_646_);
lean_closure_set(v___f_649_, 3, v___f_648_);
lean_closure_set(v___f_649_, 4, v_t_643_);
switch(lean_obj_tag(v_t_643_))
{
case 2:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_643_);
v_val_663_ = v___x_666_;
goto v___jp_662_;
}
case 3:
{
lean_object* v___x_667_; 
v___x_667_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_643_);
v_val_663_ = v___x_667_;
goto v___jp_662_;
}
default: 
{
v_val_663_ = v_t_643_;
goto v___jp_662_;
}
}
v___jp_650_:
{
lean_object* v_toPure_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_toPure_652_ = lean_ctor_get(v_toApplicative_646_, 1);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_array_get_size(v___y_651_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_inc(v_toPure_652_);
lean_dec_ref(v___y_651_);
lean_dec(v_f_641_);
lean_dec_ref(v_inst_640_);
v___x_656_ = lean_apply_2(v_toPure_652_, lean_box(0), v_init_642_);
v___x_657_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v___x_656_, v___f_649_);
return v___x_657_;
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_654_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_640_, v_f_641_, v___y_651_, v___x_658_, v___x_659_, v_init_642_);
v___x_661_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v___x_660_, v___f_649_);
return v___x_661_;
}
}
v___jp_662_:
{
if (lean_obj_tag(v_val_663_) == 0)
{
lean_object* v___x_664_; 
lean_dec_ref_known(v_val_663_, 2);
v___x_664_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_651_ = v___x_664_;
goto v___jp_650_;
}
else
{
lean_object* v_vs_665_; 
v_vs_665_ = lean_ctor_get(v_val_663_, 0);
lean_inc_ref(v_vs_665_);
lean_dec_ref_known(v_val_663_, 2);
v___y_651_ = v_vs_665_;
goto v___jp_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object* v_inst_668_, lean_object* v_f_669_, lean_object* v_s_670_, lean_object* v_x_671_){
_start:
{
lean_object* v_snd_672_; lean_object* v___x_673_; 
v_snd_672_ = lean_ctor_get(v_x_671_, 1);
lean_inc(v_snd_672_);
lean_dec_ref(v_x_671_);
v___x_673_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_668_, v_f_669_, v_s_670_, v_snd_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object* v_m_674_, lean_object* v_00_u03c3_675_, lean_object* v_00_u03b1_676_, lean_object* v_inst_677_, lean_object* v_f_678_, lean_object* v_init_679_, lean_object* v_t_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_677_, v_f_678_, v_init_679_, v_t_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object* v_f_682_, lean_object* v_x1_683_, lean_object* v_x2_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_apply_2(v_f_682_, v_x1_683_, v_x2_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object* v_f_686_, lean_object* v_init_687_, lean_object* v_t_688_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_689_, 0, v_f_686_);
v___x_690_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_691_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_690_, v___f_689_, v_init_687_, v_t_688_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object* v_00_u03c3_692_, lean_object* v_00_u03b1_693_, lean_object* v_f_694_, lean_object* v_init_695_, lean_object* v_t_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_697_, 0, v_f_694_);
v___x_698_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_699_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_698_, v___f_697_, v_init_695_, v_t_696_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object* v_t_700_){
_start:
{
lean_object* v___y_702_; lean_object* v_val_703_; lean_object* v___y_715_; lean_object* v_val_720_; 
if (lean_obj_tag(v_t_700_) == 3)
{
lean_object* v___x_723_; 
lean_dec_ref_known(v_t_700_, 3);
v___x_723_ = lean_unsigned_to_nat(1u);
return v___x_723_;
}
else
{
switch(lean_obj_tag(v_t_700_))
{
case 2:
{
lean_object* v___x_724_; 
lean_inc_ref(v_t_700_);
v___x_724_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_700_);
v_val_720_ = v___x_724_;
goto v___jp_719_;
}
case 3:
{
lean_object* v___x_725_; 
lean_inc_ref(v_t_700_);
v___x_725_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_700_);
v_val_720_ = v___x_725_;
goto v___jp_719_;
}
default: 
{
lean_inc_ref(v_t_700_);
v_val_720_ = v_t_700_;
goto v___jp_719_;
}
}
}
v___jp_701_:
{
if (lean_obj_tag(v_val_703_) == 0)
{
lean_object* v_child_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_child_704_ = lean_ctor_get(v_val_703_, 1);
lean_inc_ref(v_child_704_);
lean_dec_ref_known(v_val_703_, 2);
v___x_705_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_child_704_);
v___x_706_ = lean_nat_add(v___y_702_, v___x_705_);
lean_dec(v___x_705_);
lean_dec(v___y_702_);
return v___x_706_;
}
else
{
lean_object* v_children_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_children_707_ = lean_ctor_get(v_val_703_, 1);
lean_inc_ref(v_children_707_);
lean_dec_ref_known(v_val_703_, 2);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_array_get_size(v_children_707_);
v___x_710_ = lean_nat_dec_lt(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
lean_dec_ref(v_children_707_);
return v___y_702_;
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_709_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_707_, v___x_711_, v___x_712_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v_children_707_);
return v___x_713_;
}
}
}
v___jp_714_:
{
lean_object* v___x_716_; 
v___x_716_ = lean_array_get_size(v___y_715_);
lean_dec_ref(v___y_715_);
switch(lean_obj_tag(v_t_700_))
{
case 2:
{
lean_object* v___x_717_; 
v___x_717_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_700_);
v___y_702_ = v___x_716_;
v_val_703_ = v___x_717_;
goto v___jp_701_;
}
case 3:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_700_);
v___y_702_ = v___x_716_;
v_val_703_ = v___x_718_;
goto v___jp_701_;
}
default: 
{
v___y_702_ = v___x_716_;
v_val_703_ = v_t_700_;
goto v___jp_701_;
}
}
}
v___jp_719_:
{
if (lean_obj_tag(v_val_720_) == 0)
{
lean_object* v___x_721_; 
lean_dec_ref_known(v_val_720_, 2);
v___x_721_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_715_ = v___x_721_;
goto v___jp_714_;
}
else
{
lean_object* v_vs_722_; 
v_vs_722_ = lean_ctor_get(v_val_720_, 0);
lean_inc_ref(v_vs_722_);
lean_dec_ref_known(v_val_720_, 2);
v___y_715_ = v_vs_722_;
goto v___jp_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(lean_object* v_as_726_, size_t v_i_727_, size_t v_stop_728_, lean_object* v_b_729_){
_start:
{
uint8_t v___x_730_; 
v___x_730_ = lean_usize_dec_eq(v_i_727_, v_stop_728_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v_snd_732_; lean_object* v___x_733_; lean_object* v___x_734_; size_t v___x_735_; size_t v___x_736_; 
v___x_731_ = lean_array_uget_borrowed(v_as_726_, v_i_727_);
v_snd_732_ = lean_ctor_get(v___x_731_, 1);
lean_inc(v_snd_732_);
v___x_733_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_732_);
v___x_734_ = lean_nat_add(v_b_729_, v___x_733_);
lean_dec(v___x_733_);
lean_dec(v_b_729_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_727_, v___x_735_);
v_i_727_ = v___x_736_;
v_b_729_ = v___x_734_;
goto _start;
}
else
{
return v_b_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, lean_object* v_b_741_){
_start:
{
uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v_snd_744_; lean_object* v___x_745_; lean_object* v___x_746_; size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_743_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v_snd_744_ = lean_ctor_get(v___x_743_, 1);
lean_inc(v_snd_744_);
v___x_745_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_744_);
v___x_746_ = lean_nat_add(v_b_741_, v___x_745_);
lean_dec(v___x_745_);
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_add(v_i_739_, v___x_747_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(v_as_738_, v___x_748_, v_stop_740_, v___x_746_);
return v___x_749_;
}
else
{
lean_inc(v_b_741_);
return v_b_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_750_, lean_object* v_i_751_, lean_object* v_stop_752_, lean_object* v_b_753_){
_start:
{
size_t v_i_boxed_754_; size_t v_stop_boxed_755_; lean_object* v_res_756_; 
v_i_boxed_754_ = lean_unbox_usize(v_i_751_);
lean_dec(v_i_751_);
v_stop_boxed_755_ = lean_unbox_usize(v_stop_752_);
lean_dec(v_stop_752_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_750_, v_i_boxed_754_, v_stop_boxed_755_, v_b_753_);
lean_dec(v_b_753_);
lean_dec_ref(v_as_750_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg___boxed(lean_object* v_as_757_, lean_object* v_i_758_, lean_object* v_stop_759_, lean_object* v_b_760_){
_start:
{
size_t v_i_boxed_761_; size_t v_stop_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_stop_boxed_762_ = lean_unbox_usize(v_stop_759_);
lean_dec(v_stop_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(v_as_757_, v_i_boxed_761_, v_stop_boxed_762_, v_b_760_);
lean_dec_ref(v_as_757_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_764_, lean_object* v_t_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_767_, lean_object* v_as_768_, size_t v_i_769_, size_t v_stop_770_, lean_object* v_b_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_768_, v_i_769_, v_stop_770_, v_b_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_773_, lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_stop_776_, lean_object* v_b_777_){
_start:
{
size_t v_i_boxed_778_; size_t v_stop_boxed_779_; lean_object* v_res_780_; 
v_i_boxed_778_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_stop_boxed_779_ = lean_unbox_usize(v_stop_776_);
lean_dec(v_stop_776_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_773_, v_as_774_, v_i_boxed_778_, v_stop_boxed_779_, v_b_777_);
lean_dec(v_b_777_);
lean_dec_ref(v_as_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0(lean_object* v_00_u03b1_781_, lean_object* v_as_782_, size_t v_i_783_, size_t v_stop_784_, lean_object* v_b_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(v_as_782_, v_i_783_, v_stop_784_, v_b_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___boxed(lean_object* v_00_u03b1_787_, lean_object* v_as_788_, lean_object* v_i_789_, lean_object* v_stop_790_, lean_object* v_b_791_){
_start:
{
size_t v_i_boxed_792_; size_t v_stop_boxed_793_; lean_object* v_res_794_; 
v_i_boxed_792_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_stop_boxed_793_ = lean_unbox_usize(v_stop_790_);
lean_dec(v_stop_790_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0(v_00_u03b1_787_, v_as_788_, v_i_boxed_792_, v_stop_boxed_793_, v_b_791_);
lean_dec_ref(v_as_788_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_795_, lean_object* v_f_796_, lean_object* v_s_797_, lean_object* v_k_798_, lean_object* v_t_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_800_);
v___x_802_ = lean_array_push(v___x_801_, v_k_798_);
v___x_803_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_795_, v___x_802_, v_f_796_, v_s_797_, v_t_799_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_804_, lean_object* v_f_805_, lean_object* v_init_806_, lean_object* v_t_807_){
_start:
{
lean_object* v___f_808_; lean_object* v___x_809_; 
lean_inc_ref(v_inst_804_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_808_, 0, v_inst_804_);
lean_closure_set(v___f_808_, 1, v_f_805_);
v___x_809_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_804_, v___f_808_, v_t_807_, v_init_806_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_810_, lean_object* v_00_u03c3_811_, lean_object* v_00_u03b1_812_, lean_object* v_inst_813_, lean_object* v_f_814_, lean_object* v_init_815_, lean_object* v_t_816_){
_start:
{
lean_object* v___f_817_; lean_object* v___x_818_; 
lean_inc_ref(v_inst_813_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_817_, 0, v_inst_813_);
lean_closure_set(v___f_817_, 1, v_f_814_);
v___x_818_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_813_, v___f_817_, v_t_816_, v_init_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_819_, lean_object* v_s_820_, lean_object* v_keys_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_apply_3(v_f_819_, v_s_820_, v_keys_821_, v_a_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_824_, lean_object* v___f_825_, lean_object* v_s_826_, lean_object* v_k_827_, lean_object* v_t_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = lean_mk_empty_array_with_capacity(v___x_829_);
v___x_831_ = lean_array_push(v___x_830_, v_k_827_);
v___x_832_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_824_, v___x_831_, v___f_825_, v_s_826_, v_t_828_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_833_, lean_object* v_init_834_, lean_object* v_t_835_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_836_, 0, v_f_833_);
v___x_837_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_838_, 0, v___x_837_);
lean_closure_set(v___f_838_, 1, v___f_836_);
v___x_839_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_837_, v___f_838_, v_t_835_, v_init_834_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_840_, lean_object* v_00_u03b1_841_, lean_object* v_f_842_, lean_object* v_init_843_, lean_object* v_t_844_){
_start:
{
lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___x_848_; 
v___f_845_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_845_, 0, v_f_842_);
v___x_846_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_847_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_847_, 0, v___x_846_);
lean_closure_set(v___f_847_, 1, v___f_845_);
v___x_848_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_846_, v___f_847_, v_t_844_, v_init_843_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_849_, lean_object* v_f_850_, lean_object* v_s_851_, lean_object* v_x_852_, lean_object* v_t_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_849_, v_f_850_, v_s_851_, v_t_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_855_, lean_object* v_f_856_, lean_object* v_s_857_, lean_object* v_x_858_, lean_object* v_t_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_855_, v_f_856_, v_s_857_, v_x_858_, v_t_859_);
lean_dec(v_x_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_861_, lean_object* v_f_862_, lean_object* v_init_863_, lean_object* v_t_864_){
_start:
{
lean_object* v___f_865_; lean_object* v___x_866_; 
lean_inc_ref(v_inst_861_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_865_, 0, v_inst_861_);
lean_closure_set(v___f_865_, 1, v_f_862_);
v___x_866_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_861_, v___f_865_, v_t_864_, v_init_863_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_867_, lean_object* v_00_u03c3_868_, lean_object* v_00_u03b1_869_, lean_object* v_inst_870_, lean_object* v_f_871_, lean_object* v_init_872_, lean_object* v_t_873_){
_start:
{
lean_object* v___f_874_; lean_object* v___x_875_; 
lean_inc_ref(v_inst_870_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_874_, 0, v_inst_870_);
lean_closure_set(v___f_874_, 1, v_f_871_);
v___x_875_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_870_, v___f_874_, v_t_873_, v_init_872_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_876_, lean_object* v___f_877_, lean_object* v_s_878_, lean_object* v_x_879_, lean_object* v_t_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_876_, v___f_877_, v_s_878_, v_t_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_882_, lean_object* v___f_883_, lean_object* v_s_884_, lean_object* v_x_885_, lean_object* v_t_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_882_, v___f_883_, v_s_884_, v_x_885_, v_t_886_);
lean_dec(v_x_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_888_, lean_object* v_init_889_, lean_object* v_t_890_){
_start:
{
lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___x_894_; 
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_891_, 0, v_f_888_);
v___x_892_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_893_, 0, v___x_892_);
lean_closure_set(v___f_893_, 1, v___f_891_);
v___x_894_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_892_, v___f_893_, v_t_890_, v_init_889_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_895_, lean_object* v_00_u03b1_896_, lean_object* v_f_897_, lean_object* v_init_898_, lean_object* v_t_899_){
_start:
{
lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v___x_903_; 
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_900_, 0, v_f_897_);
v___x_901_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_902_, 0, v___x_901_);
lean_closure_set(v___f_902_, 1, v___f_900_);
v___x_903_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_901_, v___f_902_, v_t_899_, v_init_898_);
return v___x_903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_904_, uint8_t v_x1_905_, lean_object* v_x2_906_){
_start:
{
if (v_x1_905_ == 0)
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_apply_1(v_f_904_, v_x2_906_);
v___x_908_ = lean_unbox(v___x_907_);
return v___x_908_;
}
else
{
lean_dec(v_x2_906_);
lean_dec_ref(v_f_904_);
return v_x1_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_909_, lean_object* v_x1_910_, lean_object* v_x2_911_){
_start:
{
uint8_t v_x1_83__boxed_912_; uint8_t v_res_913_; lean_object* v_r_914_; 
v_x1_83__boxed_912_ = lean_unbox(v_x1_910_);
v_res_913_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_909_, v_x1_83__boxed_912_, v_x2_911_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_915_, lean_object* v___f_916_, uint8_t v_s_917_, lean_object* v_x_918_, lean_object* v_t_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_box(v_s_917_);
v___x_921_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_915_, v___f_916_, v___x_920_, v_t_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_922_, lean_object* v___f_923_, lean_object* v_s_924_, lean_object* v_x_925_, lean_object* v_t_926_){
_start:
{
uint8_t v_s_boxed_927_; lean_object* v_res_928_; 
v_s_boxed_927_ = lean_unbox(v_s_924_);
v_res_928_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_922_, v___f_923_, v_s_boxed_927_, v_x_925_, v_t_926_);
lean_dec(v_x_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_929_, lean_object* v_f_930_){
_start:
{
lean_object* v___f_931_; uint8_t v___x_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_931_, 0, v_f_930_);
v___x_932_ = 0;
v___x_933_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_934_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_934_, 0, v___x_933_);
lean_closure_set(v___f_934_, 1, v___f_931_);
v___x_935_ = lean_box(v___x_932_);
v___x_936_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_933_, v___f_934_, v_t_929_, v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_937_, lean_object* v_t_938_, lean_object* v_f_939_){
_start:
{
lean_object* v___f_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___f_940_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_940_, 0, v_f_939_);
v___x_941_ = 0;
v___x_942_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_943_, 0, v___x_942_);
lean_closure_set(v___f_943_, 1, v___f_940_);
v___x_944_ = lean_box(v___x_941_);
v___x_945_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_942_, v___f_943_, v_t_938_, v___x_944_);
v___x_946_ = lean_unbox(v___x_945_);
lean_dec(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_947_, lean_object* v_t_948_, lean_object* v_f_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_947_, v_t_948_, v_f_949_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_952_, lean_object* v_x2_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_array_push(v_x1_952_, v_x2_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_955_, lean_object* v___f_956_, lean_object* v_s_957_, lean_object* v_x_958_, lean_object* v_t_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_955_, v___f_956_, v_s_957_, v_t_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_961_, lean_object* v___f_962_, lean_object* v_s_963_, lean_object* v_x_964_, lean_object* v_t_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_961_, v___f_962_, v_s_963_, v_x_964_, v_t_965_);
lean_dec(v_x_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___x_975_; 
v___x_972_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_973_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_974_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_975_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_973_, v___f_974_, v_t_971_, v___x_972_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_976_, lean_object* v_t_977_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___f_980_; lean_object* v___x_981_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_979_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_980_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_981_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_979_, v___f_980_, v_t_977_, v___x_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_982_, lean_object* v_keys_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v_keys_983_);
lean_ctor_set(v___x_985_, 1, v_a_984_);
v___x_986_ = lean_array_push(v_s_982_, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_987_, lean_object* v___f_988_, lean_object* v_s_989_, lean_object* v_k_990_, lean_object* v_t_991_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_994_ = lean_array_push(v___x_993_, v_k_990_);
v___x_995_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_987_, v___x_994_, v___f_988_, v_s_989_, v_t_991_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; 
v___x_1003_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_1004_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1005_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_1006_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1004_, v___f_1005_, v_t_1002_, v___x_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_1007_, lean_object* v_t_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___x_1009_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_1010_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1011_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_1012_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1010_, v___f_1011_, v_t_1008_, v___x_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_1013_, lean_object* v_x_1014_, lean_object* v_t_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_1015_);
v___x_1017_ = lean_nat_add(v_n_1013_, v___x_1016_);
lean_dec(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_1018_, lean_object* v_x_1019_, lean_object* v_t_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_1018_, v_x_1019_, v_t_1020_);
lean_dec(v_x_1019_);
lean_dec(v_n_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_1023_){
_start:
{
lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___f_1024_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_1023_, v___f_1024_, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_1027_, lean_object* v_t_1028_){
_start:
{
lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___f_1029_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_1028_, v___f_1029_, v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_vs_1034_, lean_object* v_toPure_1035_, lean_object* v_key_1036_, lean_object* v_c_1037_){
_start:
{
lean_object* v___y_1039_; lean_object* v_val_1067_; 
switch(lean_obj_tag(v_c_1037_))
{
case 2:
{
lean_object* v___x_1076_; 
lean_inc_ref(v_c_1037_);
v___x_1076_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1037_);
v_val_1067_ = v___x_1076_;
goto v___jp_1066_;
}
case 3:
{
lean_object* v___x_1077_; 
lean_inc_ref(v_c_1037_);
v___x_1077_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1037_);
v_val_1067_ = v___x_1077_;
goto v___jp_1066_;
}
default: 
{
lean_inc_ref(v_c_1037_);
v_val_1067_ = v_c_1037_;
goto v___jp_1066_;
}
}
v___jp_1038_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = lean_array_get_size(v_vs_1034_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_nat_dec_eq(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_vs_1034_);
lean_ctor_set(v___x_1043_, 1, v___y_1039_);
v___x_1044_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1045_ = lean_array_get_size(v___y_1039_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_dec_eq(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_vs_1034_);
lean_ctor_set(v___x_1048_, 1, v___y_1039_);
v___x_1049_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1048_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v_fst_1051_; lean_object* v_snd_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_vs_1034_);
v___x_1050_ = lean_array_fget(v___y_1039_, v___x_1041_);
lean_dec_ref(v___y_1039_);
v_fst_1051_ = lean_ctor_get(v___x_1050_, 0);
v_snd_1052_ = lean_ctor_get(v___x_1050_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1054_ = v___x_1050_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_snd_1052_);
lean_inc(v_fst_1051_);
lean_dec(v___x_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_fst_1051_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1052_);
v___x_1057_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_apply_2(v_toPure_1035_, lean_box(0), v___x_1057_);
return v___x_1058_;
}
}
}
}
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_key_1036_);
lean_ctor_set(v___x_1062_, 1, v_c_1037_);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_mk_empty_array_with_capacity(v___x_1063_);
v___x_1065_ = lean_array_push(v___x_1064_, v___x_1062_);
v___y_1039_ = v___x_1065_;
goto v___jp_1038_;
}
v___jp_1066_:
{
if (lean_obj_tag(v_val_1067_) == 0)
{
lean_dec_ref_known(v_val_1067_, 2);
goto v___jp_1061_;
}
else
{
lean_object* v_vs_1068_; lean_object* v_children_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_vs_1068_ = lean_ctor_get(v_val_1067_, 0);
lean_inc_ref(v_vs_1068_);
v_children_1069_ = lean_ctor_get(v_val_1067_, 1);
lean_inc_ref(v_children_1069_);
lean_dec_ref_known(v_val_1067_, 2);
v___x_1070_ = lean_array_get_size(v_vs_1068_);
lean_dec_ref(v_vs_1068_);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_nat_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v_children_1069_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_array_get_size(v_children_1069_);
lean_dec_ref(v_children_1069_);
v___x_1074_ = lean_nat_dec_eq(v___x_1073_, v___x_1071_);
if (v___x_1074_ == 0)
{
goto v___jp_1061_;
}
else
{
lean_object* v___x_1075_; 
lean_dec_ref(v_c_1037_);
lean_dec(v_key_1036_);
v___x_1075_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0));
v___y_1039_ = v___x_1075_;
goto v___jp_1038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object* v_vs_1078_, lean_object* v_toPure_1079_, lean_object* v_children_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_array_get_size(v_vs_1078_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_nat_dec_eq(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_vs_1078_);
lean_ctor_set(v___x_1084_, 1, v_children_1080_);
v___x_1085_ = lean_apply_2(v_toPure_1079_, lean_box(0), v___x_1084_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_array_get_size(v_children_1080_);
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = lean_nat_dec_eq(v___x_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v_vs_1078_);
lean_ctor_set(v___x_1089_, 1, v_children_1080_);
v___x_1090_ = lean_apply_2(v_toPure_1079_, lean_box(0), v___x_1089_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_vs_1078_);
v___x_1091_ = lean_array_fget(v_children_1080_, v___x_1082_);
lean_dec_ref(v_children_1080_);
v_fst_1092_ = lean_ctor_get(v___x_1091_, 0);
v_snd_1093_ = lean_ctor_get(v___x_1091_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v___x_1091_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_snd_1093_);
lean_inc(v_fst_1092_);
lean_dec(v___x_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_fst_1092_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_snd_1093_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_apply_2(v_toPure_1079_, lean_box(0), v___x_1098_);
return v___x_1099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object* v_toPure_1102_, lean_object* v_children_1103_, lean_object* v_inst_1104_, lean_object* v___f_1105_, lean_object* v_toBind_1106_, lean_object* v_vs_1107_){
_start:
{
lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1108_, 0, v_vs_1107_);
lean_closure_set(v___f_1108_, 1, v_toPure_1102_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_array_get_size(v_children_1103_);
v___x_1111_ = l_Array_filterMapM___redArg(v_inst_1104_, v___f_1105_, v_children_1103_, v___x_1109_, v___x_1110_);
v___x_1112_ = lean_apply_4(v_toBind_1106_, lean_box(0), lean_box(0), v___x_1111_, v___f_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_fst_1113_, lean_object* v_toPure_1114_, lean_object* v_child_1115_){
_start:
{
lean_object* v_val_1121_; 
switch(lean_obj_tag(v_child_1115_))
{
case 2:
{
lean_object* v___x_1131_; 
lean_inc_ref(v_child_1115_);
v___x_1131_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_child_1115_);
v_val_1121_ = v___x_1131_;
goto v___jp_1120_;
}
case 3:
{
lean_object* v___x_1132_; 
lean_inc_ref(v_child_1115_);
v___x_1132_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_child_1115_);
v_val_1121_ = v___x_1132_;
goto v___jp_1120_;
}
default: 
{
lean_inc_ref(v_child_1115_);
v_val_1121_ = v_child_1115_;
goto v___jp_1120_;
}
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_fst_1113_);
lean_ctor_set(v___x_1117_, 1, v_child_1115_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
v___x_1119_ = lean_apply_2(v_toPure_1114_, lean_box(0), v___x_1118_);
return v___x_1119_;
}
v___jp_1120_:
{
if (lean_obj_tag(v_val_1121_) == 0)
{
lean_dec_ref_known(v_val_1121_, 2);
goto v___jp_1116_;
}
else
{
lean_object* v_vs_1122_; lean_object* v_children_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_vs_1122_ = lean_ctor_get(v_val_1121_, 0);
lean_inc_ref(v_vs_1122_);
v_children_1123_ = lean_ctor_get(v_val_1121_, 1);
lean_inc_ref(v_children_1123_);
lean_dec_ref_known(v_val_1121_, 2);
v___x_1124_ = lean_array_get_size(v_vs_1122_);
lean_dec_ref(v_vs_1122_);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_nat_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_children_1123_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_array_get_size(v_children_1123_);
lean_dec_ref(v_children_1123_);
v___x_1128_ = lean_nat_dec_eq(v___x_1127_, v___x_1125_);
if (v___x_1128_ == 0)
{
goto v___jp_1116_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v_child_1115_);
lean_dec(v_fst_1113_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_apply_2(v_toPure_1114_, lean_box(0), v___x_1129_);
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_1133_, lean_object* v_inst_1134_, lean_object* v_f_1135_, lean_object* v_toBind_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_fst_1138_ = lean_ctor_get(v_x_1137_, 0);
lean_inc(v_fst_1138_);
v_snd_1139_ = lean_ctor_get(v_x_1137_, 1);
lean_inc(v_snd_1139_);
lean_dec_ref(v_x_1137_);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1140_, 0, v_fst_1138_);
lean_closure_set(v___f_1140_, 1, v_toPure_1133_);
v___x_1141_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1134_, v_snd_1139_, v_f_1135_);
v___x_1142_ = lean_apply_4(v_toBind_1136_, lean_box(0), lean_box(0), v___x_1141_, v___f_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_1143_, lean_object* v_t_1144_, lean_object* v_f_1145_){
_start:
{
switch(lean_obj_tag(v_t_1144_))
{
case 0:
{
lean_object* v_toApplicative_1146_; lean_object* v_toBind_1147_; lean_object* v_toPure_1148_; lean_object* v_key_1149_; lean_object* v_child_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_toApplicative_1146_ = lean_ctor_get(v_inst_1143_, 0);
v_toBind_1147_ = lean_ctor_get(v_inst_1143_, 1);
lean_inc_n(v_toBind_1147_, 2);
v_toPure_1148_ = lean_ctor_get(v_toApplicative_1146_, 1);
lean_inc(v_toPure_1148_);
v_key_1149_ = lean_ctor_get(v_t_1144_, 0);
lean_inc(v_key_1149_);
v_child_1150_ = lean_ctor_get(v_t_1144_, 1);
lean_inc_ref(v_child_1150_);
lean_dec_ref_known(v_t_1144_, 2);
lean_inc(v_f_1145_);
v___f_1151_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1151_, 0, v_toPure_1148_);
lean_closure_set(v___f_1151_, 1, v_key_1149_);
lean_closure_set(v___f_1151_, 2, v_inst_1143_);
lean_closure_set(v___f_1151_, 3, v_child_1150_);
lean_closure_set(v___f_1151_, 4, v_f_1145_);
lean_closure_set(v___f_1151_, 5, v_toBind_1147_);
v___x_1152_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_1153_ = lean_apply_1(v_f_1145_, v___x_1152_);
v___x_1154_ = lean_apply_4(v_toBind_1147_, lean_box(0), lean_box(0), v___x_1153_, v___f_1151_);
return v___x_1154_;
}
case 1:
{
lean_object* v_toApplicative_1155_; lean_object* v_toBind_1156_; lean_object* v_toPure_1157_; lean_object* v_vs_1158_; lean_object* v_children_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_toApplicative_1155_ = lean_ctor_get(v_inst_1143_, 0);
v_toBind_1156_ = lean_ctor_get(v_inst_1143_, 1);
lean_inc_n(v_toBind_1156_, 3);
v_toPure_1157_ = lean_ctor_get(v_toApplicative_1155_, 1);
lean_inc_n(v_toPure_1157_, 2);
v_vs_1158_ = lean_ctor_get(v_t_1144_, 0);
lean_inc_ref(v_vs_1158_);
v_children_1159_ = lean_ctor_get(v_t_1144_, 1);
lean_inc_ref(v_children_1159_);
lean_dec_ref_known(v_t_1144_, 2);
lean_inc(v_f_1145_);
lean_inc_ref(v_inst_1143_);
v___f_1160_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1160_, 0, v_toPure_1157_);
lean_closure_set(v___f_1160_, 1, v_inst_1143_);
lean_closure_set(v___f_1160_, 2, v_f_1145_);
lean_closure_set(v___f_1160_, 3, v_toBind_1156_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_1161_, 0, v_toPure_1157_);
lean_closure_set(v___f_1161_, 1, v_children_1159_);
lean_closure_set(v___f_1161_, 2, v_inst_1143_);
lean_closure_set(v___f_1161_, 3, v___f_1160_);
lean_closure_set(v___f_1161_, 4, v_toBind_1156_);
v___x_1162_ = lean_apply_1(v_f_1145_, v_vs_1158_);
v___x_1163_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v___x_1162_, v___f_1161_);
return v___x_1163_;
}
default: 
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_1144_);
v_t_1144_ = v___x_1164_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_1166_, lean_object* v_key_1167_, lean_object* v_inst_1168_, lean_object* v_child_1169_, lean_object* v_f_1170_, lean_object* v_toBind_1171_, lean_object* v_vs_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___f_1173_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1173_, 0, v_vs_1172_);
lean_closure_set(v___f_1173_, 1, v_toPure_1166_);
lean_closure_set(v___f_1173_, 2, v_key_1167_);
v___x_1174_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1168_, v_child_1169_, v_f_1170_);
v___x_1175_ = lean_apply_4(v_toBind_1171_, lean_box(0), lean_box(0), v___x_1174_, v___f_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_1176_, lean_object* v_inst_1177_, lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_t_1180_, lean_object* v_f_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1177_, v_t_1180_, v_f_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_1183_, lean_object* v_f_1184_, lean_object* v_t_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1183_, v_t_1185_, v_f_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_1187_, lean_object* v___x_1188_, lean_object* v_acc_1189_, lean_object* v_k_1190_, lean_object* v_t_1191_){
_start:
{
lean_object* v_val_1193_; 
switch(lean_obj_tag(v_t_1191_))
{
case 2:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_1191_);
v_val_1193_ = v___x_1202_;
goto v___jp_1192_;
}
case 3:
{
lean_object* v___x_1203_; 
v___x_1203_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_1191_);
v_val_1193_ = v___x_1203_;
goto v___jp_1192_;
}
default: 
{
v_val_1193_ = v_t_1191_;
goto v___jp_1192_;
}
}
v___jp_1192_:
{
if (lean_obj_tag(v_val_1193_) == 0)
{
lean_dec_ref_known(v_val_1193_, 2);
lean_dec(v_k_1190_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
return v_acc_1189_;
}
else
{
lean_object* v_vs_1194_; lean_object* v_children_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_vs_1194_ = lean_ctor_get(v_val_1193_, 0);
lean_inc_ref(v_vs_1194_);
v_children_1195_ = lean_ctor_get(v_val_1193_, 1);
lean_inc_ref(v_children_1195_);
lean_dec_ref_known(v_val_1193_, 2);
v___x_1196_ = lean_array_get_size(v_vs_1194_);
lean_dec_ref(v_vs_1194_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_nat_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_children_1195_);
lean_dec(v_k_1190_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
return v_acc_1189_;
}
else
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_array_get_size(v_children_1195_);
lean_dec_ref(v_children_1195_);
v___x_1200_ = lean_nat_dec_eq(v___x_1199_, v___x_1197_);
if (v___x_1200_ == 0)
{
lean_dec(v_k_1190_);
lean_dec_ref(v___x_1188_);
lean_dec_ref(v___x_1187_);
return v_acc_1189_;
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_PersistentHashMap_erase___redArg(v___x_1187_, v___x_1188_, v_acc_1189_, v_k_1190_);
return v___x_1201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_1204_, lean_object* v_toPure_1205_, lean_object* v_root_1206_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_inc_ref(v_root_1206_);
v___x_1207_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_1206_, v___f_1204_, v_root_1206_);
v___x_1208_ = lean_apply_2(v_toPure_1205_, lean_box(0), v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_1214_, lean_object* v_d_1215_, lean_object* v_f_1216_){
_start:
{
lean_object* v_toApplicative_1217_; lean_object* v_toBind_1218_; lean_object* v_toPure_1219_; lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_toApplicative_1217_ = lean_ctor_get(v_inst_1214_, 0);
v_toBind_1218_ = lean_ctor_get(v_inst_1214_, 1);
lean_inc(v_toBind_1218_);
v_toPure_1219_ = lean_ctor_get(v_toApplicative_1217_, 1);
lean_inc_ref(v_inst_1214_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1220_, 0, v_inst_1214_);
lean_closure_set(v___f_1220_, 1, v_f_1216_);
v___f_1221_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_1219_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1222_, 0, v___f_1221_);
lean_closure_set(v___f_1222_, 1, v_toPure_1219_);
v___x_1223_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1214_, v_d_1215_, v___f_1220_);
v___x_1224_ = lean_apply_4(v_toBind_1218_, lean_box(0), lean_box(0), v___x_1223_, v___f_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_1225_, lean_object* v_inst_1226_, lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_d_1229_, lean_object* v_f_1230_){
_start:
{
lean_object* v_toApplicative_1231_; lean_object* v_toBind_1232_; lean_object* v_toPure_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_toApplicative_1231_ = lean_ctor_get(v_inst_1226_, 0);
v_toBind_1232_ = lean_ctor_get(v_inst_1226_, 1);
lean_inc(v_toBind_1232_);
v_toPure_1233_ = lean_ctor_get(v_toApplicative_1231_, 1);
lean_inc_ref(v_inst_1226_);
v___f_1234_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1234_, 0, v_inst_1226_);
lean_closure_set(v___f_1234_, 1, v_f_1230_);
v___f_1235_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_1233_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1236_, 0, v___f_1235_);
lean_closure_set(v___f_1236_, 1, v_toPure_1233_);
v___x_1237_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1226_, v_d_1229_, v___f_1234_);
v___x_1238_ = lean_apply_4(v_toBind_1232_, lean_box(0), lean_box(0), v___x_1237_, v___f_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_1239_, lean_object* v_A_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_apply_1(v_f_1239_, v_A_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_1242_, lean_object* v___f_1243_, lean_object* v_t_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_1242_, v_t_1244_, v___f_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_1246_, lean_object* v_f_1247_){
_start:
{
lean_object* v___f_1248_; lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___f_1248_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1248_, 0, v_f_1247_);
v___x_1249_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1250_, 0, v___x_1249_);
lean_closure_set(v___f_1250_, 1, v___f_1248_);
v___f_1251_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_1252_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1249_, v_d_1246_, v___f_1250_);
lean_inc(v___x_1252_);
v___x_1253_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_1252_, v___f_1251_, v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_d_1256_, lean_object* v_f_1257_){
_start:
{
lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1258_, 0, v_f_1257_);
v___x_1259_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1260_, 0, v___x_1259_);
lean_closure_set(v___f_1260_, 1, v___f_1258_);
v___f_1261_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_1262_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1259_, v_d_1256_, v___f_1260_);
lean_inc(v___x_1262_);
v___x_1263_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_1262_, v___f_1261_, v___x_1262_);
return v___x_1263_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_DiscrTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_DiscrTree_Util(builtin);
}
#ifdef __cplusplus
}
#endif
