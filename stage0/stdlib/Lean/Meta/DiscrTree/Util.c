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
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__3(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0___boxed(lean_object* v___x_383_, lean_object* v_toPure_384_, lean_object* v_push_385_, lean_object* v_todo_386_, lean_object* v_i_387_, lean_object* v___x_388_, lean_object* v_inst_389_, lean_object* v_key_390_, lean_object* v_ks_391_, lean_object* v_____x_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0(v___x_383_, v_toPure_384_, v_push_385_, v_todo_386_, v_i_387_, v___x_388_, v_inst_389_, v_key_390_, v_ks_391_, v_____x_392_);
lean_dec(v___x_388_);
lean_dec(v_i_387_);
lean_dec(v___x_383_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(lean_object* v_inst_394_, lean_object* v_key_395_, lean_object* v_push_396_, lean_object* v_todo_397_, lean_object* v_ks_398_, lean_object* v_i_399_){
_start:
{
lean_object* v_toApplicative_400_; lean_object* v_toBind_401_; lean_object* v_toPure_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_toApplicative_400_ = lean_ctor_get(v_inst_394_, 0);
v_toBind_401_ = lean_ctor_get(v_inst_394_, 1);
v_toPure_402_ = lean_ctor_get(v_toApplicative_400_, 1);
v___x_403_ = lean_array_get_size(v_ks_398_);
v___x_404_ = lean_nat_dec_lt(v_i_399_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc(v_toPure_402_);
lean_dec(v_i_399_);
lean_dec_ref(v_ks_398_);
lean_dec_ref(v_push_396_);
lean_dec(v_key_395_);
lean_dec_ref(v_inst_394_);
v___x_405_ = lean_array_get_size(v_todo_397_);
lean_dec_ref(v_todo_397_);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_nat_dec_eq(v___x_405_, v___x_406_);
v___x_408_ = lean_box(v___x_407_);
v___x_409_ = lean_apply_2(v_toPure_402_, lean_box(0), v___x_408_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_array_get_size(v_todo_397_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_nat_dec_eq(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_e_416_; lean_object* v_todo_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_413_ = l_Lean_instInhabitedExpr;
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_sub(v___x_410_, v___x_414_);
v_e_416_ = lean_array_get(v___x_413_, v_todo_397_, v___x_415_);
lean_dec(v___x_415_);
v_todo_417_ = lean_array_pop(v_todo_397_);
v___x_418_ = lean_array_fget_borrowed(v_ks_398_, v_i_399_);
v___x_419_ = lean_box(0);
v___x_420_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
lean_inc(v___x_418_);
lean_inc(v_toPure_402_);
lean_inc(v_toBind_401_);
lean_inc(v_key_395_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_421_, 0, v___x_418_);
lean_closure_set(v___f_421_, 1, v_toPure_402_);
lean_closure_set(v___f_421_, 2, v_push_396_);
lean_closure_set(v___f_421_, 3, v_todo_417_);
lean_closure_set(v___f_421_, 4, v_i_399_);
lean_closure_set(v___f_421_, 5, v___x_414_);
lean_closure_set(v___f_421_, 6, v_inst_394_);
lean_closure_set(v___f_421_, 7, v_key_395_);
lean_closure_set(v___f_421_, 8, v_ks_398_);
v___x_422_ = lean_apply_1(v_key_395_, v_e_416_);
v___x_423_ = lean_apply_4(v_toBind_401_, lean_box(0), lean_box(0), v___x_422_, v___f_421_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; 
lean_dec(v_e_416_);
v___x_424_ = lean_nat_add(v_i_399_, v___x_414_);
lean_dec(v_i_399_);
v_todo_397_ = v_todo_417_;
v_i_399_ = v___x_424_;
goto _start;
}
}
else
{
uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_inc(v_toPure_402_);
lean_dec(v_i_399_);
lean_dec_ref(v_ks_398_);
lean_dec_ref(v_todo_397_);
lean_dec_ref(v_push_396_);
lean_dec(v_key_395_);
lean_dec_ref(v_inst_394_);
v___x_426_ = 0;
v___x_427_ = lean_box(v___x_426_);
v___x_428_ = lean_apply_2(v_toPure_402_, lean_box(0), v___x_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg___lam__0(lean_object* v___x_429_, lean_object* v_toPure_430_, lean_object* v_push_431_, lean_object* v_todo_432_, lean_object* v_i_433_, lean_object* v___x_434_, lean_object* v_inst_435_, lean_object* v_key_436_, lean_object* v_ks_437_, lean_object* v_____x_438_){
_start:
{
lean_object* v_fst_439_; lean_object* v_snd_440_; uint8_t v___x_441_; 
v_fst_439_ = lean_ctor_get(v_____x_438_, 0);
lean_inc(v_fst_439_);
v_snd_440_ = lean_ctor_get(v_____x_438_, 1);
lean_inc(v_snd_440_);
lean_dec_ref(v_____x_438_);
v___x_441_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_429_, v_fst_439_);
lean_dec(v_fst_439_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_snd_440_);
lean_dec_ref(v_ks_437_);
lean_dec(v_key_436_);
lean_dec_ref(v_inst_435_);
lean_dec_ref(v_todo_432_);
lean_dec_ref(v_push_431_);
v___x_442_ = lean_box(v___x_441_);
v___x_443_ = lean_apply_2(v_toPure_430_, lean_box(0), v___x_442_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_toPure_430_);
lean_inc_ref(v_push_431_);
v___x_444_ = lean_apply_2(v_push_431_, v_todo_432_, v_snd_440_);
v___x_445_ = lean_nat_add(v_i_433_, v___x_434_);
v___x_446_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(v_inst_435_, v_key_436_, v_push_431_, v___x_444_, v_ks_437_, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_matchesSuffix(lean_object* v_m_447_, lean_object* v_00_u03b2_448_, lean_object* v_inst_449_, lean_object* v_key_450_, lean_object* v_push_451_, lean_object* v_todo_452_, lean_object* v_ks_453_, lean_object* v_i_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(v_inst_449_, v_key_450_, v_push_451_, v_todo_452_, v_ks_453_, v_i_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter___redArg(lean_object* v_x_456_, lean_object* v_h__1_457_){
_start:
{
lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v___x_460_; 
v_fst_458_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_fst_458_);
v_snd_459_ = lean_ctor_get(v_x_456_, 1);
lean_inc(v_snd_459_);
lean_dec_ref(v_x_456_);
v___x_460_ = lean_apply_2(v_h__1_457_, v_fst_458_, v_snd_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Util_0__Lean_Meta_DiscrTree_Trie_matchesSuffix_match__1_splitter(lean_object* v_00_u03b2_461_, lean_object* v_motive_462_, lean_object* v_x_463_, lean_object* v_h__1_464_){
_start:
{
lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_467_; 
v_fst_465_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_fst_465_);
v_snd_466_ = lean_ctor_get(v_x_463_, 1);
lean_inc(v_snd_466_);
lean_dec_ref(v_x_463_);
v___x_467_ = lean_apply_2(v_h__1_464_, v_fst_465_, v_snd_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__0(lean_object* v_toPure_468_, lean_object* v_result_469_, lean_object* v_v_470_, uint8_t v_____do__lift_471_){
_start:
{
if (v_____do__lift_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v_v_470_);
v___x_472_ = lean_apply_2(v_toPure_468_, lean_box(0), v_result_469_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_array_push(v_result_469_, v_v_470_);
v___x_474_ = lean_apply_2(v_toPure_468_, lean_box(0), v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__0___boxed(lean_object* v_toPure_475_, lean_object* v_result_476_, lean_object* v_v_477_, lean_object* v_____do__lift_478_){
_start:
{
uint8_t v_____do__lift_1142__boxed_479_; lean_object* v_res_480_; 
v_____do__lift_1142__boxed_479_ = lean_unbox(v_____do__lift_478_);
v_res_480_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__0(v_toPure_475_, v_result_476_, v_v_477_, v_____do__lift_1142__boxed_479_);
return v_res_480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__1(lean_object* v_a_481_, lean_object* v_b_482_){
_start:
{
lean_object* v_fst_483_; lean_object* v_fst_484_; uint8_t v___x_485_; 
v_fst_483_ = lean_ctor_get(v_a_481_, 0);
v_fst_484_ = lean_ctor_get(v_b_482_, 0);
v___x_485_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_483_, v_fst_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__1___boxed(lean_object* v_a_486_, lean_object* v_b_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__1(v_a_486_, v_b_487_);
lean_dec_ref(v_b_487_);
lean_dec_ref(v_a_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__3(lean_object* v___f_490_, lean_object* v_result_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = lean_apply_1(v___f_490_, v_result_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg(lean_object* v_inst_494_, lean_object* v_key_495_, lean_object* v_push_496_, lean_object* v_todo_497_, lean_object* v_c_498_, lean_object* v_result_499_){
_start:
{
lean_object* v_toApplicative_500_; lean_object* v_toBind_501_; lean_object* v_toPure_502_; lean_object* v___y_504_; 
v_toApplicative_500_ = lean_ctor_get(v_inst_494_, 0);
v_toBind_501_ = lean_ctor_get(v_inst_494_, 1);
lean_inc(v_toBind_501_);
v_toPure_502_ = lean_ctor_get(v_toApplicative_500_, 1);
if (lean_obj_tag(v_c_498_) == 3)
{
lean_object* v_keys_507_; lean_object* v_i_508_; lean_object* v_v_509_; lean_object* v___f_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_keys_507_ = lean_ctor_get(v_c_498_, 0);
lean_inc_ref(v_keys_507_);
v_i_508_ = lean_ctor_get(v_c_498_, 1);
lean_inc(v_i_508_);
v_v_509_ = lean_ctor_get(v_c_498_, 2);
lean_inc(v_v_509_);
lean_dec_ref_known(v_c_498_, 3);
lean_inc(v_toPure_502_);
v___f_510_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_510_, 0, v_toPure_502_);
lean_closure_set(v___f_510_, 1, v_result_499_);
lean_closure_set(v___f_510_, 2, v_v_509_);
v___x_511_ = l_Lean_Meta_DiscrTree_Trie_matchesSuffix___redArg(v_inst_494_, v_key_495_, v_push_496_, v_todo_497_, v_keys_507_, v_i_508_);
v___x_512_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v___x_511_, v___f_510_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_val_516_; uint8_t v___x_519_; 
lean_inc(v_toPure_502_);
v___x_513_ = lean_array_get_size(v_todo_497_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_eq(v___x_513_, v___x_514_);
if (v___x_519_ == 0)
{
lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v_val_531_; 
v___f_520_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___closed__0));
v___x_521_ = l_Lean_instInhabitedExpr;
switch(lean_obj_tag(v_c_498_))
{
case 2:
{
lean_object* v___x_536_; 
lean_inc_ref(v_c_498_);
v___x_536_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_498_);
v_val_531_ = v___x_536_;
goto v___jp_530_;
}
case 3:
{
lean_object* v___x_537_; 
lean_inc_ref(v_c_498_);
v___x_537_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_498_);
v_val_531_ = v___x_537_;
goto v___jp_530_;
}
default: 
{
lean_inc_ref(v_c_498_);
v_val_531_ = v_c_498_;
goto v___jp_530_;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_e_525_; lean_object* v_todo_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_sub(v___x_513_, v___x_523_);
v_e_525_ = lean_array_get(v___x_521_, v_todo_497_, v___x_524_);
lean_dec(v___x_524_);
v_todo_526_ = lean_array_pop(v_todo_497_);
lean_inc(v_toBind_501_);
lean_inc(v_key_495_);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__5), 11, 10);
lean_closure_set(v___f_527_, 0, v_push_496_);
lean_closure_set(v___f_527_, 1, v_todo_526_);
lean_closure_set(v___f_527_, 2, v_inst_494_);
lean_closure_set(v___f_527_, 3, v_key_495_);
lean_closure_set(v___f_527_, 4, v_toPure_502_);
lean_closure_set(v___f_527_, 5, v___x_523_);
lean_closure_set(v___f_527_, 6, v___f_520_);
lean_closure_set(v___f_527_, 7, v_c_498_);
lean_closure_set(v___f_527_, 8, v_result_499_);
lean_closure_set(v___f_527_, 9, v_toBind_501_);
v___x_528_ = lean_apply_1(v_key_495_, v_e_525_);
v___x_529_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v___x_528_, v___f_527_);
return v___x_529_;
}
v___jp_530_:
{
if (lean_obj_tag(v_val_531_) == 0)
{
lean_dec_ref_known(v_val_531_, 2);
goto v___jp_522_;
}
else
{
lean_object* v_children_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_children_532_ = lean_ctor_get(v_val_531_, 1);
lean_inc_ref(v_children_532_);
lean_dec_ref_known(v_val_531_, 2);
v___x_533_ = lean_array_get_size(v_children_532_);
lean_dec_ref(v_children_532_);
v___x_534_ = lean_nat_dec_eq(v___x_533_, v___x_514_);
if (v___x_534_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v___x_535_; 
lean_dec(v_toBind_501_);
lean_dec_ref(v_c_498_);
lean_dec_ref(v_todo_497_);
lean_dec_ref(v_push_496_);
lean_dec(v_key_495_);
lean_dec_ref(v_inst_494_);
v___x_535_ = lean_apply_2(v_toPure_502_, lean_box(0), v_result_499_);
return v___x_535_;
}
}
}
}
else
{
lean_dec(v_toBind_501_);
lean_dec_ref(v_todo_497_);
lean_dec_ref(v_push_496_);
lean_dec(v_key_495_);
lean_dec_ref(v_inst_494_);
switch(lean_obj_tag(v_c_498_))
{
case 2:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_498_);
v_val_516_ = v___x_538_;
goto v___jp_515_;
}
case 3:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_498_);
v_val_516_ = v___x_539_;
goto v___jp_515_;
}
default: 
{
v_val_516_ = v_c_498_;
goto v___jp_515_;
}
}
}
v___jp_515_:
{
if (lean_obj_tag(v_val_516_) == 0)
{
lean_object* v___x_517_; 
lean_dec_ref_known(v_val_516_, 2);
v___x_517_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_504_ = v___x_517_;
goto v___jp_503_;
}
else
{
lean_object* v_vs_518_; 
v_vs_518_ = lean_ctor_get(v_val_516_, 0);
lean_inc_ref(v_vs_518_);
lean_dec_ref_known(v_val_516_, 2);
v___y_504_ = v_vs_518_;
goto v___jp_503_;
}
}
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = l_Array_append___redArg(v_result_499_, v___y_504_);
lean_dec_ref(v___y_504_);
v___x_506_ = lean_apply_2(v_toPure_502_, lean_box(0), v___x_505_);
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__2(lean_object* v_fst_540_, lean_object* v_push_541_, lean_object* v_todo_542_, lean_object* v_snd_543_, lean_object* v_inst_544_, lean_object* v_key_545_, lean_object* v_toPure_546_, lean_object* v___x_547_, lean_object* v___f_548_, lean_object* v_c_549_, lean_object* v_result_550_){
_start:
{
lean_object* v_val_552_; lean_object* v_val_556_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_box(0);
v___x_584_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_540_, v___x_583_);
if (v___x_584_ == 0)
{
switch(lean_obj_tag(v_c_549_))
{
case 2:
{
lean_object* v___x_585_; 
v___x_585_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_549_);
v_val_556_ = v___x_585_;
goto v___jp_555_;
}
case 3:
{
lean_object* v___x_586_; 
v___x_586_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_549_);
v_val_556_ = v___x_586_;
goto v___jp_555_;
}
default: 
{
v_val_556_ = v_c_549_;
goto v___jp_555_;
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v_c_549_);
lean_dec_ref(v___f_548_);
lean_dec(v_key_545_);
lean_dec_ref(v_inst_544_);
lean_dec(v_snd_543_);
lean_dec_ref(v_todo_542_);
lean_dec_ref(v_push_541_);
lean_dec(v_fst_540_);
v___x_587_ = lean_apply_2(v_toPure_546_, lean_box(0), v_result_550_);
return v___x_587_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_push_541_);
v___x_553_ = lean_apply_2(v_push_541_, v_todo_542_, v_snd_543_);
v___x_554_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg(v_inst_544_, v_key_545_, v_push_541_, v___x_553_, v_val_552_, v_result_550_);
return v___x_554_;
}
v___jp_555_:
{
if (lean_obj_tag(v_val_556_) == 0)
{
lean_object* v_key_557_; lean_object* v_child_558_; uint8_t v___x_559_; 
lean_dec_ref(v___f_548_);
v_key_557_ = lean_ctor_get(v_val_556_, 0);
lean_inc(v_key_557_);
v_child_558_ = lean_ctor_get(v_val_556_, 1);
lean_inc_ref(v_child_558_);
lean_dec_ref_known(v_val_556_, 2);
v___x_559_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_557_, v_fst_540_);
lean_dec(v_fst_540_);
lean_dec(v_key_557_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec_ref(v_child_558_);
lean_dec(v_key_545_);
lean_dec_ref(v_inst_544_);
lean_dec(v_snd_543_);
lean_dec_ref(v_todo_542_);
lean_dec_ref(v_push_541_);
v___x_560_ = lean_apply_2(v_toPure_546_, lean_box(0), v_result_550_);
return v___x_560_;
}
else
{
lean_dec(v_toPure_546_);
v_val_552_ = v_child_558_;
goto v___jp_551_;
}
}
else
{
lean_object* v_children_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_581_; 
v_children_561_ = lean_ctor_get(v_val_556_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_val_556_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_val_556_, 0);
lean_dec(v_unused_582_);
v___x_563_ = v_val_556_;
v_isShared_564_ = v_isSharedCheck_581_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_children_561_);
lean_dec(v_val_556_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_581_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_array_get_size(v_children_561_);
v___x_567_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_del_object(v___x_563_);
lean_dec_ref(v_children_561_);
lean_dec_ref(v___f_548_);
lean_dec(v_key_545_);
lean_dec_ref(v_inst_544_);
lean_dec(v_snd_543_);
lean_dec_ref(v_todo_542_);
lean_dec_ref(v_push_541_);
lean_dec(v_fst_540_);
v___x_568_ = lean_apply_2(v_toPure_546_, lean_box(0), v_result_550_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_nat_sub(v___x_566_, v___x_547_);
v___x_570_ = lean_nat_dec_le(v___x_565_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v___x_569_);
lean_del_object(v___x_563_);
lean_dec_ref(v_children_561_);
lean_dec_ref(v___f_548_);
lean_dec(v_key_545_);
lean_dec_ref(v_inst_544_);
lean_dec(v_snd_543_);
lean_dec_ref(v_todo_542_);
lean_dec_ref(v_push_541_);
lean_dec(v_fst_540_);
v___x_571_ = lean_apply_2(v_toPure_546_, lean_box(0), v_result_550_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__1));
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 0);
lean_ctor_set(v___x_563_, 1, v___x_572_);
lean_ctor_set(v___x_563_, 0, v_fst_540_);
v___x_574_ = v___x_563_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_fst_540_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_572_);
v___x_574_ = v_reuseFailAlloc_580_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_findChild_x3f___redArg___closed__2));
v___x_576_ = l_Array_binSearchAux___redArg(v___f_548_, v___x_575_, v_children_561_, v___x_574_, v___x_565_, v___x_569_);
lean_dec_ref(v_children_561_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; 
lean_dec(v_key_545_);
lean_dec_ref(v_inst_544_);
lean_dec(v_snd_543_);
lean_dec_ref(v_todo_542_);
lean_dec_ref(v_push_541_);
v___x_577_ = lean_apply_2(v_toPure_546_, lean_box(0), v_result_550_);
return v___x_577_;
}
else
{
lean_object* v_val_578_; lean_object* v_snd_579_; 
lean_dec(v_toPure_546_);
v_val_578_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v___x_576_, 1);
v_snd_579_ = lean_ctor_get(v_val_578_, 1);
lean_inc(v_snd_579_);
lean_dec(v_val_578_);
v_val_552_ = v_snd_579_;
goto v___jp_551_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__2___boxed(lean_object* v_fst_588_, lean_object* v_push_589_, lean_object* v_todo_590_, lean_object* v_snd_591_, lean_object* v_inst_592_, lean_object* v_key_593_, lean_object* v_toPure_594_, lean_object* v___x_595_, lean_object* v___f_596_, lean_object* v_c_597_, lean_object* v_result_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__2(v_fst_588_, v_push_589_, v_todo_590_, v_snd_591_, v_inst_592_, v_key_593_, v_toPure_594_, v___x_595_, v___f_596_, v_c_597_, v_result_598_);
lean_dec(v___x_595_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__5(lean_object* v_push_600_, lean_object* v_todo_601_, lean_object* v_inst_602_, lean_object* v_key_603_, lean_object* v_toPure_604_, lean_object* v___x_605_, lean_object* v___f_606_, lean_object* v_c_607_, lean_object* v_result_608_, lean_object* v_toBind_609_, lean_object* v_____x_610_){
_start:
{
lean_object* v_fst_611_; lean_object* v_snd_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v_val_619_; lean_object* v_val_623_; 
v_fst_611_ = lean_ctor_get(v_____x_610_, 0);
lean_inc(v_fst_611_);
v_snd_612_ = lean_ctor_get(v_____x_610_, 1);
lean_inc(v_snd_612_);
lean_dec_ref(v_____x_610_);
lean_inc_ref(v_c_607_);
lean_inc(v_toPure_604_);
lean_inc(v_key_603_);
lean_inc_ref(v_inst_602_);
lean_inc_ref(v_todo_601_);
lean_inc_ref(v_push_600_);
v___f_613_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_613_, 0, v_fst_611_);
lean_closure_set(v___f_613_, 1, v_push_600_);
lean_closure_set(v___f_613_, 2, v_todo_601_);
lean_closure_set(v___f_613_, 3, v_snd_612_);
lean_closure_set(v___f_613_, 4, v_inst_602_);
lean_closure_set(v___f_613_, 5, v_key_603_);
lean_closure_set(v___f_613_, 6, v_toPure_604_);
lean_closure_set(v___f_613_, 7, v___x_605_);
lean_closure_set(v___f_613_, 8, v___f_606_);
lean_closure_set(v___f_613_, 9, v_c_607_);
v___f_614_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg___lam__3), 2, 1);
lean_closure_set(v___f_614_, 0, v___f_613_);
switch(lean_obj_tag(v_c_607_))
{
case 2:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_607_);
v_val_623_ = v___x_637_;
goto v___jp_622_;
}
case 3:
{
lean_object* v___x_638_; 
v___x_638_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_607_);
v_val_623_ = v___x_638_;
goto v___jp_622_;
}
default: 
{
v_val_623_ = v_c_607_;
goto v___jp_622_;
}
}
v___jp_615_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_apply_2(v_toPure_604_, lean_box(0), v_result_608_);
v___x_617_ = lean_apply_4(v_toBind_609_, lean_box(0), lean_box(0), v___x_616_, v___f_614_);
return v___x_617_;
}
v___jp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg(v_inst_602_, v_key_603_, v_push_600_, v_todo_601_, v_val_619_, v_result_608_);
v___x_621_ = lean_apply_4(v_toBind_609_, lean_box(0), lean_box(0), v___x_620_, v___f_614_);
return v___x_621_;
}
v___jp_622_:
{
if (lean_obj_tag(v_val_623_) == 0)
{
lean_object* v_key_624_; lean_object* v_child_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_key_624_ = lean_ctor_get(v_val_623_, 0);
lean_inc(v_key_624_);
v_child_625_ = lean_ctor_get(v_val_623_, 1);
lean_inc_ref(v_child_625_);
lean_dec_ref_known(v_val_623_, 2);
v___x_626_ = lean_box(0);
v___x_627_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_key_624_, v___x_626_);
lean_dec(v_key_624_);
if (v___x_627_ == 0)
{
lean_dec_ref(v_child_625_);
lean_dec(v_key_603_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_todo_601_);
lean_dec_ref(v_push_600_);
goto v___jp_615_;
}
else
{
lean_dec(v_toPure_604_);
v_val_619_ = v_child_625_;
goto v___jp_618_;
}
}
else
{
lean_object* v_children_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_children_628_ = lean_ctor_get(v_val_623_, 1);
lean_inc_ref(v_children_628_);
lean_dec_ref_known(v_val_623_, 2);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_array_get_size(v_children_628_);
v___x_631_ = lean_nat_dec_lt(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec_ref(v_children_628_);
lean_dec(v_key_603_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_todo_601_);
lean_dec_ref(v_push_600_);
goto v___jp_615_;
}
else
{
lean_object* v___x_632_; lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_632_ = lean_array_fget(v_children_628_, v___x_629_);
lean_dec_ref(v_children_628_);
v_fst_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_fst_633_);
v_snd_634_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_snd_634_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_633_, v___x_635_);
lean_dec(v_fst_633_);
if (v___x_636_ == 0)
{
lean_dec(v_snd_634_);
lean_dec(v_key_603_);
lean_dec_ref(v_inst_602_);
lean_dec_ref(v_todo_601_);
lean_dec_ref(v_push_600_);
goto v___jp_615_;
}
else
{
lean_dec(v_toPure_604_);
v_val_619_ = v_snd_634_;
goto v___jp_618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_getMatchLoop(lean_object* v_m_639_, lean_object* v_00_u03b2_640_, lean_object* v_00_u03b1_641_, lean_object* v_inst_642_, lean_object* v_key_643_, lean_object* v_push_644_, lean_object* v_todo_645_, lean_object* v_c_646_, lean_object* v_result_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_DiscrTree_Trie_getMatchLoop___redArg(v_inst_642_, v_key_643_, v_push_644_, v_todo_645_, v_c_646_, v_result_647_);
return v___x_648_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_t_649_){
_start:
{
lean_object* v_val_651_; 
switch(lean_obj_tag(v_t_649_))
{
case 2:
{
lean_object* v___x_660_; 
v___x_660_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_649_);
v_val_651_ = v___x_660_;
goto v___jp_650_;
}
case 3:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_649_);
v_val_651_ = v___x_661_;
goto v___jp_650_;
}
default: 
{
v_val_651_ = v_t_649_;
goto v___jp_650_;
}
}
v___jp_650_:
{
if (lean_obj_tag(v_val_651_) == 0)
{
uint8_t v___x_652_; 
lean_dec_ref_known(v_val_651_, 2);
v___x_652_ = 0;
return v___x_652_;
}
else
{
lean_object* v_vs_653_; lean_object* v_children_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_vs_653_ = lean_ctor_get(v_val_651_, 0);
lean_inc_ref(v_vs_653_);
v_children_654_ = lean_ctor_get(v_val_651_, 1);
lean_inc_ref(v_children_654_);
lean_dec_ref_known(v_val_651_, 2);
v___x_655_ = lean_array_get_size(v_vs_653_);
lean_dec_ref(v_vs_653_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec_ref(v_children_654_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_658_ = lean_array_get_size(v_children_654_);
lean_dec_ref(v_children_654_);
v___x_659_ = lean_nat_dec_eq(v___x_658_, v___x_656_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_t_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_t_662_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_665_, lean_object* v_t_666_){
_start:
{
lean_object* v_val_668_; 
switch(lean_obj_tag(v_t_666_))
{
case 2:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_666_);
v_val_668_ = v___x_677_;
goto v___jp_667_;
}
case 3:
{
lean_object* v___x_678_; 
v___x_678_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_666_);
v_val_668_ = v___x_678_;
goto v___jp_667_;
}
default: 
{
v_val_668_ = v_t_666_;
goto v___jp_667_;
}
}
v___jp_667_:
{
if (lean_obj_tag(v_val_668_) == 0)
{
uint8_t v___x_669_; 
lean_dec_ref_known(v_val_668_, 2);
v___x_669_ = 0;
return v___x_669_;
}
else
{
lean_object* v_vs_670_; lean_object* v_children_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_vs_670_ = lean_ctor_get(v_val_668_, 0);
lean_inc_ref(v_vs_670_);
v_children_671_ = lean_ctor_get(v_val_668_, 1);
lean_inc_ref(v_children_671_);
lean_dec_ref_known(v_val_668_, 2);
v___x_672_ = lean_array_get_size(v_vs_670_);
lean_dec_ref(v_vs_670_);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_nat_dec_eq(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec_ref(v_children_671_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_children_671_);
lean_dec_ref(v_children_671_);
v___x_676_ = lean_nat_dec_eq(v___x_675_, v___x_673_);
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_679_, lean_object* v_t_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_679_, v_t_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__3(lean_object* v_f_683_, lean_object* v_initialKeys_684_, lean_object* v_s_685_, lean_object* v_v_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_apply_3(v_f_683_, v_s_685_, v_initialKeys_684_, v_v_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(lean_object* v___f_688_, lean_object* v_s_689_, lean_object* v_x_690_){
_start:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_693_; 
v_fst_691_ = lean_ctor_get(v_x_690_, 0);
lean_inc(v_fst_691_);
v_snd_692_ = lean_ctor_get(v_x_690_, 1);
lean_inc(v_snd_692_);
lean_dec_ref(v_x_690_);
v___x_693_ = lean_apply_3(v___f_688_, v_s_689_, v_fst_691_, v_snd_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object* v___f_694_, lean_object* v_toApplicative_695_, lean_object* v_inst_696_, lean_object* v___f_697_, lean_object* v_t_698_, lean_object* v_s_699_){
_start:
{
lean_object* v_val_701_; 
switch(lean_obj_tag(v_t_698_))
{
case 2:
{
lean_object* v___x_714_; 
v___x_714_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_698_);
v_val_701_ = v___x_714_;
goto v___jp_700_;
}
case 3:
{
lean_object* v___x_715_; 
v___x_715_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_698_);
v_val_701_ = v___x_715_;
goto v___jp_700_;
}
default: 
{
v_val_701_ = v_t_698_;
goto v___jp_700_;
}
}
v___jp_700_:
{
if (lean_obj_tag(v_val_701_) == 0)
{
lean_object* v_key_702_; lean_object* v_child_703_; lean_object* v___x_704_; 
lean_dec(v___f_697_);
lean_dec_ref(v_inst_696_);
lean_dec_ref(v_toApplicative_695_);
v_key_702_ = lean_ctor_get(v_val_701_, 0);
lean_inc(v_key_702_);
v_child_703_ = lean_ctor_get(v_val_701_, 1);
lean_inc_ref(v_child_703_);
lean_dec_ref_known(v_val_701_, 2);
v___x_704_ = lean_apply_3(v___f_694_, v_s_699_, v_key_702_, v_child_703_);
return v___x_704_;
}
else
{
lean_object* v_children_705_; lean_object* v_toPure_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
lean_dec(v___f_694_);
v_children_705_ = lean_ctor_get(v_val_701_, 1);
lean_inc_ref(v_children_705_);
lean_dec_ref_known(v_val_701_, 2);
v_toPure_706_ = lean_ctor_get(v_toApplicative_695_, 1);
lean_inc(v_toPure_706_);
lean_dec_ref(v_toApplicative_695_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_array_get_size(v_children_705_);
v___x_709_ = lean_nat_dec_lt(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v_children_705_);
lean_dec(v___f_697_);
lean_dec_ref(v_inst_696_);
v___x_710_ = lean_apply_2(v_toPure_706_, lean_box(0), v_s_699_);
return v___x_710_;
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
lean_dec(v_toPure_706_);
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_708_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_696_, v___f_697_, v_children_705_, v___x_711_, v___x_712_, v_s_699_);
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object* v_inst_716_, lean_object* v_initialKeys_717_, lean_object* v_f_718_, lean_object* v_init_719_, lean_object* v_t_720_){
_start:
{
if (lean_obj_tag(v_t_720_) == 3)
{
lean_object* v_keys_721_; lean_object* v_i_722_; lean_object* v_v_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_inst_716_);
v_keys_721_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_keys_721_);
v_i_722_ = lean_ctor_get(v_t_720_, 1);
lean_inc(v_i_722_);
v_v_723_ = lean_ctor_get(v_t_720_, 2);
lean_inc(v_v_723_);
lean_dec_ref_known(v_t_720_, 3);
v___x_724_ = lean_array_get_size(v_keys_721_);
v___x_725_ = l_Array_extract___redArg(v_keys_721_, v_i_722_, v___x_724_);
lean_dec_ref(v_keys_721_);
v___x_726_ = l_Array_append___redArg(v_initialKeys_717_, v___x_725_);
lean_dec_ref(v___x_725_);
v___x_727_ = lean_apply_3(v_f_718_, v_init_719_, v___x_726_, v_v_723_);
return v___x_727_;
}
else
{
lean_object* v_toApplicative_728_; lean_object* v_toBind_729_; lean_object* v___f_730_; lean_object* v___f_731_; lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___y_735_; lean_object* v_val_747_; 
v_toApplicative_728_ = lean_ctor_get(v_inst_716_, 0);
v_toBind_729_ = lean_ctor_get(v_inst_716_, 1);
lean_inc(v_toBind_729_);
lean_inc(v_f_718_);
lean_inc_ref_n(v_inst_716_, 2);
lean_inc_ref(v_initialKeys_717_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0), 6, 3);
lean_closure_set(v___f_730_, 0, v_initialKeys_717_);
lean_closure_set(v___f_730_, 1, v_inst_716_);
lean_closure_set(v___f_730_, 2, v_f_718_);
lean_inc_ref(v___f_730_);
v___f_731_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1), 3, 1);
lean_closure_set(v___f_731_, 0, v___f_730_);
lean_inc_ref(v_t_720_);
lean_inc_ref(v_toApplicative_728_);
v___f_732_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2), 6, 5);
lean_closure_set(v___f_732_, 0, v___f_730_);
lean_closure_set(v___f_732_, 1, v_toApplicative_728_);
lean_closure_set(v___f_732_, 2, v_inst_716_);
lean_closure_set(v___f_732_, 3, v___f_731_);
lean_closure_set(v___f_732_, 4, v_t_720_);
v___f_733_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__3), 4, 2);
lean_closure_set(v___f_733_, 0, v_f_718_);
lean_closure_set(v___f_733_, 1, v_initialKeys_717_);
switch(lean_obj_tag(v_t_720_))
{
case 2:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_720_);
v_val_747_ = v___x_750_;
goto v___jp_746_;
}
case 3:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_720_);
v_val_747_ = v___x_751_;
goto v___jp_746_;
}
default: 
{
v_val_747_ = v_t_720_;
goto v___jp_746_;
}
}
v___jp_734_:
{
lean_object* v_toPure_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_toPure_736_ = lean_ctor_get(v_toApplicative_728_, 1);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_array_get_size(v___y_735_);
v___x_739_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_inc(v_toPure_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v___f_733_);
lean_dec_ref(v_inst_716_);
v___x_740_ = lean_apply_2(v_toPure_736_, lean_box(0), v_init_719_);
v___x_741_ = lean_apply_4(v_toBind_729_, lean_box(0), lean_box(0), v___x_740_, v___f_732_);
return v___x_741_;
}
else
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_742_ = ((size_t)0ULL);
v___x_743_ = lean_usize_of_nat(v___x_738_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_716_, v___f_733_, v___y_735_, v___x_742_, v___x_743_, v_init_719_);
v___x_745_ = lean_apply_4(v_toBind_729_, lean_box(0), lean_box(0), v___x_744_, v___f_732_);
return v___x_745_;
}
}
v___jp_746_:
{
if (lean_obj_tag(v_val_747_) == 0)
{
lean_object* v___x_748_; 
lean_dec_ref_known(v_val_747_, 2);
v___x_748_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_735_ = v___x_748_;
goto v___jp_734_;
}
else
{
lean_object* v_vs_749_; 
v_vs_749_ = lean_ctor_get(v_val_747_, 0);
lean_inc_ref(v_vs_749_);
lean_dec_ref_known(v_val_747_, 2);
v___y_735_ = v_vs_749_;
goto v___jp_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object* v_initialKeys_752_, lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_s_755_, lean_object* v_k_756_, lean_object* v_c_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_array_push(v_initialKeys_752_, v_k_756_);
v___x_759_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_753_, v___x_758_, v_f_754_, v_s_755_, v_c_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object* v_m_760_, lean_object* v_00_u03c3_761_, lean_object* v_00_u03b1_762_, lean_object* v_inst_763_, lean_object* v_initialKeys_764_, lean_object* v_f_765_, lean_object* v_init_766_, lean_object* v_t_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_763_, v_initialKeys_764_, v_f_765_, v_init_766_, v_t_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object* v_f_769_, lean_object* v_s_770_, lean_object* v_k_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_apply_3(v_f_769_, v_s_770_, v_k_771_, v_a_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object* v_initialKeys_793_, lean_object* v_f_794_, lean_object* v_init_795_, lean_object* v_t_796_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_797_, 0, v_f_794_);
v___x_798_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_799_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_798_, v_initialKeys_793_, v___f_797_, v_init_795_, v_t_796_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object* v_00_u03c3_800_, lean_object* v_00_u03b1_801_, lean_object* v_initialKeys_802_, lean_object* v_f_803_, lean_object* v_init_804_, lean_object* v_t_805_){
_start:
{
lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_806_, 0, v_f_803_);
v___x_807_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_808_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_807_, v_initialKeys_802_, v___f_806_, v_init_804_, v_t_805_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__1(lean_object* v_inst_809_, lean_object* v_f_810_, lean_object* v_toApplicative_811_, lean_object* v___f_812_, lean_object* v_t_813_, lean_object* v_s_814_){
_start:
{
lean_object* v_val_816_; 
switch(lean_obj_tag(v_t_813_))
{
case 2:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_813_);
v_val_816_ = v___x_828_;
goto v___jp_815_;
}
case 3:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_813_);
v_val_816_ = v___x_829_;
goto v___jp_815_;
}
default: 
{
v_val_816_ = v_t_813_;
goto v___jp_815_;
}
}
v___jp_815_:
{
if (lean_obj_tag(v_val_816_) == 0)
{
lean_object* v_child_817_; lean_object* v___x_818_; 
lean_dec(v___f_812_);
lean_dec_ref(v_toApplicative_811_);
v_child_817_ = lean_ctor_get(v_val_816_, 1);
lean_inc_ref(v_child_817_);
lean_dec_ref_known(v_val_816_, 2);
v___x_818_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_809_, v_f_810_, v_s_814_, v_child_817_);
return v___x_818_;
}
else
{
lean_object* v_children_819_; lean_object* v_toPure_820_; lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
lean_dec(v_f_810_);
v_children_819_ = lean_ctor_get(v_val_816_, 1);
lean_inc_ref(v_children_819_);
lean_dec_ref_known(v_val_816_, 2);
v_toPure_820_ = lean_ctor_get(v_toApplicative_811_, 1);
lean_inc(v_toPure_820_);
lean_dec_ref(v_toApplicative_811_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_array_get_size(v_children_819_);
v___x_823_ = lean_nat_dec_lt(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v_children_819_);
lean_dec(v___f_812_);
lean_dec_ref(v_inst_809_);
v___x_824_ = lean_apply_2(v_toPure_820_, lean_box(0), v_s_814_);
return v___x_824_;
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
lean_dec(v_toPure_820_);
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_822_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_809_, v___f_812_, v_children_819_, v___x_825_, v___x_826_, v_s_814_);
return v___x_827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object* v_inst_830_, lean_object* v_f_831_, lean_object* v_init_832_, lean_object* v_t_833_){
_start:
{
if (lean_obj_tag(v_t_833_) == 3)
{
lean_object* v_v_834_; lean_object* v___x_835_; 
lean_dec_ref(v_inst_830_);
v_v_834_ = lean_ctor_get(v_t_833_, 2);
lean_inc(v_v_834_);
lean_dec_ref_known(v_t_833_, 3);
v___x_835_ = lean_apply_2(v_f_831_, v_init_832_, v_v_834_);
return v___x_835_;
}
else
{
lean_object* v_toApplicative_836_; lean_object* v_toBind_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___y_841_; lean_object* v_val_853_; 
v_toApplicative_836_ = lean_ctor_get(v_inst_830_, 0);
v_toBind_837_ = lean_ctor_get(v_inst_830_, 1);
lean_inc(v_toBind_837_);
lean_inc_n(v_f_831_, 2);
lean_inc_ref_n(v_inst_830_, 2);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_838_, 0, v_inst_830_);
lean_closure_set(v___f_838_, 1, v_f_831_);
lean_inc_ref(v_t_833_);
lean_inc_ref(v_toApplicative_836_);
v___f_839_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_839_, 0, v_inst_830_);
lean_closure_set(v___f_839_, 1, v_f_831_);
lean_closure_set(v___f_839_, 2, v_toApplicative_836_);
lean_closure_set(v___f_839_, 3, v___f_838_);
lean_closure_set(v___f_839_, 4, v_t_833_);
switch(lean_obj_tag(v_t_833_))
{
case 2:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_833_);
v_val_853_ = v___x_856_;
goto v___jp_852_;
}
case 3:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_833_);
v_val_853_ = v___x_857_;
goto v___jp_852_;
}
default: 
{
v_val_853_ = v_t_833_;
goto v___jp_852_;
}
}
v___jp_840_:
{
lean_object* v_toPure_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_toPure_842_ = lean_ctor_get(v_toApplicative_836_, 1);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_array_get_size(v___y_841_);
v___x_845_ = lean_nat_dec_lt(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_inc(v_toPure_842_);
lean_dec_ref(v___y_841_);
lean_dec(v_f_831_);
lean_dec_ref(v_inst_830_);
v___x_846_ = lean_apply_2(v_toPure_842_, lean_box(0), v_init_832_);
v___x_847_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v___x_846_, v___f_839_);
return v___x_847_;
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = ((size_t)0ULL);
v___x_849_ = lean_usize_of_nat(v___x_844_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_830_, v_f_831_, v___y_841_, v___x_848_, v___x_849_, v_init_832_);
v___x_851_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v___x_850_, v___f_839_);
return v___x_851_;
}
}
v___jp_852_:
{
if (lean_obj_tag(v_val_853_) == 0)
{
lean_object* v___x_854_; 
lean_dec_ref_known(v_val_853_, 2);
v___x_854_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_841_ = v___x_854_;
goto v___jp_840_;
}
else
{
lean_object* v_vs_855_; 
v_vs_855_ = lean_ctor_get(v_val_853_, 0);
lean_inc_ref(v_vs_855_);
lean_dec_ref_known(v_val_853_, 2);
v___y_841_ = v_vs_855_;
goto v___jp_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object* v_inst_858_, lean_object* v_f_859_, lean_object* v_s_860_, lean_object* v_x_861_){
_start:
{
lean_object* v_snd_862_; lean_object* v___x_863_; 
v_snd_862_ = lean_ctor_get(v_x_861_, 1);
lean_inc(v_snd_862_);
lean_dec_ref(v_x_861_);
v___x_863_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_858_, v_f_859_, v_s_860_, v_snd_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object* v_m_864_, lean_object* v_00_u03c3_865_, lean_object* v_00_u03b1_866_, lean_object* v_inst_867_, lean_object* v_f_868_, lean_object* v_init_869_, lean_object* v_t_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_867_, v_f_868_, v_init_869_, v_t_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object* v_f_872_, lean_object* v_x1_873_, lean_object* v_x2_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = lean_apply_2(v_f_872_, v_x1_873_, v_x2_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object* v_f_876_, lean_object* v_init_877_, lean_object* v_t_878_){
_start:
{
lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___f_879_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_879_, 0, v_f_876_);
v___x_880_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_881_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_880_, v___f_879_, v_init_877_, v_t_878_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object* v_00_u03c3_882_, lean_object* v_00_u03b1_883_, lean_object* v_f_884_, lean_object* v_init_885_, lean_object* v_t_886_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_887_, 0, v_f_884_);
v___x_888_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_889_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_888_, v___f_887_, v_init_885_, v_t_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object* v_t_890_){
_start:
{
lean_object* v___y_892_; lean_object* v_val_893_; lean_object* v___y_905_; lean_object* v_val_910_; 
if (lean_obj_tag(v_t_890_) == 3)
{
lean_object* v___x_913_; 
lean_dec_ref_known(v_t_890_, 3);
v___x_913_ = lean_unsigned_to_nat(1u);
return v___x_913_;
}
else
{
switch(lean_obj_tag(v_t_890_))
{
case 2:
{
lean_object* v___x_914_; 
lean_inc_ref(v_t_890_);
v___x_914_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_890_);
v_val_910_ = v___x_914_;
goto v___jp_909_;
}
case 3:
{
lean_object* v___x_915_; 
lean_inc_ref(v_t_890_);
v___x_915_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_890_);
v_val_910_ = v___x_915_;
goto v___jp_909_;
}
default: 
{
lean_inc_ref(v_t_890_);
v_val_910_ = v_t_890_;
goto v___jp_909_;
}
}
}
v___jp_891_:
{
if (lean_obj_tag(v_val_893_) == 0)
{
lean_object* v_child_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_child_894_ = lean_ctor_get(v_val_893_, 1);
lean_inc_ref(v_child_894_);
lean_dec_ref_known(v_val_893_, 2);
v___x_895_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_child_894_);
v___x_896_ = lean_nat_add(v___y_892_, v___x_895_);
lean_dec(v___x_895_);
lean_dec(v___y_892_);
return v___x_896_;
}
else
{
lean_object* v_children_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_children_897_ = lean_ctor_get(v_val_893_, 1);
lean_inc_ref(v_children_897_);
lean_dec_ref_known(v_val_893_, 2);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_array_get_size(v_children_897_);
v___x_900_ = lean_nat_dec_lt(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_dec_ref(v_children_897_);
return v___y_892_;
}
else
{
size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
v___x_901_ = ((size_t)0ULL);
v___x_902_ = lean_usize_of_nat(v___x_899_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_897_, v___x_901_, v___x_902_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v_children_897_);
return v___x_903_;
}
}
}
v___jp_904_:
{
lean_object* v___x_906_; 
v___x_906_ = lean_array_get_size(v___y_905_);
lean_dec_ref(v___y_905_);
switch(lean_obj_tag(v_t_890_))
{
case 2:
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_890_);
v___y_892_ = v___x_906_;
v_val_893_ = v___x_907_;
goto v___jp_891_;
}
case 3:
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_890_);
v___y_892_ = v___x_906_;
v_val_893_ = v___x_908_;
goto v___jp_891_;
}
default: 
{
v___y_892_ = v___x_906_;
v_val_893_ = v_t_890_;
goto v___jp_891_;
}
}
}
v___jp_909_:
{
if (lean_obj_tag(v_val_910_) == 0)
{
lean_object* v___x_911_; 
lean_dec_ref_known(v_val_910_, 2);
v___x_911_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___y_905_ = v___x_911_;
goto v___jp_904_;
}
else
{
lean_object* v_vs_912_; 
v_vs_912_ = lean_ctor_get(v_val_910_, 0);
lean_inc_ref(v_vs_912_);
lean_dec_ref_known(v_val_910_, 2);
v___y_905_ = v_vs_912_;
goto v___jp_904_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(lean_object* v_as_916_, size_t v_i_917_, size_t v_stop_918_, lean_object* v_b_919_){
_start:
{
uint8_t v___x_920_; 
v___x_920_ = lean_usize_dec_eq(v_i_917_, v_stop_918_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v_snd_922_; lean_object* v___x_923_; lean_object* v___x_924_; size_t v___x_925_; size_t v___x_926_; 
v___x_921_ = lean_array_uget_borrowed(v_as_916_, v_i_917_);
v_snd_922_ = lean_ctor_get(v___x_921_, 1);
lean_inc(v_snd_922_);
v___x_923_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_922_);
v___x_924_ = lean_nat_add(v_b_919_, v___x_923_);
lean_dec(v___x_923_);
lean_dec(v_b_919_);
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_917_, v___x_925_);
v_i_917_ = v___x_926_;
v_b_919_ = v___x_924_;
goto _start;
}
else
{
return v_b_919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_928_, size_t v_i_929_, size_t v_stop_930_, lean_object* v_b_931_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = lean_usize_dec_eq(v_i_929_, v_stop_930_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v_snd_934_; lean_object* v___x_935_; lean_object* v___x_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; 
v___x_933_ = lean_array_uget_borrowed(v_as_928_, v_i_929_);
v_snd_934_ = lean_ctor_get(v___x_933_, 1);
lean_inc(v_snd_934_);
v___x_935_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_934_);
v___x_936_ = lean_nat_add(v_b_931_, v___x_935_);
lean_dec(v___x_935_);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_929_, v___x_937_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(v_as_928_, v___x_938_, v_stop_930_, v___x_936_);
return v___x_939_;
}
else
{
lean_inc(v_b_931_);
return v_b_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_940_, lean_object* v_i_941_, lean_object* v_stop_942_, lean_object* v_b_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; lean_object* v_res_946_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_942_);
lean_dec(v_stop_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_940_, v_i_boxed_944_, v_stop_boxed_945_, v_b_943_);
lean_dec(v_b_943_);
lean_dec_ref(v_as_940_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg___boxed(lean_object* v_as_947_, lean_object* v_i_948_, lean_object* v_stop_949_, lean_object* v_b_950_){
_start:
{
size_t v_i_boxed_951_; size_t v_stop_boxed_952_; lean_object* v_res_953_; 
v_i_boxed_951_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_stop_boxed_952_ = lean_unbox_usize(v_stop_949_);
lean_dec(v_stop_949_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(v_as_947_, v_i_boxed_951_, v_stop_boxed_952_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_954_, lean_object* v_t_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_957_, lean_object* v_as_958_, size_t v_i_959_, size_t v_stop_960_, lean_object* v_b_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_958_, v_i_959_, v_stop_960_, v_b_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_963_, lean_object* v_as_964_, lean_object* v_i_965_, lean_object* v_stop_966_, lean_object* v_b_967_){
_start:
{
size_t v_i_boxed_968_; size_t v_stop_boxed_969_; lean_object* v_res_970_; 
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_stop_boxed_969_ = lean_unbox_usize(v_stop_966_);
lean_dec(v_stop_966_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_963_, v_as_964_, v_i_boxed_968_, v_stop_boxed_969_, v_b_967_);
lean_dec(v_b_967_);
lean_dec_ref(v_as_964_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0(lean_object* v_00_u03b1_971_, lean_object* v_as_972_, size_t v_i_973_, size_t v_stop_974_, lean_object* v_b_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___redArg(v_as_972_, v_i_973_, v_stop_974_, v_b_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0___boxed(lean_object* v_00_u03b1_977_, lean_object* v_as_978_, lean_object* v_i_979_, lean_object* v_stop_980_, lean_object* v_b_981_){
_start:
{
size_t v_i_boxed_982_; size_t v_stop_boxed_983_; lean_object* v_res_984_; 
v_i_boxed_982_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_stop_boxed_983_ = lean_unbox_usize(v_stop_980_);
lean_dec(v_stop_980_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_spec__0(v_00_u03b1_977_, v_as_978_, v_i_boxed_982_, v_stop_boxed_983_, v_b_981_);
lean_dec_ref(v_as_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_985_, lean_object* v_f_986_, lean_object* v_s_987_, lean_object* v_k_988_, lean_object* v_t_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
v___x_992_ = lean_array_push(v___x_991_, v_k_988_);
v___x_993_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_985_, v___x_992_, v_f_986_, v_s_987_, v_t_989_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_994_, lean_object* v_f_995_, lean_object* v_init_996_, lean_object* v_t_997_){
_start:
{
lean_object* v___f_998_; lean_object* v___x_999_; 
lean_inc_ref(v_inst_994_);
v___f_998_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_998_, 0, v_inst_994_);
lean_closure_set(v___f_998_, 1, v_f_995_);
v___x_999_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_994_, v___f_998_, v_t_997_, v_init_996_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_1000_, lean_object* v_00_u03c3_1001_, lean_object* v_00_u03b1_1002_, lean_object* v_inst_1003_, lean_object* v_f_1004_, lean_object* v_init_1005_, lean_object* v_t_1006_){
_start:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; 
lean_inc_ref(v_inst_1003_);
v___f_1007_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1007_, 0, v_inst_1003_);
lean_closure_set(v___f_1007_, 1, v_f_1004_);
v___x_1008_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1003_, v___f_1007_, v_t_1006_, v_init_1005_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_1009_, lean_object* v_s_1010_, lean_object* v_keys_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_apply_3(v_f_1009_, v_s_1010_, v_keys_1011_, v_a_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_1014_, lean_object* v___f_1015_, lean_object* v_s_1016_, lean_object* v_k_1017_, lean_object* v_t_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_mk_empty_array_with_capacity(v___x_1019_);
v___x_1021_ = lean_array_push(v___x_1020_, v_k_1017_);
v___x_1022_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_1014_, v___x_1021_, v___f_1015_, v_s_1016_, v_t_1018_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_1023_, lean_object* v_init_1024_, lean_object* v_t_1025_){
_start:
{
lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; 
v___f_1026_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1026_, 0, v_f_1023_);
v___x_1027_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
lean_closure_set(v___f_1028_, 1, v___f_1026_);
v___x_1029_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1027_, v___f_1028_, v_t_1025_, v_init_1024_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_1030_, lean_object* v_00_u03b1_1031_, lean_object* v_f_1032_, lean_object* v_init_1033_, lean_object* v_t_1034_){
_start:
{
lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; 
v___f_1035_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1035_, 0, v_f_1032_);
v___x_1036_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1037_, 0, v___x_1036_);
lean_closure_set(v___f_1037_, 1, v___f_1035_);
v___x_1038_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1036_, v___f_1037_, v_t_1034_, v_init_1033_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_1039_, lean_object* v_f_1040_, lean_object* v_s_1041_, lean_object* v_x_1042_, lean_object* v_t_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_1039_, v_f_1040_, v_s_1041_, v_t_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_1045_, lean_object* v_f_1046_, lean_object* v_s_1047_, lean_object* v_x_1048_, lean_object* v_t_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_1045_, v_f_1046_, v_s_1047_, v_x_1048_, v_t_1049_);
lean_dec(v_x_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_1051_, lean_object* v_f_1052_, lean_object* v_init_1053_, lean_object* v_t_1054_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; 
lean_inc_ref(v_inst_1051_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1055_, 0, v_inst_1051_);
lean_closure_set(v___f_1055_, 1, v_f_1052_);
v___x_1056_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1051_, v___f_1055_, v_t_1054_, v_init_1053_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_1057_, lean_object* v_00_u03c3_1058_, lean_object* v_00_u03b1_1059_, lean_object* v_inst_1060_, lean_object* v_f_1061_, lean_object* v_init_1062_, lean_object* v_t_1063_){
_start:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; 
lean_inc_ref(v_inst_1060_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1064_, 0, v_inst_1060_);
lean_closure_set(v___f_1064_, 1, v_f_1061_);
v___x_1065_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1060_, v___f_1064_, v_t_1063_, v_init_1062_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_1066_, lean_object* v___f_1067_, lean_object* v_s_1068_, lean_object* v_x_1069_, lean_object* v_t_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_1066_, v___f_1067_, v_s_1068_, v_t_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_1072_, lean_object* v___f_1073_, lean_object* v_s_1074_, lean_object* v_x_1075_, lean_object* v_t_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_1072_, v___f_1073_, v_s_1074_, v_x_1075_, v_t_1076_);
lean_dec(v_x_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_1078_, lean_object* v_init_1079_, lean_object* v_t_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___f_1081_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1081_, 0, v_f_1078_);
v___x_1082_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1083_, 0, v___x_1082_);
lean_closure_set(v___f_1083_, 1, v___f_1081_);
v___x_1084_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1082_, v___f_1083_, v_t_1080_, v_init_1079_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_1085_, lean_object* v_00_u03b1_1086_, lean_object* v_f_1087_, lean_object* v_init_1088_, lean_object* v_t_1089_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; 
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1090_, 0, v_f_1087_);
v___x_1091_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1092_, 0, v___x_1091_);
lean_closure_set(v___f_1092_, 1, v___f_1090_);
v___x_1093_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1091_, v___f_1092_, v_t_1089_, v_init_1088_);
return v___x_1093_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_1094_, uint8_t v_x1_1095_, lean_object* v_x2_1096_){
_start:
{
if (v_x1_1095_ == 0)
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_apply_1(v_f_1094_, v_x2_1096_);
v___x_1098_ = lean_unbox(v___x_1097_);
return v___x_1098_;
}
else
{
lean_dec(v_x2_1096_);
lean_dec_ref(v_f_1094_);
return v_x1_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_1099_, lean_object* v_x1_1100_, lean_object* v_x2_1101_){
_start:
{
uint8_t v_x1_83__boxed_1102_; uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_x1_83__boxed_1102_ = lean_unbox(v_x1_1100_);
v_res_1103_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_1099_, v_x1_83__boxed_1102_, v_x2_1101_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_1105_, lean_object* v___f_1106_, uint8_t v_s_1107_, lean_object* v_x_1108_, lean_object* v_t_1109_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_box(v_s_1107_);
v___x_1111_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_1105_, v___f_1106_, v___x_1110_, v_t_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_1112_, lean_object* v___f_1113_, lean_object* v_s_1114_, lean_object* v_x_1115_, lean_object* v_t_1116_){
_start:
{
uint8_t v_s_boxed_1117_; lean_object* v_res_1118_; 
v_s_boxed_1117_ = lean_unbox(v_s_1114_);
v_res_1118_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_1112_, v___f_1113_, v_s_boxed_1117_, v_x_1115_, v_t_1116_);
lean_dec(v_x_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_1119_, lean_object* v_f_1120_){
_start:
{
lean_object* v___f_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___f_1121_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1121_, 0, v_f_1120_);
v___x_1122_ = 0;
v___x_1123_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1124_, 0, v___x_1123_);
lean_closure_set(v___f_1124_, 1, v___f_1121_);
v___x_1125_ = lean_box(v___x_1122_);
v___x_1126_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1123_, v___f_1124_, v_t_1119_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_1127_, lean_object* v_t_1128_, lean_object* v_f_1129_){
_start:
{
lean_object* v___f_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1130_, 0, v_f_1129_);
v___x_1131_ = 0;
v___x_1132_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_1133_, 0, v___x_1132_);
lean_closure_set(v___f_1133_, 1, v___f_1130_);
v___x_1134_ = lean_box(v___x_1131_);
v___x_1135_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1132_, v___f_1133_, v_t_1128_, v___x_1134_);
v___x_1136_ = lean_unbox(v___x_1135_);
lean_dec(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_t_1138_, lean_object* v_f_1139_){
_start:
{
uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_res_1140_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_1137_, v_t_1138_, v_f_1139_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_1142_, lean_object* v_x2_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_array_push(v_x1_1142_, v_x2_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_1145_, lean_object* v___f_1146_, lean_object* v_s_1147_, lean_object* v_x_1148_, lean_object* v_t_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_1145_, v___f_1146_, v_s_1147_, v_t_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_1151_, lean_object* v___f_1152_, lean_object* v_s_1153_, lean_object* v_x_1154_, lean_object* v_t_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_1151_, v___f_1152_, v_s_1153_, v_x_1154_, v_t_1155_);
lean_dec(v_x_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_1163_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1164_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_1165_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1163_, v___f_1164_, v_t_1161_, v___x_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_1166_, lean_object* v_t_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; 
v___x_1168_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_1169_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1170_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_1171_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1169_, v___f_1170_, v_t_1167_, v___x_1168_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_1172_, lean_object* v_keys_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_keys_1173_);
lean_ctor_set(v___x_1175_, 1, v_a_1174_);
v___x_1176_ = lean_array_push(v_s_1172_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_1177_, lean_object* v___f_1178_, lean_object* v_s_1179_, lean_object* v_k_1180_, lean_object* v_t_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1182_);
v___x_1184_ = lean_array_push(v___x_1183_, v_k_1180_);
v___x_1185_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_1177_, v___x_1184_, v___f_1178_, v_s_1179_, v_t_1181_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; 
v___x_1193_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_1194_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1195_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_1196_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1194_, v___f_1195_, v_t_1192_, v___x_1193_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_1197_, lean_object* v_t_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v___x_1199_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_1200_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1201_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_1202_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1200_, v___f_1201_, v_t_1198_, v___x_1199_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_1203_, lean_object* v_x_1204_, lean_object* v_t_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_1205_);
v___x_1207_ = lean_nat_add(v_n_1203_, v___x_1206_);
lean_dec(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_1208_, lean_object* v_x_1209_, lean_object* v_t_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_1208_, v_x_1209_, v_t_1210_);
lean_dec(v_x_1209_);
lean_dec(v_n_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_1213_){
_start:
{
lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___f_1214_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_1213_, v___f_1214_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_1217_, lean_object* v_t_1218_){
_start:
{
lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___f_1219_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_1218_, v___f_1219_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_vs_1224_, lean_object* v_toPure_1225_, lean_object* v_key_1226_, lean_object* v_c_1227_){
_start:
{
lean_object* v___y_1229_; lean_object* v_val_1257_; 
switch(lean_obj_tag(v_c_1227_))
{
case 2:
{
lean_object* v___x_1266_; 
lean_inc_ref(v_c_1227_);
v___x_1266_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1227_);
v_val_1257_ = v___x_1266_;
goto v___jp_1256_;
}
case 3:
{
lean_object* v___x_1267_; 
lean_inc_ref(v_c_1227_);
v___x_1267_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_c_1227_);
v_val_1257_ = v___x_1267_;
goto v___jp_1256_;
}
default: 
{
lean_inc_ref(v_c_1227_);
v_val_1257_ = v_c_1227_;
goto v___jp_1256_;
}
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_array_get_size(v_vs_1224_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = lean_nat_dec_eq(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_vs_1224_);
lean_ctor_set(v___x_1233_, 1, v___y_1229_);
v___x_1234_ = lean_apply_2(v_toPure_1225_, lean_box(0), v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = lean_array_get_size(v___y_1229_);
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_dec_eq(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_vs_1224_);
lean_ctor_set(v___x_1238_, 1, v___y_1229_);
v___x_1239_ = lean_apply_2(v_toPure_1225_, lean_box(0), v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_vs_1224_);
v___x_1240_ = lean_array_fget(v___y_1229_, v___x_1231_);
lean_dec_ref(v___y_1229_);
v_fst_1241_ = lean_ctor_get(v___x_1240_, 0);
v_snd_1242_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1244_ = v___x_1240_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v___x_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_fst_1241_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_snd_1242_);
v___x_1247_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_apply_2(v_toPure_1225_, lean_box(0), v___x_1247_);
return v___x_1248_;
}
}
}
}
}
v___jp_1251_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_key_1226_);
lean_ctor_set(v___x_1252_, 1, v_c_1227_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1253_);
v___x_1255_ = lean_array_push(v___x_1254_, v___x_1252_);
v___y_1229_ = v___x_1255_;
goto v___jp_1228_;
}
v___jp_1256_:
{
if (lean_obj_tag(v_val_1257_) == 0)
{
lean_dec_ref_known(v_val_1257_, 2);
goto v___jp_1251_;
}
else
{
lean_object* v_vs_1258_; lean_object* v_children_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_vs_1258_ = lean_ctor_get(v_val_1257_, 0);
lean_inc_ref(v_vs_1258_);
v_children_1259_ = lean_ctor_get(v_val_1257_, 1);
lean_inc_ref(v_children_1259_);
lean_dec_ref_known(v_val_1257_, 2);
v___x_1260_ = lean_array_get_size(v_vs_1258_);
lean_dec_ref(v_vs_1258_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_nat_dec_eq(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_dec_ref(v_children_1259_);
goto v___jp_1251_;
}
else
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_array_get_size(v_children_1259_);
lean_dec_ref(v_children_1259_);
v___x_1264_ = lean_nat_dec_eq(v___x_1263_, v___x_1261_);
if (v___x_1264_ == 0)
{
goto v___jp_1251_;
}
else
{
lean_object* v___x_1265_; 
lean_dec_ref(v_c_1227_);
lean_dec(v_key_1226_);
v___x_1265_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0));
v___y_1229_ = v___x_1265_;
goto v___jp_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object* v_vs_1268_, lean_object* v_toPure_1269_, lean_object* v_children_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = lean_array_get_size(v_vs_1268_);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_nat_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_vs_1268_);
lean_ctor_set(v___x_1274_, 1, v_children_1270_);
v___x_1275_ = lean_apply_2(v_toPure_1269_, lean_box(0), v___x_1274_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1276_ = lean_array_get_size(v_children_1270_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_vs_1268_);
lean_ctor_set(v___x_1279_, 1, v_children_1270_);
v___x_1280_ = lean_apply_2(v_toPure_1269_, lean_box(0), v___x_1279_);
return v___x_1280_;
}
else
{
lean_object* v___x_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_vs_1268_);
v___x_1281_ = lean_array_fget(v_children_1270_, v___x_1272_);
lean_dec_ref(v_children_1270_);
v_fst_1282_ = lean_ctor_get(v___x_1281_, 0);
v_snd_1283_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_inc(v_fst_1282_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_fst_1282_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_snd_1283_);
v___x_1288_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_apply_2(v_toPure_1269_, lean_box(0), v___x_1288_);
return v___x_1289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object* v_toPure_1292_, lean_object* v_children_1293_, lean_object* v_inst_1294_, lean_object* v___f_1295_, lean_object* v_toBind_1296_, lean_object* v_vs_1297_){
_start:
{
lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1298_, 0, v_vs_1297_);
lean_closure_set(v___f_1298_, 1, v_toPure_1292_);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_array_get_size(v_children_1293_);
v___x_1301_ = l_Array_filterMapM___redArg(v_inst_1294_, v___f_1295_, v_children_1293_, v___x_1299_, v___x_1300_);
v___x_1302_ = lean_apply_4(v_toBind_1296_, lean_box(0), lean_box(0), v___x_1301_, v___f_1298_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_fst_1303_, lean_object* v_toPure_1304_, lean_object* v_child_1305_){
_start:
{
lean_object* v_val_1311_; 
switch(lean_obj_tag(v_child_1305_))
{
case 2:
{
lean_object* v___x_1321_; 
lean_inc_ref(v_child_1305_);
v___x_1321_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_child_1305_);
v_val_1311_ = v___x_1321_;
goto v___jp_1310_;
}
case 3:
{
lean_object* v___x_1322_; 
lean_inc_ref(v_child_1305_);
v___x_1322_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_child_1305_);
v_val_1311_ = v___x_1322_;
goto v___jp_1310_;
}
default: 
{
lean_inc_ref(v_child_1305_);
v_val_1311_ = v_child_1305_;
goto v___jp_1310_;
}
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_fst_1303_);
lean_ctor_set(v___x_1307_, 1, v_child_1305_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
v___x_1309_ = lean_apply_2(v_toPure_1304_, lean_box(0), v___x_1308_);
return v___x_1309_;
}
v___jp_1310_:
{
if (lean_obj_tag(v_val_1311_) == 0)
{
lean_dec_ref_known(v_val_1311_, 2);
goto v___jp_1306_;
}
else
{
lean_object* v_vs_1312_; lean_object* v_children_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_vs_1312_ = lean_ctor_get(v_val_1311_, 0);
lean_inc_ref(v_vs_1312_);
v_children_1313_ = lean_ctor_get(v_val_1311_, 1);
lean_inc_ref(v_children_1313_);
lean_dec_ref_known(v_val_1311_, 2);
v___x_1314_ = lean_array_get_size(v_vs_1312_);
lean_dec_ref(v_vs_1312_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_nat_dec_eq(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_children_1313_);
goto v___jp_1306_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_array_get_size(v_children_1313_);
lean_dec_ref(v_children_1313_);
v___x_1318_ = lean_nat_dec_eq(v___x_1317_, v___x_1315_);
if (v___x_1318_ == 0)
{
goto v___jp_1306_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec_ref(v_child_1305_);
lean_dec(v_fst_1303_);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_apply_2(v_toPure_1304_, lean_box(0), v___x_1319_);
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_1323_, lean_object* v_inst_1324_, lean_object* v_f_1325_, lean_object* v_toBind_1326_, lean_object* v_x_1327_){
_start:
{
lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_fst_1328_ = lean_ctor_get(v_x_1327_, 0);
lean_inc(v_fst_1328_);
v_snd_1329_ = lean_ctor_get(v_x_1327_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v_x_1327_);
v___f_1330_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1330_, 0, v_fst_1328_);
lean_closure_set(v___f_1330_, 1, v_toPure_1323_);
v___x_1331_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1324_, v_snd_1329_, v_f_1325_);
v___x_1332_ = lean_apply_4(v_toBind_1326_, lean_box(0), lean_box(0), v___x_1331_, v___f_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_1333_, lean_object* v_t_1334_, lean_object* v_f_1335_){
_start:
{
switch(lean_obj_tag(v_t_1334_))
{
case 0:
{
lean_object* v_toApplicative_1336_; lean_object* v_toBind_1337_; lean_object* v_toPure_1338_; lean_object* v_key_1339_; lean_object* v_child_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_toApplicative_1336_ = lean_ctor_get(v_inst_1333_, 0);
v_toBind_1337_ = lean_ctor_get(v_inst_1333_, 1);
lean_inc_n(v_toBind_1337_, 2);
v_toPure_1338_ = lean_ctor_get(v_toApplicative_1336_, 1);
lean_inc(v_toPure_1338_);
v_key_1339_ = lean_ctor_get(v_t_1334_, 0);
lean_inc(v_key_1339_);
v_child_1340_ = lean_ctor_get(v_t_1334_, 1);
lean_inc_ref(v_child_1340_);
lean_dec_ref_known(v_t_1334_, 2);
lean_inc(v_f_1335_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1341_, 0, v_toPure_1338_);
lean_closure_set(v___f_1341_, 1, v_key_1339_);
lean_closure_set(v___f_1341_, 2, v_inst_1333_);
lean_closure_set(v___f_1341_, 3, v_child_1340_);
lean_closure_set(v___f_1341_, 4, v_f_1335_);
lean_closure_set(v___f_1341_, 5, v_toBind_1337_);
v___x_1342_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_1343_ = lean_apply_1(v_f_1335_, v___x_1342_);
v___x_1344_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v___x_1343_, v___f_1341_);
return v___x_1344_;
}
case 1:
{
lean_object* v_toApplicative_1345_; lean_object* v_toBind_1346_; lean_object* v_toPure_1347_; lean_object* v_vs_1348_; lean_object* v_children_1349_; lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_toApplicative_1345_ = lean_ctor_get(v_inst_1333_, 0);
v_toBind_1346_ = lean_ctor_get(v_inst_1333_, 1);
lean_inc_n(v_toBind_1346_, 3);
v_toPure_1347_ = lean_ctor_get(v_toApplicative_1345_, 1);
lean_inc_n(v_toPure_1347_, 2);
v_vs_1348_ = lean_ctor_get(v_t_1334_, 0);
lean_inc_ref(v_vs_1348_);
v_children_1349_ = lean_ctor_get(v_t_1334_, 1);
lean_inc_ref(v_children_1349_);
lean_dec_ref_known(v_t_1334_, 2);
lean_inc(v_f_1335_);
lean_inc_ref(v_inst_1333_);
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1350_, 0, v_toPure_1347_);
lean_closure_set(v___f_1350_, 1, v_inst_1333_);
lean_closure_set(v___f_1350_, 2, v_f_1335_);
lean_closure_set(v___f_1350_, 3, v_toBind_1346_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_1351_, 0, v_toPure_1347_);
lean_closure_set(v___f_1351_, 1, v_children_1349_);
lean_closure_set(v___f_1351_, 2, v_inst_1333_);
lean_closure_set(v___f_1351_, 3, v___f_1350_);
lean_closure_set(v___f_1351_, 4, v_toBind_1346_);
v___x_1352_ = lean_apply_1(v_f_1335_, v_vs_1348_);
v___x_1353_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1352_, v___f_1351_);
return v___x_1353_;
}
default: 
{
lean_object* v___x_1354_; 
v___x_1354_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_1334_);
v_t_1334_ = v___x_1354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_1356_, lean_object* v_key_1357_, lean_object* v_inst_1358_, lean_object* v_child_1359_, lean_object* v_f_1360_, lean_object* v_toBind_1361_, lean_object* v_vs_1362_){
_start:
{
lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1363_, 0, v_vs_1362_);
lean_closure_set(v___f_1363_, 1, v_toPure_1356_);
lean_closure_set(v___f_1363_, 2, v_key_1357_);
v___x_1364_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1358_, v_child_1359_, v_f_1360_);
v___x_1365_ = lean_apply_4(v_toBind_1361_, lean_box(0), lean_box(0), v___x_1364_, v___f_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_1366_, lean_object* v_inst_1367_, lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_t_1370_, lean_object* v_f_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1367_, v_t_1370_, v_f_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_1373_, lean_object* v_f_1374_, lean_object* v_t_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_1373_, v_t_1375_, v_f_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v_acc_1379_, lean_object* v_k_1380_, lean_object* v_t_1381_){
_start:
{
lean_object* v_val_1383_; 
switch(lean_obj_tag(v_t_1381_))
{
case 2:
{
lean_object* v___x_1392_; 
v___x_1392_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_1381_);
v_val_1383_ = v___x_1392_;
goto v___jp_1382_;
}
case 3:
{
lean_object* v___x_1393_; 
v___x_1393_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_Trie_forceSlow(lean_box(0), v_t_1381_);
v_val_1383_ = v___x_1393_;
goto v___jp_1382_;
}
default: 
{
v_val_1383_ = v_t_1381_;
goto v___jp_1382_;
}
}
v___jp_1382_:
{
if (lean_obj_tag(v_val_1383_) == 0)
{
lean_dec_ref_known(v_val_1383_, 2);
lean_dec(v_k_1380_);
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___x_1377_);
return v_acc_1379_;
}
else
{
lean_object* v_vs_1384_; lean_object* v_children_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_vs_1384_ = lean_ctor_get(v_val_1383_, 0);
lean_inc_ref(v_vs_1384_);
v_children_1385_ = lean_ctor_get(v_val_1383_, 1);
lean_inc_ref(v_children_1385_);
lean_dec_ref_known(v_val_1383_, 2);
v___x_1386_ = lean_array_get_size(v_vs_1384_);
lean_dec_ref(v_vs_1384_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_nat_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_dec_ref(v_children_1385_);
lean_dec(v_k_1380_);
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___x_1377_);
return v_acc_1379_;
}
else
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = lean_array_get_size(v_children_1385_);
lean_dec_ref(v_children_1385_);
v___x_1390_ = lean_nat_dec_eq(v___x_1389_, v___x_1387_);
if (v___x_1390_ == 0)
{
lean_dec(v_k_1380_);
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___x_1377_);
return v_acc_1379_;
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_erase___redArg(v___x_1377_, v___x_1378_, v_acc_1379_, v_k_1380_);
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_1394_, lean_object* v_toPure_1395_, lean_object* v_root_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc_ref(v_root_1396_);
v___x_1397_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_1396_, v___f_1394_, v_root_1396_);
v___x_1398_ = lean_apply_2(v_toPure_1395_, lean_box(0), v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_1404_, lean_object* v_d_1405_, lean_object* v_f_1406_){
_start:
{
lean_object* v_toApplicative_1407_; lean_object* v_toBind_1408_; lean_object* v_toPure_1409_; lean_object* v___f_1410_; lean_object* v___f_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_toApplicative_1407_ = lean_ctor_get(v_inst_1404_, 0);
v_toBind_1408_ = lean_ctor_get(v_inst_1404_, 1);
lean_inc(v_toBind_1408_);
v_toPure_1409_ = lean_ctor_get(v_toApplicative_1407_, 1);
lean_inc_ref(v_inst_1404_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1410_, 0, v_inst_1404_);
lean_closure_set(v___f_1410_, 1, v_f_1406_);
v___f_1411_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_1409_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1412_, 0, v___f_1411_);
lean_closure_set(v___f_1412_, 1, v_toPure_1409_);
v___x_1413_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1404_, v_d_1405_, v___f_1410_);
v___x_1414_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1413_, v___f_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_1415_, lean_object* v_inst_1416_, lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_d_1419_, lean_object* v_f_1420_){
_start:
{
lean_object* v_toApplicative_1421_; lean_object* v_toBind_1422_; lean_object* v_toPure_1423_; lean_object* v___f_1424_; lean_object* v___f_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_toApplicative_1421_ = lean_ctor_get(v_inst_1416_, 0);
v_toBind_1422_ = lean_ctor_get(v_inst_1416_, 1);
lean_inc(v_toBind_1422_);
v_toPure_1423_ = lean_ctor_get(v_toApplicative_1421_, 1);
lean_inc_ref(v_inst_1416_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1424_, 0, v_inst_1416_);
lean_closure_set(v___f_1424_, 1, v_f_1420_);
v___f_1425_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_1423_);
v___f_1426_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1426_, 0, v___f_1425_);
lean_closure_set(v___f_1426_, 1, v_toPure_1423_);
v___x_1427_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1416_, v_d_1419_, v___f_1424_);
v___x_1428_ = lean_apply_4(v_toBind_1422_, lean_box(0), lean_box(0), v___x_1427_, v___f_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_1429_, lean_object* v_A_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_apply_1(v_f_1429_, v_A_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_1432_, lean_object* v___f_1433_, lean_object* v_t_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_1432_, v_t_1434_, v___f_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_1436_, lean_object* v_f_1437_){
_start:
{
lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1438_, 0, v_f_1437_);
v___x_1439_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
lean_closure_set(v___f_1440_, 1, v___f_1438_);
v___f_1441_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_1442_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1439_, v_d_1436_, v___f_1440_);
lean_inc(v___x_1442_);
v___x_1443_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_1442_, v___f_1441_, v___x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_d_1446_, lean_object* v_f_1447_){
_start:
{
lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1448_, 0, v_f_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_1450_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1450_, 0, v___x_1449_);
lean_closure_set(v___f_1450_, 1, v___f_1448_);
v___f_1451_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_1452_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1449_, v_d_1446_, v___f_1450_);
lean_inc(v___x_1452_);
v___x_1453_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_1452_, v___f_1451_, v___x_1452_);
return v___x_1453_;
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
