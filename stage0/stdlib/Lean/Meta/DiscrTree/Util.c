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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_filterMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_Key_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__1_value)} };
static const lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(lean_object* v_children_1_, lean_object* v___x_2_, lean_object* v_toPure_3_, lean_object* v_inst_4_, lean_object* v___f_5_, lean_object* v_s_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_array_get_size(v_children_1_);
v___x_8_ = lean_nat_dec_lt(v___x_2_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec(v___f_5_);
lean_dec_ref(v_inst_4_);
lean_dec_ref(v_children_1_);
v___x_9_ = lean_apply_2(v_toPure_3_, lean_box(0), v_s_6_);
return v___x_9_;
}
else
{
size_t v___x_10_; size_t v___x_11_; lean_object* v___x_12_; 
lean_dec(v_toPure_3_);
v___x_10_ = ((size_t)0ULL);
v___x_11_ = lean_usize_of_nat(v___x_7_);
v___x_12_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4_, v___f_5_, v_children_1_, v___x_10_, v___x_11_, v_s_6_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed(lean_object* v_children_13_, lean_object* v___x_14_, lean_object* v_toPure_15_, lean_object* v_inst_16_, lean_object* v___f_17_, lean_object* v_s_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(v_children_13_, v___x_14_, v_toPure_15_, v_inst_16_, v___f_17_, v_s_18_);
lean_dec(v___x_14_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object* v_f_20_, lean_object* v_initialKeys_21_, lean_object* v_s_22_, lean_object* v_v_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_apply_3(v_f_20_, v_s_22_, v_initialKeys_21_, v_v_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object* v_inst_25_, lean_object* v_initialKeys_26_, lean_object* v_f_27_, lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
if (lean_obj_tag(v_x_29_) == 0)
{
lean_object* v_key_30_; lean_object* v_child_31_; lean_object* v___x_32_; 
v_key_30_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_key_30_);
v_child_31_ = lean_ctor_get(v_x_29_, 1);
lean_inc_ref(v_child_31_);
lean_dec_ref_known(v_x_29_, 2);
v___x_32_ = lean_array_push(v_initialKeys_26_, v_key_30_);
v_initialKeys_26_ = v___x_32_;
v_x_29_ = v_child_31_;
goto _start;
}
else
{
lean_object* v_toApplicative_34_; lean_object* v_toBind_35_; lean_object* v_vs_36_; lean_object* v_children_37_; lean_object* v_toPure_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___f_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_toApplicative_34_ = lean_ctor_get(v_inst_25_, 0);
v_toBind_35_ = lean_ctor_get(v_inst_25_, 1);
lean_inc(v_toBind_35_);
v_vs_36_ = lean_ctor_get(v_x_29_, 0);
lean_inc_ref(v_vs_36_);
v_children_37_ = lean_ctor_get(v_x_29_, 1);
lean_inc_ref(v_children_37_);
lean_dec_ref_known(v_x_29_, 2);
v_toPure_38_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_inc(v_f_27_);
lean_inc_ref_n(v_inst_25_, 2);
lean_inc_ref(v_initialKeys_26_);
v___f_39_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0), 5, 3);
lean_closure_set(v___f_39_, 0, v_initialKeys_26_);
lean_closure_set(v___f_39_, 1, v_inst_25_);
lean_closure_set(v___f_39_, 2, v_f_27_);
v___x_40_ = lean_unsigned_to_nat(0u);
lean_inc(v_toPure_38_);
v___f_41_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_41_, 0, v_children_37_);
lean_closure_set(v___f_41_, 1, v___x_40_);
lean_closure_set(v___f_41_, 2, v_toPure_38_);
lean_closure_set(v___f_41_, 3, v_inst_25_);
lean_closure_set(v___f_41_, 4, v___f_39_);
v___x_42_ = lean_array_get_size(v_vs_36_);
v___x_43_ = lean_nat_dec_lt(v___x_40_, v___x_42_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_inc(v_toPure_38_);
lean_dec_ref(v_vs_36_);
lean_dec(v_f_27_);
lean_dec_ref(v_initialKeys_26_);
lean_dec_ref(v_inst_25_);
v___x_44_ = lean_apply_2(v_toPure_38_, lean_box(0), v_x_28_);
v___x_45_ = lean_apply_4(v_toBind_35_, lean_box(0), lean_box(0), v___x_44_, v___f_41_);
return v___x_45_;
}
else
{
lean_object* v___f_46_; size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_46_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_46_, 0, v_f_27_);
lean_closure_set(v___f_46_, 1, v_initialKeys_26_);
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_42_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_25_, v___f_46_, v_vs_36_, v___x_47_, v___x_48_, v_x_28_);
v___x_50_ = lean_apply_4(v_toBind_35_, lean_box(0), lean_box(0), v___x_49_, v___f_41_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object* v_initialKeys_51_, lean_object* v_inst_52_, lean_object* v_f_53_, lean_object* v_s_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_fst_56_; lean_object* v_snd_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v_fst_56_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_fst_56_);
v_snd_57_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_snd_57_);
lean_dec_ref(v_x_55_);
v___x_58_ = lean_array_push(v_initialKeys_51_, v_fst_56_);
v___x_59_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_52_, v___x_58_, v_f_53_, v_s_54_, v_snd_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object* v_m_60_, lean_object* v_00_u03c3_61_, lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_initialKeys_64_, lean_object* v_f_65_, lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_63_, v_initialKeys_64_, v_f_65_, v_x_66_, v_x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object* v_f_69_, lean_object* v_s_70_, lean_object* v_k_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_apply_3(v_f_69_, v_s_70_, v_k_71_, v_a_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object* v_initialKeys_93_, lean_object* v_f_94_, lean_object* v_init_95_, lean_object* v_t_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___f_97_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_97_, 0, v_f_94_);
v___x_98_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_99_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_98_, v_initialKeys_93_, v___f_97_, v_init_95_, v_t_96_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object* v_00_u03c3_100_, lean_object* v_00_u03b1_101_, lean_object* v_initialKeys_102_, lean_object* v_f_103_, lean_object* v_init_104_, lean_object* v_t_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_106_, 0, v_f_103_);
v___x_107_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_108_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_107_, v_initialKeys_102_, v___f_106_, v_init_104_, v_t_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object* v_inst_109_, lean_object* v_f_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v_child_113_; 
v_child_113_ = lean_ctor_get(v_x_112_, 1);
lean_inc_ref(v_child_113_);
lean_dec_ref_known(v_x_112_, 2);
v_x_112_ = v_child_113_;
goto _start;
}
else
{
lean_object* v_toApplicative_115_; lean_object* v_toBind_116_; lean_object* v_vs_117_; lean_object* v_children_118_; lean_object* v_toPure_119_; lean_object* v___f_120_; lean_object* v___x_121_; lean_object* v___f_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_toApplicative_115_ = lean_ctor_get(v_inst_109_, 0);
v_toBind_116_ = lean_ctor_get(v_inst_109_, 1);
lean_inc(v_toBind_116_);
v_vs_117_ = lean_ctor_get(v_x_112_, 0);
lean_inc_ref(v_vs_117_);
v_children_118_ = lean_ctor_get(v_x_112_, 1);
lean_inc_ref(v_children_118_);
lean_dec_ref_known(v_x_112_, 2);
v_toPure_119_ = lean_ctor_get(v_toApplicative_115_, 1);
lean_inc(v_f_110_);
lean_inc_ref_n(v_inst_109_, 2);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_120_, 0, v_inst_109_);
lean_closure_set(v___f_120_, 1, v_f_110_);
v___x_121_ = lean_unsigned_to_nat(0u);
lean_inc(v_toPure_119_);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_122_, 0, v_children_118_);
lean_closure_set(v___f_122_, 1, v___x_121_);
lean_closure_set(v___f_122_, 2, v_toPure_119_);
lean_closure_set(v___f_122_, 3, v_inst_109_);
lean_closure_set(v___f_122_, 4, v___f_120_);
v___x_123_ = lean_array_get_size(v_vs_117_);
v___x_124_ = lean_nat_dec_lt(v___x_121_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_inc(v_toPure_119_);
lean_dec_ref(v_vs_117_);
lean_dec(v_f_110_);
lean_dec_ref(v_inst_109_);
v___x_125_ = lean_apply_2(v_toPure_119_, lean_box(0), v_x_111_);
v___x_126_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v___x_125_, v___f_122_);
return v___x_126_;
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_123_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_109_, v_f_110_, v_vs_117_, v___x_127_, v___x_128_, v_x_111_);
v___x_130_ = lean_apply_4(v_toBind_116_, lean_box(0), lean_box(0), v___x_129_, v___f_122_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object* v_inst_131_, lean_object* v_f_132_, lean_object* v_s_133_, lean_object* v_x_134_){
_start:
{
lean_object* v_snd_135_; lean_object* v___x_136_; 
v_snd_135_ = lean_ctor_get(v_x_134_, 1);
lean_inc(v_snd_135_);
lean_dec_ref(v_x_134_);
v___x_136_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_131_, v_f_132_, v_s_133_, v_snd_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object* v_m_137_, lean_object* v_00_u03c3_138_, lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_f_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_140_, v_f_141_, v_x_142_, v_x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object* v_f_145_, lean_object* v_x1_146_, lean_object* v_x2_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_apply_2(v_f_145_, v_x1_146_, v_x2_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object* v_f_149_, lean_object* v_init_150_, lean_object* v_t_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___f_152_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_152_, 0, v_f_149_);
v___x_153_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_154_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_153_, v___f_152_, v_init_150_, v_t_151_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object* v_00_u03c3_155_, lean_object* v_00_u03b1_156_, lean_object* v_f_157_, lean_object* v_init_158_, lean_object* v_t_159_){
_start:
{
lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___f_160_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_160_, 0, v_f_157_);
v___x_161_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_162_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_161_, v___f_160_, v_init_158_, v_t_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_child_164_; 
v_child_164_ = lean_ctor_get(v_x_163_, 1);
v_x_163_ = v_child_164_;
goto _start;
}
else
{
lean_object* v_vs_166_; lean_object* v_children_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_vs_166_ = lean_ctor_get(v_x_163_, 0);
v_children_167_ = lean_ctor_get(v_x_163_, 1);
v___x_168_ = lean_array_get_size(v_vs_166_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_array_get_size(v_children_167_);
v___x_171_ = lean_nat_dec_lt(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
return v___x_168_;
}
else
{
size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((size_t)0ULL);
v___x_173_ = lean_usize_of_nat(v___x_170_);
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_167_, v___x_172_, v___x_173_, v___x_168_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_175_, size_t v_i_176_, size_t v_stop_177_, lean_object* v_b_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_usize_dec_eq(v_i_176_, v_stop_177_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v_snd_181_; lean_object* v___x_182_; lean_object* v___x_183_; size_t v___x_184_; size_t v___x_185_; 
v___x_180_ = lean_array_uget_borrowed(v_as_175_, v_i_176_);
v_snd_181_ = lean_ctor_get(v___x_180_, 1);
v___x_182_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_181_);
v___x_183_ = lean_nat_add(v_b_178_, v___x_182_);
lean_dec(v___x_182_);
lean_dec(v_b_178_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_add(v_i_176_, v___x_184_);
v_i_176_ = v___x_185_;
v_b_178_ = v___x_183_;
goto _start;
}
else
{
return v_b_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_187_, lean_object* v_i_188_, lean_object* v_stop_189_, lean_object* v_b_190_){
_start:
{
size_t v_i_boxed_191_; size_t v_stop_boxed_192_; lean_object* v_res_193_; 
v_i_boxed_191_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_stop_boxed_192_ = lean_unbox_usize(v_stop_189_);
lean_dec(v_stop_189_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_187_, v_i_boxed_191_, v_stop_boxed_192_, v_b_190_);
lean_dec_ref(v_as_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_196_, lean_object* v_x_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___boxed(lean_object* v_00_u03b1_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_DiscrTree_Trie_size(v_00_u03b1_199_, v_x_200_);
lean_dec_ref(v_x_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_202_, lean_object* v_as_203_, size_t v_i_204_, size_t v_stop_205_, lean_object* v_b_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_203_, v_i_204_, v_stop_205_, v_b_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_stop_211_, lean_object* v_b_212_){
_start:
{
size_t v_i_boxed_213_; size_t v_stop_boxed_214_; lean_object* v_res_215_; 
v_i_boxed_213_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_211_);
lean_dec(v_stop_211_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_208_, v_as_209_, v_i_boxed_213_, v_stop_boxed_214_, v_b_212_);
lean_dec_ref(v_as_209_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object* v_vs_216_, lean_object* v_cs_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_array_get_size(v_vs_216_);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_dec_eq(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v_vs_216_);
lean_ctor_set(v___x_221_, 1, v_cs_217_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = lean_array_get_size(v_cs_217_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_dec_eq(v___x_222_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v_vs_216_);
lean_ctor_set(v___x_225_, 1, v_cs_217_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_vs_216_);
v___x_226_ = lean_array_fget(v_cs_217_, v___x_219_);
lean_dec_ref(v_cs_217_);
v_fst_227_ = lean_ctor_get(v___x_226_, 0);
v_snd_228_ = lean_ctor_get(v___x_226_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_fst_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_snd_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object* v_00_u03b1_236_, lean_object* v_vs_237_, lean_object* v_cs_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_239_ = lean_array_get_size(v_vs_237_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_nat_dec_eq(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_242_, 0, v_vs_237_);
lean_ctor_set(v___x_242_, 1, v_cs_238_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_array_get_size(v_cs_238_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v_vs_237_);
lean_ctor_set(v___x_246_, 1, v_cs_238_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v_fst_248_; lean_object* v_snd_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v_vs_237_);
v___x_247_ = lean_array_fget(v_cs_238_, v___x_240_);
lean_dec_ref(v_cs_238_);
v_fst_248_ = lean_ctor_get(v___x_247_, 0);
v_snd_249_ = lean_ctor_get(v___x_247_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_247_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snd_249_);
lean_inc(v_fst_248_);
lean_dec(v___x_247_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_fst_248_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_snd_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_key_260_; lean_object* v_child_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_273_; 
v_key_260_ = lean_ctor_get(v_x_259_, 0);
v_child_261_ = lean_ctor_get(v_x_259_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_273_ == 0)
{
v___x_263_ = v_x_259_;
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_child_261_);
lean_inc(v_key_260_);
lean_dec(v_x_259_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_264_ == 0)
{
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_key_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_child_261_);
v___x_267_ = v_reuseFailAlloc_272_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_268_);
v___x_270_ = lean_array_push(v___x_269_, v___x_267_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_265_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
}
}
else
{
lean_object* v_vs_274_; lean_object* v_children_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_vs_274_ = lean_ctor_get(v_x_259_, 0);
v_children_275_ = lean_ctor_get(v_x_259_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v_x_259_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_children_275_);
lean_inc(v_vs_274_);
lean_dec(v_x_259_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 0);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_vs_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_children_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object* v_00_u03b1_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_key_285_; lean_object* v_child_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_298_; 
v_key_285_ = lean_ctor_get(v_x_284_, 0);
v_child_286_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_298_ == 0)
{
v___x_288_ = v_x_284_;
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_child_286_);
lean_inc(v_key_285_);
lean_dec(v_x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_289_ == 0)
{
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_key_285_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_child_286_);
v___x_292_ = v_reuseFailAlloc_297_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_array_push(v___x_294_, v___x_292_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_290_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
return v___x_296_;
}
}
}
else
{
lean_object* v_vs_299_; lean_object* v_children_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_vs_299_ = lean_ctor_get(v_x_284_, 0);
v_children_300_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v_x_284_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_children_300_);
lean_inc(v_vs_299_);
lean_dec(v_x_284_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 0);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_vs_299_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_children_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v___x_309_; 
v___x_309_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_309_;
}
else
{
lean_object* v_vs_310_; 
v_vs_310_ = lean_ctor_get(v_x_308_, 0);
lean_inc_ref(v_vs_310_);
return v_vs_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg___boxed(lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(v_x_311_);
lean_dec_ref(v_x_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object* v_00_u03b1_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v___x_315_; 
v___x_315_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_315_;
}
else
{
lean_object* v_vs_316_; 
v_vs_316_ = lean_ctor_get(v_x_314_, 0);
lean_inc_ref(v_vs_316_);
return v_vs_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___boxed(lean_object* v_00_u03b1_317_, lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_DiscrTree_Trie_nodeValues(v_00_u03b1_317_, v_x_318_);
lean_dec_ref(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_object* v_key_321_; lean_object* v_child_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_332_; 
v_key_321_ = lean_ctor_get(v_x_320_, 0);
v_child_322_ = lean_ctor_get(v_x_320_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_332_ == 0)
{
v___x_324_ = v_x_320_;
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_child_322_);
lean_inc(v_key_321_);
lean_dec(v_x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_key_321_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_child_322_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_array_push(v___x_329_, v___x_327_);
return v___x_330_;
}
}
}
else
{
lean_object* v_children_333_; 
v_children_333_ = lean_ctor_get(v_x_320_, 1);
lean_inc_ref(v_children_333_);
lean_dec_ref_known(v_x_320_, 2);
return v_children_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object* v_00_u03b1_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v_key_336_; lean_object* v_child_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_347_; 
v_key_336_ = lean_ctor_get(v_x_335_, 0);
v_child_337_ = lean_ctor_get(v_x_335_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_335_);
if (v_isSharedCheck_347_ == 0)
{
v___x_339_ = v_x_335_;
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_child_337_);
lean_inc(v_key_336_);
lean_dec(v_x_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_347_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_key_336_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_child_337_);
v___x_342_ = v_reuseFailAlloc_346_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_mk_empty_array_with_capacity(v___x_343_);
v___x_345_ = lean_array_push(v___x_344_, v___x_342_);
return v___x_345_;
}
}
}
else
{
lean_object* v_children_348_; 
v_children_348_ = lean_ctor_get(v_x_335_, 1);
lean_inc_ref(v_children_348_);
lean_dec_ref_known(v_x_335_, 2);
return v_children_348_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
else
{
lean_object* v_vs_351_; lean_object* v_children_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_vs_351_ = lean_ctor_get(v_x_349_, 0);
v_children_352_ = lean_ctor_get(v_x_349_, 1);
v___x_353_ = lean_array_get_size(v_vs_351_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_nat_dec_eq(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
return v___x_355_;
}
else
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_children_352_);
v___x_357_ = lean_nat_dec_eq(v___x_356_, v___x_354_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_358_);
lean_dec_ref(v_x_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
else
{
lean_object* v_vs_364_; lean_object* v_children_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_vs_364_ = lean_ctor_get(v_x_362_, 0);
v_children_365_ = lean_ctor_get(v_x_362_, 1);
v___x_366_ = lean_array_get_size(v_vs_364_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_nat_dec_eq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
return v___x_368_;
}
else
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_array_get_size(v_children_365_);
v___x_370_ = lean_nat_dec_eq(v___x_369_, v___x_367_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_371_, v_x_372_);
lean_dec_ref(v_x_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_375_, lean_object* v_f_376_, lean_object* v_s_377_, lean_object* v_k_378_, lean_object* v_t_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_380_);
v___x_382_ = lean_array_push(v___x_381_, v_k_378_);
v___x_383_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_375_, v___x_382_, v_f_376_, v_s_377_, v_t_379_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_384_, lean_object* v_f_385_, lean_object* v_init_386_, lean_object* v_t_387_){
_start:
{
lean_object* v___f_388_; lean_object* v___x_389_; 
lean_inc_ref(v_inst_384_);
v___f_388_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_388_, 0, v_inst_384_);
lean_closure_set(v___f_388_, 1, v_f_385_);
v___x_389_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_384_, v___f_388_, v_t_387_, v_init_386_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_390_, lean_object* v_00_u03c3_391_, lean_object* v_00_u03b1_392_, lean_object* v_inst_393_, lean_object* v_f_394_, lean_object* v_init_395_, lean_object* v_t_396_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; 
lean_inc_ref(v_inst_393_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_397_, 0, v_inst_393_);
lean_closure_set(v___f_397_, 1, v_f_394_);
v___x_398_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_393_, v___f_397_, v_t_396_, v_init_395_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_399_, lean_object* v_s_400_, lean_object* v_keys_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_apply_3(v_f_399_, v_s_400_, v_keys_401_, v_a_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_404_, lean_object* v___f_405_, lean_object* v_s_406_, lean_object* v_k_407_, lean_object* v_t_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
v___x_411_ = lean_array_push(v___x_410_, v_k_407_);
v___x_412_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_404_, v___x_411_, v___f_405_, v_s_406_, v_t_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_413_, lean_object* v_init_414_, lean_object* v_t_415_){
_start:
{
lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___f_418_; lean_object* v___x_419_; 
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_416_, 0, v_f_413_);
v___x_417_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_418_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_418_, 0, v___x_417_);
lean_closure_set(v___f_418_, 1, v___f_416_);
v___x_419_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_417_, v___f_418_, v_t_415_, v_init_414_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_420_, lean_object* v_00_u03b1_421_, lean_object* v_f_422_, lean_object* v_init_423_, lean_object* v_t_424_){
_start:
{
lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___x_428_; 
v___f_425_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_425_, 0, v_f_422_);
v___x_426_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_427_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_427_, 0, v___x_426_);
lean_closure_set(v___f_427_, 1, v___f_425_);
v___x_428_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_426_, v___f_427_, v_t_424_, v_init_423_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_429_, lean_object* v_f_430_, lean_object* v_s_431_, lean_object* v_x_432_, lean_object* v_t_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_429_, v_f_430_, v_s_431_, v_t_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_435_, lean_object* v_f_436_, lean_object* v_s_437_, lean_object* v_x_438_, lean_object* v_t_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_435_, v_f_436_, v_s_437_, v_x_438_, v_t_439_);
lean_dec(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_441_, lean_object* v_f_442_, lean_object* v_init_443_, lean_object* v_t_444_){
_start:
{
lean_object* v___f_445_; lean_object* v___x_446_; 
lean_inc_ref(v_inst_441_);
v___f_445_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_445_, 0, v_inst_441_);
lean_closure_set(v___f_445_, 1, v_f_442_);
v___x_446_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_441_, v___f_445_, v_t_444_, v_init_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_447_, lean_object* v_00_u03c3_448_, lean_object* v_00_u03b1_449_, lean_object* v_inst_450_, lean_object* v_f_451_, lean_object* v_init_452_, lean_object* v_t_453_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; 
lean_inc_ref(v_inst_450_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_454_, 0, v_inst_450_);
lean_closure_set(v___f_454_, 1, v_f_451_);
v___x_455_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_450_, v___f_454_, v_t_453_, v_init_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_456_, lean_object* v___f_457_, lean_object* v_s_458_, lean_object* v_x_459_, lean_object* v_t_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_456_, v___f_457_, v_s_458_, v_t_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_462_, lean_object* v___f_463_, lean_object* v_s_464_, lean_object* v_x_465_, lean_object* v_t_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_462_, v___f_463_, v_s_464_, v_x_465_, v_t_466_);
lean_dec(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_468_, lean_object* v_init_469_, lean_object* v_t_470_){
_start:
{
lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___x_474_; 
v___f_471_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_471_, 0, v_f_468_);
v___x_472_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_473_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_473_, 0, v___x_472_);
lean_closure_set(v___f_473_, 1, v___f_471_);
v___x_474_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_472_, v___f_473_, v_t_470_, v_init_469_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_475_, lean_object* v_00_u03b1_476_, lean_object* v_f_477_, lean_object* v_init_478_, lean_object* v_t_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___f_482_; lean_object* v___x_483_; 
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_480_, 0, v_f_477_);
v___x_481_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_482_, 0, v___x_481_);
lean_closure_set(v___f_482_, 1, v___f_480_);
v___x_483_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_481_, v___f_482_, v_t_479_, v_init_478_);
return v___x_483_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_484_, uint8_t v_x1_485_, lean_object* v_x2_486_){
_start:
{
if (v_x1_485_ == 0)
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = lean_apply_1(v_f_484_, v_x2_486_);
v___x_488_ = lean_unbox(v___x_487_);
return v___x_488_;
}
else
{
lean_dec(v_x2_486_);
lean_dec_ref(v_f_484_);
return v_x1_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_489_, lean_object* v_x1_490_, lean_object* v_x2_491_){
_start:
{
uint8_t v_x1_83__boxed_492_; uint8_t v_res_493_; lean_object* v_r_494_; 
v_x1_83__boxed_492_ = lean_unbox(v_x1_490_);
v_res_493_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_489_, v_x1_83__boxed_492_, v_x2_491_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_495_, lean_object* v___f_496_, uint8_t v_s_497_, lean_object* v_x_498_, lean_object* v_t_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_box(v_s_497_);
v___x_501_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_495_, v___f_496_, v___x_500_, v_t_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_502_, lean_object* v___f_503_, lean_object* v_s_504_, lean_object* v_x_505_, lean_object* v_t_506_){
_start:
{
uint8_t v_s_boxed_507_; lean_object* v_res_508_; 
v_s_boxed_507_ = lean_unbox(v_s_504_);
v_res_508_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_502_, v___f_503_, v_s_boxed_507_, v_x_505_, v_t_506_);
lean_dec(v_x_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_509_, lean_object* v_f_510_){
_start:
{
lean_object* v___f_511_; uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___f_511_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_511_, 0, v_f_510_);
v___x_512_ = 0;
v___x_513_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_514_, 0, v___x_513_);
lean_closure_set(v___f_514_, 1, v___f_511_);
v___x_515_ = lean_box(v___x_512_);
v___x_516_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_513_, v___f_514_, v_t_509_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_517_, lean_object* v_t_518_, lean_object* v_f_519_){
_start:
{
lean_object* v___f_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___f_520_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_520_, 0, v_f_519_);
v___x_521_ = 0;
v___x_522_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_523_, 0, v___x_522_);
lean_closure_set(v___f_523_, 1, v___f_520_);
v___x_524_ = lean_box(v___x_521_);
v___x_525_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_522_, v___f_523_, v_t_518_, v___x_524_);
v___x_526_ = lean_unbox(v___x_525_);
lean_dec(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_527_, lean_object* v_t_528_, lean_object* v_f_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_527_, v_t_528_, v_f_529_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_532_, lean_object* v_x2_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_array_push(v_x1_532_, v_x2_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_535_, lean_object* v___f_536_, lean_object* v_s_537_, lean_object* v_x_538_, lean_object* v_t_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_535_, v___f_536_, v_s_537_, v_t_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_541_, lean_object* v___f_542_, lean_object* v_s_543_, lean_object* v_x_544_, lean_object* v_t_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_541_, v___f_542_, v_s_543_, v_x_544_, v_t_545_);
lean_dec(v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_551_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; 
v___x_552_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_553_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_554_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_555_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_553_, v___f_554_, v_t_551_, v___x_552_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_556_, lean_object* v_t_557_){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___f_560_; lean_object* v___x_561_; 
v___x_558_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_559_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_560_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_561_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_559_, v___f_560_, v_t_557_, v___x_558_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_562_, lean_object* v_keys_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_keys_563_);
lean_ctor_set(v___x_565_, 1, v_a_564_);
v___x_566_ = lean_array_push(v_s_562_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_567_, lean_object* v___f_568_, lean_object* v_s_569_, lean_object* v_k_570_, lean_object* v_t_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_array_push(v___x_573_, v_k_570_);
v___x_575_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_567_, v___x_574_, v___f_568_, v_s_569_, v_t_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v___x_583_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_584_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_585_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_586_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_584_, v___f_585_, v_t_582_, v___x_583_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_587_, lean_object* v_t_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___f_591_; lean_object* v___x_592_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_590_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_591_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_592_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_590_, v___f_591_, v_t_588_, v___x_589_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_593_, lean_object* v_x_594_, lean_object* v_t_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_595_);
v___x_597_ = lean_nat_add(v_n_593_, v___x_596_);
lean_dec(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_598_, lean_object* v_x_599_, lean_object* v_t_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_598_, v_x_599_, v_t_600_);
lean_dec_ref(v_t_600_);
lean_dec(v_x_599_);
lean_dec(v_n_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_603_){
_start:
{
lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___f_604_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_603_, v___f_604_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_607_, lean_object* v_t_608_){
_start:
{
lean_object* v___f_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___f_609_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_608_, v___f_609_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_vs_614_, lean_object* v_toPure_615_, lean_object* v_key_616_, lean_object* v_c_617_){
_start:
{
lean_object* v___y_619_; 
if (lean_obj_tag(v_c_617_) == 0)
{
goto v___jp_641_;
}
else
{
lean_object* v_vs_646_; lean_object* v_children_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_vs_646_ = lean_ctor_get(v_c_617_, 0);
v_children_647_ = lean_ctor_get(v_c_617_, 1);
v___x_648_ = lean_array_get_size(v_vs_646_);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_nat_dec_eq(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
goto v___jp_641_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_array_get_size(v_children_647_);
v___x_652_ = lean_nat_dec_eq(v___x_651_, v___x_649_);
if (v___x_652_ == 0)
{
goto v___jp_641_;
}
else
{
lean_object* v___x_653_; 
lean_dec_ref_known(v_c_617_, 2);
lean_dec(v_key_616_);
v___x_653_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0));
v___y_619_ = v___x_653_;
goto v___jp_618_;
}
}
}
v___jp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_array_get_size(v_vs_614_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_623_, 0, v_vs_614_);
lean_ctor_set(v___x_623_, 1, v___y_619_);
v___x_624_ = lean_apply_2(v_toPure_615_, lean_box(0), v___x_623_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_array_get_size(v___y_619_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_dec_eq(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v_vs_614_);
lean_ctor_set(v___x_628_, 1, v___y_619_);
v___x_629_ = lean_apply_2(v_toPure_615_, lean_box(0), v___x_628_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v_fst_631_; lean_object* v_snd_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v_vs_614_);
v___x_630_ = lean_array_fget(v___y_619_, v___x_621_);
lean_dec_ref(v___y_619_);
v_fst_631_ = lean_ctor_get(v___x_630_, 0);
v_snd_632_ = lean_ctor_get(v___x_630_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_snd_632_);
lean_inc(v_fst_631_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_fst_631_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_snd_632_);
v___x_637_ = v_reuseFailAlloc_639_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_apply_2(v_toPure_615_, lean_box(0), v___x_637_);
return v___x_638_;
}
}
}
}
}
v___jp_641_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_key_616_);
lean_ctor_set(v___x_642_, 1, v_c_617_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_643_);
v___x_645_ = lean_array_push(v___x_644_, v___x_642_);
v___y_619_ = v___x_645_;
goto v___jp_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object* v_vs_654_, lean_object* v_toPure_655_, lean_object* v_children_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_array_get_size(v_vs_654_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v_vs_654_);
lean_ctor_set(v___x_660_, 1, v_children_656_);
v___x_661_ = lean_apply_2(v_toPure_655_, lean_box(0), v___x_660_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_array_get_size(v_children_656_);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_dec_eq(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_665_, 0, v_vs_654_);
lean_ctor_set(v___x_665_, 1, v_children_656_);
v___x_666_ = lean_apply_2(v_toPure_655_, lean_box(0), v___x_665_);
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_vs_654_);
v___x_667_ = lean_array_fget(v_children_656_, v___x_658_);
lean_dec_ref(v_children_656_);
v_fst_668_ = lean_ctor_get(v___x_667_, 0);
v_snd_669_ = lean_ctor_get(v___x_667_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_667_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v___x_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_snd_669_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_apply_2(v_toPure_655_, lean_box(0), v___x_674_);
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object* v_toPure_678_, lean_object* v_children_679_, lean_object* v_inst_680_, lean_object* v___f_681_, lean_object* v_toBind_682_, lean_object* v_vs_683_){
_start:
{
lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_684_, 0, v_vs_683_);
lean_closure_set(v___f_684_, 1, v_toPure_678_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_children_679_);
v___x_687_ = l_Array_filterMapM___redArg(v_inst_680_, v___f_681_, v_children_679_, v___x_685_, v___x_686_);
v___x_688_ = lean_apply_4(v_toBind_682_, lean_box(0), lean_box(0), v___x_687_, v___f_684_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_fst_689_, lean_object* v_toPure_690_, lean_object* v_child_691_){
_start:
{
if (lean_obj_tag(v_child_691_) == 0)
{
goto v___jp_692_;
}
else
{
lean_object* v_vs_696_; lean_object* v_children_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_vs_696_ = lean_ctor_get(v_child_691_, 0);
v_children_697_ = lean_ctor_get(v_child_691_, 1);
v___x_698_ = lean_array_get_size(v_vs_696_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
goto v___jp_692_;
}
else
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_array_get_size(v_children_697_);
v___x_702_ = lean_nat_dec_eq(v___x_701_, v___x_699_);
if (v___x_702_ == 0)
{
goto v___jp_692_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref_known(v_child_691_, 2);
lean_dec(v_fst_689_);
v___x_703_ = lean_box(0);
v___x_704_ = lean_apply_2(v_toPure_690_, lean_box(0), v___x_703_);
return v___x_704_;
}
}
}
v___jp_692_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_fst_689_);
lean_ctor_set(v___x_693_, 1, v_child_691_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
v___x_695_ = lean_apply_2(v_toPure_690_, lean_box(0), v___x_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_705_, lean_object* v_inst_706_, lean_object* v_f_707_, lean_object* v_toBind_708_, lean_object* v_x_709_){
_start:
{
lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_fst_710_ = lean_ctor_get(v_x_709_, 0);
lean_inc(v_fst_710_);
v_snd_711_ = lean_ctor_get(v_x_709_, 1);
lean_inc(v_snd_711_);
lean_dec_ref(v_x_709_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_712_, 0, v_fst_710_);
lean_closure_set(v___f_712_, 1, v_toPure_705_);
v___x_713_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_706_, v_snd_711_, v_f_707_);
v___x_714_ = lean_apply_4(v_toBind_708_, lean_box(0), lean_box(0), v___x_713_, v___f_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_715_, lean_object* v_t_716_, lean_object* v_f_717_){
_start:
{
if (lean_obj_tag(v_t_716_) == 0)
{
lean_object* v_toApplicative_718_; lean_object* v_toBind_719_; lean_object* v_toPure_720_; lean_object* v_key_721_; lean_object* v_child_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_715_, 0);
v_toBind_719_ = lean_ctor_get(v_inst_715_, 1);
lean_inc_n(v_toBind_719_, 2);
v_toPure_720_ = lean_ctor_get(v_toApplicative_718_, 1);
lean_inc(v_toPure_720_);
v_key_721_ = lean_ctor_get(v_t_716_, 0);
lean_inc(v_key_721_);
v_child_722_ = lean_ctor_get(v_t_716_, 1);
lean_inc_ref(v_child_722_);
lean_dec_ref_known(v_t_716_, 2);
lean_inc(v_f_717_);
v___f_723_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_723_, 0, v_toPure_720_);
lean_closure_set(v___f_723_, 1, v_key_721_);
lean_closure_set(v___f_723_, 2, v_inst_715_);
lean_closure_set(v___f_723_, 3, v_child_722_);
lean_closure_set(v___f_723_, 4, v_f_717_);
lean_closure_set(v___f_723_, 5, v_toBind_719_);
v___x_724_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_725_ = lean_apply_1(v_f_717_, v___x_724_);
v___x_726_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_725_, v___f_723_);
return v___x_726_;
}
else
{
lean_object* v_toApplicative_727_; lean_object* v_toBind_728_; lean_object* v_toPure_729_; lean_object* v_vs_730_; lean_object* v_children_731_; lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_toApplicative_727_ = lean_ctor_get(v_inst_715_, 0);
v_toBind_728_ = lean_ctor_get(v_inst_715_, 1);
lean_inc_n(v_toBind_728_, 3);
v_toPure_729_ = lean_ctor_get(v_toApplicative_727_, 1);
lean_inc_n(v_toPure_729_, 2);
v_vs_730_ = lean_ctor_get(v_t_716_, 0);
lean_inc_ref(v_vs_730_);
v_children_731_ = lean_ctor_get(v_t_716_, 1);
lean_inc_ref(v_children_731_);
lean_dec_ref_known(v_t_716_, 2);
lean_inc(v_f_717_);
lean_inc_ref(v_inst_715_);
v___f_732_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_732_, 0, v_toPure_729_);
lean_closure_set(v___f_732_, 1, v_inst_715_);
lean_closure_set(v___f_732_, 2, v_f_717_);
lean_closure_set(v___f_732_, 3, v_toBind_728_);
v___f_733_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_733_, 0, v_toPure_729_);
lean_closure_set(v___f_733_, 1, v_children_731_);
lean_closure_set(v___f_733_, 2, v_inst_715_);
lean_closure_set(v___f_733_, 3, v___f_732_);
lean_closure_set(v___f_733_, 4, v_toBind_728_);
v___x_734_ = lean_apply_1(v_f_717_, v_vs_730_);
v___x_735_ = lean_apply_4(v_toBind_728_, lean_box(0), lean_box(0), v___x_734_, v___f_733_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_736_, lean_object* v_key_737_, lean_object* v_inst_738_, lean_object* v_child_739_, lean_object* v_f_740_, lean_object* v_toBind_741_, lean_object* v_vs_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_743_, 0, v_vs_742_);
lean_closure_set(v___f_743_, 1, v_toPure_736_);
lean_closure_set(v___f_743_, 2, v_key_737_);
v___x_744_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_738_, v_child_739_, v_f_740_);
v___x_745_ = lean_apply_4(v_toBind_741_, lean_box(0), lean_box(0), v___x_744_, v___f_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_746_, lean_object* v_inst_747_, lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_t_750_, lean_object* v_f_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_747_, v_t_750_, v_f_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_t_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_753_, v_t_755_, v_f_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_757_, lean_object* v___x_758_, lean_object* v_acc_759_, lean_object* v_k_760_, lean_object* v_t_761_){
_start:
{
if (lean_obj_tag(v_t_761_) == 0)
{
lean_dec(v_k_760_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v___x_757_);
return v_acc_759_;
}
else
{
lean_object* v_vs_762_; lean_object* v_children_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_vs_762_ = lean_ctor_get(v_t_761_, 0);
v_children_763_ = lean_ctor_get(v_t_761_, 1);
v___x_764_ = lean_array_get_size(v_vs_762_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_nat_dec_eq(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_k_760_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v___x_757_);
return v_acc_759_;
}
else
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_array_get_size(v_children_763_);
v___x_768_ = lean_nat_dec_eq(v___x_767_, v___x_765_);
if (v___x_768_ == 0)
{
lean_dec(v_k_760_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v___x_757_);
return v_acc_759_;
}
else
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_erase___redArg(v___x_757_, v___x_758_, v_acc_759_, v_k_760_);
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v_acc_772_, lean_object* v_k_773_, lean_object* v_t_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(v___x_770_, v___x_771_, v_acc_772_, v_k_773_, v_t_774_);
lean_dec_ref(v_t_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_776_, lean_object* v_toPure_777_, lean_object* v_root_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc_ref(v_root_778_);
v___x_779_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_778_, v___f_776_, v_root_778_);
v___x_780_ = lean_apply_2(v_toPure_777_, lean_box(0), v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_786_, lean_object* v_d_787_, lean_object* v_f_788_){
_start:
{
lean_object* v_toApplicative_789_; lean_object* v_toBind_790_; lean_object* v_toPure_791_; lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_toApplicative_789_ = lean_ctor_get(v_inst_786_, 0);
v_toBind_790_ = lean_ctor_get(v_inst_786_, 1);
lean_inc(v_toBind_790_);
v_toPure_791_ = lean_ctor_get(v_toApplicative_789_, 1);
lean_inc_ref(v_inst_786_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_792_, 0, v_inst_786_);
lean_closure_set(v___f_792_, 1, v_f_788_);
v___f_793_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_791_);
v___f_794_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_794_, 0, v___f_793_);
lean_closure_set(v___f_794_, 1, v_toPure_791_);
v___x_795_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_786_, v_d_787_, v___f_792_);
v___x_796_ = lean_apply_4(v_toBind_790_, lean_box(0), lean_box(0), v___x_795_, v___f_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_797_, lean_object* v_inst_798_, lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_d_801_, lean_object* v_f_802_){
_start:
{
lean_object* v_toApplicative_803_; lean_object* v_toBind_804_; lean_object* v_toPure_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_toApplicative_803_ = lean_ctor_get(v_inst_798_, 0);
v_toBind_804_ = lean_ctor_get(v_inst_798_, 1);
lean_inc(v_toBind_804_);
v_toPure_805_ = lean_ctor_get(v_toApplicative_803_, 1);
lean_inc_ref(v_inst_798_);
v___f_806_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_806_, 0, v_inst_798_);
lean_closure_set(v___f_806_, 1, v_f_802_);
v___f_807_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_805_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_808_, 0, v___f_807_);
lean_closure_set(v___f_808_, 1, v_toPure_805_);
v___x_809_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_798_, v_d_801_, v___f_806_);
v___x_810_ = lean_apply_4(v_toBind_804_, lean_box(0), lean_box(0), v___x_809_, v___f_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_811_, lean_object* v_A_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_apply_1(v_f_811_, v_A_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_814_, lean_object* v___f_815_, lean_object* v_t_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_814_, v_t_816_, v___f_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_818_, lean_object* v_f_819_){
_start:
{
lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_820_, 0, v_f_819_);
v___x_821_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_822_, 0, v___x_821_);
lean_closure_set(v___f_822_, 1, v___f_820_);
v___f_823_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_824_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_821_, v_d_818_, v___f_822_);
lean_inc(v___x_824_);
v___x_825_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_824_, v___f_823_, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_d_828_, lean_object* v_f_829_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___f_830_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_830_, 0, v_f_829_);
v___x_831_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_832_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_832_, 0, v___x_831_);
lean_closure_set(v___f_832_, 1, v___f_830_);
v___f_833_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_834_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_831_, v_d_828_, v___f_832_);
lean_inc(v___x_834_);
v___x_835_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_834_, v___f_833_, v___x_834_);
return v___x_835_;
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
