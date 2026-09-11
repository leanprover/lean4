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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___boxed(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_DiscrTree_values___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_DiscrTree_values___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_values___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_DiscrTree_values___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9_value),((lean_object*)&l_Lean_Meta_DiscrTree_values___redArg___closed__0_value)} };
static const lean_object* l_Lean_Meta_DiscrTree_values___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_values___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_le(v___x_7_, v___x_7_);
if (v___x_10_ == 0)
{
if (v___x_8_ == 0)
{
lean_object* v___x_11_; 
lean_dec(v___f_5_);
lean_dec_ref(v_inst_4_);
lean_dec_ref(v_children_1_);
v___x_11_ = lean_apply_2(v_toPure_3_, lean_box(0), v_s_6_);
return v___x_11_;
}
else
{
size_t v___x_12_; size_t v___x_13_; lean_object* v___x_14_; 
lean_dec(v_toPure_3_);
v___x_12_ = ((size_t)0ULL);
v___x_13_ = lean_usize_of_nat(v___x_7_);
v___x_14_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4_, v___f_5_, v_children_1_, v___x_12_, v___x_13_, v_s_6_);
return v___x_14_;
}
}
else
{
size_t v___x_15_; size_t v___x_16_; lean_object* v___x_17_; 
lean_dec(v_toPure_3_);
v___x_15_ = ((size_t)0ULL);
v___x_16_ = lean_usize_of_nat(v___x_7_);
v___x_17_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4_, v___f_5_, v_children_1_, v___x_15_, v___x_16_, v_s_6_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed(lean_object* v_children_18_, lean_object* v___x_19_, lean_object* v_toPure_20_, lean_object* v_inst_21_, lean_object* v___f_22_, lean_object* v_s_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(v_children_18_, v___x_19_, v_toPure_20_, v_inst_21_, v___f_22_, v_s_23_);
lean_dec(v___x_19_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object* v_f_25_, lean_object* v_initialKeys_26_, lean_object* v_s_27_, lean_object* v_v_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_3(v_f_25_, v_s_27_, v_initialKeys_26_, v_v_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object* v_inst_30_, lean_object* v_initialKeys_31_, lean_object* v_f_32_, lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_toApplicative_35_; lean_object* v_toBind_36_; lean_object* v_vs_37_; lean_object* v_children_38_; lean_object* v_toPure_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_toApplicative_35_ = lean_ctor_get(v_inst_30_, 0);
v_toBind_36_ = lean_ctor_get(v_inst_30_, 1);
lean_inc(v_toBind_36_);
v_vs_37_ = lean_ctor_get(v_x_34_, 0);
lean_inc_ref(v_vs_37_);
v_children_38_ = lean_ctor_get(v_x_34_, 1);
lean_inc_ref(v_children_38_);
lean_dec_ref(v_x_34_);
v_toPure_39_ = lean_ctor_get(v_toApplicative_35_, 1);
lean_inc(v_f_32_);
lean_inc_ref_n(v_inst_30_, 2);
lean_inc_ref(v_initialKeys_31_);
v___f_40_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0), 5, 3);
lean_closure_set(v___f_40_, 0, v_initialKeys_31_);
lean_closure_set(v___f_40_, 1, v_inst_30_);
lean_closure_set(v___f_40_, 2, v_f_32_);
v___x_41_ = lean_unsigned_to_nat(0u);
lean_inc(v_toPure_39_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_42_, 0, v_children_38_);
lean_closure_set(v___f_42_, 1, v___x_41_);
lean_closure_set(v___f_42_, 2, v_toPure_39_);
lean_closure_set(v___f_42_, 3, v_inst_30_);
lean_closure_set(v___f_42_, 4, v___f_40_);
v___x_43_ = lean_array_get_size(v_vs_37_);
v___x_44_ = lean_nat_dec_lt(v___x_41_, v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_inc(v_toPure_39_);
lean_dec_ref(v_vs_37_);
lean_dec(v_f_32_);
lean_dec_ref(v_initialKeys_31_);
lean_dec_ref(v_inst_30_);
v___x_45_ = lean_apply_2(v_toPure_39_, lean_box(0), v_x_33_);
v___x_46_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_45_, v___f_42_);
return v___x_46_;
}
else
{
lean_object* v___f_47_; uint8_t v___x_48_; 
v___f_47_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_47_, 0, v_f_32_);
lean_closure_set(v___f_47_, 1, v_initialKeys_31_);
v___x_48_ = lean_nat_dec_le(v___x_43_, v___x_43_);
if (v___x_48_ == 0)
{
if (v___x_44_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_inc(v_toPure_39_);
lean_dec_ref(v___f_47_);
lean_dec_ref(v_vs_37_);
lean_dec_ref(v_inst_30_);
v___x_49_ = lean_apply_2(v_toPure_39_, lean_box(0), v_x_33_);
v___x_50_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_49_, v___f_42_);
return v___x_50_;
}
else
{
size_t v___x_51_; size_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((size_t)0ULL);
v___x_52_ = lean_usize_of_nat(v___x_43_);
v___x_53_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_30_, v___f_47_, v_vs_37_, v___x_51_, v___x_52_, v_x_33_);
v___x_54_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_53_, v___f_42_);
return v___x_54_;
}
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_43_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_30_, v___f_47_, v_vs_37_, v___x_55_, v___x_56_, v_x_33_);
v___x_58_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v___x_57_, v___f_42_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object* v_initialKeys_59_, lean_object* v_inst_60_, lean_object* v_f_61_, lean_object* v_s_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_fst_64_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_fst_64_);
v_snd_65_ = lean_ctor_get(v_x_63_, 1);
lean_inc(v_snd_65_);
lean_dec_ref(v_x_63_);
v___x_66_ = lean_array_push(v_initialKeys_59_, v_fst_64_);
v___x_67_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_60_, v___x_66_, v_f_61_, v_s_62_, v_snd_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object* v_m_68_, lean_object* v_00_u03c3_69_, lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_initialKeys_72_, lean_object* v_f_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_71_, v_initialKeys_72_, v_f_73_, v_x_74_, v_x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object* v_f_77_, lean_object* v_s_78_, lean_object* v_k_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_apply_3(v_f_77_, v_s_78_, v_k_79_, v_a_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object* v_initialKeys_101_, lean_object* v_f_102_, lean_object* v_init_103_, lean_object* v_t_104_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_105_, 0, v_f_102_);
v___x_106_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_107_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_106_, v_initialKeys_101_, v___f_105_, v_init_103_, v_t_104_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object* v_00_u03c3_108_, lean_object* v_00_u03b1_109_, lean_object* v_initialKeys_110_, lean_object* v_f_111_, lean_object* v_init_112_, lean_object* v_t_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___f_114_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_114_, 0, v_f_111_);
v___x_115_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_116_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_115_, v_initialKeys_110_, v___f_114_, v_init_112_, v_t_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object* v_inst_117_, lean_object* v_f_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_toApplicative_121_; lean_object* v_toBind_122_; lean_object* v_vs_123_; lean_object* v_children_124_; lean_object* v_toPure_125_; lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___f_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_toApplicative_121_ = lean_ctor_get(v_inst_117_, 0);
v_toBind_122_ = lean_ctor_get(v_inst_117_, 1);
lean_inc(v_toBind_122_);
v_vs_123_ = lean_ctor_get(v_x_120_, 0);
lean_inc_ref(v_vs_123_);
v_children_124_ = lean_ctor_get(v_x_120_, 1);
lean_inc_ref(v_children_124_);
lean_dec_ref(v_x_120_);
v_toPure_125_ = lean_ctor_get(v_toApplicative_121_, 1);
lean_inc(v_f_118_);
lean_inc_ref_n(v_inst_117_, 2);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_126_, 0, v_inst_117_);
lean_closure_set(v___f_126_, 1, v_f_118_);
v___x_127_ = lean_unsigned_to_nat(0u);
lean_inc(v_toPure_125_);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_128_, 0, v_children_124_);
lean_closure_set(v___f_128_, 1, v___x_127_);
lean_closure_set(v___f_128_, 2, v_toPure_125_);
lean_closure_set(v___f_128_, 3, v_inst_117_);
lean_closure_set(v___f_128_, 4, v___f_126_);
v___x_129_ = lean_array_get_size(v_vs_123_);
v___x_130_ = lean_nat_dec_lt(v___x_127_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_inc(v_toPure_125_);
lean_dec_ref(v_vs_123_);
lean_dec(v_f_118_);
lean_dec_ref(v_inst_117_);
v___x_131_ = lean_apply_2(v_toPure_125_, lean_box(0), v_x_119_);
v___x_132_ = lean_apply_4(v_toBind_122_, lean_box(0), lean_box(0), v___x_131_, v___f_128_);
return v___x_132_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = lean_nat_dec_le(v___x_129_, v___x_129_);
if (v___x_133_ == 0)
{
if (v___x_130_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_inc(v_toPure_125_);
lean_dec_ref(v_vs_123_);
lean_dec(v_f_118_);
lean_dec_ref(v_inst_117_);
v___x_134_ = lean_apply_2(v_toPure_125_, lean_box(0), v_x_119_);
v___x_135_ = lean_apply_4(v_toBind_122_, lean_box(0), lean_box(0), v___x_134_, v___f_128_);
return v___x_135_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_129_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_117_, v_f_118_, v_vs_123_, v___x_136_, v___x_137_, v_x_119_);
v___x_139_ = lean_apply_4(v_toBind_122_, lean_box(0), lean_box(0), v___x_138_, v___f_128_);
return v___x_139_;
}
}
else
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_129_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_117_, v_f_118_, v_vs_123_, v___x_140_, v___x_141_, v_x_119_);
v___x_143_ = lean_apply_4(v_toBind_122_, lean_box(0), lean_box(0), v___x_142_, v___f_128_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object* v_inst_144_, lean_object* v_f_145_, lean_object* v_s_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_snd_148_; lean_object* v___x_149_; 
v_snd_148_ = lean_ctor_get(v_x_147_, 1);
lean_inc(v_snd_148_);
lean_dec_ref(v_x_147_);
v___x_149_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_144_, v_f_145_, v_s_146_, v_snd_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object* v_m_150_, lean_object* v_00_u03c3_151_, lean_object* v_00_u03b1_152_, lean_object* v_inst_153_, lean_object* v_f_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_153_, v_f_154_, v_x_155_, v_x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object* v_f_158_, lean_object* v_x1_159_, lean_object* v_x2_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_apply_2(v_f_158_, v_x1_159_, v_x2_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object* v_f_162_, lean_object* v_init_163_, lean_object* v_t_164_){
_start:
{
lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___f_165_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_165_, 0, v_f_162_);
v___x_166_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_167_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_166_, v___f_165_, v_init_163_, v_t_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object* v_00_u03c3_168_, lean_object* v_00_u03b1_169_, lean_object* v_f_170_, lean_object* v_init_171_, lean_object* v_t_172_){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___f_173_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_173_, 0, v_f_170_);
v___x_174_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_175_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_174_, v___f_173_, v_init_171_, v_t_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object* v_x_176_){
_start:
{
lean_object* v_vs_177_; lean_object* v_children_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_vs_177_ = lean_ctor_get(v_x_176_, 0);
v_children_178_ = lean_ctor_get(v_x_176_, 1);
v___x_179_ = lean_array_get_size(v_vs_177_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_array_get_size(v_children_178_);
v___x_182_ = lean_nat_dec_lt(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_le(v___x_181_, v___x_181_);
if (v___x_183_ == 0)
{
if (v___x_182_ == 0)
{
return v___x_179_;
}
else
{
size_t v___x_184_; size_t v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((size_t)0ULL);
v___x_185_ = lean_usize_of_nat(v___x_181_);
v___x_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_178_, v___x_184_, v___x_185_, v___x_179_);
return v___x_186_;
}
}
else
{
size_t v___x_187_; size_t v___x_188_; lean_object* v___x_189_; 
v___x_187_ = ((size_t)0ULL);
v___x_188_ = lean_usize_of_nat(v___x_181_);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_178_, v___x_187_, v___x_188_, v___x_179_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v_b_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_snd_196_; lean_object* v___x_197_; lean_object* v___x_198_; size_t v___x_199_; size_t v___x_200_; 
v___x_195_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
v_snd_196_ = lean_ctor_get(v___x_195_, 1);
v___x_197_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_196_);
v___x_198_ = lean_nat_add(v_b_193_, v___x_197_);
lean_dec(v___x_197_);
lean_dec(v_b_193_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_191_, v___x_199_);
v_i_191_ = v___x_200_;
v_b_193_ = v___x_198_;
goto _start;
}
else
{
return v_b_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_202_, lean_object* v_i_203_, lean_object* v_stop_204_, lean_object* v_b_205_){
_start:
{
size_t v_i_boxed_206_; size_t v_stop_boxed_207_; lean_object* v_res_208_; 
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_stop_boxed_207_ = lean_unbox_usize(v_stop_204_);
lean_dec(v_stop_204_);
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_202_, v_i_boxed_206_, v_stop_boxed_207_, v_b_205_);
lean_dec_ref(v_as_202_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_209_);
lean_dec_ref(v_x_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___boxed(lean_object* v_00_u03b1_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Meta_DiscrTree_Trie_size(v_00_u03b1_214_, v_x_215_);
lean_dec_ref(v_x_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_217_, lean_object* v_as_218_, size_t v_i_219_, size_t v_stop_220_, lean_object* v_b_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_218_, v_i_219_, v_stop_220_, v_b_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_223_, lean_object* v_as_224_, lean_object* v_i_225_, lean_object* v_stop_226_, lean_object* v_b_227_){
_start:
{
size_t v_i_boxed_228_; size_t v_stop_boxed_229_; lean_object* v_res_230_; 
v_i_boxed_228_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_stop_boxed_229_ = lean_unbox_usize(v_stop_226_);
lean_dec(v_stop_226_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_223_, v_as_224_, v_i_boxed_228_, v_stop_boxed_229_, v_b_227_);
lean_dec_ref(v_as_224_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object* v_vs_231_, lean_object* v_cs_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_vs_231_);
lean_ctor_set(v___x_233_, 1, v_cs_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object* v_00_u03b1_234_, lean_object* v_vs_235_, lean_object* v_cs_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_vs_235_);
lean_ctor_set(v___x_237_, 1, v_cs_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object* v_x_238_){
_start:
{
lean_object* v_vs_239_; lean_object* v_children_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_vs_239_ = lean_ctor_get(v_x_238_, 0);
v_children_240_ = lean_ctor_get(v_x_238_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v_x_238_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_children_240_);
lean_inc(v_vs_239_);
lean_dec(v_x_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_vs_239_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_children_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object* v_00_u03b1_248_, lean_object* v_x_249_){
_start:
{
lean_object* v_vs_250_; lean_object* v_children_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_vs_250_ = lean_ctor_get(v_x_249_, 0);
v_children_251_ = lean_ctor_get(v_x_249_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v_x_249_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_children_251_);
lean_inc(v_vs_250_);
lean_dec(v_x_249_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_vs_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_children_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object* v_x_259_){
_start:
{
lean_object* v_vs_260_; 
v_vs_260_ = lean_ctor_get(v_x_259_, 0);
lean_inc_ref(v_vs_260_);
return v_vs_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg___boxed(lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(v_x_261_);
lean_dec_ref(v_x_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object* v_00_u03b1_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_vs_265_; 
v_vs_265_ = lean_ctor_get(v_x_264_, 0);
lean_inc_ref(v_vs_265_);
return v_vs_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___boxed(lean_object* v_00_u03b1_266_, lean_object* v_x_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_DiscrTree_Trie_nodeValues(v_00_u03b1_266_, v_x_267_);
lean_dec_ref(v_x_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object* v_x_269_){
_start:
{
lean_object* v_children_270_; 
v_children_270_ = lean_ctor_get(v_x_269_, 1);
lean_inc_ref(v_children_270_);
return v_children_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg___boxed(lean_object* v_x_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(v_x_271_);
lean_dec_ref(v_x_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object* v_00_u03b1_273_, lean_object* v_x_274_){
_start:
{
lean_object* v_children_275_; 
v_children_275_ = lean_ctor_get(v_x_274_, 1);
lean_inc_ref(v_children_275_);
return v_children_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___boxed(lean_object* v_00_u03b1_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_DiscrTree_Trie_nodeChildren(v_00_u03b1_276_, v_x_277_);
lean_dec_ref(v_x_277_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_x_279_){
_start:
{
lean_object* v_vs_280_; lean_object* v_children_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_vs_280_ = lean_ctor_get(v_x_279_, 0);
v_children_281_ = lean_ctor_get(v_x_279_, 1);
v___x_282_ = lean_array_get_size(v_vs_280_);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_nat_dec_eq(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
return v___x_284_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_array_get_size(v_children_281_);
v___x_286_ = lean_nat_dec_eq(v___x_285_, v___x_283_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_287_);
lean_dec_ref(v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_vs_292_; lean_object* v_children_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_vs_292_ = lean_ctor_get(v_x_291_, 0);
v_children_293_ = lean_ctor_get(v_x_291_, 1);
v___x_294_ = lean_array_get_size(v_vs_292_);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
return v___x_296_;
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_array_get_size(v_children_293_);
v___x_298_ = lean_nat_dec_eq(v___x_297_, v___x_295_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_299_, v_x_300_);
lean_dec_ref(v_x_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_303_, lean_object* v_f_304_, lean_object* v_s_305_, lean_object* v_k_306_, lean_object* v_t_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_array_push(v___x_309_, v_k_306_);
v___x_311_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_303_, v___x_310_, v_f_304_, v_s_305_, v_t_307_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_312_, lean_object* v_f_313_, lean_object* v_init_314_, lean_object* v_t_315_){
_start:
{
lean_object* v___f_316_; lean_object* v___x_317_; 
lean_inc_ref(v_inst_312_);
v___f_316_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_316_, 0, v_inst_312_);
lean_closure_set(v___f_316_, 1, v_f_313_);
v___x_317_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_312_, v___f_316_, v_t_315_, v_init_314_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_318_, lean_object* v_00_u03c3_319_, lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_f_322_, lean_object* v_init_323_, lean_object* v_t_324_){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; 
lean_inc_ref(v_inst_321_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_325_, 0, v_inst_321_);
lean_closure_set(v___f_325_, 1, v_f_322_);
v___x_326_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_321_, v___f_325_, v_t_324_, v_init_323_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_327_, lean_object* v_s_328_, lean_object* v_keys_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_apply_3(v_f_327_, v_s_328_, v_keys_329_, v_a_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_332_, lean_object* v___f_333_, lean_object* v_s_334_, lean_object* v_k_335_, lean_object* v_t_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_mk_empty_array_with_capacity(v___x_337_);
v___x_339_ = lean_array_push(v___x_338_, v_k_335_);
v___x_340_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_332_, v___x_339_, v___f_333_, v_s_334_, v_t_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_341_, lean_object* v_init_342_, lean_object* v_t_343_){
_start:
{
lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_344_, 0, v_f_341_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_346_, 0, v___x_345_);
lean_closure_set(v___f_346_, 1, v___f_344_);
v___x_347_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_345_, v___f_346_, v_t_343_, v_init_342_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_348_, lean_object* v_00_u03b1_349_, lean_object* v_f_350_, lean_object* v_init_351_, lean_object* v_t_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___x_356_; 
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_353_, 0, v_f_350_);
v___x_354_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_355_, 0, v___x_354_);
lean_closure_set(v___f_355_, 1, v___f_353_);
v___x_356_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_354_, v___f_355_, v_t_352_, v_init_351_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_357_, lean_object* v_f_358_, lean_object* v_s_359_, lean_object* v_x_360_, lean_object* v_t_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_357_, v_f_358_, v_s_359_, v_t_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_363_, lean_object* v_f_364_, lean_object* v_s_365_, lean_object* v_x_366_, lean_object* v_t_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_363_, v_f_364_, v_s_365_, v_x_366_, v_t_367_);
lean_dec(v_x_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_369_, lean_object* v_f_370_, lean_object* v_init_371_, lean_object* v_t_372_){
_start:
{
lean_object* v___f_373_; lean_object* v___x_374_; 
lean_inc_ref(v_inst_369_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_373_, 0, v_inst_369_);
lean_closure_set(v___f_373_, 1, v_f_370_);
v___x_374_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_369_, v___f_373_, v_t_372_, v_init_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_375_, lean_object* v_00_u03c3_376_, lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_f_379_, lean_object* v_init_380_, lean_object* v_t_381_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; 
lean_inc_ref(v_inst_378_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_382_, 0, v_inst_378_);
lean_closure_set(v___f_382_, 1, v_f_379_);
v___x_383_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_378_, v___f_382_, v_t_381_, v_init_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_384_, lean_object* v___f_385_, lean_object* v_s_386_, lean_object* v_x_387_, lean_object* v_t_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_384_, v___f_385_, v_s_386_, v_t_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_390_, lean_object* v___f_391_, lean_object* v_s_392_, lean_object* v_x_393_, lean_object* v_t_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_390_, v___f_391_, v_s_392_, v_x_393_, v_t_394_);
lean_dec(v_x_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_396_, lean_object* v_init_397_, lean_object* v_t_398_){
_start:
{
lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___f_401_; lean_object* v___x_402_; 
v___f_399_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_399_, 0, v_f_396_);
v___x_400_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_401_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_401_, 0, v___x_400_);
lean_closure_set(v___f_401_, 1, v___f_399_);
v___x_402_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_400_, v___f_401_, v_t_398_, v_init_397_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_403_, lean_object* v_00_u03b1_404_, lean_object* v_f_405_, lean_object* v_init_406_, lean_object* v_t_407_){
_start:
{
lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_408_, 0, v_f_405_);
v___x_409_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_410_, 0, v___x_409_);
lean_closure_set(v___f_410_, 1, v___f_408_);
v___x_411_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_409_, v___f_410_, v_t_407_, v_init_406_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_412_, uint8_t v_x1_413_, lean_object* v_x2_414_){
_start:
{
if (v_x1_413_ == 0)
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_apply_1(v_f_412_, v_x2_414_);
v___x_416_ = lean_unbox(v___x_415_);
return v___x_416_;
}
else
{
lean_dec(v_x2_414_);
lean_dec_ref(v_f_412_);
return v_x1_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_417_, lean_object* v_x1_418_, lean_object* v_x2_419_){
_start:
{
uint8_t v_x1_83__boxed_420_; uint8_t v_res_421_; lean_object* v_r_422_; 
v_x1_83__boxed_420_ = lean_unbox(v_x1_418_);
v_res_421_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_417_, v_x1_83__boxed_420_, v_x2_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_423_, lean_object* v___f_424_, uint8_t v_s_425_, lean_object* v_x_426_, lean_object* v_t_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(v_s_425_);
v___x_429_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_423_, v___f_424_, v___x_428_, v_t_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_430_, lean_object* v___f_431_, lean_object* v_s_432_, lean_object* v_x_433_, lean_object* v_t_434_){
_start:
{
uint8_t v_s_boxed_435_; lean_object* v_res_436_; 
v_s_boxed_435_ = lean_unbox(v_s_432_);
v_res_436_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_430_, v___f_431_, v_s_boxed_435_, v_x_433_, v_t_434_);
lean_dec(v_x_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_437_, lean_object* v_f_438_){
_start:
{
lean_object* v___f_439_; uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___f_439_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_439_, 0, v_f_438_);
v___x_440_ = 0;
v___x_441_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_442_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_442_, 0, v___x_441_);
lean_closure_set(v___f_442_, 1, v___f_439_);
v___x_443_ = lean_box(v___x_440_);
v___x_444_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_441_, v___f_442_, v_t_437_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_445_, lean_object* v_t_446_, lean_object* v_f_447_){
_start:
{
lean_object* v___f_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_448_, 0, v_f_447_);
v___x_449_ = 0;
v___x_450_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_451_, 0, v___x_450_);
lean_closure_set(v___f_451_, 1, v___f_448_);
v___x_452_ = lean_box(v___x_449_);
v___x_453_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_450_, v___f_451_, v_t_446_, v___x_452_);
v___x_454_ = lean_unbox(v___x_453_);
lean_dec(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_455_, lean_object* v_t_456_, lean_object* v_f_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_455_, v_t_456_, v_f_457_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_460_, lean_object* v_x2_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_array_push(v_x1_460_, v_x2_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_463_, lean_object* v___f_464_, lean_object* v_s_465_, lean_object* v_x_466_, lean_object* v_t_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_463_, v___f_464_, v_s_465_, v_t_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_469_, lean_object* v___f_470_, lean_object* v_s_471_, lean_object* v_x_472_, lean_object* v_t_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_469_, v___f_470_, v_s_471_, v_x_472_, v_t_473_);
lean_dec(v_x_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___x_485_; 
v___x_482_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_483_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_484_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_485_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_483_, v___f_484_, v_t_481_, v___x_482_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_486_, lean_object* v_t_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___f_490_; lean_object* v___x_491_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_489_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_490_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_491_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_489_, v___f_490_, v_t_487_, v___x_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_492_, lean_object* v_keys_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_keys_493_);
lean_ctor_set(v___x_495_, 1, v_a_494_);
v___x_496_ = lean_array_push(v_s_492_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_497_, lean_object* v___f_498_, lean_object* v_s_499_, lean_object* v_k_500_, lean_object* v_t_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_mk_empty_array_with_capacity(v___x_502_);
v___x_504_ = lean_array_push(v___x_503_, v_k_500_);
v___x_505_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_497_, v___x_504_, v___f_498_, v_s_499_, v_t_501_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v___x_513_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_514_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_515_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_516_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_514_, v___f_515_, v_t_512_, v___x_513_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_517_, lean_object* v_t_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v___x_519_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_520_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_521_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_522_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_520_, v___f_521_, v_t_518_, v___x_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_523_, lean_object* v_x_524_, lean_object* v_t_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_525_);
v___x_527_ = lean_nat_add(v_n_523_, v___x_526_);
lean_dec(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_528_, lean_object* v_x_529_, lean_object* v_t_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_528_, v_x_529_, v_t_530_);
lean_dec_ref(v_t_530_);
lean_dec(v_x_529_);
lean_dec(v_n_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_533_){
_start:
{
lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___f_534_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_533_, v___f_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_537_, lean_object* v_t_538_){
_start:
{
lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___f_539_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_538_, v___f_539_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_fst_542_, lean_object* v_toPure_543_, lean_object* v_child_544_){
_start:
{
lean_object* v_vs_549_; lean_object* v_children_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_vs_549_ = lean_ctor_get(v_child_544_, 0);
v_children_550_ = lean_ctor_get(v_child_544_, 1);
v___x_551_ = lean_array_get_size(v_vs_549_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
goto v___jp_545_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_size(v_children_550_);
v___x_555_ = lean_nat_dec_eq(v___x_554_, v___x_552_);
if (v___x_555_ == 0)
{
goto v___jp_545_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec_ref(v_child_544_);
lean_dec(v_fst_542_);
v___x_556_ = lean_box(0);
v___x_557_ = lean_apply_2(v_toPure_543_, lean_box(0), v___x_556_);
return v___x_557_;
}
}
v___jp_545_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_fst_542_);
lean_ctor_set(v___x_546_, 1, v_child_544_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = lean_apply_2(v_toPure_543_, lean_box(0), v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_vs_558_, lean_object* v_toPure_559_, lean_object* v_children_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_vs_558_);
lean_ctor_set(v___x_561_, 1, v_children_560_);
v___x_562_ = lean_apply_2(v_toPure_559_, lean_box(0), v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_563_, lean_object* v_children_564_, lean_object* v_inst_565_, lean_object* v___f_566_, lean_object* v_toBind_567_, lean_object* v_vs_568_){
_start:
{
lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_569_, 0, v_vs_568_);
lean_closure_set(v___f_569_, 1, v_toPure_563_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_array_get_size(v_children_564_);
v___x_572_ = l_Array_filterMapM___redArg(v_inst_565_, v___f_566_, v_children_564_, v___x_570_, v___x_571_);
v___x_573_ = lean_apply_4(v_toBind_567_, lean_box(0), lean_box(0), v___x_572_, v___f_569_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_574_, lean_object* v_t_575_, lean_object* v_f_576_){
_start:
{
lean_object* v_toApplicative_577_; lean_object* v_toBind_578_; lean_object* v_toPure_579_; lean_object* v_vs_580_; lean_object* v_children_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_toApplicative_577_ = lean_ctor_get(v_inst_574_, 0);
v_toBind_578_ = lean_ctor_get(v_inst_574_, 1);
lean_inc_n(v_toBind_578_, 3);
v_toPure_579_ = lean_ctor_get(v_toApplicative_577_, 1);
lean_inc_n(v_toPure_579_, 2);
v_vs_580_ = lean_ctor_get(v_t_575_, 0);
lean_inc_ref(v_vs_580_);
v_children_581_ = lean_ctor_get(v_t_575_, 1);
lean_inc_ref(v_children_581_);
lean_dec_ref(v_t_575_);
lean_inc(v_f_576_);
lean_inc_ref(v_inst_574_);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_582_, 0, v_toPure_579_);
lean_closure_set(v___f_582_, 1, v_inst_574_);
lean_closure_set(v___f_582_, 2, v_f_576_);
lean_closure_set(v___f_582_, 3, v_toBind_578_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 6, 5);
lean_closure_set(v___f_583_, 0, v_toPure_579_);
lean_closure_set(v___f_583_, 1, v_children_581_);
lean_closure_set(v___f_583_, 2, v_inst_574_);
lean_closure_set(v___f_583_, 3, v___f_582_);
lean_closure_set(v___f_583_, 4, v_toBind_578_);
v___x_584_ = lean_apply_1(v_f_576_, v_vs_580_);
v___x_585_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_584_, v___f_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_586_, lean_object* v_inst_587_, lean_object* v_f_588_, lean_object* v_toBind_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_fst_591_ = lean_ctor_get(v_x_590_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v_x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v_x_590_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_593_, 0, v_fst_591_);
lean_closure_set(v___f_593_, 1, v_toPure_586_);
v___x_594_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_587_, v_snd_592_, v_f_588_);
v___x_595_ = lean_apply_4(v_toBind_589_, lean_box(0), lean_box(0), v___x_594_, v___f_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_596_, lean_object* v_inst_597_, lean_object* v_00_u03b1_598_, lean_object* v_00_u03b2_599_, lean_object* v_t_600_, lean_object* v_f_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_597_, v_t_600_, v_f_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_603_, lean_object* v_f_604_, lean_object* v_t_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_603_, v_t_605_, v_f_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v_acc_609_, lean_object* v_k_610_, lean_object* v_t_611_){
_start:
{
lean_object* v_vs_612_; lean_object* v_children_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_vs_612_ = lean_ctor_get(v_t_611_, 0);
v_children_613_ = lean_ctor_get(v_t_611_, 1);
v___x_614_ = lean_array_get_size(v_vs_612_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_dec(v_k_610_);
lean_dec_ref(v___x_608_);
lean_dec_ref(v___x_607_);
return v_acc_609_;
}
else
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_array_get_size(v_children_613_);
v___x_618_ = lean_nat_dec_eq(v___x_617_, v___x_615_);
if (v___x_618_ == 0)
{
lean_dec(v_k_610_);
lean_dec_ref(v___x_608_);
lean_dec_ref(v___x_607_);
return v_acc_609_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_erase___redArg(v___x_607_, v___x_608_, v_acc_609_, v_k_610_);
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v_acc_622_, lean_object* v_k_623_, lean_object* v_t_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(v___x_620_, v___x_621_, v_acc_622_, v_k_623_, v_t_624_);
lean_dec_ref(v_t_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_626_, lean_object* v_toPure_627_, lean_object* v_root_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc_ref(v_root_628_);
v___x_629_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_628_, v___f_626_, v_root_628_);
v___x_630_ = lean_apply_2(v_toPure_627_, lean_box(0), v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_636_, lean_object* v_d_637_, lean_object* v_f_638_){
_start:
{
lean_object* v_toApplicative_639_; lean_object* v_toBind_640_; lean_object* v_toPure_641_; lean_object* v___f_642_; lean_object* v___f_643_; lean_object* v___f_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_toApplicative_639_ = lean_ctor_get(v_inst_636_, 0);
v_toBind_640_ = lean_ctor_get(v_inst_636_, 1);
lean_inc(v_toBind_640_);
v_toPure_641_ = lean_ctor_get(v_toApplicative_639_, 1);
lean_inc_ref(v_inst_636_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_642_, 0, v_inst_636_);
lean_closure_set(v___f_642_, 1, v_f_638_);
v___f_643_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_641_);
v___f_644_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_644_, 0, v___f_643_);
lean_closure_set(v___f_644_, 1, v_toPure_641_);
v___x_645_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_636_, v_d_637_, v___f_642_);
v___x_646_ = lean_apply_4(v_toBind_640_, lean_box(0), lean_box(0), v___x_645_, v___f_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_647_, lean_object* v_inst_648_, lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_d_651_, lean_object* v_f_652_){
_start:
{
lean_object* v_toApplicative_653_; lean_object* v_toBind_654_; lean_object* v_toPure_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_toApplicative_653_ = lean_ctor_get(v_inst_648_, 0);
v_toBind_654_ = lean_ctor_get(v_inst_648_, 1);
lean_inc(v_toBind_654_);
v_toPure_655_ = lean_ctor_get(v_toApplicative_653_, 1);
lean_inc_ref(v_inst_648_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_656_, 0, v_inst_648_);
lean_closure_set(v___f_656_, 1, v_f_652_);
v___f_657_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_655_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_658_, 0, v___f_657_);
lean_closure_set(v___f_658_, 1, v_toPure_655_);
v___x_659_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_648_, v_d_651_, v___f_656_);
v___x_660_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v___x_659_, v___f_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_661_, lean_object* v_A_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_apply_1(v_f_661_, v_A_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_664_, lean_object* v___f_665_, lean_object* v_t_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_664_, v_t_666_, v___f_665_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_668_, lean_object* v_f_669_){
_start:
{
lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___f_670_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_670_, 0, v_f_669_);
v___x_671_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_672_, 0, v___x_671_);
lean_closure_set(v___f_672_, 1, v___f_670_);
v___f_673_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_674_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_671_, v_d_668_, v___f_672_);
lean_inc(v___x_674_);
v___x_675_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_674_, v___f_673_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_d_678_, lean_object* v_f_679_){
_start:
{
lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v___f_682_; lean_object* v___f_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___f_680_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_680_, 0, v_f_679_);
v___x_681_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_682_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_682_, 0, v___x_681_);
lean_closure_set(v___f_682_, 1, v___f_680_);
v___f_683_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_684_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_681_, v_d_678_, v___f_682_);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_684_, v___f_683_, v___x_684_);
return v___x_685_;
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
