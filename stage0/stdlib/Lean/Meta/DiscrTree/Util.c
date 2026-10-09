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
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v_key_35_; lean_object* v_child_36_; lean_object* v___x_37_; 
v_key_35_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_key_35_);
v_child_36_ = lean_ctor_get(v_x_34_, 1);
lean_inc_ref(v_child_36_);
lean_dec_ref_known(v_x_34_, 2);
v___x_37_ = lean_array_push(v_initialKeys_31_, v_key_35_);
v_initialKeys_31_ = v___x_37_;
v_x_34_ = v_child_36_;
goto _start;
}
else
{
lean_object* v_toApplicative_39_; lean_object* v_toBind_40_; lean_object* v_vs_41_; lean_object* v_children_42_; lean_object* v_toPure_43_; lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___f_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v_toApplicative_39_ = lean_ctor_get(v_inst_30_, 0);
v_toBind_40_ = lean_ctor_get(v_inst_30_, 1);
lean_inc(v_toBind_40_);
v_vs_41_ = lean_ctor_get(v_x_34_, 0);
lean_inc_ref(v_vs_41_);
v_children_42_ = lean_ctor_get(v_x_34_, 1);
lean_inc_ref(v_children_42_);
lean_dec_ref_known(v_x_34_, 2);
v_toPure_43_ = lean_ctor_get(v_toApplicative_39_, 1);
lean_inc(v_f_32_);
lean_inc_ref_n(v_inst_30_, 2);
lean_inc_ref(v_initialKeys_31_);
v___f_44_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0), 5, 3);
lean_closure_set(v___f_44_, 0, v_initialKeys_31_);
lean_closure_set(v___f_44_, 1, v_inst_30_);
lean_closure_set(v___f_44_, 2, v_f_32_);
v___x_45_ = lean_unsigned_to_nat(0u);
lean_inc(v_toPure_43_);
v___f_46_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_46_, 0, v_children_42_);
lean_closure_set(v___f_46_, 1, v___x_45_);
lean_closure_set(v___f_46_, 2, v_toPure_43_);
lean_closure_set(v___f_46_, 3, v_inst_30_);
lean_closure_set(v___f_46_, 4, v___f_44_);
v___x_47_ = lean_array_get_size(v_vs_41_);
v___x_48_ = lean_nat_dec_lt(v___x_45_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_inc(v_toPure_43_);
lean_dec_ref(v_vs_41_);
lean_dec(v_f_32_);
lean_dec_ref(v_initialKeys_31_);
lean_dec_ref(v_inst_30_);
v___x_49_ = lean_apply_2(v_toPure_43_, lean_box(0), v_x_33_);
v___x_50_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v___x_49_, v___f_46_);
return v___x_50_;
}
else
{
lean_object* v___f_51_; uint8_t v___x_52_; 
v___f_51_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_51_, 0, v_f_32_);
lean_closure_set(v___f_51_, 1, v_initialKeys_31_);
v___x_52_ = lean_nat_dec_le(v___x_47_, v___x_47_);
if (v___x_52_ == 0)
{
if (v___x_48_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_toPure_43_);
lean_dec_ref(v___f_51_);
lean_dec_ref(v_vs_41_);
lean_dec_ref(v_inst_30_);
v___x_53_ = lean_apply_2(v_toPure_43_, lean_box(0), v_x_33_);
v___x_54_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v___x_53_, v___f_46_);
return v___x_54_;
}
else
{
size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((size_t)0ULL);
v___x_56_ = lean_usize_of_nat(v___x_47_);
v___x_57_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_30_, v___f_51_, v_vs_41_, v___x_55_, v___x_56_, v_x_33_);
v___x_58_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v___x_57_, v___f_46_);
return v___x_58_;
}
}
else
{
size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((size_t)0ULL);
v___x_60_ = lean_usize_of_nat(v___x_47_);
v___x_61_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_30_, v___f_51_, v_vs_41_, v___x_59_, v___x_60_, v_x_33_);
v___x_62_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v___x_61_, v___f_46_);
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object* v_initialKeys_63_, lean_object* v_inst_64_, lean_object* v_f_65_, lean_object* v_s_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_fst_68_; lean_object* v_snd_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_fst_68_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_fst_68_);
v_snd_69_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_snd_69_);
lean_dec_ref(v_x_67_);
v___x_70_ = lean_array_push(v_initialKeys_63_, v_fst_68_);
v___x_71_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_64_, v___x_70_, v_f_65_, v_s_66_, v_snd_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object* v_m_72_, lean_object* v_00_u03c3_73_, lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_initialKeys_76_, lean_object* v_f_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_75_, v_initialKeys_76_, v_f_77_, v_x_78_, v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object* v_f_81_, lean_object* v_s_82_, lean_object* v_k_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_apply_3(v_f_81_, v_s_82_, v_k_83_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object* v_initialKeys_105_, lean_object* v_f_106_, lean_object* v_init_107_, lean_object* v_t_108_){
_start:
{
lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___f_109_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_109_, 0, v_f_106_);
v___x_110_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_111_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_110_, v_initialKeys_105_, v___f_109_, v_init_107_, v_t_108_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object* v_00_u03c3_112_, lean_object* v_00_u03b1_113_, lean_object* v_initialKeys_114_, lean_object* v_f_115_, lean_object* v_init_116_, lean_object* v_t_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_118_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_118_, 0, v_f_115_);
v___x_119_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_120_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_119_, v_initialKeys_114_, v___f_118_, v_init_116_, v_t_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object* v_inst_121_, lean_object* v_f_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v_child_125_; 
v_child_125_ = lean_ctor_get(v_x_124_, 1);
lean_inc_ref(v_child_125_);
lean_dec_ref_known(v_x_124_, 2);
v_x_124_ = v_child_125_;
goto _start;
}
else
{
lean_object* v_toApplicative_127_; lean_object* v_toBind_128_; lean_object* v_vs_129_; lean_object* v_children_130_; lean_object* v_toPure_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___f_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_toApplicative_127_ = lean_ctor_get(v_inst_121_, 0);
v_toBind_128_ = lean_ctor_get(v_inst_121_, 1);
lean_inc(v_toBind_128_);
v_vs_129_ = lean_ctor_get(v_x_124_, 0);
lean_inc_ref(v_vs_129_);
v_children_130_ = lean_ctor_get(v_x_124_, 1);
lean_inc_ref(v_children_130_);
lean_dec_ref_known(v_x_124_, 2);
v_toPure_131_ = lean_ctor_get(v_toApplicative_127_, 1);
lean_inc(v_f_122_);
lean_inc_ref_n(v_inst_121_, 2);
v___f_132_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_132_, 0, v_inst_121_);
lean_closure_set(v___f_132_, 1, v_f_122_);
v___x_133_ = lean_unsigned_to_nat(0u);
lean_inc(v_toPure_131_);
v___f_134_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_134_, 0, v_children_130_);
lean_closure_set(v___f_134_, 1, v___x_133_);
lean_closure_set(v___f_134_, 2, v_toPure_131_);
lean_closure_set(v___f_134_, 3, v_inst_121_);
lean_closure_set(v___f_134_, 4, v___f_132_);
v___x_135_ = lean_array_get_size(v_vs_129_);
v___x_136_ = lean_nat_dec_lt(v___x_133_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_inc(v_toPure_131_);
lean_dec_ref(v_vs_129_);
lean_dec(v_f_122_);
lean_dec_ref(v_inst_121_);
v___x_137_ = lean_apply_2(v_toPure_131_, lean_box(0), v_x_123_);
v___x_138_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_137_, v___f_134_);
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_le(v___x_135_, v___x_135_);
if (v___x_139_ == 0)
{
if (v___x_136_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_inc(v_toPure_131_);
lean_dec_ref(v_vs_129_);
lean_dec(v_f_122_);
lean_dec_ref(v_inst_121_);
v___x_140_ = lean_apply_2(v_toPure_131_, lean_box(0), v_x_123_);
v___x_141_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_140_, v___f_134_);
return v___x_141_;
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_135_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_121_, v_f_122_, v_vs_129_, v___x_142_, v___x_143_, v_x_123_);
v___x_145_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_144_, v___f_134_);
return v___x_145_;
}
}
else
{
size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_135_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_121_, v_f_122_, v_vs_129_, v___x_146_, v___x_147_, v_x_123_);
v___x_149_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_148_, v___f_134_);
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object* v_inst_150_, lean_object* v_f_151_, lean_object* v_s_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_snd_154_; lean_object* v___x_155_; 
v_snd_154_ = lean_ctor_get(v_x_153_, 1);
lean_inc(v_snd_154_);
lean_dec_ref(v_x_153_);
v___x_155_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_150_, v_f_151_, v_s_152_, v_snd_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object* v_m_156_, lean_object* v_00_u03c3_157_, lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_f_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_159_, v_f_160_, v_x_161_, v_x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object* v_f_164_, lean_object* v_x1_165_, lean_object* v_x2_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_apply_2(v_f_164_, v_x1_165_, v_x2_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object* v_f_168_, lean_object* v_init_169_, lean_object* v_t_170_){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_171_, 0, v_f_168_);
v___x_172_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_173_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_172_, v___f_171_, v_init_169_, v_t_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object* v_00_u03c3_174_, lean_object* v_00_u03b1_175_, lean_object* v_f_176_, lean_object* v_init_177_, lean_object* v_t_178_){
_start:
{
lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___f_179_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_179_, 0, v_f_176_);
v___x_180_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_181_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_180_, v___f_179_, v_init_177_, v_t_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v_child_183_; 
v_child_183_ = lean_ctor_get(v_x_182_, 1);
v_x_182_ = v_child_183_;
goto _start;
}
else
{
lean_object* v_vs_185_; lean_object* v_children_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_vs_185_ = lean_ctor_get(v_x_182_, 0);
v_children_186_ = lean_ctor_get(v_x_182_, 1);
v___x_187_ = lean_array_get_size(v_vs_185_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_array_get_size(v_children_186_);
v___x_190_ = lean_nat_dec_lt(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
return v___x_187_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = lean_nat_dec_le(v___x_189_, v___x_189_);
if (v___x_191_ == 0)
{
if (v___x_190_ == 0)
{
return v___x_187_;
}
else
{
size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((size_t)0ULL);
v___x_193_ = lean_usize_of_nat(v___x_189_);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_186_, v___x_192_, v___x_193_, v___x_187_);
return v___x_194_;
}
}
else
{
size_t v___x_195_; size_t v___x_196_; lean_object* v___x_197_; 
v___x_195_ = ((size_t)0ULL);
v___x_196_ = lean_usize_of_nat(v___x_189_);
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_186_, v___x_195_, v___x_196_, v___x_187_);
return v___x_197_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_198_, size_t v_i_199_, size_t v_stop_200_, lean_object* v_b_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = lean_usize_dec_eq(v_i_199_, v_stop_200_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v_snd_204_; lean_object* v___x_205_; lean_object* v___x_206_; size_t v___x_207_; size_t v___x_208_; 
v___x_203_ = lean_array_uget_borrowed(v_as_198_, v_i_199_);
v_snd_204_ = lean_ctor_get(v___x_203_, 1);
v___x_205_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_204_);
v___x_206_ = lean_nat_add(v_b_201_, v___x_205_);
lean_dec(v___x_205_);
lean_dec(v_b_201_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_add(v_i_199_, v___x_207_);
v_i_199_ = v___x_208_;
v_b_201_ = v___x_206_;
goto _start;
}
else
{
return v_b_201_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_198_ = stack[0].m_obj;
size_t v_i_199_ = stack[1].m_num;
size_t v_stop_200_ = stack[2].m_num;
lean_object* v_b_201_ = stack[3].m_obj;
lean_object* v_res_210_;
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_198_, v_i_199_, v_stop_200_, v_b_201_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_211_, lean_object* v_i_212_, lean_object* v_stop_213_, lean_object* v_b_214_){
_start:
{
size_t v_i_boxed_215_; size_t v_stop_boxed_216_; lean_object* v_res_217_; 
v_i_boxed_215_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_stop_boxed_216_ = lean_unbox_usize(v_stop_213_);
lean_dec(v_stop_213_);
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_211_, v_i_boxed_215_, v_stop_boxed_216_, v_b_214_);
lean_dec_ref(v_as_211_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_218_);
lean_dec_ref(v_x_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___boxed(lean_object* v_00_u03b1_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_DiscrTree_Trie_size(v_00_u03b1_223_, v_x_224_);
lean_dec_ref(v_x_224_);
return v_res_225_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_226_, lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_, lean_object* v_b_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_227_, v_i_228_, v_stop_229_, v_b_230_);
return v___x_231_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_227_ = stack[1].m_obj;
size_t v_i_228_ = stack[2].m_num;
size_t v_stop_229_ = stack[3].m_num;
lean_object* v_b_230_ = stack[4].m_obj;
lean_object* v_res_232_;
v_res_232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_box(0), v_as_227_, v_i_228_, v_stop_229_, v_b_230_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_233_, lean_object* v_as_234_, lean_object* v_i_235_, lean_object* v_stop_236_, lean_object* v_b_237_){
_start:
{
size_t v_i_boxed_238_; size_t v_stop_boxed_239_; lean_object* v_res_240_; 
v_i_boxed_238_ = lean_unbox_usize(v_i_235_);
lean_dec(v_i_235_);
v_stop_boxed_239_ = lean_unbox_usize(v_stop_236_);
lean_dec(v_stop_236_);
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_233_, v_as_234_, v_i_boxed_238_, v_stop_boxed_239_, v_b_237_);
lean_dec_ref(v_as_234_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object* v_vs_241_, lean_object* v_cs_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_array_get_size(v_vs_241_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v_vs_241_);
lean_ctor_set(v___x_246_, 1, v_cs_242_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_array_get_size(v_cs_242_);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v_vs_241_);
lean_ctor_set(v___x_250_, 1, v_cs_242_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v_fst_252_; lean_object* v_snd_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_vs_241_);
v___x_251_ = lean_array_fget(v_cs_242_, v___x_244_);
lean_dec_ref(v_cs_242_);
v_fst_252_ = lean_ctor_get(v___x_251_, 0);
v_snd_253_ = lean_ctor_get(v___x_251_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_251_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_snd_253_);
lean_inc(v_fst_252_);
lean_dec(v___x_251_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_fst_252_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_snd_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object* v_00_u03b1_261_, lean_object* v_vs_262_, lean_object* v_cs_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_array_get_size(v_vs_262_);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_nat_dec_eq(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v_vs_262_);
lean_ctor_set(v___x_267_, 1, v_cs_263_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = lean_array_get_size(v_cs_263_);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_dec_eq(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v_vs_262_);
lean_ctor_set(v___x_271_, 1, v_cs_263_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_vs_262_);
v___x_272_ = lean_array_fget(v_cs_263_, v___x_265_);
lean_dec_ref(v_cs_263_);
v_fst_273_ = lean_ctor_get(v___x_272_, 0);
v_snd_274_ = lean_ctor_get(v___x_272_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_272_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_snd_274_);
lean_inc(v_fst_273_);
lean_dec(v___x_272_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_fst_273_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_snd_274_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object* v_x_284_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object* v_00_u03b1_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v_key_310_; lean_object* v_child_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_323_; 
v_key_310_ = lean_ctor_get(v_x_309_, 0);
v_child_311_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_323_ == 0)
{
v___x_313_ = v_x_309_;
v_isShared_314_ = v_isSharedCheck_323_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_child_311_);
lean_inc(v_key_310_);
lean_dec(v_x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_323_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_314_ == 0)
{
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_key_310_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_child_311_);
v___x_317_ = v_reuseFailAlloc_322_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_mk_empty_array_with_capacity(v___x_318_);
v___x_320_ = lean_array_push(v___x_319_, v___x_317_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_315_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
return v___x_321_;
}
}
}
else
{
lean_object* v_vs_324_; lean_object* v_children_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_vs_324_ = lean_ctor_get(v_x_309_, 0);
v_children_325_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v_x_309_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_children_325_);
lean_inc(v_vs_324_);
lean_dec(v_x_309_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 0);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_vs_324_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_children_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_334_;
}
else
{
lean_object* v_vs_335_; 
v_vs_335_ = lean_ctor_get(v_x_333_, 0);
lean_inc_ref(v_vs_335_);
return v_vs_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg___boxed(lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(v_x_336_);
lean_dec_ref(v_x_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object* v_00_u03b1_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_340_;
}
else
{
lean_object* v_vs_341_; 
v_vs_341_ = lean_ctor_get(v_x_339_, 0);
lean_inc_ref(v_vs_341_);
return v_vs_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___boxed(lean_object* v_00_u03b1_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_DiscrTree_Trie_nodeValues(v_00_u03b1_342_, v_x_343_);
lean_dec_ref(v_x_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v_key_346_; lean_object* v_child_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_357_; 
v_key_346_ = lean_ctor_get(v_x_345_, 0);
v_child_347_ = lean_ctor_get(v_x_345_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_357_ == 0)
{
v___x_349_ = v_x_345_;
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_child_347_);
lean_inc(v_key_346_);
lean_dec(v_x_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_357_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_key_346_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_child_347_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_mk_empty_array_with_capacity(v___x_353_);
v___x_355_ = lean_array_push(v___x_354_, v___x_352_);
return v___x_355_;
}
}
}
else
{
lean_object* v_children_358_; 
v_children_358_ = lean_ctor_get(v_x_345_, 1);
lean_inc_ref(v_children_358_);
lean_dec_ref_known(v_x_345_, 2);
return v_children_358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object* v_00_u03b1_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_key_361_; lean_object* v_child_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
v_key_361_ = lean_ctor_get(v_x_360_, 0);
v_child_362_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_372_ == 0)
{
v___x_364_ = v_x_360_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_child_362_);
lean_inc(v_key_361_);
lean_dec(v_x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_key_361_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_child_362_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_mk_empty_array_with_capacity(v___x_368_);
v___x_370_ = lean_array_push(v___x_369_, v___x_367_);
return v___x_370_;
}
}
}
else
{
lean_object* v_children_373_; 
v_children_373_ = lean_ctor_get(v_x_360_, 1);
lean_inc_ref(v_children_373_);
lean_dec_ref_known(v_x_360_, 2);
return v_children_373_;
}
}
}
uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
else
{
lean_object* v_vs_376_; lean_object* v_children_377_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_vs_376_ = lean_ctor_get(v_x_374_, 0);
v_children_377_ = lean_ctor_get(v_x_374_, 1);
v___x_378_ = lean_array_get_size(v_vs_376_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = lean_nat_dec_eq(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
return v___x_380_;
}
else
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_children_377_);
v___x_382_ = lean_nat_dec_eq(v___x_381_, v___x_379_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_374_ = stack[0].m_obj;
uint8_t v_res_383_;
v_res_383_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_374_);
stack->m_num = v_res_383_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_x_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_384_);
lean_dec_ref(v_x_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
else
{
lean_object* v_vs_390_; lean_object* v_children_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_vs_390_ = lean_ctor_get(v_x_388_, 0);
v_children_391_ = lean_ctor_get(v_x_388_, 1);
v___x_392_ = lean_array_get_size(v_vs_390_);
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = lean_nat_dec_eq(v___x_392_, v___x_393_);
if (v___x_394_ == 0)
{
return v___x_394_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_array_get_size(v_children_391_);
v___x_396_ = lean_nat_dec_eq(v___x_395_, v___x_393_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_Trie_isEmptyNode_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_388_ = stack[1].m_obj;
uint8_t v_res_397_;
v_res_397_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_box(0), v_x_388_);
stack->m_num = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_398_, v_x_399_);
lean_dec_ref(v_x_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_402_, lean_object* v_f_403_, lean_object* v_s_404_, lean_object* v_k_405_, lean_object* v_t_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_array_push(v___x_408_, v_k_405_);
v___x_410_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_402_, v___x_409_, v_f_403_, v_s_404_, v_t_406_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_411_, lean_object* v_f_412_, lean_object* v_init_413_, lean_object* v_t_414_){
_start:
{
lean_object* v___f_415_; lean_object* v___x_416_; 
lean_inc_ref(v_inst_411_);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_415_, 0, v_inst_411_);
lean_closure_set(v___f_415_, 1, v_f_412_);
v___x_416_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_411_, v___f_415_, v_t_414_, v_init_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_417_, lean_object* v_00_u03c3_418_, lean_object* v_00_u03b1_419_, lean_object* v_inst_420_, lean_object* v_f_421_, lean_object* v_init_422_, lean_object* v_t_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; 
lean_inc_ref(v_inst_420_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_424_, 0, v_inst_420_);
lean_closure_set(v___f_424_, 1, v_f_421_);
v___x_425_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_420_, v___f_424_, v_t_423_, v_init_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_426_, lean_object* v_s_427_, lean_object* v_keys_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_apply_3(v_f_426_, v_s_427_, v_keys_428_, v_a_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_431_, lean_object* v___f_432_, lean_object* v_s_433_, lean_object* v_k_434_, lean_object* v_t_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_array_push(v___x_437_, v_k_434_);
v___x_439_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_431_, v___x_438_, v___f_432_, v_s_433_, v_t_435_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_440_, lean_object* v_init_441_, lean_object* v_t_442_){
_start:
{
lean_object* v___f_443_; lean_object* v___x_444_; lean_object* v___f_445_; lean_object* v___x_446_; 
v___f_443_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_443_, 0, v_f_440_);
v___x_444_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_445_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_445_, 0, v___x_444_);
lean_closure_set(v___f_445_, 1, v___f_443_);
v___x_446_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_444_, v___f_445_, v_t_442_, v_init_441_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_447_, lean_object* v_00_u03b1_448_, lean_object* v_f_449_, lean_object* v_init_450_, lean_object* v_t_451_){
_start:
{
lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
v___f_452_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_452_, 0, v_f_449_);
v___x_453_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_454_, 0, v___x_453_);
lean_closure_set(v___f_454_, 1, v___f_452_);
v___x_455_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_453_, v___f_454_, v_t_451_, v_init_450_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_456_, lean_object* v_f_457_, lean_object* v_s_458_, lean_object* v_x_459_, lean_object* v_t_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_456_, v_f_457_, v_s_458_, v_t_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_462_, lean_object* v_f_463_, lean_object* v_s_464_, lean_object* v_x_465_, lean_object* v_t_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_462_, v_f_463_, v_s_464_, v_x_465_, v_t_466_);
lean_dec(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_468_, lean_object* v_f_469_, lean_object* v_init_470_, lean_object* v_t_471_){
_start:
{
lean_object* v___f_472_; lean_object* v___x_473_; 
lean_inc_ref(v_inst_468_);
v___f_472_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_472_, 0, v_inst_468_);
lean_closure_set(v___f_472_, 1, v_f_469_);
v___x_473_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_468_, v___f_472_, v_t_471_, v_init_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_474_, lean_object* v_00_u03c3_475_, lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_f_478_, lean_object* v_init_479_, lean_object* v_t_480_){
_start:
{
lean_object* v___f_481_; lean_object* v___x_482_; 
lean_inc_ref(v_inst_477_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_481_, 0, v_inst_477_);
lean_closure_set(v___f_481_, 1, v_f_478_);
v___x_482_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_477_, v___f_481_, v_t_480_, v_init_479_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_483_, lean_object* v___f_484_, lean_object* v_s_485_, lean_object* v_x_486_, lean_object* v_t_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_483_, v___f_484_, v_s_485_, v_t_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_489_, lean_object* v___f_490_, lean_object* v_s_491_, lean_object* v_x_492_, lean_object* v_t_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_489_, v___f_490_, v_s_491_, v_x_492_, v_t_493_);
lean_dec(v_x_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_495_, lean_object* v_init_496_, lean_object* v_t_497_){
_start:
{
lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; 
v___f_498_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_498_, 0, v_f_495_);
v___x_499_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_500_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_500_, 0, v___x_499_);
lean_closure_set(v___f_500_, 1, v___f_498_);
v___x_501_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_499_, v___f_500_, v_t_497_, v_init_496_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_502_, lean_object* v_00_u03b1_503_, lean_object* v_f_504_, lean_object* v_init_505_, lean_object* v_t_506_){
_start:
{
lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___f_509_; lean_object* v___x_510_; 
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_507_, 0, v_f_504_);
v___x_508_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_509_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_509_, 0, v___x_508_);
lean_closure_set(v___f_509_, 1, v___f_507_);
v___x_510_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_508_, v___f_509_, v_t_506_, v_init_505_);
return v___x_510_;
}
}
uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_511_, uint8_t v_x1_512_, lean_object* v_x2_513_){
_start:
{
if (v_x1_512_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_apply_1(v_f_511_, v_x2_513_);
v___x_515_ = lean_unbox(v___x_514_);
return v___x_515_;
}
else
{
lean_dec(v_x2_513_);
lean_dec_ref(v_f_511_);
return v_x1_512_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_511_ = stack[0].m_obj;
uint8_t v_x1_512_ = stack[1].m_num;
lean_object* v_x2_513_ = stack[2].m_obj;
uint8_t v_res_516_;
v_res_516_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_511_, v_x1_512_, v_x2_513_);
stack->m_num = v_res_516_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_517_, lean_object* v_x1_518_, lean_object* v_x2_519_){
_start:
{
uint8_t v_x1_83__boxed_520_; uint8_t v_res_521_; lean_object* v_r_522_; 
v_x1_83__boxed_520_ = lean_unbox(v_x1_518_);
v_res_521_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_517_, v_x1_83__boxed_520_, v_x2_519_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_523_, lean_object* v___f_524_, uint8_t v_s_525_, lean_object* v_x_526_, lean_object* v_t_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_box(v_s_525_);
v___x_529_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_523_, v___f_524_, v___x_528_, v_t_527_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_523_ = stack[0].m_obj;
lean_object* v___f_524_ = stack[1].m_obj;
uint8_t v_s_525_ = stack[2].m_num;
lean_object* v_x_526_ = stack[3].m_obj;
lean_object* v_t_527_ = stack[4].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_523_, v___f_524_, v_s_525_, v_x_526_, v_t_527_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_531_, lean_object* v___f_532_, lean_object* v_s_533_, lean_object* v_x_534_, lean_object* v_t_535_){
_start:
{
uint8_t v_s_boxed_536_; lean_object* v_res_537_; 
v_s_boxed_536_ = lean_unbox(v_s_533_);
v_res_537_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_531_, v___f_532_, v_s_boxed_536_, v_x_534_, v_t_535_);
lean_dec(v_x_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_538_, lean_object* v_f_539_){
_start:
{
lean_object* v___f_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_540_, 0, v_f_539_);
v___x_541_ = 0;
v___x_542_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_543_, 0, v___x_542_);
lean_closure_set(v___f_543_, 1, v___f_540_);
v___x_544_ = lean_box(v___x_541_);
v___x_545_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_542_, v___f_543_, v_t_538_, v___x_544_);
return v___x_545_;
}
}
uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_546_, lean_object* v_t_547_, lean_object* v_f_548_){
_start:
{
lean_object* v___f_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___f_549_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_549_, 0, v_f_548_);
v___x_550_ = 0;
v___x_551_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_552_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_552_, 0, v___x_551_);
lean_closure_set(v___f_552_, 1, v___f_549_);
v___x_553_ = lean_box(v___x_550_);
v___x_554_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_551_, v___f_552_, v_t_547_, v___x_553_);
v___x_555_ = lean_unbox(v___x_554_);
lean_dec(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT void l_Lean_Meta_DiscrTree_containsValueP_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_547_ = stack[1].m_obj;
lean_object* v_f_548_ = stack[2].m_obj;
uint8_t v_res_556_;
v_res_556_ = l_Lean_Meta_DiscrTree_containsValueP(lean_box(0), v_t_547_, v_f_548_);
stack->m_num = v_res_556_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_557_, lean_object* v_t_558_, lean_object* v_f_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_557_, v_t_558_, v_f_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_562_, lean_object* v_x2_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_push(v_x1_562_, v_x2_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_565_, lean_object* v___f_566_, lean_object* v_s_567_, lean_object* v_x_568_, lean_object* v_t_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_565_, v___f_566_, v_s_567_, v_t_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_571_, lean_object* v___f_572_, lean_object* v_s_573_, lean_object* v_x_574_, lean_object* v_t_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_571_, v___f_572_, v_s_573_, v_x_574_, v_t_575_);
lean_dec(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v___x_582_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_583_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_584_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_585_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_583_, v___f_584_, v_t_581_, v___x_582_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_586_, lean_object* v_t_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___f_590_; lean_object* v___x_591_; 
v___x_588_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_589_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_590_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_591_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_589_, v___f_590_, v_t_587_, v___x_588_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_592_, lean_object* v_keys_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_keys_593_);
lean_ctor_set(v___x_595_, 1, v_a_594_);
v___x_596_ = lean_array_push(v_s_592_, v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_597_, lean_object* v___f_598_, lean_object* v_s_599_, lean_object* v_k_600_, lean_object* v_t_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_array_push(v___x_603_, v_k_600_);
v___x_605_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_597_, v___x_604_, v___f_598_, v_s_599_, v_t_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___x_616_; 
v___x_613_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_614_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_615_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_616_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_614_, v___f_615_, v_t_612_, v___x_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_617_, lean_object* v_t_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; 
v___x_619_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_620_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_621_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_622_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_620_, v___f_621_, v_t_618_, v___x_619_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_623_, lean_object* v_x_624_, lean_object* v_t_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_625_);
v___x_627_ = lean_nat_add(v_n_623_, v___x_626_);
lean_dec(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_628_, lean_object* v_x_629_, lean_object* v_t_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_628_, v_x_629_, v_t_630_);
lean_dec_ref(v_t_630_);
lean_dec(v_x_629_);
lean_dec(v_n_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___f_634_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_633_, v___f_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_637_, lean_object* v_t_638_){
_start:
{
lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___f_639_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_638_, v___f_639_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_vs_644_, lean_object* v_toPure_645_, lean_object* v_key_646_, lean_object* v_c_647_){
_start:
{
lean_object* v___y_649_; 
if (lean_obj_tag(v_c_647_) == 0)
{
goto v___jp_671_;
}
else
{
lean_object* v_vs_676_; lean_object* v_children_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_vs_676_ = lean_ctor_get(v_c_647_, 0);
v_children_677_ = lean_ctor_get(v_c_647_, 1);
v___x_678_ = lean_array_get_size(v_vs_676_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_nat_dec_eq(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
goto v___jp_671_;
}
else
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_array_get_size(v_children_677_);
v___x_682_ = lean_nat_dec_eq(v___x_681_, v___x_679_);
if (v___x_682_ == 0)
{
goto v___jp_671_;
}
else
{
lean_object* v___x_683_; 
lean_dec_ref_known(v_c_647_, 2);
lean_dec(v_key_646_);
v___x_683_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0));
v___y_649_ = v___x_683_;
goto v___jp_648_;
}
}
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_array_get_size(v_vs_644_);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_nat_dec_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_653_, 0, v_vs_644_);
lean_ctor_set(v___x_653_, 1, v___y_649_);
v___x_654_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_653_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_array_get_size(v___y_649_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v_vs_644_);
lean_ctor_set(v___x_658_, 1, v___y_649_);
v___x_659_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_658_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v_fst_661_; lean_object* v_snd_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_vs_644_);
v___x_660_ = lean_array_fget(v___y_649_, v___x_651_);
lean_dec_ref(v___y_649_);
v_fst_661_ = lean_ctor_get(v___x_660_, 0);
v_snd_662_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snd_662_);
lean_inc(v_fst_661_);
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_662_);
v___x_667_ = v_reuseFailAlloc_669_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_apply_2(v_toPure_645_, lean_box(0), v___x_667_);
return v___x_668_;
}
}
}
}
}
v___jp_671_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_key_646_);
lean_ctor_set(v___x_672_, 1, v_c_647_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_mk_empty_array_with_capacity(v___x_673_);
v___x_675_ = lean_array_push(v___x_674_, v___x_672_);
v___y_649_ = v___x_675_;
goto v___jp_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object* v_vs_684_, lean_object* v_toPure_685_, lean_object* v_children_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_array_get_size(v_vs_684_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_690_, 0, v_vs_684_);
lean_ctor_set(v___x_690_, 1, v_children_686_);
v___x_691_ = lean_apply_2(v_toPure_685_, lean_box(0), v___x_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = lean_array_get_size(v_children_686_);
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v_vs_684_);
lean_ctor_set(v___x_695_, 1, v_children_686_);
v___x_696_ = lean_apply_2(v_toPure_685_, lean_box(0), v___x_695_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_vs_684_);
v___x_697_ = lean_array_fget(v_children_686_, v___x_688_);
lean_dec_ref(v_children_686_);
v_fst_698_ = lean_ctor_get(v___x_697_, 0);
v_snd_699_ = lean_ctor_get(v___x_697_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_inc(v_fst_698_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_fst_698_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_699_);
v___x_704_ = v_reuseFailAlloc_706_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; 
v___x_705_ = lean_apply_2(v_toPure_685_, lean_box(0), v___x_704_);
return v___x_705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object* v_toPure_708_, lean_object* v_children_709_, lean_object* v_inst_710_, lean_object* v___f_711_, lean_object* v_toBind_712_, lean_object* v_vs_713_){
_start:
{
lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___f_714_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_714_, 0, v_vs_713_);
lean_closure_set(v___f_714_, 1, v_toPure_708_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_children_709_);
v___x_717_ = l_Array_filterMapM___redArg(v_inst_710_, v___f_711_, v_children_709_, v___x_715_, v___x_716_);
v___x_718_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v___x_717_, v___f_714_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_fst_719_, lean_object* v_toPure_720_, lean_object* v_child_721_){
_start:
{
if (lean_obj_tag(v_child_721_) == 0)
{
goto v___jp_722_;
}
else
{
lean_object* v_vs_726_; lean_object* v_children_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_vs_726_ = lean_ctor_get(v_child_721_, 0);
v_children_727_ = lean_ctor_get(v_child_721_, 1);
v___x_728_ = lean_array_get_size(v_vs_726_);
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_nat_dec_eq(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
goto v___jp_722_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = lean_array_get_size(v_children_727_);
v___x_732_ = lean_nat_dec_eq(v___x_731_, v___x_729_);
if (v___x_732_ == 0)
{
goto v___jp_722_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec_ref_known(v_child_721_, 2);
lean_dec(v_fst_719_);
v___x_733_ = lean_box(0);
v___x_734_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_733_);
return v___x_734_;
}
}
}
v___jp_722_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_fst_719_);
lean_ctor_set(v___x_723_, 1, v_child_721_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_735_, lean_object* v_inst_736_, lean_object* v_f_737_, lean_object* v_toBind_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_fst_740_ = lean_ctor_get(v_x_739_, 0);
lean_inc(v_fst_740_);
v_snd_741_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_snd_741_);
lean_dec_ref(v_x_739_);
v___f_742_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_742_, 0, v_fst_740_);
lean_closure_set(v___f_742_, 1, v_toPure_735_);
v___x_743_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_736_, v_snd_741_, v_f_737_);
v___x_744_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v___x_743_, v___f_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_745_, lean_object* v_t_746_, lean_object* v_f_747_){
_start:
{
if (lean_obj_tag(v_t_746_) == 0)
{
lean_object* v_toApplicative_748_; lean_object* v_toBind_749_; lean_object* v_toPure_750_; lean_object* v_key_751_; lean_object* v_child_752_; lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_toApplicative_748_ = lean_ctor_get(v_inst_745_, 0);
v_toBind_749_ = lean_ctor_get(v_inst_745_, 1);
lean_inc_n(v_toBind_749_, 2);
v_toPure_750_ = lean_ctor_get(v_toApplicative_748_, 1);
lean_inc(v_toPure_750_);
v_key_751_ = lean_ctor_get(v_t_746_, 0);
lean_inc(v_key_751_);
v_child_752_ = lean_ctor_get(v_t_746_, 1);
lean_inc_ref(v_child_752_);
lean_dec_ref_known(v_t_746_, 2);
lean_inc(v_f_747_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_753_, 0, v_toPure_750_);
lean_closure_set(v___f_753_, 1, v_key_751_);
lean_closure_set(v___f_753_, 2, v_inst_745_);
lean_closure_set(v___f_753_, 3, v_child_752_);
lean_closure_set(v___f_753_, 4, v_f_747_);
lean_closure_set(v___f_753_, 5, v_toBind_749_);
v___x_754_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_755_ = lean_apply_1(v_f_747_, v___x_754_);
v___x_756_ = lean_apply_4(v_toBind_749_, lean_box(0), lean_box(0), v___x_755_, v___f_753_);
return v___x_756_;
}
else
{
lean_object* v_toApplicative_757_; lean_object* v_toBind_758_; lean_object* v_toPure_759_; lean_object* v_vs_760_; lean_object* v_children_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_toApplicative_757_ = lean_ctor_get(v_inst_745_, 0);
v_toBind_758_ = lean_ctor_get(v_inst_745_, 1);
lean_inc_n(v_toBind_758_, 3);
v_toPure_759_ = lean_ctor_get(v_toApplicative_757_, 1);
lean_inc_n(v_toPure_759_, 2);
v_vs_760_ = lean_ctor_get(v_t_746_, 0);
lean_inc_ref(v_vs_760_);
v_children_761_ = lean_ctor_get(v_t_746_, 1);
lean_inc_ref(v_children_761_);
lean_dec_ref_known(v_t_746_, 2);
lean_inc(v_f_747_);
lean_inc_ref(v_inst_745_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_762_, 0, v_toPure_759_);
lean_closure_set(v___f_762_, 1, v_inst_745_);
lean_closure_set(v___f_762_, 2, v_f_747_);
lean_closure_set(v___f_762_, 3, v_toBind_758_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_763_, 0, v_toPure_759_);
lean_closure_set(v___f_763_, 1, v_children_761_);
lean_closure_set(v___f_763_, 2, v_inst_745_);
lean_closure_set(v___f_763_, 3, v___f_762_);
lean_closure_set(v___f_763_, 4, v_toBind_758_);
v___x_764_ = lean_apply_1(v_f_747_, v_vs_760_);
v___x_765_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_764_, v___f_763_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_766_, lean_object* v_key_767_, lean_object* v_inst_768_, lean_object* v_child_769_, lean_object* v_f_770_, lean_object* v_toBind_771_, lean_object* v_vs_772_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_773_, 0, v_vs_772_);
lean_closure_set(v___f_773_, 1, v_toPure_766_);
lean_closure_set(v___f_773_, 2, v_key_767_);
v___x_774_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_768_, v_child_769_, v_f_770_);
v___x_775_ = lean_apply_4(v_toBind_771_, lean_box(0), lean_box(0), v___x_774_, v___f_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_776_, lean_object* v_inst_777_, lean_object* v_00_u03b1_778_, lean_object* v_00_u03b2_779_, lean_object* v_t_780_, lean_object* v_f_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_777_, v_t_780_, v_f_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_783_, lean_object* v_f_784_, lean_object* v_t_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_783_, v_t_785_, v_f_784_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_787_, lean_object* v___x_788_, lean_object* v_acc_789_, lean_object* v_k_790_, lean_object* v_t_791_){
_start:
{
if (lean_obj_tag(v_t_791_) == 0)
{
lean_dec(v_k_790_);
lean_dec_ref(v___x_788_);
lean_dec_ref(v___x_787_);
return v_acc_789_;
}
else
{
lean_object* v_vs_792_; lean_object* v_children_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_vs_792_ = lean_ctor_get(v_t_791_, 0);
v_children_793_ = lean_ctor_get(v_t_791_, 1);
v___x_794_ = lean_array_get_size(v_vs_792_);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_nat_dec_eq(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec(v_k_790_);
lean_dec_ref(v___x_788_);
lean_dec_ref(v___x_787_);
return v_acc_789_;
}
else
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = lean_array_get_size(v_children_793_);
v___x_798_ = lean_nat_dec_eq(v___x_797_, v___x_795_);
if (v___x_798_ == 0)
{
lean_dec(v_k_790_);
lean_dec_ref(v___x_788_);
lean_dec_ref(v___x_787_);
return v_acc_789_;
}
else
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_erase___redArg(v___x_787_, v___x_788_, v_acc_789_, v_k_790_);
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v_acc_802_, lean_object* v_k_803_, lean_object* v_t_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(v___x_800_, v___x_801_, v_acc_802_, v_k_803_, v_t_804_);
lean_dec_ref(v_t_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_806_, lean_object* v_toPure_807_, lean_object* v_root_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v_root_808_);
v___x_809_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_808_, v___f_806_, v_root_808_);
v___x_810_ = lean_apply_2(v_toPure_807_, lean_box(0), v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_816_, lean_object* v_d_817_, lean_object* v_f_818_){
_start:
{
lean_object* v_toApplicative_819_; lean_object* v_toBind_820_; lean_object* v_toPure_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_toApplicative_819_ = lean_ctor_get(v_inst_816_, 0);
v_toBind_820_ = lean_ctor_get(v_inst_816_, 1);
lean_inc(v_toBind_820_);
v_toPure_821_ = lean_ctor_get(v_toApplicative_819_, 1);
lean_inc_ref(v_inst_816_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_822_, 0, v_inst_816_);
lean_closure_set(v___f_822_, 1, v_f_818_);
v___f_823_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_821_);
v___f_824_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_824_, 0, v___f_823_);
lean_closure_set(v___f_824_, 1, v_toPure_821_);
v___x_825_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_816_, v_d_817_, v___f_822_);
v___x_826_ = lean_apply_4(v_toBind_820_, lean_box(0), lean_box(0), v___x_825_, v___f_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_827_, lean_object* v_inst_828_, lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_d_831_, lean_object* v_f_832_){
_start:
{
lean_object* v_toApplicative_833_; lean_object* v_toBind_834_; lean_object* v_toPure_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_toApplicative_833_ = lean_ctor_get(v_inst_828_, 0);
v_toBind_834_ = lean_ctor_get(v_inst_828_, 1);
lean_inc(v_toBind_834_);
v_toPure_835_ = lean_ctor_get(v_toApplicative_833_, 1);
lean_inc_ref(v_inst_828_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_836_, 0, v_inst_828_);
lean_closure_set(v___f_836_, 1, v_f_832_);
v___f_837_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_835_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_838_, 0, v___f_837_);
lean_closure_set(v___f_838_, 1, v_toPure_835_);
v___x_839_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_828_, v_d_831_, v___f_836_);
v___x_840_ = lean_apply_4(v_toBind_834_, lean_box(0), lean_box(0), v___x_839_, v___f_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_841_, lean_object* v_A_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_1(v_f_841_, v_A_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_844_, lean_object* v___f_845_, lean_object* v_t_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_844_, v_t_846_, v___f_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_848_, lean_object* v_f_849_){
_start:
{
lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___f_850_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_850_, 0, v_f_849_);
v___x_851_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_852_, 0, v___x_851_);
lean_closure_set(v___f_852_, 1, v___f_850_);
v___f_853_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_854_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_851_, v_d_848_, v___f_852_);
lean_inc(v___x_854_);
v___x_855_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_854_, v___f_853_, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_d_858_, lean_object* v_f_859_){
_start:
{
lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___f_860_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_860_, 0, v_f_859_);
v___x_861_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_862_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_862_, 0, v___x_861_);
lean_closure_set(v___f_862_, 1, v___f_860_);
v___f_863_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_864_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_861_, v_d_858_, v___f_862_);
lean_inc(v___x_864_);
v___x_865_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_864_, v___f_863_, v___x_864_);
return v___x_865_;
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
