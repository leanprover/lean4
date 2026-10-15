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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_198_, size_t v_i_199_, size_t v_stop_200_, lean_object* v_b_201_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_, lean_object* v_b_213_){
_start:
{
size_t v_i_boxed_214_; size_t v_stop_boxed_215_; lean_object* v_res_216_; 
v_i_boxed_214_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_215_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_210_, v_i_boxed_214_, v_stop_boxed_215_, v_b_213_);
lean_dec_ref(v_as_210_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_217_);
lean_dec_ref(v_x_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___boxed(lean_object* v_00_u03b1_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Meta_DiscrTree_Trie_size(v_00_u03b1_222_, v_x_223_);
lean_dec_ref(v_x_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_225_, lean_object* v_as_226_, size_t v_i_227_, size_t v_stop_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_226_, v_i_227_, v_stop_228_, v_b_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_231_, lean_object* v_as_232_, lean_object* v_i_233_, lean_object* v_stop_234_, lean_object* v_b_235_){
_start:
{
size_t v_i_boxed_236_; size_t v_stop_boxed_237_; lean_object* v_res_238_; 
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_stop_boxed_237_ = lean_unbox_usize(v_stop_234_);
lean_dec(v_stop_234_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_231_, v_as_232_, v_i_boxed_236_, v_stop_boxed_237_, v_b_235_);
lean_dec_ref(v_as_232_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode___redArg(lean_object* v_vs_239_, lean_object* v_cs_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_241_ = lean_array_get_size(v_vs_239_);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_nat_dec_eq(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v_vs_239_);
lean_ctor_set(v___x_244_, 1, v_cs_240_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_array_get_size(v_cs_240_);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_dec_eq(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v_vs_239_);
lean_ctor_set(v___x_248_, 1, v_cs_240_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v_vs_239_);
v___x_249_ = lean_array_fget(v_cs_240_, v___x_242_);
lean_dec_ref(v_cs_240_);
v_fst_250_ = lean_ctor_get(v___x_249_, 0);
v_snd_251_ = lean_ctor_get(v___x_249_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_249_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_snd_251_);
lean_inc(v_fst_250_);
lean_dec(v___x_249_);
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
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_fst_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_snd_251_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object* v_00_u03b1_259_, lean_object* v_vs_260_, lean_object* v_cs_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_array_get_size(v_vs_260_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_nat_dec_eq(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v_vs_260_);
lean_ctor_set(v___x_265_, 1, v_cs_261_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_266_ = lean_array_get_size(v_cs_261_);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v_vs_260_);
lean_ctor_set(v___x_269_, 1, v_cs_261_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v_vs_260_);
v___x_270_ = lean_array_fget(v_cs_261_, v___x_263_);
lean_dec_ref(v_cs_261_);
v_fst_271_ = lean_ctor_get(v___x_270_, 0);
v_snd_272_ = lean_ctor_get(v___x_270_, 1);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_270_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_snd_272_);
lean_inc(v_fst_271_);
lean_dec(v___x_270_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_fst_271_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_snd_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode___redArg(lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v_key_283_; lean_object* v_child_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_296_; 
v_key_283_ = lean_ctor_get(v_x_282_, 0);
v_child_284_ = lean_ctor_get(v_x_282_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_296_ == 0)
{
v___x_286_ = v_x_282_;
v_isShared_287_ = v_isSharedCheck_296_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_child_284_);
lean_inc(v_key_283_);
lean_dec(v_x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_296_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_287_ == 0)
{
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_key_283_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_child_284_);
v___x_290_ = v_reuseFailAlloc_295_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_mk_empty_array_with_capacity(v___x_291_);
v___x_293_ = lean_array_push(v___x_292_, v___x_290_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_288_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
return v___x_294_;
}
}
}
else
{
lean_object* v_vs_297_; lean_object* v_children_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v_vs_297_ = lean_ctor_get(v_x_282_, 0);
v_children_298_ = lean_ctor_get(v_x_282_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v_x_282_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_children_298_);
lean_inc(v_vs_297_);
lean_dec(v_x_282_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 0);
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_vs_297_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_children_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_asNode(lean_object* v_00_u03b1_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_key_308_; lean_object* v_child_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_321_; 
v_key_308_ = lean_ctor_get(v_x_307_, 0);
v_child_309_ = lean_ctor_get(v_x_307_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_321_ == 0)
{
v___x_311_ = v_x_307_;
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_child_309_);
lean_inc(v_key_308_);
lean_dec(v_x_307_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_321_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
if (v_isShared_312_ == 0)
{
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_key_308_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_child_309_);
v___x_315_ = v_reuseFailAlloc_320_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_mk_empty_array_with_capacity(v___x_316_);
v___x_318_ = lean_array_push(v___x_317_, v___x_315_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_313_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
}
}
else
{
lean_object* v_vs_322_; lean_object* v_children_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
v_vs_322_ = lean_ctor_get(v_x_307_, 0);
v_children_323_ = lean_ctor_get(v_x_307_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v_x_307_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_children_323_);
lean_inc(v_vs_322_);
lean_dec(v_x_307_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 0);
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_vs_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_children_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_332_;
}
else
{
lean_object* v_vs_333_; 
v_vs_333_ = lean_ctor_get(v_x_331_, 0);
lean_inc_ref(v_vs_333_);
return v_vs_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg___boxed(lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Meta_DiscrTree_Trie_nodeValues___redArg(v_x_334_);
lean_dec_ref(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues(lean_object* v_00_u03b1_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_338_; 
v___x_338_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
return v___x_338_;
}
else
{
lean_object* v_vs_339_; 
v_vs_339_ = lean_ctor_get(v_x_337_, 0);
lean_inc_ref(v_vs_339_);
return v_vs_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeValues___boxed(lean_object* v_00_u03b1_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_DiscrTree_Trie_nodeValues(v_00_u03b1_340_, v_x_341_);
lean_dec_ref(v_x_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren___redArg(lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v_key_344_; lean_object* v_child_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v_key_344_ = lean_ctor_get(v_x_343_, 0);
v_child_345_ = lean_ctor_get(v_x_343_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_343_);
if (v_isSharedCheck_355_ == 0)
{
v___x_347_ = v_x_343_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_child_345_);
lean_inc(v_key_344_);
lean_dec(v_x_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_key_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_child_345_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_mk_empty_array_with_capacity(v___x_351_);
v___x_353_ = lean_array_push(v___x_352_, v___x_350_);
return v___x_353_;
}
}
}
else
{
lean_object* v_children_356_; 
v_children_356_ = lean_ctor_get(v_x_343_, 1);
lean_inc_ref(v_children_356_);
lean_dec_ref_known(v_x_343_, 2);
return v_children_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_nodeChildren(lean_object* v_00_u03b1_357_, lean_object* v_x_358_){
_start:
{
if (lean_obj_tag(v_x_358_) == 0)
{
lean_object* v_key_359_; lean_object* v_child_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_370_; 
v_key_359_ = lean_ctor_get(v_x_358_, 0);
v_child_360_ = lean_ctor_get(v_x_358_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_358_);
if (v_isSharedCheck_370_ == 0)
{
v___x_362_ = v_x_358_;
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_child_360_);
lean_inc(v_key_359_);
lean_dec(v_x_358_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_key_359_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_child_360_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_mk_empty_array_with_capacity(v___x_366_);
v___x_368_ = lean_array_push(v___x_367_, v___x_365_);
return v___x_368_;
}
}
}
else
{
lean_object* v_children_371_; 
v_children_371_ = lean_ctor_get(v_x_358_, 1);
lean_inc_ref(v_children_371_);
lean_dec_ref_known(v_x_358_, 2);
return v_children_371_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
uint8_t v___x_373_; 
v___x_373_ = 0;
return v___x_373_;
}
else
{
lean_object* v_vs_374_; lean_object* v_children_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_vs_374_ = lean_ctor_get(v_x_372_, 0);
v_children_375_ = lean_ctor_get(v_x_372_, 1);
v___x_376_ = lean_array_get_size(v_vs_374_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_nat_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
return v___x_378_;
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_array_get_size(v_children_375_);
v___x_380_ = lean_nat_dec_eq(v___x_379_, v___x_377_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_x_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_381_);
lean_dec_ref(v_x_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
else
{
lean_object* v_vs_387_; lean_object* v_children_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_vs_387_ = lean_ctor_get(v_x_385_, 0);
v_children_388_ = lean_ctor_get(v_x_385_, 1);
v___x_389_ = lean_array_get_size(v_vs_387_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
return v___x_391_;
}
else
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_array_get_size(v_children_388_);
v___x_393_ = lean_nat_dec_eq(v___x_392_, v___x_390_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_394_, lean_object* v_x_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_394_, v_x_395_);
lean_dec_ref(v_x_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_398_, lean_object* v_f_399_, lean_object* v_s_400_, lean_object* v_k_401_, lean_object* v_t_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_mk_empty_array_with_capacity(v___x_403_);
v___x_405_ = lean_array_push(v___x_404_, v_k_401_);
v___x_406_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_398_, v___x_405_, v_f_399_, v_s_400_, v_t_402_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_407_, lean_object* v_f_408_, lean_object* v_init_409_, lean_object* v_t_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; 
lean_inc_ref(v_inst_407_);
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_411_, 0, v_inst_407_);
lean_closure_set(v___f_411_, 1, v_f_408_);
v___x_412_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_407_, v___f_411_, v_t_410_, v_init_409_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_413_, lean_object* v_00_u03c3_414_, lean_object* v_00_u03b1_415_, lean_object* v_inst_416_, lean_object* v_f_417_, lean_object* v_init_418_, lean_object* v_t_419_){
_start:
{
lean_object* v___f_420_; lean_object* v___x_421_; 
lean_inc_ref(v_inst_416_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_420_, 0, v_inst_416_);
lean_closure_set(v___f_420_, 1, v_f_417_);
v___x_421_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_416_, v___f_420_, v_t_419_, v_init_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_422_, lean_object* v_s_423_, lean_object* v_keys_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_apply_3(v_f_422_, v_s_423_, v_keys_424_, v_a_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_427_, lean_object* v___f_428_, lean_object* v_s_429_, lean_object* v_k_430_, lean_object* v_t_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_mk_empty_array_with_capacity(v___x_432_);
v___x_434_ = lean_array_push(v___x_433_, v_k_430_);
v___x_435_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_427_, v___x_434_, v___f_428_, v_s_429_, v_t_431_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_436_, lean_object* v_init_437_, lean_object* v_t_438_){
_start:
{
lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___f_441_; lean_object* v___x_442_; 
v___f_439_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_439_, 0, v_f_436_);
v___x_440_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_441_, 0, v___x_440_);
lean_closure_set(v___f_441_, 1, v___f_439_);
v___x_442_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_440_, v___f_441_, v_t_438_, v_init_437_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_443_, lean_object* v_00_u03b1_444_, lean_object* v_f_445_, lean_object* v_init_446_, lean_object* v_t_447_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___f_450_; lean_object* v___x_451_; 
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_448_, 0, v_f_445_);
v___x_449_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_450_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_450_, 0, v___x_449_);
lean_closure_set(v___f_450_, 1, v___f_448_);
v___x_451_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_449_, v___f_450_, v_t_447_, v_init_446_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_452_, lean_object* v_f_453_, lean_object* v_s_454_, lean_object* v_x_455_, lean_object* v_t_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_452_, v_f_453_, v_s_454_, v_t_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_458_, lean_object* v_f_459_, lean_object* v_s_460_, lean_object* v_x_461_, lean_object* v_t_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_458_, v_f_459_, v_s_460_, v_x_461_, v_t_462_);
lean_dec(v_x_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_464_, lean_object* v_f_465_, lean_object* v_init_466_, lean_object* v_t_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; 
lean_inc_ref(v_inst_464_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_468_, 0, v_inst_464_);
lean_closure_set(v___f_468_, 1, v_f_465_);
v___x_469_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_464_, v___f_468_, v_t_467_, v_init_466_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_470_, lean_object* v_00_u03c3_471_, lean_object* v_00_u03b1_472_, lean_object* v_inst_473_, lean_object* v_f_474_, lean_object* v_init_475_, lean_object* v_t_476_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_478_; 
lean_inc_ref(v_inst_473_);
v___f_477_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_477_, 0, v_inst_473_);
lean_closure_set(v___f_477_, 1, v_f_474_);
v___x_478_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_473_, v___f_477_, v_t_476_, v_init_475_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_479_, lean_object* v___f_480_, lean_object* v_s_481_, lean_object* v_x_482_, lean_object* v_t_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_479_, v___f_480_, v_s_481_, v_t_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_485_, lean_object* v___f_486_, lean_object* v_s_487_, lean_object* v_x_488_, lean_object* v_t_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_485_, v___f_486_, v_s_487_, v_x_488_, v_t_489_);
lean_dec(v_x_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_491_, lean_object* v_init_492_, lean_object* v_t_493_){
_start:
{
lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___f_496_; lean_object* v___x_497_; 
v___f_494_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_494_, 0, v_f_491_);
v___x_495_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_496_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_496_, 0, v___x_495_);
lean_closure_set(v___f_496_, 1, v___f_494_);
v___x_497_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_495_, v___f_496_, v_t_493_, v_init_492_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_498_, lean_object* v_00_u03b1_499_, lean_object* v_f_500_, lean_object* v_init_501_, lean_object* v_t_502_){
_start:
{
lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___f_505_; lean_object* v___x_506_; 
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_503_, 0, v_f_500_);
v___x_504_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_505_, 0, v___x_504_);
lean_closure_set(v___f_505_, 1, v___f_503_);
v___x_506_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_504_, v___f_505_, v_t_502_, v_init_501_);
return v___x_506_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_507_, uint8_t v_x1_508_, lean_object* v_x2_509_){
_start:
{
if (v_x1_508_ == 0)
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_apply_1(v_f_507_, v_x2_509_);
v___x_511_ = lean_unbox(v___x_510_);
return v___x_511_;
}
else
{
lean_dec(v_x2_509_);
lean_dec_ref(v_f_507_);
return v_x1_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_512_, lean_object* v_x1_513_, lean_object* v_x2_514_){
_start:
{
uint8_t v_x1_83__boxed_515_; uint8_t v_res_516_; lean_object* v_r_517_; 
v_x1_83__boxed_515_ = lean_unbox(v_x1_513_);
v_res_516_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_512_, v_x1_83__boxed_515_, v_x2_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_518_, lean_object* v___f_519_, uint8_t v_s_520_, lean_object* v_x_521_, lean_object* v_t_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(v_s_520_);
v___x_524_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_518_, v___f_519_, v___x_523_, v_t_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_525_, lean_object* v___f_526_, lean_object* v_s_527_, lean_object* v_x_528_, lean_object* v_t_529_){
_start:
{
uint8_t v_s_boxed_530_; lean_object* v_res_531_; 
v_s_boxed_530_ = lean_unbox(v_s_527_);
v_res_531_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_525_, v___f_526_, v_s_boxed_530_, v_x_528_, v_t_529_);
lean_dec(v_x_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_532_, lean_object* v_f_533_){
_start:
{
lean_object* v___f_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___f_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_534_, 0, v_f_533_);
v___x_535_ = 0;
v___x_536_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_537_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_537_, 0, v___x_536_);
lean_closure_set(v___f_537_, 1, v___f_534_);
v___x_538_ = lean_box(v___x_535_);
v___x_539_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_536_, v___f_537_, v_t_532_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_540_, lean_object* v_t_541_, lean_object* v_f_542_){
_start:
{
lean_object* v___f_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___f_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___f_543_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_543_, 0, v_f_542_);
v___x_544_ = 0;
v___x_545_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_546_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_546_, 0, v___x_545_);
lean_closure_set(v___f_546_, 1, v___f_543_);
v___x_547_ = lean_box(v___x_544_);
v___x_548_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_545_, v___f_546_, v_t_541_, v___x_547_);
v___x_549_ = lean_unbox(v___x_548_);
lean_dec(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_550_, lean_object* v_t_551_, lean_object* v_f_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_550_, v_t_551_, v_f_552_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_555_, lean_object* v_x2_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = lean_array_push(v_x1_555_, v_x2_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_558_, lean_object* v___f_559_, lean_object* v_s_560_, lean_object* v_x_561_, lean_object* v_t_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_558_, v___f_559_, v_s_560_, v_t_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_564_, lean_object* v___f_565_, lean_object* v_s_566_, lean_object* v_x_567_, lean_object* v_t_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_564_, v___f_565_, v_s_566_, v_x_567_, v_t_568_);
lean_dec(v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; 
v___x_575_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_576_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_577_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_578_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_576_, v___f_577_, v_t_574_, v___x_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_579_, lean_object* v_t_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
v___x_581_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_582_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_583_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_584_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_582_, v___f_583_, v_t_580_, v___x_581_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_585_, lean_object* v_keys_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_keys_586_);
lean_ctor_set(v___x_588_, 1, v_a_587_);
v___x_589_ = lean_array_push(v_s_585_, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_590_, lean_object* v___f_591_, lean_object* v_s_592_, lean_object* v_k_593_, lean_object* v_t_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_mk_empty_array_with_capacity(v___x_595_);
v___x_597_ = lean_array_push(v___x_596_, v_k_593_);
v___x_598_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_590_, v___x_597_, v___f_591_, v_s_592_, v_t_594_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___f_608_; lean_object* v___x_609_; 
v___x_606_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_607_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_608_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_609_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_607_, v___f_608_, v_t_605_, v___x_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_610_, lean_object* v_t_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
v___x_612_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_613_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_614_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_615_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_613_, v___f_614_, v_t_611_, v___x_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_616_, lean_object* v_x_617_, lean_object* v_t_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_618_);
v___x_620_ = lean_nat_add(v_n_616_, v___x_619_);
lean_dec(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_621_, lean_object* v_x_622_, lean_object* v_t_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_621_, v_x_622_, v_t_623_);
lean_dec_ref(v_t_623_);
lean_dec(v_x_622_);
lean_dec(v_n_621_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_626_){
_start:
{
lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___f_627_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_626_, v___f_627_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_630_, lean_object* v_t_631_){
_start:
{
lean_object* v___f_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___f_632_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_631_, v___f_632_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_vs_637_, lean_object* v_toPure_638_, lean_object* v_key_639_, lean_object* v_c_640_){
_start:
{
lean_object* v___y_642_; 
if (lean_obj_tag(v_c_640_) == 0)
{
goto v___jp_664_;
}
else
{
lean_object* v_vs_669_; lean_object* v_children_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_vs_669_ = lean_ctor_get(v_c_640_, 0);
v_children_670_ = lean_ctor_get(v_c_640_, 1);
v___x_671_ = lean_array_get_size(v_vs_669_);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_nat_dec_eq(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
goto v___jp_664_;
}
else
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_array_get_size(v_children_670_);
v___x_675_ = lean_nat_dec_eq(v___x_674_, v___x_672_);
if (v___x_675_ == 0)
{
goto v___jp_664_;
}
else
{
lean_object* v___x_676_; 
lean_dec_ref_known(v_c_640_, 2);
lean_dec(v_key_639_);
v___x_676_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0));
v___y_642_ = v___x_676_;
goto v___jp_641_;
}
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_array_get_size(v_vs_637_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_nat_dec_eq(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_646_, 0, v_vs_637_);
lean_ctor_set(v___x_646_, 1, v___y_642_);
v___x_647_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_646_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_648_ = lean_array_get_size(v___y_642_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_dec_eq(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v_vs_637_);
lean_ctor_set(v___x_651_, 1, v___y_642_);
v___x_652_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_651_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_vs_637_);
v___x_653_ = lean_array_fget(v___y_642_, v___x_644_);
lean_dec_ref(v___y_642_);
v_fst_654_ = lean_ctor_get(v___x_653_, 0);
v_snd_655_ = lean_ctor_get(v___x_653_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_653_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_inc(v_fst_654_);
lean_dec(v___x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_fst_654_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_snd_655_);
v___x_660_ = v_reuseFailAlloc_662_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; 
v___x_661_ = lean_apply_2(v_toPure_638_, lean_box(0), v___x_660_);
return v___x_661_;
}
}
}
}
}
v___jp_664_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_key_639_);
lean_ctor_set(v___x_665_, 1, v_c_640_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_array_push(v___x_667_, v___x_665_);
v___y_642_ = v___x_668_;
goto v___jp_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object* v_vs_677_, lean_object* v_toPure_678_, lean_object* v_children_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_680_ = lean_array_get_size(v_vs_677_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_nat_dec_eq(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_683_, 0, v_vs_677_);
lean_ctor_set(v___x_683_, 1, v_children_679_);
v___x_684_ = lean_apply_2(v_toPure_678_, lean_box(0), v___x_683_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_array_get_size(v_children_679_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_dec_eq(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v_vs_677_);
lean_ctor_set(v___x_688_, 1, v_children_679_);
v___x_689_ = lean_apply_2(v_toPure_678_, lean_box(0), v___x_688_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_vs_677_);
v___x_690_ = lean_array_fget(v_children_679_, v___x_681_);
lean_dec_ref(v_children_679_);
v_fst_691_ = lean_ctor_get(v___x_690_, 0);
v_snd_692_ = lean_ctor_get(v___x_690_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v___x_690_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snd_692_);
lean_inc(v_fst_691_);
lean_dec(v___x_690_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_fst_691_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_snd_692_);
v___x_697_ = v_reuseFailAlloc_699_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_698_; 
v___x_698_ = lean_apply_2(v_toPure_678_, lean_box(0), v___x_697_);
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object* v_toPure_701_, lean_object* v_children_702_, lean_object* v_inst_703_, lean_object* v___f_704_, lean_object* v_toBind_705_, lean_object* v_vs_706_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___f_707_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_707_, 0, v_vs_706_);
lean_closure_set(v___f_707_, 1, v_toPure_701_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_array_get_size(v_children_702_);
v___x_710_ = l_Array_filterMapM___redArg(v_inst_703_, v___f_704_, v_children_702_, v___x_708_, v___x_709_);
v___x_711_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_710_, v___f_707_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_fst_712_, lean_object* v_toPure_713_, lean_object* v_child_714_){
_start:
{
if (lean_obj_tag(v_child_714_) == 0)
{
goto v___jp_715_;
}
else
{
lean_object* v_vs_719_; lean_object* v_children_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_vs_719_ = lean_ctor_get(v_child_714_, 0);
v_children_720_ = lean_ctor_get(v_child_714_, 1);
v___x_721_ = lean_array_get_size(v_vs_719_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
goto v___jp_715_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_array_get_size(v_children_720_);
v___x_725_ = lean_nat_dec_eq(v___x_724_, v___x_722_);
if (v___x_725_ == 0)
{
goto v___jp_715_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref_known(v_child_714_, 2);
lean_dec(v_fst_712_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_apply_2(v_toPure_713_, lean_box(0), v___x_726_);
return v___x_727_;
}
}
}
v___jp_715_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v_fst_712_);
lean_ctor_set(v___x_716_, 1, v_child_714_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = lean_apply_2(v_toPure_713_, lean_box(0), v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_728_, lean_object* v_inst_729_, lean_object* v_f_730_, lean_object* v_toBind_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_fst_733_ = lean_ctor_get(v_x_732_, 0);
lean_inc(v_fst_733_);
v_snd_734_ = lean_ctor_get(v_x_732_, 1);
lean_inc(v_snd_734_);
lean_dec_ref(v_x_732_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_735_, 0, v_fst_733_);
lean_closure_set(v___f_735_, 1, v_toPure_728_);
v___x_736_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_729_, v_snd_734_, v_f_730_);
v___x_737_ = lean_apply_4(v_toBind_731_, lean_box(0), lean_box(0), v___x_736_, v___f_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_738_, lean_object* v_t_739_, lean_object* v_f_740_){
_start:
{
if (lean_obj_tag(v_t_739_) == 0)
{
lean_object* v_toApplicative_741_; lean_object* v_toBind_742_; lean_object* v_toPure_743_; lean_object* v_key_744_; lean_object* v_child_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_toApplicative_741_ = lean_ctor_get(v_inst_738_, 0);
v_toBind_742_ = lean_ctor_get(v_inst_738_, 1);
lean_inc_n(v_toBind_742_, 2);
v_toPure_743_ = lean_ctor_get(v_toApplicative_741_, 1);
lean_inc(v_toPure_743_);
v_key_744_ = lean_ctor_get(v_t_739_, 0);
lean_inc(v_key_744_);
v_child_745_ = lean_ctor_get(v_t_739_, 1);
lean_inc_ref(v_child_745_);
lean_dec_ref_known(v_t_739_, 2);
lean_inc(v_f_740_);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_746_, 0, v_toPure_743_);
lean_closure_set(v___f_746_, 1, v_key_744_);
lean_closure_set(v___f_746_, 2, v_inst_738_);
lean_closure_set(v___f_746_, 3, v_child_745_);
lean_closure_set(v___f_746_, 4, v_f_740_);
lean_closure_set(v___f_746_, 5, v_toBind_742_);
v___x_747_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_748_ = lean_apply_1(v_f_740_, v___x_747_);
v___x_749_ = lean_apply_4(v_toBind_742_, lean_box(0), lean_box(0), v___x_748_, v___f_746_);
return v___x_749_;
}
else
{
lean_object* v_toApplicative_750_; lean_object* v_toBind_751_; lean_object* v_toPure_752_; lean_object* v_vs_753_; lean_object* v_children_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_toApplicative_750_ = lean_ctor_get(v_inst_738_, 0);
v_toBind_751_ = lean_ctor_get(v_inst_738_, 1);
lean_inc_n(v_toBind_751_, 3);
v_toPure_752_ = lean_ctor_get(v_toApplicative_750_, 1);
lean_inc_n(v_toPure_752_, 2);
v_vs_753_ = lean_ctor_get(v_t_739_, 0);
lean_inc_ref(v_vs_753_);
v_children_754_ = lean_ctor_get(v_t_739_, 1);
lean_inc_ref(v_children_754_);
lean_dec_ref_known(v_t_739_, 2);
lean_inc(v_f_740_);
lean_inc_ref(v_inst_738_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_755_, 0, v_toPure_752_);
lean_closure_set(v___f_755_, 1, v_inst_738_);
lean_closure_set(v___f_755_, 2, v_f_740_);
lean_closure_set(v___f_755_, 3, v_toBind_751_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_756_, 0, v_toPure_752_);
lean_closure_set(v___f_756_, 1, v_children_754_);
lean_closure_set(v___f_756_, 2, v_inst_738_);
lean_closure_set(v___f_756_, 3, v___f_755_);
lean_closure_set(v___f_756_, 4, v_toBind_751_);
v___x_757_ = lean_apply_1(v_f_740_, v_vs_753_);
v___x_758_ = lean_apply_4(v_toBind_751_, lean_box(0), lean_box(0), v___x_757_, v___f_756_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_759_, lean_object* v_key_760_, lean_object* v_inst_761_, lean_object* v_child_762_, lean_object* v_f_763_, lean_object* v_toBind_764_, lean_object* v_vs_765_){
_start:
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_766_, 0, v_vs_765_);
lean_closure_set(v___f_766_, 1, v_toPure_759_);
lean_closure_set(v___f_766_, 2, v_key_760_);
v___x_767_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_761_, v_child_762_, v_f_763_);
v___x_768_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_767_, v___f_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_769_, lean_object* v_inst_770_, lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_t_773_, lean_object* v_f_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_770_, v_t_773_, v_f_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_776_, lean_object* v_f_777_, lean_object* v_t_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_776_, v_t_778_, v_f_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v_acc_782_, lean_object* v_k_783_, lean_object* v_t_784_){
_start:
{
if (lean_obj_tag(v_t_784_) == 0)
{
lean_dec(v_k_783_);
lean_dec_ref(v___x_781_);
lean_dec_ref(v___x_780_);
return v_acc_782_;
}
else
{
lean_object* v_vs_785_; lean_object* v_children_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_vs_785_ = lean_ctor_get(v_t_784_, 0);
v_children_786_ = lean_ctor_get(v_t_784_, 1);
v___x_787_ = lean_array_get_size(v_vs_785_);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_nat_dec_eq(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_k_783_);
lean_dec_ref(v___x_781_);
lean_dec_ref(v___x_780_);
return v_acc_782_;
}
else
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = lean_array_get_size(v_children_786_);
v___x_791_ = lean_nat_dec_eq(v___x_790_, v___x_788_);
if (v___x_791_ == 0)
{
lean_dec(v_k_783_);
lean_dec_ref(v___x_781_);
lean_dec_ref(v___x_780_);
return v_acc_782_;
}
else
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_erase___redArg(v___x_780_, v___x_781_, v_acc_782_, v_k_783_);
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object* v___x_793_, lean_object* v___x_794_, lean_object* v_acc_795_, lean_object* v_k_796_, lean_object* v_t_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(v___x_793_, v___x_794_, v_acc_795_, v_k_796_, v_t_797_);
lean_dec_ref(v_t_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_799_, lean_object* v_toPure_800_, lean_object* v_root_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc_ref(v_root_801_);
v___x_802_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_801_, v___f_799_, v_root_801_);
v___x_803_ = lean_apply_2(v_toPure_800_, lean_box(0), v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_809_, lean_object* v_d_810_, lean_object* v_f_811_){
_start:
{
lean_object* v_toApplicative_812_; lean_object* v_toBind_813_; lean_object* v_toPure_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_toApplicative_812_ = lean_ctor_get(v_inst_809_, 0);
v_toBind_813_ = lean_ctor_get(v_inst_809_, 1);
lean_inc(v_toBind_813_);
v_toPure_814_ = lean_ctor_get(v_toApplicative_812_, 1);
lean_inc_ref(v_inst_809_);
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_815_, 0, v_inst_809_);
lean_closure_set(v___f_815_, 1, v_f_811_);
v___f_816_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_814_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_817_, 0, v___f_816_);
lean_closure_set(v___f_817_, 1, v_toPure_814_);
v___x_818_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_809_, v_d_810_, v___f_815_);
v___x_819_ = lean_apply_4(v_toBind_813_, lean_box(0), lean_box(0), v___x_818_, v___f_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_820_, lean_object* v_inst_821_, lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_d_824_, lean_object* v_f_825_){
_start:
{
lean_object* v_toApplicative_826_; lean_object* v_toBind_827_; lean_object* v_toPure_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_toApplicative_826_ = lean_ctor_get(v_inst_821_, 0);
v_toBind_827_ = lean_ctor_get(v_inst_821_, 1);
lean_inc(v_toBind_827_);
v_toPure_828_ = lean_ctor_get(v_toApplicative_826_, 1);
lean_inc_ref(v_inst_821_);
v___f_829_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_829_, 0, v_inst_821_);
lean_closure_set(v___f_829_, 1, v_f_825_);
v___f_830_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_828_);
v___f_831_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_831_, 0, v___f_830_);
lean_closure_set(v___f_831_, 1, v_toPure_828_);
v___x_832_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_821_, v_d_824_, v___f_829_);
v___x_833_ = lean_apply_4(v_toBind_827_, lean_box(0), lean_box(0), v___x_832_, v___f_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_834_, lean_object* v_A_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_1(v_f_834_, v_A_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_837_, lean_object* v___f_838_, lean_object* v_t_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_837_, v_t_839_, v___f_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_841_, lean_object* v_f_842_){
_start:
{
lean_object* v___f_843_; lean_object* v___x_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___f_843_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_843_, 0, v_f_842_);
v___x_844_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_845_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_845_, 0, v___x_844_);
lean_closure_set(v___f_845_, 1, v___f_843_);
v___f_846_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_847_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_844_, v_d_841_, v___f_845_);
lean_inc(v___x_847_);
v___x_848_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_847_, v___f_846_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_d_851_, lean_object* v_f_852_){
_start:
{
lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_853_, 0, v_f_852_);
v___x_854_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_855_, 0, v___x_854_);
lean_closure_set(v___f_855_, 1, v___f_853_);
v___f_856_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_857_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_854_, v_d_851_, v___f_855_);
lean_inc(v___x_857_);
v___x_858_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_857_, v___f_856_, v___x_857_);
return v___x_858_;
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
