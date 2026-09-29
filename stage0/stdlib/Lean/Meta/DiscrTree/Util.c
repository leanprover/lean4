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
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___y_244_; uint8_t v___x_256_; 
v___x_241_ = lean_array_get_size(v_vs_239_);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_nat_dec_eq(v___x_241_, v___x_242_);
if (v___x_256_ == 0)
{
v___y_244_ = v___x_256_;
goto v___jp_243_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = lean_array_get_size(v_cs_240_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_dec_eq(v___x_257_, v___x_258_);
v___y_244_ = v___x_259_;
goto v___jp_243_;
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v_vs_239_);
lean_ctor_set(v___x_245_, 1, v_cs_240_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v_vs_239_);
v___x_246_ = lean_array_fget(v_cs_240_, v___x_242_);
lean_dec_ref(v_cs_240_);
v_fst_247_ = lean_ctor_get(v___x_246_, 0);
v_snd_248_ = lean_ctor_get(v___x_246_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_246_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_snd_248_);
lean_inc(v_fst_247_);
lean_dec(v___x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_fst_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_snd_248_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mkNode(lean_object* v_00_u03b1_260_, lean_object* v_vs_261_, lean_object* v_cs_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___y_266_; uint8_t v___x_278_; 
v___x_263_ = lean_array_get_size(v_vs_261_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_nat_dec_eq(v___x_263_, v___x_264_);
if (v___x_278_ == 0)
{
v___y_266_ = v___x_278_;
goto v___jp_265_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = lean_array_get_size(v_cs_262_);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_dec_eq(v___x_279_, v___x_280_);
v___y_266_ = v___x_281_;
goto v___jp_265_;
}
v___jp_265_:
{
if (v___y_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_267_, 0, v_vs_261_);
lean_ctor_set(v___x_267_, 1, v_cs_262_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_vs_261_);
v___x_268_ = lean_array_fget(v_cs_262_, v___x_264_);
lean_dec_ref(v_cs_262_);
v_fst_269_ = lean_ctor_get(v___x_268_, 0);
v_snd_270_ = lean_ctor_get(v___x_268_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_268_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_snd_270_);
lean_inc(v_fst_269_);
lean_dec(v___x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_fst_269_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_snd_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
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
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_x_374_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_x_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_383_);
lean_dec_ref(v_x_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
else
{
lean_object* v_vs_389_; lean_object* v_children_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_vs_389_ = lean_ctor_get(v_x_387_, 0);
v_children_390_ = lean_ctor_get(v_x_387_, 1);
v___x_391_ = lean_array_get_size(v_vs_389_);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_nat_dec_eq(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
return v___x_393_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_children_390_);
v___x_395_ = lean_nat_dec_eq(v___x_394_, v___x_392_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_396_, lean_object* v_x_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_396_, v_x_397_);
lean_dec_ref(v_x_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_400_, lean_object* v_f_401_, lean_object* v_s_402_, lean_object* v_k_403_, lean_object* v_t_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_mk_empty_array_with_capacity(v___x_405_);
v___x_407_ = lean_array_push(v___x_406_, v_k_403_);
v___x_408_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_400_, v___x_407_, v_f_401_, v_s_402_, v_t_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_409_, lean_object* v_f_410_, lean_object* v_init_411_, lean_object* v_t_412_){
_start:
{
lean_object* v___f_413_; lean_object* v___x_414_; 
lean_inc_ref(v_inst_409_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_413_, 0, v_inst_409_);
lean_closure_set(v___f_413_, 1, v_f_410_);
v___x_414_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_409_, v___f_413_, v_t_412_, v_init_411_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_415_, lean_object* v_00_u03c3_416_, lean_object* v_00_u03b1_417_, lean_object* v_inst_418_, lean_object* v_f_419_, lean_object* v_init_420_, lean_object* v_t_421_){
_start:
{
lean_object* v___f_422_; lean_object* v___x_423_; 
lean_inc_ref(v_inst_418_);
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_422_, 0, v_inst_418_);
lean_closure_set(v___f_422_, 1, v_f_419_);
v___x_423_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_418_, v___f_422_, v_t_421_, v_init_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_424_, lean_object* v_s_425_, lean_object* v_keys_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_apply_3(v_f_424_, v_s_425_, v_keys_426_, v_a_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_429_, lean_object* v___f_430_, lean_object* v_s_431_, lean_object* v_k_432_, lean_object* v_t_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v___x_436_ = lean_array_push(v___x_435_, v_k_432_);
v___x_437_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_429_, v___x_436_, v___f_430_, v_s_431_, v_t_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_438_, lean_object* v_init_439_, lean_object* v_t_440_){
_start:
{
lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___f_443_; lean_object* v___x_444_; 
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_441_, 0, v_f_438_);
v___x_442_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_443_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_443_, 0, v___x_442_);
lean_closure_set(v___f_443_, 1, v___f_441_);
v___x_444_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_442_, v___f_443_, v_t_440_, v_init_439_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_445_, lean_object* v_00_u03b1_446_, lean_object* v_f_447_, lean_object* v_init_448_, lean_object* v_t_449_){
_start:
{
lean_object* v___f_450_; lean_object* v___x_451_; lean_object* v___f_452_; lean_object* v___x_453_; 
v___f_450_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_450_, 0, v_f_447_);
v___x_451_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_452_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_452_, 0, v___x_451_);
lean_closure_set(v___f_452_, 1, v___f_450_);
v___x_453_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_451_, v___f_452_, v_t_449_, v_init_448_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_454_, lean_object* v_f_455_, lean_object* v_s_456_, lean_object* v_x_457_, lean_object* v_t_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_454_, v_f_455_, v_s_456_, v_t_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_460_, lean_object* v_f_461_, lean_object* v_s_462_, lean_object* v_x_463_, lean_object* v_t_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_460_, v_f_461_, v_s_462_, v_x_463_, v_t_464_);
lean_dec(v_x_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_466_, lean_object* v_f_467_, lean_object* v_init_468_, lean_object* v_t_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; 
lean_inc_ref(v_inst_466_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_470_, 0, v_inst_466_);
lean_closure_set(v___f_470_, 1, v_f_467_);
v___x_471_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_466_, v___f_470_, v_t_469_, v_init_468_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_472_, lean_object* v_00_u03c3_473_, lean_object* v_00_u03b1_474_, lean_object* v_inst_475_, lean_object* v_f_476_, lean_object* v_init_477_, lean_object* v_t_478_){
_start:
{
lean_object* v___f_479_; lean_object* v___x_480_; 
lean_inc_ref(v_inst_475_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_479_, 0, v_inst_475_);
lean_closure_set(v___f_479_, 1, v_f_476_);
v___x_480_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_475_, v___f_479_, v_t_478_, v_init_477_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_481_, lean_object* v___f_482_, lean_object* v_s_483_, lean_object* v_x_484_, lean_object* v_t_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_481_, v___f_482_, v_s_483_, v_t_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_487_, lean_object* v___f_488_, lean_object* v_s_489_, lean_object* v_x_490_, lean_object* v_t_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_487_, v___f_488_, v_s_489_, v_x_490_, v_t_491_);
lean_dec(v_x_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_493_, lean_object* v_init_494_, lean_object* v_t_495_){
_start:
{
lean_object* v___f_496_; lean_object* v___x_497_; lean_object* v___f_498_; lean_object* v___x_499_; 
v___f_496_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_496_, 0, v_f_493_);
v___x_497_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_498_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_498_, 0, v___x_497_);
lean_closure_set(v___f_498_, 1, v___f_496_);
v___x_499_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_497_, v___f_498_, v_t_495_, v_init_494_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_500_, lean_object* v_00_u03b1_501_, lean_object* v_f_502_, lean_object* v_init_503_, lean_object* v_t_504_){
_start:
{
lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; 
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_505_, 0, v_f_502_);
v___x_506_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_507_, 0, v___x_506_);
lean_closure_set(v___f_507_, 1, v___f_505_);
v___x_508_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_506_, v___f_507_, v_t_504_, v_init_503_);
return v___x_508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_509_, uint8_t v_x1_510_, lean_object* v_x2_511_){
_start:
{
if (v_x1_510_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_apply_1(v_f_509_, v_x2_511_);
v___x_513_ = lean_unbox(v___x_512_);
return v___x_513_;
}
else
{
lean_dec(v_x2_511_);
lean_dec_ref(v_f_509_);
return v_x1_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_514_, lean_object* v_x1_515_, lean_object* v_x2_516_){
_start:
{
uint8_t v_x1_83__boxed_517_; uint8_t v_res_518_; lean_object* v_r_519_; 
v_x1_83__boxed_517_ = lean_unbox(v_x1_515_);
v_res_518_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_514_, v_x1_83__boxed_517_, v_x2_516_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_520_, lean_object* v___f_521_, uint8_t v_s_522_, lean_object* v_x_523_, lean_object* v_t_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_box(v_s_522_);
v___x_526_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_520_, v___f_521_, v___x_525_, v_t_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_527_, lean_object* v___f_528_, lean_object* v_s_529_, lean_object* v_x_530_, lean_object* v_t_531_){
_start:
{
uint8_t v_s_boxed_532_; lean_object* v_res_533_; 
v_s_boxed_532_ = lean_unbox(v_s_529_);
v_res_533_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_527_, v___f_528_, v_s_boxed_532_, v_x_530_, v_t_531_);
lean_dec(v_x_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_534_, lean_object* v_f_535_){
_start:
{
lean_object* v___f_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___f_536_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_536_, 0, v_f_535_);
v___x_537_ = 0;
v___x_538_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_539_, 0, v___x_538_);
lean_closure_set(v___f_539_, 1, v___f_536_);
v___x_540_ = lean_box(v___x_537_);
v___x_541_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_538_, v___f_539_, v_t_534_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_542_, lean_object* v_t_543_, lean_object* v_f_544_){
_start:
{
lean_object* v___f_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___f_545_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_545_, 0, v_f_544_);
v___x_546_ = 0;
v___x_547_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_548_, 0, v___x_547_);
lean_closure_set(v___f_548_, 1, v___f_545_);
v___x_549_ = lean_box(v___x_546_);
v___x_550_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_547_, v___f_548_, v_t_543_, v___x_549_);
v___x_551_ = lean_unbox(v___x_550_);
lean_dec(v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_552_, lean_object* v_t_553_, lean_object* v_f_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_552_, v_t_553_, v_f_554_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_557_, lean_object* v_x2_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_array_push(v_x1_557_, v_x2_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_560_, lean_object* v___f_561_, lean_object* v_s_562_, lean_object* v_x_563_, lean_object* v_t_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_560_, v___f_561_, v_s_562_, v_t_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_566_, lean_object* v___f_567_, lean_object* v_s_568_, lean_object* v_x_569_, lean_object* v_t_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_566_, v___f_567_, v_s_568_, v_x_569_, v_t_570_);
lean_dec(v_x_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v___x_577_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_578_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_579_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_580_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_578_, v___f_579_, v_t_576_, v___x_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_581_, lean_object* v_t_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v___x_583_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_584_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_585_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_586_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_584_, v___f_585_, v_t_582_, v___x_583_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_587_, lean_object* v_keys_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_keys_588_);
lean_ctor_set(v___x_590_, 1, v_a_589_);
v___x_591_ = lean_array_push(v_s_587_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_592_, lean_object* v___f_593_, lean_object* v_s_594_, lean_object* v_k_595_, lean_object* v_t_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
v___x_599_ = lean_array_push(v___x_598_, v_k_595_);
v___x_600_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_592_, v___x_599_, v___f_593_, v_s_594_, v_t_596_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___f_610_; lean_object* v___x_611_; 
v___x_608_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_609_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_610_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_611_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_609_, v___f_610_, v_t_607_, v___x_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_612_, lean_object* v_t_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v___x_614_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_615_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_616_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_617_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_615_, v___f_616_, v_t_613_, v___x_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_618_, lean_object* v_x_619_, lean_object* v_t_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_620_);
v___x_622_ = lean_nat_add(v_n_618_, v___x_621_);
lean_dec(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_623_, lean_object* v_x_624_, lean_object* v_t_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_623_, v_x_624_, v_t_625_);
lean_dec_ref(v_t_625_);
lean_dec(v_x_624_);
lean_dec(v_n_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_628_){
_start:
{
lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___f_629_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_628_, v___f_629_, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_632_, lean_object* v_t_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___f_634_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_633_, v___f_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_vs_639_, lean_object* v_toPure_640_, lean_object* v_key_641_, lean_object* v_c_642_){
_start:
{
lean_object* v___y_644_; lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_661_; 
if (lean_obj_tag(v_c_642_) == 0)
{
goto v___jp_668_;
}
else
{
lean_object* v_vs_673_; lean_object* v_children_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_vs_673_ = lean_ctor_get(v_c_642_, 0);
v_children_674_ = lean_ctor_get(v_c_642_, 1);
v___x_675_ = lean_array_get_size(v_vs_673_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_nat_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
goto v___jp_668_;
}
else
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = lean_array_get_size(v_children_674_);
v___x_679_ = lean_nat_dec_eq(v___x_678_, v___x_676_);
if (v___x_679_ == 0)
{
goto v___jp_668_;
}
else
{
lean_object* v___x_680_; 
lean_dec_ref_known(v_c_642_, 2);
lean_dec(v_key_641_);
v___x_680_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0___closed__0));
v___y_661_ = v___x_680_;
goto v___jp_660_;
}
}
}
v___jp_643_:
{
if (v___y_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_647_, 0, v_vs_639_);
lean_ctor_set(v___x_647_, 1, v___y_644_);
v___x_648_ = lean_apply_2(v_toPure_640_, lean_box(0), v___x_647_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_vs_639_);
v___x_649_ = lean_array_fget(v___y_644_, v___y_645_);
lean_dec_ref(v___y_644_);
v_fst_650_ = lean_ctor_get(v___x_649_, 0);
v_snd_651_ = lean_ctor_get(v___x_649_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_snd_651_);
lean_inc(v_fst_650_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_snd_651_);
v___x_656_ = v_reuseFailAlloc_658_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_apply_2(v_toPure_640_, lean_box(0), v___x_656_);
return v___x_657_;
}
}
}
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_array_get_size(v_vs_639_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_eq(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
v___y_644_ = v___y_661_;
v___y_645_ = v___x_663_;
v___y_646_ = v___x_664_;
goto v___jp_643_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_array_get_size(v___y_661_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_dec_eq(v___x_665_, v___x_666_);
v___y_644_ = v___y_661_;
v___y_645_ = v___x_663_;
v___y_646_ = v___x_667_;
goto v___jp_643_;
}
}
v___jp_668_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_key_641_);
lean_ctor_set(v___x_669_, 1, v_c_642_);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_mk_empty_array_with_capacity(v___x_670_);
v___x_672_ = lean_array_push(v___x_671_, v___x_669_);
v___y_661_ = v___x_672_;
goto v___jp_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4(lean_object* v_vs_681_, lean_object* v_toPure_682_, lean_object* v_children_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___y_687_; uint8_t v___x_701_; 
v___x_684_ = lean_array_get_size(v_vs_681_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v___x_684_, v___x_685_);
if (v___x_701_ == 0)
{
v___y_687_ = v___x_701_;
goto v___jp_686_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_array_get_size(v_children_683_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
v___y_687_ = v___x_704_;
goto v___jp_686_;
}
v___jp_686_:
{
if (v___y_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_688_, 0, v_vs_681_);
lean_ctor_set(v___x_688_, 1, v_children_683_);
v___x_689_ = lean_apply_2(v_toPure_682_, lean_box(0), v___x_688_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_vs_681_);
v___x_690_ = lean_array_fget(v_children_683_, v___x_685_);
lean_dec_ref(v_children_683_);
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
v___x_698_ = lean_apply_2(v_toPure_682_, lean_box(0), v___x_697_);
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5(lean_object* v_toPure_705_, lean_object* v_children_706_, lean_object* v_inst_707_, lean_object* v___f_708_, lean_object* v_toBind_709_, lean_object* v_vs_710_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_711_, 0, v_vs_710_);
lean_closure_set(v___f_711_, 1, v_toPure_705_);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_array_get_size(v_children_706_);
v___x_714_ = l_Array_filterMapM___redArg(v_inst_707_, v___f_708_, v_children_706_, v___x_712_, v___x_713_);
v___x_715_ = lean_apply_4(v_toBind_709_, lean_box(0), lean_box(0), v___x_714_, v___f_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_fst_716_, lean_object* v_toPure_717_, lean_object* v_child_718_){
_start:
{
if (lean_obj_tag(v_child_718_) == 0)
{
goto v___jp_719_;
}
else
{
lean_object* v_vs_723_; lean_object* v_children_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_vs_723_ = lean_ctor_get(v_child_718_, 0);
v_children_724_ = lean_ctor_get(v_child_718_, 1);
v___x_725_ = lean_array_get_size(v_vs_723_);
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = lean_nat_dec_eq(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
goto v___jp_719_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_array_get_size(v_children_724_);
v___x_729_ = lean_nat_dec_eq(v___x_728_, v___x_726_);
if (v___x_729_ == 0)
{
goto v___jp_719_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref_known(v_child_718_, 2);
lean_dec(v_fst_716_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_apply_2(v_toPure_717_, lean_box(0), v___x_730_);
return v___x_731_;
}
}
}
v___jp_719_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_fst_716_);
lean_ctor_set(v___x_720_, 1, v_child_718_);
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = lean_apply_2(v_toPure_717_, lean_box(0), v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_732_, lean_object* v_inst_733_, lean_object* v_f_734_, lean_object* v_toBind_735_, lean_object* v_x_736_){
_start:
{
lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_fst_737_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_snd_738_);
lean_dec_ref(v_x_736_);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_739_, 0, v_fst_737_);
lean_closure_set(v___f_739_, 1, v_toPure_732_);
v___x_740_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_733_, v_snd_738_, v_f_734_);
v___x_741_ = lean_apply_4(v_toBind_735_, lean_box(0), lean_box(0), v___x_740_, v___f_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_742_, lean_object* v_t_743_, lean_object* v_f_744_){
_start:
{
if (lean_obj_tag(v_t_743_) == 0)
{
lean_object* v_toApplicative_745_; lean_object* v_toBind_746_; lean_object* v_toPure_747_; lean_object* v_key_748_; lean_object* v_child_749_; lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_toApplicative_745_ = lean_ctor_get(v_inst_742_, 0);
v_toBind_746_ = lean_ctor_get(v_inst_742_, 1);
lean_inc_n(v_toBind_746_, 2);
v_toPure_747_ = lean_ctor_get(v_toApplicative_745_, 1);
lean_inc(v_toPure_747_);
v_key_748_ = lean_ctor_get(v_t_743_, 0);
lean_inc(v_key_748_);
v_child_749_ = lean_ctor_get(v_t_743_, 1);
lean_inc_ref(v_child_749_);
lean_dec_ref_known(v_t_743_, 2);
lean_inc(v_f_744_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_750_, 0, v_toPure_747_);
lean_closure_set(v___f_750_, 1, v_key_748_);
lean_closure_set(v___f_750_, 2, v_inst_742_);
lean_closure_set(v___f_750_, 3, v_child_749_);
lean_closure_set(v___f_750_, 4, v_f_744_);
lean_closure_set(v___f_750_, 5, v_toBind_746_);
v___x_751_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_asNode___redArg___closed__0));
v___x_752_ = lean_apply_1(v_f_744_, v___x_751_);
v___x_753_ = lean_apply_4(v_toBind_746_, lean_box(0), lean_box(0), v___x_752_, v___f_750_);
return v___x_753_;
}
else
{
lean_object* v_toApplicative_754_; lean_object* v_toBind_755_; lean_object* v_toPure_756_; lean_object* v_vs_757_; lean_object* v_children_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_toApplicative_754_ = lean_ctor_get(v_inst_742_, 0);
v_toBind_755_ = lean_ctor_get(v_inst_742_, 1);
lean_inc_n(v_toBind_755_, 3);
v_toPure_756_ = lean_ctor_get(v_toApplicative_754_, 1);
lean_inc_n(v_toPure_756_, 2);
v_vs_757_ = lean_ctor_get(v_t_743_, 0);
lean_inc_ref(v_vs_757_);
v_children_758_ = lean_ctor_get(v_t_743_, 1);
lean_inc_ref(v_children_758_);
lean_dec_ref_known(v_t_743_, 2);
lean_inc(v_f_744_);
lean_inc_ref(v_inst_742_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 5, 4);
lean_closure_set(v___f_759_, 0, v_toPure_756_);
lean_closure_set(v___f_759_, 1, v_inst_742_);
lean_closure_set(v___f_759_, 2, v_f_744_);
lean_closure_set(v___f_759_, 3, v_toBind_755_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_760_, 0, v_toPure_756_);
lean_closure_set(v___f_760_, 1, v_children_758_);
lean_closure_set(v___f_760_, 2, v_inst_742_);
lean_closure_set(v___f_760_, 3, v___f_759_);
lean_closure_set(v___f_760_, 4, v_toBind_755_);
v___x_761_ = lean_apply_1(v_f_744_, v_vs_757_);
v___x_762_ = lean_apply_4(v_toBind_755_, lean_box(0), lean_box(0), v___x_761_, v___f_760_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_763_, lean_object* v_key_764_, lean_object* v_inst_765_, lean_object* v_child_766_, lean_object* v_f_767_, lean_object* v_toBind_768_, lean_object* v_vs_769_){
_start:
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_770_, 0, v_vs_769_);
lean_closure_set(v___f_770_, 1, v_toPure_763_);
lean_closure_set(v___f_770_, 2, v_key_764_);
v___x_771_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_765_, v_child_766_, v_f_767_);
v___x_772_ = lean_apply_4(v_toBind_768_, lean_box(0), lean_box(0), v___x_771_, v___f_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_773_, lean_object* v_inst_774_, lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_t_777_, lean_object* v_f_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_774_, v_t_777_, v_f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_780_, lean_object* v_f_781_, lean_object* v_t_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_780_, v_t_782_, v_f_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_acc_786_, lean_object* v_k_787_, lean_object* v_t_788_){
_start:
{
if (lean_obj_tag(v_t_788_) == 0)
{
lean_dec(v_k_787_);
lean_dec_ref(v___x_785_);
lean_dec_ref(v___x_784_);
return v_acc_786_;
}
else
{
lean_object* v_vs_789_; lean_object* v_children_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_vs_789_ = lean_ctor_get(v_t_788_, 0);
v_children_790_ = lean_ctor_get(v_t_788_, 1);
v___x_791_ = lean_array_get_size(v_vs_789_);
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_nat_dec_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_k_787_);
lean_dec_ref(v___x_785_);
lean_dec_ref(v___x_784_);
return v_acc_786_;
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_array_get_size(v_children_790_);
v___x_795_ = lean_nat_dec_eq(v___x_794_, v___x_792_);
if (v___x_795_ == 0)
{
lean_dec(v_k_787_);
lean_dec_ref(v___x_785_);
lean_dec_ref(v___x_784_);
return v_acc_786_;
}
else
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_erase___redArg(v___x_784_, v___x_785_, v_acc_786_, v_k_787_);
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_acc_799_, lean_object* v_k_800_, lean_object* v_t_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(v___x_797_, v___x_798_, v_acc_799_, v_k_800_, v_t_801_);
lean_dec_ref(v_t_801_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_803_, lean_object* v_toPure_804_, lean_object* v_root_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_inc_ref(v_root_805_);
v___x_806_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_805_, v___f_803_, v_root_805_);
v___x_807_ = lean_apply_2(v_toPure_804_, lean_box(0), v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_813_, lean_object* v_d_814_, lean_object* v_f_815_){
_start:
{
lean_object* v_toApplicative_816_; lean_object* v_toBind_817_; lean_object* v_toPure_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_toApplicative_816_ = lean_ctor_get(v_inst_813_, 0);
v_toBind_817_ = lean_ctor_get(v_inst_813_, 1);
lean_inc(v_toBind_817_);
v_toPure_818_ = lean_ctor_get(v_toApplicative_816_, 1);
lean_inc_ref(v_inst_813_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_819_, 0, v_inst_813_);
lean_closure_set(v___f_819_, 1, v_f_815_);
v___f_820_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_818_);
v___f_821_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_821_, 0, v___f_820_);
lean_closure_set(v___f_821_, 1, v_toPure_818_);
v___x_822_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_813_, v_d_814_, v___f_819_);
v___x_823_ = lean_apply_4(v_toBind_817_, lean_box(0), lean_box(0), v___x_822_, v___f_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_824_, lean_object* v_inst_825_, lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_d_828_, lean_object* v_f_829_){
_start:
{
lean_object* v_toApplicative_830_; lean_object* v_toBind_831_; lean_object* v_toPure_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_toApplicative_830_ = lean_ctor_get(v_inst_825_, 0);
v_toBind_831_ = lean_ctor_get(v_inst_825_, 1);
lean_inc(v_toBind_831_);
v_toPure_832_ = lean_ctor_get(v_toApplicative_830_, 1);
lean_inc_ref(v_inst_825_);
v___f_833_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_833_, 0, v_inst_825_);
lean_closure_set(v___f_833_, 1, v_f_829_);
v___f_834_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_832_);
v___f_835_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_835_, 0, v___f_834_);
lean_closure_set(v___f_835_, 1, v_toPure_832_);
v___x_836_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_825_, v_d_828_, v___f_833_);
v___x_837_ = lean_apply_4(v_toBind_831_, lean_box(0), lean_box(0), v___x_836_, v___f_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_838_, lean_object* v_A_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_apply_1(v_f_838_, v_A_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_841_, lean_object* v___f_842_, lean_object* v_t_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_841_, v_t_843_, v___f_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_845_, lean_object* v_f_846_){
_start:
{
lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___f_847_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_847_, 0, v_f_846_);
v___x_848_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_849_, 0, v___x_848_);
lean_closure_set(v___f_849_, 1, v___f_847_);
v___f_850_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_851_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_848_, v_d_845_, v___f_849_);
lean_inc(v___x_851_);
v___x_852_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_851_, v___f_850_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_d_855_, lean_object* v_f_856_){
_start:
{
lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___f_857_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_857_, 0, v_f_856_);
v___x_858_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_859_, 0, v___x_858_);
lean_closure_set(v___f_859_, 1, v___f_857_);
v___f_860_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_861_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_858_, v_d_855_, v___f_859_);
lean_inc(v___x_861_);
v___x_862_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_861_, v___f_860_, v___x_861_);
return v___x_862_;
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
