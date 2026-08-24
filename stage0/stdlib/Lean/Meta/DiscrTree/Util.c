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
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(lean_object* v_x_231_){
_start:
{
lean_object* v_vs_232_; lean_object* v_children_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_vs_232_ = lean_ctor_get(v_x_231_, 0);
v_children_233_ = lean_ctor_get(v_x_231_, 1);
v___x_234_ = lean_array_get_size(v_vs_232_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_nat_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
return v___x_236_;
}
else
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_array_get_size(v_children_233_);
v___x_238_ = lean_nat_dec_eq(v___x_237_, v___x_235_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg___boxed(lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode___redArg(v_x_239_);
lean_dec_ref(v_x_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_isEmptyNode(lean_object* v_00_u03b1_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_vs_244_; lean_object* v_children_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_vs_244_ = lean_ctor_get(v_x_243_, 0);
v_children_245_ = lean_ctor_get(v_x_243_, 1);
v___x_246_ = lean_array_get_size(v_vs_244_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_nat_dec_eq(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
return v___x_248_;
}
else
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_array_get_size(v_children_245_);
v___x_250_ = lean_nat_dec_eq(v___x_249_, v___x_247_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_isEmptyNode___boxed(lean_object* v_00_u03b1_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Lean_Meta_DiscrTree_Trie_isEmptyNode(v_00_u03b1_251_, v_x_252_);
lean_dec_ref(v_x_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_255_, lean_object* v_f_256_, lean_object* v_s_257_, lean_object* v_k_258_, lean_object* v_t_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_mk_empty_array_with_capacity(v___x_260_);
v___x_262_ = lean_array_push(v___x_261_, v_k_258_);
v___x_263_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_255_, v___x_262_, v_f_256_, v_s_257_, v_t_259_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_264_, lean_object* v_f_265_, lean_object* v_init_266_, lean_object* v_t_267_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; 
lean_inc_ref(v_inst_264_);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_268_, 0, v_inst_264_);
lean_closure_set(v___f_268_, 1, v_f_265_);
v___x_269_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_264_, v___f_268_, v_t_267_, v_init_266_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_270_, lean_object* v_00_u03c3_271_, lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_f_274_, lean_object* v_init_275_, lean_object* v_t_276_){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; 
lean_inc_ref(v_inst_273_);
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_277_, 0, v_inst_273_);
lean_closure_set(v___f_277_, 1, v_f_274_);
v___x_278_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_273_, v___f_277_, v_t_276_, v_init_275_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_279_, lean_object* v_s_280_, lean_object* v_keys_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_apply_3(v_f_279_, v_s_280_, v_keys_281_, v_a_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_284_, lean_object* v___f_285_, lean_object* v_s_286_, lean_object* v_k_287_, lean_object* v_t_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_mk_empty_array_with_capacity(v___x_289_);
v___x_291_ = lean_array_push(v___x_290_, v_k_287_);
v___x_292_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_284_, v___x_291_, v___f_285_, v_s_286_, v_t_288_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_293_, lean_object* v_init_294_, lean_object* v_t_295_){
_start:
{
lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___x_299_; 
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_296_, 0, v_f_293_);
v___x_297_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_298_, 0, v___x_297_);
lean_closure_set(v___f_298_, 1, v___f_296_);
v___x_299_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_297_, v___f_298_, v_t_295_, v_init_294_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_300_, lean_object* v_00_u03b1_301_, lean_object* v_f_302_, lean_object* v_init_303_, lean_object* v_t_304_){
_start:
{
lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___f_307_; lean_object* v___x_308_; 
v___f_305_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_305_, 0, v_f_302_);
v___x_306_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_307_, 0, v___x_306_);
lean_closure_set(v___f_307_, 1, v___f_305_);
v___x_308_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_306_, v___f_307_, v_t_304_, v_init_303_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_309_, lean_object* v_f_310_, lean_object* v_s_311_, lean_object* v_x_312_, lean_object* v_t_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_309_, v_f_310_, v_s_311_, v_t_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_315_, lean_object* v_f_316_, lean_object* v_s_317_, lean_object* v_x_318_, lean_object* v_t_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_315_, v_f_316_, v_s_317_, v_x_318_, v_t_319_);
lean_dec(v_x_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_321_, lean_object* v_f_322_, lean_object* v_init_323_, lean_object* v_t_324_){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; 
lean_inc_ref(v_inst_321_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_325_, 0, v_inst_321_);
lean_closure_set(v___f_325_, 1, v_f_322_);
v___x_326_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_321_, v___f_325_, v_t_324_, v_init_323_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_327_, lean_object* v_00_u03c3_328_, lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_f_331_, lean_object* v_init_332_, lean_object* v_t_333_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; 
lean_inc_ref(v_inst_330_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_334_, 0, v_inst_330_);
lean_closure_set(v___f_334_, 1, v_f_331_);
v___x_335_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_330_, v___f_334_, v_t_333_, v_init_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_336_, lean_object* v___f_337_, lean_object* v_s_338_, lean_object* v_x_339_, lean_object* v_t_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_336_, v___f_337_, v_s_338_, v_t_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_342_, lean_object* v___f_343_, lean_object* v_s_344_, lean_object* v_x_345_, lean_object* v_t_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_342_, v___f_343_, v_s_344_, v_x_345_, v_t_346_);
lean_dec(v_x_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_348_, lean_object* v_init_349_, lean_object* v_t_350_){
_start:
{
lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___x_354_; 
v___f_351_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_351_, 0, v_f_348_);
v___x_352_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_353_, 0, v___x_352_);
lean_closure_set(v___f_353_, 1, v___f_351_);
v___x_354_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_352_, v___f_353_, v_t_350_, v_init_349_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_355_, lean_object* v_00_u03b1_356_, lean_object* v_f_357_, lean_object* v_init_358_, lean_object* v_t_359_){
_start:
{
lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___f_362_; lean_object* v___x_363_; 
v___f_360_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_360_, 0, v_f_357_);
v___x_361_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_362_, 0, v___x_361_);
lean_closure_set(v___f_362_, 1, v___f_360_);
v___x_363_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_361_, v___f_362_, v_t_359_, v_init_358_);
return v___x_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_364_, uint8_t v_x1_365_, lean_object* v_x2_366_){
_start:
{
if (v_x1_365_ == 0)
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_apply_1(v_f_364_, v_x2_366_);
v___x_368_ = lean_unbox(v___x_367_);
return v___x_368_;
}
else
{
lean_dec(v_x2_366_);
lean_dec_ref(v_f_364_);
return v_x1_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_369_, lean_object* v_x1_370_, lean_object* v_x2_371_){
_start:
{
uint8_t v_x1_82__boxed_372_; uint8_t v_res_373_; lean_object* v_r_374_; 
v_x1_82__boxed_372_ = lean_unbox(v_x1_370_);
v_res_373_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_369_, v_x1_82__boxed_372_, v_x2_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_375_, lean_object* v___f_376_, uint8_t v_s_377_, lean_object* v_x_378_, lean_object* v_t_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_380_ = lean_box(v_s_377_);
v___x_381_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_375_, v___f_376_, v___x_380_, v_t_379_);
v___x_382_ = lean_unbox(v___x_381_);
lean_dec(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_383_, lean_object* v___f_384_, lean_object* v_s_385_, lean_object* v_x_386_, lean_object* v_t_387_){
_start:
{
uint8_t v_s_boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_s_boxed_388_ = lean_unbox(v_s_385_);
v_res_389_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_383_, v___f_384_, v_s_boxed_388_, v_x_386_, v_t_387_);
lean_dec(v_x_386_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_391_, lean_object* v_f_392_){
_start:
{
lean_object* v___f_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___f_393_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_393_, 0, v_f_392_);
v___x_394_ = 0;
v___x_395_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_396_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_396_, 0, v___x_395_);
lean_closure_set(v___f_396_, 1, v___f_393_);
v___x_397_ = lean_box(v___x_394_);
v___x_398_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_395_, v___f_396_, v_t_391_, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_399_, lean_object* v_t_400_, lean_object* v_f_401_){
_start:
{
lean_object* v___f_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___f_402_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_402_, 0, v_f_401_);
v___x_403_ = 0;
v___x_404_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_405_, 0, v___x_404_);
lean_closure_set(v___f_405_, 1, v___f_402_);
v___x_406_ = lean_box(v___x_403_);
v___x_407_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_404_, v___f_405_, v_t_400_, v___x_406_);
v___x_408_ = lean_unbox(v___x_407_);
lean_dec(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_409_, lean_object* v_t_410_, lean_object* v_f_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_409_, v_t_410_, v_f_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_414_, lean_object* v_x2_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_array_push(v_x1_414_, v_x2_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_417_, lean_object* v___f_418_, lean_object* v_s_419_, lean_object* v_x_420_, lean_object* v_t_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_417_, v___f_418_, v_s_419_, v_t_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_423_, lean_object* v___f_424_, lean_object* v_s_425_, lean_object* v_x_426_, lean_object* v_t_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_423_, v___f_424_, v_s_425_, v_x_426_, v_t_427_);
lean_dec(v_x_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_437_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_438_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_439_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_437_, v___f_438_, v_t_435_, v___x_436_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_440_, lean_object* v_t_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_443_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_444_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_445_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_443_, v___f_444_, v_t_441_, v___x_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_446_, lean_object* v_keys_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_keys_447_);
lean_ctor_set(v___x_449_, 1, v_a_448_);
v___x_450_ = lean_array_push(v_s_446_, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_451_, lean_object* v___f_452_, lean_object* v_s_453_, lean_object* v_k_454_, lean_object* v_t_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = lean_mk_empty_array_with_capacity(v___x_456_);
v___x_458_ = lean_array_push(v___x_457_, v_k_454_);
v___x_459_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_451_, v___x_458_, v___f_452_, v_s_453_, v_t_455_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___f_469_; lean_object* v___x_470_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_468_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_469_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_470_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_468_, v___f_469_, v_t_466_, v___x_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_471_, lean_object* v_t_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___f_475_; lean_object* v___x_476_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_474_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_475_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_476_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_474_, v___f_475_, v_t_472_, v___x_473_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_477_, lean_object* v_x_478_, lean_object* v_t_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_479_);
v___x_481_ = lean_nat_add(v_n_477_, v___x_480_);
lean_dec(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_482_, lean_object* v_x_483_, lean_object* v_t_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_482_, v_x_483_, v_t_484_);
lean_dec_ref(v_t_484_);
lean_dec(v_x_483_);
lean_dec(v_n_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_487_){
_start:
{
lean_object* v___f_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___f_488_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_487_, v___f_488_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_491_, lean_object* v_t_492_){
_start:
{
lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___f_493_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_492_, v___f_493_, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_fst_496_, lean_object* v_toPure_497_, lean_object* v_child_498_){
_start:
{
lean_object* v_vs_503_; lean_object* v_children_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_vs_503_ = lean_ctor_get(v_child_498_, 0);
v_children_504_ = lean_ctor_get(v_child_498_, 1);
v___x_505_ = lean_array_get_size(v_vs_503_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_nat_dec_eq(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
goto v___jp_499_;
}
else
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_array_get_size(v_children_504_);
v___x_509_ = lean_nat_dec_eq(v___x_508_, v___x_506_);
if (v___x_509_ == 0)
{
goto v___jp_499_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v_child_498_);
lean_dec(v_fst_496_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_apply_2(v_toPure_497_, lean_box(0), v___x_510_);
return v___x_511_;
}
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_fst_496_);
lean_ctor_set(v___x_500_, 1, v_child_498_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
v___x_502_ = lean_apply_2(v_toPure_497_, lean_box(0), v___x_501_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_vs_512_, lean_object* v_toPure_513_, lean_object* v_children_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_vs_512_);
lean_ctor_set(v___x_515_, 1, v_children_514_);
v___x_516_ = lean_apply_2(v_toPure_513_, lean_box(0), v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_517_, lean_object* v_children_518_, lean_object* v_inst_519_, lean_object* v___f_520_, lean_object* v_toBind_521_, lean_object* v_vs_522_){
_start:
{
lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_523_, 0, v_vs_522_);
lean_closure_set(v___f_523_, 1, v_toPure_517_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_array_get_size(v_children_518_);
v___x_526_ = l_Array_filterMapM___redArg(v_inst_519_, v___f_520_, v_children_518_, v___x_524_, v___x_525_);
v___x_527_ = lean_apply_4(v_toBind_521_, lean_box(0), lean_box(0), v___x_526_, v___f_523_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_528_, lean_object* v_t_529_, lean_object* v_f_530_){
_start:
{
lean_object* v_toApplicative_531_; lean_object* v_toBind_532_; lean_object* v_toPure_533_; lean_object* v_vs_534_; lean_object* v_children_535_; lean_object* v___f_536_; lean_object* v___f_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_toApplicative_531_ = lean_ctor_get(v_inst_528_, 0);
v_toBind_532_ = lean_ctor_get(v_inst_528_, 1);
lean_inc_n(v_toBind_532_, 3);
v_toPure_533_ = lean_ctor_get(v_toApplicative_531_, 1);
lean_inc_n(v_toPure_533_, 2);
v_vs_534_ = lean_ctor_get(v_t_529_, 0);
lean_inc_ref(v_vs_534_);
v_children_535_ = lean_ctor_get(v_t_529_, 1);
lean_inc_ref(v_children_535_);
lean_dec_ref(v_t_529_);
lean_inc(v_f_530_);
lean_inc_ref(v_inst_528_);
v___f_536_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_536_, 0, v_toPure_533_);
lean_closure_set(v___f_536_, 1, v_inst_528_);
lean_closure_set(v___f_536_, 2, v_f_530_);
lean_closure_set(v___f_536_, 3, v_toBind_532_);
v___f_537_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 6, 5);
lean_closure_set(v___f_537_, 0, v_toPure_533_);
lean_closure_set(v___f_537_, 1, v_children_535_);
lean_closure_set(v___f_537_, 2, v_inst_528_);
lean_closure_set(v___f_537_, 3, v___f_536_);
lean_closure_set(v___f_537_, 4, v_toBind_532_);
v___x_538_ = lean_apply_1(v_f_530_, v_vs_534_);
v___x_539_ = lean_apply_4(v_toBind_532_, lean_box(0), lean_box(0), v___x_538_, v___f_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_540_, lean_object* v_inst_541_, lean_object* v_f_542_, lean_object* v_toBind_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_fst_545_; lean_object* v_snd_546_; lean_object* v___f_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_fst_545_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_fst_545_);
v_snd_546_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_snd_546_);
lean_dec_ref(v_x_544_);
v___f_547_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_547_, 0, v_fst_545_);
lean_closure_set(v___f_547_, 1, v_toPure_540_);
v___x_548_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_541_, v_snd_546_, v_f_542_);
v___x_549_ = lean_apply_4(v_toBind_543_, lean_box(0), lean_box(0), v___x_548_, v___f_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_550_, lean_object* v_inst_551_, lean_object* v_00_u03b1_552_, lean_object* v_00_u03b2_553_, lean_object* v_t_554_, lean_object* v_f_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_551_, v_t_554_, v_f_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_557_, lean_object* v_f_558_, lean_object* v_t_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_557_, v_t_559_, v_f_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v_acc_563_, lean_object* v_k_564_, lean_object* v_t_565_){
_start:
{
lean_object* v_vs_566_; lean_object* v_children_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_vs_566_ = lean_ctor_get(v_t_565_, 0);
v_children_567_ = lean_ctor_get(v_t_565_, 1);
v___x_568_ = lean_array_get_size(v_vs_566_);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_eq(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v_k_564_);
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_561_);
return v_acc_563_;
}
else
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_children_567_);
v___x_572_ = lean_nat_dec_eq(v___x_571_, v___x_569_);
if (v___x_572_ == 0)
{
lean_dec(v_k_564_);
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_561_);
return v_acc_563_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_PersistentHashMap_erase___redArg(v___x_561_, v___x_562_, v_acc_563_, v_k_564_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1___boxed(lean_object* v___x_574_, lean_object* v___x_575_, lean_object* v_acc_576_, lean_object* v_k_577_, lean_object* v_t_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(v___x_574_, v___x_575_, v_acc_576_, v_k_577_, v_t_578_);
lean_dec_ref(v_t_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2(lean_object* v___f_580_, lean_object* v_toPure_581_, lean_object* v_root_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_inc_ref(v_root_582_);
v___x_583_ = l_Lean_PersistentHashMap_foldl___redArg(v_root_582_, v___f_580_, v_root_582_);
v___x_584_ = lean_apply_2(v_toPure_581_, lean_box(0), v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_590_, lean_object* v_d_591_, lean_object* v_f_592_){
_start:
{
lean_object* v_toApplicative_593_; lean_object* v_toBind_594_; lean_object* v_toPure_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_toApplicative_593_ = lean_ctor_get(v_inst_590_, 0);
v_toBind_594_ = lean_ctor_get(v_inst_590_, 1);
lean_inc(v_toBind_594_);
v_toPure_595_ = lean_ctor_get(v_toApplicative_593_, 1);
lean_inc_ref(v_inst_590_);
v___f_596_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_596_, 0, v_inst_590_);
lean_closure_set(v___f_596_, 1, v_f_592_);
v___f_597_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_595_);
v___f_598_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_598_, 0, v___f_597_);
lean_closure_set(v___f_598_, 1, v_toPure_595_);
v___x_599_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_590_, v_d_591_, v___f_596_);
v___x_600_ = lean_apply_4(v_toBind_594_, lean_box(0), lean_box(0), v___x_599_, v___f_598_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_601_, lean_object* v_inst_602_, lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_d_605_, lean_object* v_f_606_){
_start:
{
lean_object* v_toApplicative_607_; lean_object* v_toBind_608_; lean_object* v_toPure_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_toApplicative_607_ = lean_ctor_get(v_inst_602_, 0);
v_toBind_608_ = lean_ctor_get(v_inst_602_, 1);
lean_inc(v_toBind_608_);
v_toPure_609_ = lean_ctor_get(v_toApplicative_607_, 1);
lean_inc_ref(v_inst_602_);
v___f_610_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_610_, 0, v_inst_602_);
lean_closure_set(v___f_610_, 1, v_f_606_);
v___f_611_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
lean_inc(v_toPure_609_);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_612_, 0, v___f_611_);
lean_closure_set(v___f_612_, 1, v_toPure_609_);
v___x_613_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_602_, v_d_605_, v___f_610_);
v___x_614_ = lean_apply_4(v_toBind_608_, lean_box(0), lean_box(0), v___x_613_, v___f_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_615_, lean_object* v_A_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_apply_1(v_f_615_, v_A_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1(lean_object* v___x_618_, lean_object* v___f_619_, lean_object* v_t_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v___x_618_, v_t_620_, v___f_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_622_, lean_object* v_f_623_){
_start:
{
lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_624_, 0, v_f_623_);
v___x_625_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_626_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_626_, 0, v___x_625_);
lean_closure_set(v___f_626_, 1, v___f_624_);
v___f_627_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_628_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_625_, v_d_622_, v___f_626_);
lean_inc(v___x_628_);
v___x_629_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_628_, v___f_627_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_d_632_, lean_object* v_f_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_634_, 0, v_f_633_);
v___x_635_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__1), 3, 2);
lean_closure_set(v___f_636_, 0, v___x_635_);
lean_closure_set(v___f_636_, 1, v___f_634_);
v___f_637_ = ((lean_object*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___closed__2));
v___x_638_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_635_, v_d_632_, v___f_636_);
lean_inc(v___x_638_);
v___x_639_ = l_Lean_PersistentHashMap_foldl___redArg(v___x_638_, v___f_637_, v___x_638_);
return v___x_639_;
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
