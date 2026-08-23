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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_231_, lean_object* v_f_232_, lean_object* v_s_233_, lean_object* v_k_234_, lean_object* v_t_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_mk_empty_array_with_capacity(v___x_236_);
v___x_238_ = lean_array_push(v___x_237_, v_k_234_);
v___x_239_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_231_, v___x_238_, v_f_232_, v_s_233_, v_t_235_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_240_, lean_object* v_f_241_, lean_object* v_init_242_, lean_object* v_t_243_){
_start:
{
lean_object* v___f_244_; lean_object* v___x_245_; 
lean_inc_ref(v_inst_240_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_244_, 0, v_inst_240_);
lean_closure_set(v___f_244_, 1, v_f_241_);
v___x_245_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_240_, v___f_244_, v_t_243_, v_init_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_246_, lean_object* v_00_u03c3_247_, lean_object* v_00_u03b1_248_, lean_object* v_inst_249_, lean_object* v_f_250_, lean_object* v_init_251_, lean_object* v_t_252_){
_start:
{
lean_object* v___f_253_; lean_object* v___x_254_; 
lean_inc_ref(v_inst_249_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_253_, 0, v_inst_249_);
lean_closure_set(v___f_253_, 1, v_f_250_);
v___x_254_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_249_, v___f_253_, v_t_252_, v_init_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_255_, lean_object* v_s_256_, lean_object* v_keys_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_apply_3(v_f_255_, v_s_256_, v_keys_257_, v_a_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_260_, lean_object* v___f_261_, lean_object* v_s_262_, lean_object* v_k_263_, lean_object* v_t_264_){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_mk_empty_array_with_capacity(v___x_265_);
v___x_267_ = lean_array_push(v___x_266_, v_k_263_);
v___x_268_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_260_, v___x_267_, v___f_261_, v_s_262_, v_t_264_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_269_, lean_object* v_init_270_, lean_object* v_t_271_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___f_272_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_272_, 0, v_f_269_);
v___x_273_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_274_, 0, v___x_273_);
lean_closure_set(v___f_274_, 1, v___f_272_);
v___x_275_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_273_, v___f_274_, v_t_271_, v_init_270_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_276_, lean_object* v_00_u03b1_277_, lean_object* v_f_278_, lean_object* v_init_279_, lean_object* v_t_280_){
_start:
{
lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___f_283_; lean_object* v___x_284_; 
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_281_, 0, v_f_278_);
v___x_282_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_283_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_283_, 0, v___x_282_);
lean_closure_set(v___f_283_, 1, v___f_281_);
v___x_284_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_282_, v___f_283_, v_t_280_, v_init_279_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_285_, lean_object* v_f_286_, lean_object* v_s_287_, lean_object* v_x_288_, lean_object* v_t_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_285_, v_f_286_, v_s_287_, v_t_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_291_, lean_object* v_f_292_, lean_object* v_s_293_, lean_object* v_x_294_, lean_object* v_t_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_291_, v_f_292_, v_s_293_, v_x_294_, v_t_295_);
lean_dec(v_x_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_297_, lean_object* v_f_298_, lean_object* v_init_299_, lean_object* v_t_300_){
_start:
{
lean_object* v___f_301_; lean_object* v___x_302_; 
lean_inc_ref(v_inst_297_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_301_, 0, v_inst_297_);
lean_closure_set(v___f_301_, 1, v_f_298_);
v___x_302_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_297_, v___f_301_, v_t_300_, v_init_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_303_, lean_object* v_00_u03c3_304_, lean_object* v_00_u03b1_305_, lean_object* v_inst_306_, lean_object* v_f_307_, lean_object* v_init_308_, lean_object* v_t_309_){
_start:
{
lean_object* v___f_310_; lean_object* v___x_311_; 
lean_inc_ref(v_inst_306_);
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_310_, 0, v_inst_306_);
lean_closure_set(v___f_310_, 1, v_f_307_);
v___x_311_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_306_, v___f_310_, v_t_309_, v_init_308_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_312_, lean_object* v___f_313_, lean_object* v_s_314_, lean_object* v_x_315_, lean_object* v_t_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_312_, v___f_313_, v_s_314_, v_t_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_318_, lean_object* v___f_319_, lean_object* v_s_320_, lean_object* v_x_321_, lean_object* v_t_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_318_, v___f_319_, v_s_320_, v_x_321_, v_t_322_);
lean_dec(v_x_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_324_, lean_object* v_init_325_, lean_object* v_t_326_){
_start:
{
lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_327_, 0, v_f_324_);
v___x_328_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_329_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_329_, 0, v___x_328_);
lean_closure_set(v___f_329_, 1, v___f_327_);
v___x_330_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_328_, v___f_329_, v_t_326_, v_init_325_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_331_, lean_object* v_00_u03b1_332_, lean_object* v_f_333_, lean_object* v_init_334_, lean_object* v_t_335_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___x_339_; 
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_336_, 0, v_f_333_);
v___x_337_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_338_, 0, v___x_337_);
lean_closure_set(v___f_338_, 1, v___f_336_);
v___x_339_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_337_, v___f_338_, v_t_335_, v_init_334_);
return v___x_339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_340_, uint8_t v_x1_341_, lean_object* v_x2_342_){
_start:
{
if (v_x1_341_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = lean_apply_1(v_f_340_, v_x2_342_);
v___x_344_ = lean_unbox(v___x_343_);
return v___x_344_;
}
else
{
lean_dec(v_x2_342_);
lean_dec_ref(v_f_340_);
return v_x1_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_345_, lean_object* v_x1_346_, lean_object* v_x2_347_){
_start:
{
uint8_t v_x1_82__boxed_348_; uint8_t v_res_349_; lean_object* v_r_350_; 
v_x1_82__boxed_348_ = lean_unbox(v_x1_346_);
v_res_349_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_345_, v_x1_82__boxed_348_, v_x2_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_351_, lean_object* v___f_352_, uint8_t v_s_353_, lean_object* v_x_354_, lean_object* v_t_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_box(v_s_353_);
v___x_357_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_351_, v___f_352_, v___x_356_, v_t_355_);
v___x_358_ = lean_unbox(v___x_357_);
lean_dec(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_359_, lean_object* v___f_360_, lean_object* v_s_361_, lean_object* v_x_362_, lean_object* v_t_363_){
_start:
{
uint8_t v_s_boxed_364_; uint8_t v_res_365_; lean_object* v_r_366_; 
v_s_boxed_364_ = lean_unbox(v_s_361_);
v_res_365_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_359_, v___f_360_, v_s_boxed_364_, v_x_362_, v_t_363_);
lean_dec(v_x_362_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_367_, lean_object* v_f_368_){
_start:
{
lean_object* v___f_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_369_, 0, v_f_368_);
v___x_370_ = 0;
v___x_371_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_372_, 0, v___x_371_);
lean_closure_set(v___f_372_, 1, v___f_369_);
v___x_373_ = lean_box(v___x_370_);
v___x_374_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_371_, v___f_372_, v_t_367_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_375_, lean_object* v_t_376_, lean_object* v_f_377_){
_start:
{
lean_object* v___f_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___f_378_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_378_, 0, v_f_377_);
v___x_379_ = 0;
v___x_380_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_381_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_381_, 0, v___x_380_);
lean_closure_set(v___f_381_, 1, v___f_378_);
v___x_382_ = lean_box(v___x_379_);
v___x_383_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_380_, v___f_381_, v_t_376_, v___x_382_);
v___x_384_ = lean_unbox(v___x_383_);
lean_dec(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_385_, lean_object* v_t_386_, lean_object* v_f_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_385_, v_t_386_, v_f_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_390_, lean_object* v_x2_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_array_push(v_x1_390_, v_x2_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_393_, lean_object* v___f_394_, lean_object* v_s_395_, lean_object* v_x_396_, lean_object* v_t_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_393_, v___f_394_, v_s_395_, v_t_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_399_, lean_object* v___f_400_, lean_object* v_s_401_, lean_object* v_x_402_, lean_object* v_t_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_399_, v___f_400_, v_s_401_, v_x_402_, v_t_403_);
lean_dec(v_x_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_413_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_414_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_415_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_413_, v___f_414_, v_t_411_, v___x_412_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_416_, lean_object* v_t_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___x_421_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_419_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_420_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_421_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_419_, v___f_420_, v_t_417_, v___x_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_422_, lean_object* v_keys_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_keys_423_);
lean_ctor_set(v___x_425_, 1, v_a_424_);
v___x_426_ = lean_array_push(v_s_422_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_427_, lean_object* v___f_428_, lean_object* v_s_429_, lean_object* v_k_430_, lean_object* v_t_431_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___f_445_; lean_object* v___x_446_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_444_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_445_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_446_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_444_, v___f_445_, v_t_442_, v___x_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_447_, lean_object* v_t_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___x_452_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_450_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_451_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_452_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_450_, v___f_451_, v_t_448_, v___x_449_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_453_, lean_object* v_x_454_, lean_object* v_t_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_455_);
v___x_457_ = lean_nat_add(v_n_453_, v___x_456_);
lean_dec(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_458_, lean_object* v_x_459_, lean_object* v_t_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_458_, v_x_459_, v_t_460_);
lean_dec_ref(v_t_460_);
lean_dec(v_x_459_);
lean_dec(v_n_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_463_){
_start:
{
lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___f_464_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_463_, v___f_464_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_467_, lean_object* v_t_468_){
_start:
{
lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___f_469_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_468_, v___f_469_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_fst_472_, lean_object* v_toPure_473_, lean_object* v_____do__lift_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v_fst_472_);
lean_ctor_set(v___x_475_, 1, v_____do__lift_474_);
v___x_476_ = lean_apply_2(v_toPure_473_, lean_box(0), v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_____do__lift_477_, lean_object* v_toPure_478_, lean_object* v_____do__lift_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_____do__lift_477_);
lean_ctor_set(v___x_480_, 1, v_____do__lift_479_);
v___x_481_ = lean_apply_2(v_toPure_478_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_482_, lean_object* v_children_483_, lean_object* v_inst_484_, lean_object* v___f_485_, lean_object* v_toBind_486_, lean_object* v_____do__lift_487_){
_start:
{
lean_object* v___f_488_; size_t v_sz_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___f_488_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_488_, 0, v_____do__lift_487_);
lean_closure_set(v___f_488_, 1, v_toPure_482_);
v_sz_489_ = lean_array_size(v_children_483_);
v___x_490_ = ((size_t)0ULL);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_484_, v___f_485_, v_sz_489_, v___x_490_, v_children_483_);
v___x_492_ = lean_apply_4(v_toBind_486_, lean_box(0), lean_box(0), v___x_491_, v___f_488_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_493_, lean_object* v_t_494_, lean_object* v_f_495_){
_start:
{
lean_object* v_toApplicative_496_; lean_object* v_toBind_497_; lean_object* v_toPure_498_; lean_object* v_vs_499_; lean_object* v_children_500_; lean_object* v___f_501_; lean_object* v___f_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_toApplicative_496_ = lean_ctor_get(v_inst_493_, 0);
v_toBind_497_ = lean_ctor_get(v_inst_493_, 1);
lean_inc_n(v_toBind_497_, 3);
v_toPure_498_ = lean_ctor_get(v_toApplicative_496_, 1);
lean_inc_n(v_toPure_498_, 2);
v_vs_499_ = lean_ctor_get(v_t_494_, 0);
lean_inc_ref(v_vs_499_);
v_children_500_ = lean_ctor_get(v_t_494_, 1);
lean_inc_ref(v_children_500_);
lean_dec_ref(v_t_494_);
lean_inc(v_f_495_);
lean_inc_ref(v_inst_493_);
v___f_501_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_501_, 0, v_toPure_498_);
lean_closure_set(v___f_501_, 1, v_inst_493_);
lean_closure_set(v___f_501_, 2, v_f_495_);
lean_closure_set(v___f_501_, 3, v_toBind_497_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 6, 5);
lean_closure_set(v___f_502_, 0, v_toPure_498_);
lean_closure_set(v___f_502_, 1, v_children_500_);
lean_closure_set(v___f_502_, 2, v_inst_493_);
lean_closure_set(v___f_502_, 3, v___f_501_);
lean_closure_set(v___f_502_, 4, v_toBind_497_);
v___x_503_ = lean_apply_1(v_f_495_, v_vs_499_);
v___x_504_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v___x_503_, v___f_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_505_, lean_object* v_inst_506_, lean_object* v_f_507_, lean_object* v_toBind_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_fst_510_; lean_object* v_snd_511_; lean_object* v___f_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_fst_510_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_fst_510_);
v_snd_511_ = lean_ctor_get(v_x_509_, 1);
lean_inc(v_snd_511_);
lean_dec_ref(v_x_509_);
v___f_512_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_512_, 0, v_fst_510_);
lean_closure_set(v___f_512_, 1, v_toPure_505_);
v___x_513_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_506_, v_snd_511_, v_f_507_);
v___x_514_ = lean_apply_4(v_toBind_508_, lean_box(0), lean_box(0), v___x_513_, v___f_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_515_, lean_object* v_inst_516_, lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_t_519_, lean_object* v_f_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_516_, v_t_519_, v_f_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_522_, lean_object* v_f_523_, lean_object* v_t_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_522_, v_t_524_, v_f_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v_toPure_526_, lean_object* v_____do__lift_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_apply_2(v_toPure_526_, lean_box(0), v_____do__lift_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_529_, lean_object* v_d_530_, lean_object* v_f_531_){
_start:
{
lean_object* v_toApplicative_532_; lean_object* v_toBind_533_; lean_object* v_toPure_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_toApplicative_532_ = lean_ctor_get(v_inst_529_, 0);
v_toBind_533_ = lean_ctor_get(v_inst_529_, 1);
lean_inc(v_toBind_533_);
v_toPure_534_ = lean_ctor_get(v_toApplicative_532_, 1);
lean_inc_ref(v_inst_529_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_535_, 0, v_inst_529_);
lean_closure_set(v___f_535_, 1, v_f_531_);
lean_inc(v_toPure_534_);
v___f_536_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_536_, 0, v_toPure_534_);
v___x_537_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_529_, v_d_530_, v___f_535_);
v___x_538_ = lean_apply_4(v_toBind_533_, lean_box(0), lean_box(0), v___x_537_, v___f_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_539_, lean_object* v_inst_540_, lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_d_543_, lean_object* v_f_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg(v_inst_540_, v_d_543_, v_f_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_546_, lean_object* v_A_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_apply_1(v_f_546_, v_A_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(lean_object* v_f_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_bs_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_553_ == 0)
{
lean_dec_ref(v_f_549_);
return v_bs_552_;
}
else
{
lean_object* v_v_554_; lean_object* v_fst_555_; lean_object* v_snd_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_570_; 
v_v_554_ = lean_array_uget(v_bs_552_, v_i_551_);
v_fst_555_ = lean_ctor_get(v_v_554_, 0);
v_snd_556_ = lean_ctor_get(v_v_554_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_v_554_);
if (v_isSharedCheck_570_ == 0)
{
v___x_558_ = v_v_554_;
v_isShared_559_ = v_isSharedCheck_570_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_556_);
lean_inc(v_fst_555_);
lean_dec(v_v_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_570_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v_bs_x27_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v_bs_x27_561_ = lean_array_uset(v_bs_552_, v_i_551_, v___x_560_);
lean_inc_ref(v_f_549_);
v___x_562_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_snd_556_, v_f_549_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_fst_555_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_569_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_add(v_i_551_, v___x_565_);
v___x_567_ = lean_array_uset(v_bs_x27_561_, v_i_551_, v___x_564_);
v_i_551_ = v___x_566_;
v_bs_552_ = v___x_567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(lean_object* v_t_571_, lean_object* v_f_572_){
_start:
{
lean_object* v_vs_573_; lean_object* v_children_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_vs_573_ = lean_ctor_get(v_t_571_, 0);
v_children_574_ = lean_ctor_get(v_t_571_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_t_571_);
if (v_isSharedCheck_585_ == 0)
{
v___x_576_ = v_t_571_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_children_574_);
lean_inc(v_vs_573_);
lean_dec(v_t_571_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
lean_inc_ref(v_f_572_);
v___x_578_ = lean_apply_1(v_f_572_, v_vs_573_);
v_sz_579_ = lean_array_size(v_children_574_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_572_, v_sz_579_, v___x_580_, v_children_574_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v___x_581_);
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_583_ = v___x_576_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_586_, lean_object* v_sz_587_, lean_object* v_i_588_, lean_object* v_bs_589_){
_start:
{
size_t v_sz_boxed_590_; size_t v_i_boxed_591_; lean_object* v_res_592_; 
v_sz_boxed_590_ = lean_unbox_usize(v_sz_587_);
lean_dec(v_sz_587_);
v_i_boxed_591_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_586_, v_sz_boxed_590_, v_i_boxed_591_, v_bs_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0(lean_object* v_f_593_, lean_object* v_t_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_t_594_, v_f_593_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_f_596_, lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_acc_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_as_597_);
v___x_601_ = lean_nat_dec_eq(v_i_598_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_602_ = lean_array_fget_borrowed(v_as_597_, v_i_598_);
lean_inc(v_f_596_);
lean_inc(v___x_602_);
v___x_603_ = lean_apply_1(v_f_596_, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_598_, v___x_604_);
lean_dec(v_i_598_);
v___x_606_ = lean_array_push(v_acc_599_, v___x_603_);
v_i_598_ = v___x_605_;
v_acc_599_ = v___x_606_;
goto _start;
}
else
{
lean_dec(v_i_598_);
lean_dec(v_f_596_);
return v_acc_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_f_608_, lean_object* v_as_609_, lean_object* v_i_610_, lean_object* v_acc_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_608_, v_as_609_, v_i_610_, v_acc_611_);
lean_dec_ref(v_as_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_613_, lean_object* v_as_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_get_size(v_as_614_);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_616_);
v___x_618_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_613_, v_as_614_, v___x_615_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_619_, lean_object* v_as_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_619_, v_as_620_);
lean_dec_ref(v_as_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_f_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_bs_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_626_ == 0)
{
lean_dec(v_f_622_);
return v_bs_625_;
}
else
{
lean_object* v_v_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; lean_object* v___y_631_; 
v_v_627_ = lean_array_uget(v_bs_625_, v_i_624_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_625_, v_i_624_, v___x_628_);
switch(lean_obj_tag(v_v_627_))
{
case 0:
{
lean_object* v_key_636_; lean_object* v_val_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_key_636_ = lean_ctor_get(v_v_627_, 0);
v_val_637_ = lean_ctor_get(v_v_627_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_v_627_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v_v_627_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_val_637_);
lean_inc(v_key_636_);
lean_dec(v_v_627_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_inc(v_f_622_);
v___x_641_ = lean_apply_1(v_f_622_, v_val_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
v___y_631_ = v___x_643_;
goto v___jp_630_;
}
}
}
case 1:
{
lean_object* v_node_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
v_node_646_ = lean_ctor_get(v_v_627_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_v_627_);
if (v_isSharedCheck_654_ == 0)
{
v___x_648_ = v_v_627_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_node_646_);
lean_dec(v_v_627_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_inc(v_f_622_);
v___x_650_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_622_, v_node_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v___y_631_ = v___x_652_;
goto v___jp_630_;
}
}
}
default: 
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(2);
v___y_631_ = v___x_655_;
goto v___jp_630_;
}
}
v___jp_630_:
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_624_, v___x_632_);
v___x_634_ = lean_array_uset(v_bs_x27_629_, v_i_624_, v___y_631_);
v_i_624_ = v___x_633_;
v_bs_625_ = v___x_634_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(lean_object* v_f_656_, lean_object* v_n_657_){
_start:
{
if (lean_obj_tag(v_n_657_) == 0)
{
lean_object* v_es_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v_es_658_ = lean_ctor_get(v_n_657_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_n_657_);
if (v_isSharedCheck_668_ == 0)
{
v___x_660_ = v_n_657_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_es_658_);
lean_dec(v_n_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
size_t v_sz_662_; size_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_sz_662_ = lean_array_size(v_es_658_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_656_, v_sz_662_, v___x_663_, v_es_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v_ks_669_; lean_object* v_vs_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_ks_669_ = lean_ctor_get(v_n_657_, 0);
v_vs_670_ = lean_ctor_get(v_n_657_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_n_657_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_n_657_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_vs_670_);
lean_inc(v_ks_669_);
lean_dec(v_n_657_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_val_674_; lean_object* v___x_676_; 
v_val_674_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_656_, v_vs_670_);
lean_dec_ref(v_vs_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_val_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_ks_669_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_val_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_bs_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_684_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_679_, v_sz_boxed_683_, v_i_boxed_684_, v_bs_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(lean_object* v_d_686_, lean_object* v_f_687_){
_start:
{
lean_object* v___f_688_; lean_object* v___x_689_; 
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_688_, 0, v_f_687_);
v___x_689_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v___f_688_, v_d_686_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_690_, lean_object* v_f_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; 
v___f_692_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_692_, 0, v_f_691_);
v___x_693_ = l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(v_d_690_, v___f_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_d_696_, lean_object* v_f_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_DiscrTree_mapArrays___redArg(v_d_696_, v_f_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_d_701_, lean_object* v_f_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(v_d_701_, v_f_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b2_705_, lean_object* v_t_706_, lean_object* v_f_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_t_706_, v_f_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1___redArg(lean_object* v_pm_709_, lean_object* v_f_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_710_, v_pm_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1(lean_object* v_00_u03b2_712_, lean_object* v_00_u03c3_713_, lean_object* v_pm_714_, lean_object* v_f_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_715_, v_pm_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_f_719_, size_t v_sz_720_, size_t v_i_721_, lean_object* v_bs_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_719_, v_sz_720_, v_i_721_, v_bs_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_f_726_, lean_object* v_sz_727_, lean_object* v_i_728_, lean_object* v_bs_729_){
_start:
{
size_t v_sz_boxed_730_; size_t v_i_boxed_731_; lean_object* v_res_732_; 
v_sz_boxed_730_ = lean_unbox_usize(v_sz_727_);
lean_dec(v_sz_727_);
v_i_boxed_731_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(v_00_u03b1_724_, v_00_u03b2_725_, v_f_726_, v_sz_boxed_730_, v_i_boxed_731_, v_bs_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_00_u03c3_735_, lean_object* v_f_736_, lean_object* v_n_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_736_, v_n_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_00_u03c3_741_, lean_object* v_f_742_, size_t v_sz_743_, size_t v_i_744_, lean_object* v_bs_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_742_, v_sz_743_, v_i_744_, v_bs_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_747_, lean_object* v_00_u03b2_748_, lean_object* v_00_u03c3_749_, lean_object* v_f_750_, lean_object* v_sz_751_, lean_object* v_i_752_, lean_object* v_bs_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_751_);
lean_dec(v_sz_751_);
v_i_boxed_755_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(v_00_u03b1_747_, v_00_u03b2_748_, v_00_u03c3_749_, v_f_750_, v_sz_boxed_754_, v_i_boxed_755_, v_bs_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_f_759_, lean_object* v_as_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_759_, v_as_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_f_764_, lean_object* v_as_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_762_, v_00_u03b2_763_, v_f_764_, v_as_765_);
lean_dec_ref(v_as_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b1_767_, lean_object* v_00_u03b2_768_, lean_object* v_f_769_, lean_object* v_as_770_, lean_object* v_i_771_, lean_object* v_acc_772_, lean_object* v_hle_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_769_, v_as_770_, v_i_771_, v_acc_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_f_777_, lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_acc_780_, lean_object* v_hle_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(v_00_u03b1_775_, v_00_u03b2_776_, v_f_777_, v_as_778_, v_i_779_, v_acc_780_, v_hle_781_);
lean_dec_ref(v_as_778_);
return v_res_782_;
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
