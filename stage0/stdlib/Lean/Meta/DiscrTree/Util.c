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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(lean_object* v_children_1_, lean_object* v___x_2_, lean_object* v_toApplicative_3_, lean_object* v_inst_4_, lean_object* v___f_5_, lean_object* v_s_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_array_get_size(v_children_1_);
v___x_8_ = lean_nat_dec_lt(v___x_2_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v_toPure_9_; lean_object* v___x_10_; 
lean_dec(v___f_5_);
lean_dec_ref(v_inst_4_);
lean_dec_ref(v_children_1_);
v_toPure_9_ = lean_ctor_get(v_toApplicative_3_, 1);
lean_inc(v_toPure_9_);
lean_dec_ref(v_toApplicative_3_);
v___x_10_ = lean_apply_2(v_toPure_9_, lean_box(0), v_s_6_);
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_le(v___x_7_, v___x_7_);
if (v___x_11_ == 0)
{
if (v___x_8_ == 0)
{
lean_object* v_toPure_12_; lean_object* v___x_13_; 
lean_dec(v___f_5_);
lean_dec_ref(v_inst_4_);
lean_dec_ref(v_children_1_);
v_toPure_12_ = lean_ctor_get(v_toApplicative_3_, 1);
lean_inc(v_toPure_12_);
lean_dec_ref(v_toApplicative_3_);
v___x_13_ = lean_apply_2(v_toPure_12_, lean_box(0), v_s_6_);
return v___x_13_;
}
else
{
size_t v___x_14_; size_t v___x_15_; lean_object* v___x_16_; 
lean_dec_ref(v_toApplicative_3_);
v___x_14_ = ((size_t)0ULL);
v___x_15_ = lean_usize_of_nat(v___x_7_);
v___x_16_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4_, v___f_5_, v_children_1_, v___x_14_, v___x_15_, v_s_6_);
return v___x_16_;
}
}
else
{
size_t v___x_17_; size_t v___x_18_; lean_object* v___x_19_; 
lean_dec_ref(v_toApplicative_3_);
v___x_17_ = ((size_t)0ULL);
v___x_18_ = lean_usize_of_nat(v___x_7_);
v___x_19_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_4_, v___f_5_, v_children_1_, v___x_17_, v___x_18_, v_s_6_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed(lean_object* v_children_20_, lean_object* v___x_21_, lean_object* v_toApplicative_22_, lean_object* v_inst_23_, lean_object* v___f_24_, lean_object* v_s_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1(v_children_20_, v___x_21_, v_toApplicative_22_, v_inst_23_, v___f_24_, v_s_25_);
lean_dec(v___x_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2(lean_object* v_f_27_, lean_object* v_initialKeys_28_, lean_object* v_s_29_, lean_object* v_v_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_apply_3(v_f_27_, v_s_29_, v_initialKeys_28_, v_v_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg(lean_object* v_inst_32_, lean_object* v_initialKeys_33_, lean_object* v_f_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_toApplicative_37_; lean_object* v_toBind_38_; lean_object* v_vs_39_; lean_object* v_children_40_; lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v_toApplicative_37_ = lean_ctor_get(v_inst_32_, 0);
v_toBind_38_ = lean_ctor_get(v_inst_32_, 1);
lean_inc(v_toBind_38_);
v_vs_39_ = lean_ctor_get(v_x_36_, 0);
lean_inc_ref(v_vs_39_);
v_children_40_ = lean_ctor_get(v_x_36_, 1);
lean_inc_ref(v_children_40_);
lean_dec_ref(v_x_36_);
lean_inc(v_f_34_);
lean_inc_ref_n(v_inst_32_, 2);
lean_inc_ref(v_initialKeys_33_);
v___f_41_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0), 5, 3);
lean_closure_set(v___f_41_, 0, v_initialKeys_33_);
lean_closure_set(v___f_41_, 1, v_inst_32_);
lean_closure_set(v___f_41_, 2, v_f_34_);
v___x_42_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toApplicative_37_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_43_, 0, v_children_40_);
lean_closure_set(v___f_43_, 1, v___x_42_);
lean_closure_set(v___f_43_, 2, v_toApplicative_37_);
lean_closure_set(v___f_43_, 3, v_inst_32_);
lean_closure_set(v___f_43_, 4, v___f_41_);
v___x_44_ = lean_array_get_size(v_vs_39_);
v___x_45_ = lean_nat_dec_lt(v___x_42_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v_toPure_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_inc_ref(v_toApplicative_37_);
lean_dec_ref(v_vs_39_);
lean_dec(v_f_34_);
lean_dec_ref(v_initialKeys_33_);
lean_dec_ref(v_inst_32_);
v_toPure_46_ = lean_ctor_get(v_toApplicative_37_, 1);
lean_inc(v_toPure_46_);
lean_dec_ref(v_toApplicative_37_);
v___x_47_ = lean_apply_2(v_toPure_46_, lean_box(0), v_x_35_);
v___x_48_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v___x_47_, v___f_43_);
return v___x_48_;
}
else
{
lean_object* v___f_49_; uint8_t v___x_50_; 
v___f_49_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_49_, 0, v_f_34_);
lean_closure_set(v___f_49_, 1, v_initialKeys_33_);
v___x_50_ = lean_nat_dec_le(v___x_44_, v___x_44_);
if (v___x_50_ == 0)
{
if (v___x_45_ == 0)
{
lean_object* v_toPure_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_inc_ref(v_toApplicative_37_);
lean_dec_ref(v___f_49_);
lean_dec_ref(v_vs_39_);
lean_dec_ref(v_inst_32_);
v_toPure_51_ = lean_ctor_get(v_toApplicative_37_, 1);
lean_inc(v_toPure_51_);
lean_dec_ref(v_toApplicative_37_);
v___x_52_ = lean_apply_2(v_toPure_51_, lean_box(0), v_x_35_);
v___x_53_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v___x_52_, v___f_43_);
return v___x_53_;
}
else
{
size_t v___x_54_; size_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((size_t)0ULL);
v___x_55_ = lean_usize_of_nat(v___x_44_);
v___x_56_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_32_, v___f_49_, v_vs_39_, v___x_54_, v___x_55_, v_x_35_);
v___x_57_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v___x_56_, v___f_43_);
return v___x_57_;
}
}
else
{
size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((size_t)0ULL);
v___x_59_ = lean_usize_of_nat(v___x_44_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_32_, v___f_49_, v_vs_39_, v___x_58_, v___x_59_, v_x_35_);
v___x_61_ = lean_apply_4(v_toBind_38_, lean_box(0), lean_box(0), v___x_60_, v___f_43_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__0(lean_object* v_initialKeys_62_, lean_object* v_inst_63_, lean_object* v_f_64_, lean_object* v_s_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_fst_67_; lean_object* v_snd_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_fst_67_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_fst_67_);
v_snd_68_ = lean_ctor_get(v_x_66_, 1);
lean_inc(v_snd_68_);
lean_dec_ref(v_x_66_);
v___x_69_ = lean_array_push(v_initialKeys_62_, v_fst_67_);
v___x_70_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_63_, v___x_69_, v_f_64_, v_s_65_, v_snd_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldM(lean_object* v_m_71_, lean_object* v_00_u03c3_72_, lean_object* v_00_u03b1_73_, lean_object* v_inst_74_, lean_object* v_initialKeys_75_, lean_object* v_f_76_, lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_74_, v_initialKeys_75_, v_f_76_, v_x_77_, v_x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0(lean_object* v_f_80_, lean_object* v_s_81_, lean_object* v_k_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_3(v_f_80_, v_s_81_, v_k_82_, v_a_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold___redArg(lean_object* v_initialKeys_104_, lean_object* v_f_105_, lean_object* v_init_106_, lean_object* v_t_107_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___f_108_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_108_, 0, v_f_105_);
v___x_109_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_110_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_109_, v_initialKeys_104_, v___f_108_, v_init_106_, v_t_107_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_fold(lean_object* v_00_u03c3_111_, lean_object* v_00_u03b1_112_, lean_object* v_initialKeys_113_, lean_object* v_f_114_, lean_object* v_init_115_, lean_object* v_t_116_){
_start:
{
lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___f_117_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_117_, 0, v_f_114_);
v___x_118_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_119_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_118_, v_initialKeys_113_, v___f_117_, v_init_115_, v_t_116_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(lean_object* v_inst_120_, lean_object* v_f_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
lean_object* v_toApplicative_124_; lean_object* v_toBind_125_; lean_object* v_vs_126_; lean_object* v_children_127_; lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_toApplicative_124_ = lean_ctor_get(v_inst_120_, 0);
v_toBind_125_ = lean_ctor_get(v_inst_120_, 1);
lean_inc(v_toBind_125_);
v_vs_126_ = lean_ctor_get(v_x_123_, 0);
lean_inc_ref(v_vs_126_);
v_children_127_ = lean_ctor_get(v_x_123_, 1);
lean_inc_ref(v_children_127_);
lean_dec_ref(v_x_123_);
lean_inc(v_f_121_);
lean_inc_ref_n(v_inst_120_, 2);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_128_, 0, v_inst_120_);
lean_closure_set(v___f_128_, 1, v_f_121_);
v___x_129_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toApplicative_124_);
v___f_130_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_130_, 0, v_children_127_);
lean_closure_set(v___f_130_, 1, v___x_129_);
lean_closure_set(v___f_130_, 2, v_toApplicative_124_);
lean_closure_set(v___f_130_, 3, v_inst_120_);
lean_closure_set(v___f_130_, 4, v___f_128_);
v___x_131_ = lean_array_get_size(v_vs_126_);
v___x_132_ = lean_nat_dec_lt(v___x_129_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v_toPure_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_inc_ref(v_toApplicative_124_);
lean_dec_ref(v_vs_126_);
lean_dec(v_f_121_);
lean_dec_ref(v_inst_120_);
v_toPure_133_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_inc(v_toPure_133_);
lean_dec_ref(v_toApplicative_124_);
v___x_134_ = lean_apply_2(v_toPure_133_, lean_box(0), v_x_122_);
v___x_135_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v___x_134_, v___f_130_);
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = lean_nat_dec_le(v___x_131_, v___x_131_);
if (v___x_136_ == 0)
{
if (v___x_132_ == 0)
{
lean_object* v_toPure_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
lean_inc_ref(v_toApplicative_124_);
lean_dec_ref(v_vs_126_);
lean_dec(v_f_121_);
lean_dec_ref(v_inst_120_);
v_toPure_137_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_inc(v_toPure_137_);
lean_dec_ref(v_toApplicative_124_);
v___x_138_ = lean_apply_2(v_toPure_137_, lean_box(0), v_x_122_);
v___x_139_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v___x_138_, v___f_130_);
return v___x_139_;
}
else
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_131_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_120_, v_f_121_, v_vs_126_, v___x_140_, v___x_141_, v_x_122_);
v___x_143_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v___x_142_, v___f_130_);
return v___x_143_;
}
}
else
{
size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = ((size_t)0ULL);
v___x_145_ = lean_usize_of_nat(v___x_131_);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_120_, v_f_121_, v_vs_126_, v___x_144_, v___x_145_, v_x_122_);
v___x_147_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v___x_146_, v___f_130_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg___lam__0(lean_object* v_inst_148_, lean_object* v_f_149_, lean_object* v_s_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_snd_152_; lean_object* v___x_153_; 
v_snd_152_ = lean_ctor_get(v_x_151_, 1);
lean_inc(v_snd_152_);
lean_dec_ref(v_x_151_);
v___x_153_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_148_, v_f_149_, v_s_150_, v_snd_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM(lean_object* v_m_154_, lean_object* v_00_u03c3_155_, lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_157_, v_f_158_, v_x_159_, v_x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0(lean_object* v_f_162_, lean_object* v_x1_163_, lean_object* v_x2_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_apply_2(v_f_162_, v_x1_163_, v_x2_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues___redArg(lean_object* v_f_166_, lean_object* v_init_167_, lean_object* v_t_168_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___f_169_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_169_, 0, v_f_166_);
v___x_170_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_171_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_170_, v___f_169_, v_init_167_, v_t_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValues(lean_object* v_00_u03c3_172_, lean_object* v_00_u03b1_173_, lean_object* v_f_174_, lean_object* v_init_175_, lean_object* v_t_176_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_177_, 0, v_f_174_);
v___x_178_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___x_179_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_178_, v___f_177_, v_init_175_, v_t_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg(lean_object* v_x_180_){
_start:
{
lean_object* v_vs_181_; lean_object* v_children_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_vs_181_ = lean_ctor_get(v_x_180_, 0);
v_children_182_ = lean_ctor_get(v_x_180_, 1);
v___x_183_ = lean_array_get_size(v_vs_181_);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_array_get_size(v_children_182_);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
return v___x_183_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_le(v___x_185_, v___x_185_);
if (v___x_187_ == 0)
{
if (v___x_186_ == 0)
{
return v___x_183_;
}
else
{
size_t v___x_188_; size_t v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((size_t)0ULL);
v___x_189_ = lean_usize_of_nat(v___x_185_);
v___x_190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_182_, v___x_188_, v___x_189_, v___x_183_);
return v___x_190_;
}
}
else
{
size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; 
v___x_191_ = ((size_t)0ULL);
v___x_192_ = lean_usize_of_nat(v___x_185_);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_children_182_, v___x_191_, v___x_192_, v___x_183_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(lean_object* v_as_194_, size_t v_i_195_, size_t v_stop_196_, lean_object* v_b_197_){
_start:
{
uint8_t v___x_198_; 
v___x_198_ = lean_usize_dec_eq(v_i_195_, v_stop_196_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v_snd_200_; lean_object* v___x_201_; lean_object* v___x_202_; size_t v___x_203_; size_t v___x_204_; 
v___x_199_ = lean_array_uget_borrowed(v_as_194_, v_i_195_);
v_snd_200_ = lean_ctor_get(v___x_199_, 1);
v___x_201_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_snd_200_);
v___x_202_ = lean_nat_add(v_b_197_, v___x_201_);
lean_dec(v___x_201_);
lean_dec(v_b_197_);
v___x_203_ = ((size_t)1ULL);
v___x_204_ = lean_usize_add(v_i_195_, v___x_203_);
v_i_195_ = v___x_204_;
v_b_197_ = v___x_202_;
goto _start;
}
else
{
return v_b_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg___boxed(lean_object* v_as_206_, lean_object* v_i_207_, lean_object* v_stop_208_, lean_object* v_b_209_){
_start:
{
size_t v_i_boxed_210_; size_t v_stop_boxed_211_; lean_object* v_res_212_; 
v_i_boxed_210_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_stop_boxed_211_ = lean_unbox_usize(v_stop_208_);
lean_dec(v_stop_208_);
v_res_212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_206_, v_i_boxed_210_, v_stop_boxed_211_, v_b_209_);
lean_dec_ref(v_as_206_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___redArg___boxed(lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_213_);
lean_dec_ref(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size(lean_object* v_00_u03b1_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_size___boxed(lean_object* v_00_u03b1_218_, lean_object* v_x_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_DiscrTree_Trie_size(v_00_u03b1_218_, v_x_219_);
lean_dec_ref(v_x_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(lean_object* v_00_u03b1_221_, lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_, lean_object* v_b_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___redArg(v_as_222_, v_i_223_, v_stop_224_, v_b_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0___boxed(lean_object* v_00_u03b1_227_, lean_object* v_as_228_, lean_object* v_i_229_, lean_object* v_stop_230_, lean_object* v_b_231_){
_start:
{
size_t v_i_boxed_232_; size_t v_stop_boxed_233_; lean_object* v_res_234_; 
v_i_boxed_232_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_stop_boxed_233_ = lean_unbox_usize(v_stop_230_);
lean_dec(v_stop_230_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_size_spec__0(v_00_u03b1_227_, v_as_228_, v_i_boxed_232_, v_stop_boxed_233_, v_b_231_);
lean_dec_ref(v_as_228_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg___lam__0(lean_object* v_inst_235_, lean_object* v_f_236_, lean_object* v_s_237_, lean_object* v_k_238_, lean_object* v_t_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_mk_empty_array_with_capacity(v___x_240_);
v___x_242_ = lean_array_push(v___x_241_, v_k_238_);
v___x_243_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v_inst_235_, v___x_242_, v_f_236_, v_s_237_, v_t_239_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM___redArg(lean_object* v_inst_244_, lean_object* v_f_245_, lean_object* v_init_246_, lean_object* v_t_247_){
_start:
{
lean_object* v___f_248_; lean_object* v___x_249_; 
lean_inc_ref(v_inst_244_);
v___f_248_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_248_, 0, v_inst_244_);
lean_closure_set(v___f_248_, 1, v_f_245_);
v___x_249_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_244_, v___f_248_, v_t_247_, v_init_246_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldM(lean_object* v_m_250_, lean_object* v_00_u03c3_251_, lean_object* v_00_u03b1_252_, lean_object* v_inst_253_, lean_object* v_f_254_, lean_object* v_init_255_, lean_object* v_t_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; 
lean_inc_ref(v_inst_253_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldM___redArg___lam__0), 5, 2);
lean_closure_set(v___f_257_, 0, v_inst_253_);
lean_closure_set(v___f_257_, 1, v_f_254_);
v___x_258_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_253_, v___f_257_, v_t_256_, v_init_255_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__0(lean_object* v_f_259_, lean_object* v_s_260_, lean_object* v_keys_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_apply_3(v_f_259_, v_s_260_, v_keys_261_, v_a_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg___lam__1(lean_object* v___x_264_, lean_object* v___f_265_, lean_object* v_s_266_, lean_object* v_k_267_, lean_object* v_t_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_mk_empty_array_with_capacity(v___x_269_);
v___x_271_ = lean_array_push(v___x_270_, v_k_267_);
v___x_272_ = l_Lean_Meta_DiscrTree_Trie_foldM___redArg(v___x_264_, v___x_271_, v___f_265_, v_s_266_, v_t_268_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold___redArg(lean_object* v_f_273_, lean_object* v_init_274_, lean_object* v_t_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___f_278_; lean_object* v___x_279_; 
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_276_, 0, v_f_273_);
v___x_277_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_278_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_278_, 0, v___x_277_);
lean_closure_set(v___f_278_, 1, v___f_276_);
v___x_279_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_277_, v___f_278_, v_t_275_, v_init_274_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_fold(lean_object* v_00_u03c3_280_, lean_object* v_00_u03b1_281_, lean_object* v_f_282_, lean_object* v_init_283_, lean_object* v_t_284_){
_start:
{
lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_285_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_285_, 0, v_f_282_);
v___x_286_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_287_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_fold___redArg___lam__1), 5, 2);
lean_closure_set(v___f_287_, 0, v___x_286_);
lean_closure_set(v___f_287_, 1, v___f_285_);
v___x_288_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_286_, v___f_287_, v_t_284_, v_init_283_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(lean_object* v_inst_289_, lean_object* v_f_290_, lean_object* v_s_291_, lean_object* v_x_292_, lean_object* v_t_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v_inst_289_, v_f_290_, v_s_291_, v_t_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed(lean_object* v_inst_295_, lean_object* v_f_296_, lean_object* v_s_297_, lean_object* v_x_298_, lean_object* v_t_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0(v_inst_295_, v_f_296_, v_s_297_, v_x_298_, v_t_299_);
lean_dec(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM___redArg(lean_object* v_inst_301_, lean_object* v_f_302_, lean_object* v_init_303_, lean_object* v_t_304_){
_start:
{
lean_object* v___f_305_; lean_object* v___x_306_; 
lean_inc_ref(v_inst_301_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_305_, 0, v_inst_301_);
lean_closure_set(v___f_305_, 1, v_f_302_);
v___x_306_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_301_, v___f_305_, v_t_304_, v_init_303_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValuesM(lean_object* v_m_307_, lean_object* v_00_u03c3_308_, lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_f_311_, lean_object* v_init_312_, lean_object* v_t_313_){
_start:
{
lean_object* v___f_314_; lean_object* v___x_315_; 
lean_inc_ref(v_inst_310_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValuesM___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_314_, 0, v_inst_310_);
lean_closure_set(v___f_314_, 1, v_f_311_);
v___x_315_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_310_, v___f_314_, v_t_313_, v_init_312_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(lean_object* v___x_316_, lean_object* v___f_317_, lean_object* v_s_318_, lean_object* v_x_319_, lean_object* v_t_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_316_, v___f_317_, v_s_318_, v_t_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed(lean_object* v___x_322_, lean_object* v___f_323_, lean_object* v_s_324_, lean_object* v_x_325_, lean_object* v_t_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1(v___x_322_, v___f_323_, v_s_324_, v_x_325_, v_t_326_);
lean_dec(v_x_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues___redArg(lean_object* v_f_328_, lean_object* v_init_329_, lean_object* v_t_330_){
_start:
{
lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___f_333_; lean_object* v___x_334_; 
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_331_, 0, v_f_328_);
v___x_332_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_333_, 0, v___x_332_);
lean_closure_set(v___f_333_, 1, v___f_331_);
v___x_334_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_332_, v___f_333_, v_t_330_, v_init_329_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_foldValues(lean_object* v_00_u03c3_335_, lean_object* v_00_u03b1_336_, lean_object* v_f_337_, lean_object* v_init_338_, lean_object* v_t_339_){
_start:
{
lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_foldValues___redArg___lam__0), 3, 1);
lean_closure_set(v___f_340_, 0, v_f_337_);
v___x_341_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_foldValues___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_342_, 0, v___x_341_);
lean_closure_set(v___f_342_, 1, v___f_340_);
v___x_343_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_341_, v___f_342_, v_t_339_, v_init_338_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(lean_object* v_f_344_, uint8_t v_x1_345_, lean_object* v_x2_346_){
_start:
{
if (v_x1_345_ == 0)
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_apply_1(v_f_344_, v_x2_346_);
v___x_348_ = lean_unbox(v___x_347_);
return v___x_348_;
}
else
{
lean_dec(v_x2_346_);
lean_dec_ref(v_f_344_);
return v_x1_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed(lean_object* v_f_349_, lean_object* v_x1_350_, lean_object* v_x2_351_){
_start:
{
uint8_t v_x1_82__boxed_352_; uint8_t v_res_353_; lean_object* v_r_354_; 
v_x1_82__boxed_352_ = lean_unbox(v_x1_350_);
v_res_353_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0(v_f_349_, v_x1_82__boxed_352_, v_x2_351_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(lean_object* v___x_355_, lean_object* v___f_356_, uint8_t v_s_357_, lean_object* v_x_358_, lean_object* v_t_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = lean_box(v_s_357_);
v___x_361_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_355_, v___f_356_, v___x_360_, v_t_359_);
v___x_362_ = lean_unbox(v___x_361_);
lean_dec(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed(lean_object* v___x_363_, lean_object* v___f_364_, lean_object* v_s_365_, lean_object* v_x_366_, lean_object* v_t_367_){
_start:
{
uint8_t v_s_boxed_368_; uint8_t v_res_369_; lean_object* v_r_370_; 
v_s_boxed_368_ = lean_unbox(v_s_365_);
v_res_369_ = l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1(v___x_363_, v___f_364_, v_s_boxed_368_, v_x_366_, v_t_367_);
lean_dec(v_x_366_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___redArg(lean_object* v_t_371_, lean_object* v_f_372_){
_start:
{
lean_object* v___f_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_373_, 0, v_f_372_);
v___x_374_ = 0;
v___x_375_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_376_, 0, v___x_375_);
lean_closure_set(v___f_376_, 1, v___f_373_);
v___x_377_ = lean_box(v___x_374_);
v___x_378_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_375_, v___f_376_, v_t_371_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_containsValueP(lean_object* v_00_u03b1_379_, lean_object* v_t_380_, lean_object* v_f_381_){
_start:
{
lean_object* v___f_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___f_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_382_, 0, v_f_381_);
v___x_383_ = 0;
v___x_384_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_containsValueP___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_385_, 0, v___x_384_);
lean_closure_set(v___f_385_, 1, v___f_382_);
v___x_386_ = lean_box(v___x_383_);
v___x_387_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_384_, v___f_385_, v_t_380_, v___x_386_);
v___x_388_ = lean_unbox(v___x_387_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_containsValueP___boxed(lean_object* v_00_u03b1_389_, lean_object* v_t_390_, lean_object* v_f_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_Meta_DiscrTree_containsValueP(v_00_u03b1_389_, v_t_390_, v_f_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__0(lean_object* v_x1_394_, lean_object* v_x2_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_array_push(v_x1_394_, v_x2_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1(lean_object* v___x_397_, lean_object* v___f_398_, lean_object* v_s_399_, lean_object* v_x_400_, lean_object* v_t_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___redArg(v___x_397_, v___f_398_, v_s_399_, v_t_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg___lam__1___boxed(lean_object* v___x_403_, lean_object* v___f_404_, lean_object* v_s_405_, lean_object* v_x_406_, lean_object* v_t_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_DiscrTree_values___redArg___lam__1(v___x_403_, v___f_404_, v_s_405_, v_x_406_, v_t_407_);
lean_dec(v_x_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values___redArg(lean_object* v_t_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___f_418_; lean_object* v___x_419_; 
v___x_416_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_417_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_418_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_419_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_417_, v___f_418_, v_t_415_, v___x_416_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_values(lean_object* v_00_u03b1_420_, lean_object* v_t_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___f_424_; lean_object* v___x_425_; 
v___x_422_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__1));
v___x_423_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_424_ = ((lean_object*)(l_Lean_Meta_DiscrTree_values___redArg___closed__2));
v___x_425_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_423_, v___f_424_, v_t_421_, v___x_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__0(lean_object* v_s_426_, lean_object* v_keys_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_keys_427_);
lean_ctor_set(v___x_429_, 1, v_a_428_);
v___x_430_ = lean_array_push(v_s_426_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg___lam__1(lean_object* v___x_431_, lean_object* v___f_432_, lean_object* v_s_433_, lean_object* v_k_434_, lean_object* v_t_435_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray___redArg(lean_object* v_t_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_448_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_449_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_450_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_448_, v___f_449_, v_t_446_, v___x_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_toArray(lean_object* v_00_u03b1_451_, lean_object* v_t_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v___x_453_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__1));
v___x_454_ = ((lean_object*)(l_Lean_Meta_DiscrTree_Trie_fold___redArg___closed__9));
v___f_455_ = ((lean_object*)(l_Lean_Meta_DiscrTree_toArray___redArg___closed__2));
v___x_456_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_454_, v___f_455_, v_t_452_, v___x_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0(lean_object* v_n_457_, lean_object* v_x_458_, lean_object* v_t_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_Lean_Meta_DiscrTree_Trie_size___redArg(v_t_459_);
v___x_461_ = lean_nat_add(v_n_457_, v___x_460_);
lean_dec(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg___lam__0___boxed(lean_object* v_n_462_, lean_object* v_x_463_, lean_object* v_t_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_DiscrTree_size___redArg___lam__0(v_n_462_, v_x_463_, v_t_464_);
lean_dec_ref(v_t_464_);
lean_dec(v_x_463_);
lean_dec(v_n_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size___redArg(lean_object* v_t_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___f_468_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_467_, v___f_468_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_size(lean_object* v_00_u03b1_471_, lean_object* v_t_472_){
_start:
{
lean_object* v___f_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___f_473_ = ((lean_object*)(l_Lean_Meta_DiscrTree_size___redArg___closed__0));
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = l_Lean_PersistentHashMap_foldl___redArg(v_t_472_, v___f_473_, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0(lean_object* v_fst_476_, lean_object* v_toPure_477_, lean_object* v_____do__lift_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_fst_476_);
lean_ctor_set(v___x_479_, 1, v_____do__lift_478_);
v___x_480_ = lean_apply_2(v_toPure_477_, lean_box(0), v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2(lean_object* v_____do__lift_481_, lean_object* v_toPure_482_, lean_object* v_____do__lift_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v_____do__lift_481_);
lean_ctor_set(v___x_484_, 1, v_____do__lift_483_);
v___x_485_ = lean_apply_2(v_toPure_482_, lean_box(0), v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3(lean_object* v_toPure_486_, lean_object* v_children_487_, lean_object* v_inst_488_, lean_object* v___f_489_, lean_object* v_toBind_490_, lean_object* v_____do__lift_491_){
_start:
{
lean_object* v___f_492_; size_t v_sz_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_492_, 0, v_____do__lift_491_);
lean_closure_set(v___f_492_, 1, v_toPure_486_);
v_sz_493_ = lean_array_size(v_children_487_);
v___x_494_ = ((size_t)0ULL);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_488_, v___f_489_, v_sz_493_, v___x_494_, v_children_487_);
v___x_496_ = lean_apply_4(v_toBind_490_, lean_box(0), lean_box(0), v___x_495_, v___f_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(lean_object* v_inst_497_, lean_object* v_t_498_, lean_object* v_f_499_){
_start:
{
lean_object* v_toApplicative_500_; lean_object* v_toBind_501_; lean_object* v_toPure_502_; lean_object* v_vs_503_; lean_object* v_children_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_toApplicative_500_ = lean_ctor_get(v_inst_497_, 0);
v_toBind_501_ = lean_ctor_get(v_inst_497_, 1);
lean_inc_n(v_toBind_501_, 3);
v_toPure_502_ = lean_ctor_get(v_toApplicative_500_, 1);
lean_inc_n(v_toPure_502_, 2);
v_vs_503_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_vs_503_);
v_children_504_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_children_504_);
lean_dec_ref(v_t_498_);
lean_inc(v_f_499_);
lean_inc_ref(v_inst_497_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1), 5, 4);
lean_closure_set(v___f_505_, 0, v_toPure_502_);
lean_closure_set(v___f_505_, 1, v_inst_497_);
lean_closure_set(v___f_505_, 2, v_f_499_);
lean_closure_set(v___f_505_, 3, v_toBind_501_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__3), 6, 5);
lean_closure_set(v___f_506_, 0, v_toPure_502_);
lean_closure_set(v___f_506_, 1, v_children_504_);
lean_closure_set(v___f_506_, 2, v_inst_497_);
lean_closure_set(v___f_506_, 3, v___f_505_);
lean_closure_set(v___f_506_, 4, v_toBind_501_);
v___x_507_ = lean_apply_1(v_f_499_, v_vs_503_);
v___x_508_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v___x_507_, v___f_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__1(lean_object* v_toPure_509_, lean_object* v_inst_510_, lean_object* v_f_511_, lean_object* v_toBind_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_fst_514_; lean_object* v_snd_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_fst_514_ = lean_ctor_get(v_x_513_, 0);
lean_inc(v_fst_514_);
v_snd_515_ = lean_ctor_get(v_x_513_, 1);
lean_inc(v_snd_515_);
lean_dec_ref(v_x_513_);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_516_, 0, v_fst_514_);
lean_closure_set(v___f_516_, 1, v_toPure_509_);
v___x_517_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_510_, v_snd_515_, v_f_511_);
v___x_518_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_517_, v___f_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM(lean_object* v_m_519_, lean_object* v_inst_520_, lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_t_523_, lean_object* v_f_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_520_, v_t_523_, v_f_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0(lean_object* v_inst_526_, lean_object* v_f_527_, lean_object* v_t_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___redArg(v_inst_526_, v_t_528_, v_f_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1(lean_object* v_toPure_530_, lean_object* v_____do__lift_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_apply_2(v_toPure_530_, lean_box(0), v_____do__lift_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___redArg(lean_object* v_inst_533_, lean_object* v_d_534_, lean_object* v_f_535_){
_start:
{
lean_object* v_toApplicative_536_; lean_object* v_toBind_537_; lean_object* v_toPure_538_; lean_object* v___f_539_; lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_toApplicative_536_ = lean_ctor_get(v_inst_533_, 0);
v_toBind_537_ = lean_ctor_get(v_inst_533_, 1);
lean_inc(v_toBind_537_);
v_toPure_538_ = lean_ctor_get(v_toApplicative_536_, 1);
lean_inc_ref(v_inst_533_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_539_, 0, v_inst_533_);
lean_closure_set(v___f_539_, 1, v_f_535_);
lean_inc(v_toPure_538_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_540_, 0, v_toPure_538_);
v___x_541_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_533_, v_d_534_, v___f_539_);
v___x_542_ = lean_apply_4(v_toBind_537_, lean_box(0), lean_box(0), v___x_541_, v___f_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM(lean_object* v_m_543_, lean_object* v_inst_544_, lean_object* v_00_u03b1_545_, lean_object* v_00_u03b2_546_, lean_object* v_d_547_, lean_object* v_f_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_DiscrTree_mapArraysM___redArg(v_inst_544_, v_d_547_, v_f_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0(lean_object* v_f_550_, lean_object* v_A_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_apply_1(v_f_550_, v_A_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(lean_object* v_f_553_, size_t v_sz_554_, size_t v_i_555_, lean_object* v_bs_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
if (v___x_557_ == 0)
{
lean_dec_ref(v_f_553_);
return v_bs_556_;
}
else
{
lean_object* v_v_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_574_; 
v_v_558_ = lean_array_uget(v_bs_556_, v_i_555_);
v_fst_559_ = lean_ctor_get(v_v_558_, 0);
v_snd_560_ = lean_ctor_get(v_v_558_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_v_558_);
if (v_isSharedCheck_574_ == 0)
{
v___x_562_ = v_v_558_;
v_isShared_563_ = v_isSharedCheck_574_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snd_560_);
lean_inc(v_fst_559_);
lean_dec(v_v_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_574_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v_bs_x27_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v_bs_x27_565_ = lean_array_uset(v_bs_556_, v_i_555_, v___x_564_);
lean_inc_ref(v_f_553_);
v___x_566_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_snd_560_, v_f_553_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_566_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_fst_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_566_);
v___x_568_ = v_reuseFailAlloc_573_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_555_, v___x_569_);
v___x_571_ = lean_array_uset(v_bs_x27_565_, v_i_555_, v___x_568_);
v_i_555_ = v___x_570_;
v_bs_556_ = v___x_571_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(lean_object* v_t_575_, lean_object* v_f_576_){
_start:
{
lean_object* v_vs_577_; lean_object* v_children_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_589_; 
v_vs_577_ = lean_ctor_get(v_t_575_, 0);
v_children_578_ = lean_ctor_get(v_t_575_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_t_575_);
if (v_isSharedCheck_589_ == 0)
{
v___x_580_ = v_t_575_;
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_children_578_);
lean_inc(v_vs_577_);
lean_dec(v_t_575_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; size_t v_sz_583_; size_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
lean_inc_ref(v_f_576_);
v___x_582_ = lean_apply_1(v_f_576_, v_vs_577_);
v_sz_583_ = lean_array_size(v_children_578_);
v___x_584_ = ((size_t)0ULL);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_576_, v_sz_583_, v___x_584_, v_children_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_585_);
lean_ctor_set(v___x_580_, 0, v___x_582_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_590_, lean_object* v_sz_591_, lean_object* v_i_592_, lean_object* v_bs_593_){
_start:
{
size_t v_sz_boxed_594_; size_t v_i_boxed_595_; lean_object* v_res_596_; 
v_sz_boxed_594_ = lean_unbox_usize(v_sz_591_);
lean_dec(v_sz_591_);
v_i_boxed_595_ = lean_unbox_usize(v_i_592_);
lean_dec(v_i_592_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_590_, v_sz_boxed_594_, v_i_boxed_595_, v_bs_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0(lean_object* v_f_597_, lean_object* v_t_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_t_598_, v_f_597_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_f_600_, lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_acc_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_as_601_);
v___x_605_ = lean_nat_dec_eq(v_i_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_606_ = lean_array_fget_borrowed(v_as_601_, v_i_602_);
lean_inc(v_f_600_);
lean_inc(v___x_606_);
v___x_607_ = lean_apply_1(v_f_600_, v___x_606_);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_i_602_, v___x_608_);
lean_dec(v_i_602_);
v___x_610_ = lean_array_push(v_acc_603_, v___x_607_);
v_i_602_ = v___x_609_;
v_acc_603_ = v___x_610_;
goto _start;
}
else
{
lean_dec(v_i_602_);
lean_dec(v_f_600_);
return v_acc_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_f_612_, lean_object* v_as_613_, lean_object* v_i_614_, lean_object* v_acc_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_612_, v_as_613_, v_i_614_, v_acc_615_);
lean_dec_ref(v_as_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_617_, lean_object* v_as_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_array_get_size(v_as_618_);
v___x_621_ = lean_mk_empty_array_with_capacity(v___x_620_);
v___x_622_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_617_, v_as_618_, v___x_619_, v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_623_, lean_object* v_as_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_623_, v_as_624_);
lean_dec_ref(v_as_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_f_626_, size_t v_sz_627_, size_t v_i_628_, lean_object* v_bs_629_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_lt(v_i_628_, v_sz_627_);
if (v___x_630_ == 0)
{
lean_dec(v_f_626_);
return v_bs_629_;
}
else
{
lean_object* v_v_631_; lean_object* v___x_632_; lean_object* v_bs_x27_633_; lean_object* v___y_635_; 
v_v_631_ = lean_array_uget(v_bs_629_, v_i_628_);
v___x_632_ = lean_unsigned_to_nat(0u);
v_bs_x27_633_ = lean_array_uset(v_bs_629_, v_i_628_, v___x_632_);
switch(lean_obj_tag(v_v_631_))
{
case 0:
{
lean_object* v_key_640_; lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
v_key_640_ = lean_ctor_get(v_v_631_, 0);
v_val_641_ = lean_ctor_get(v_v_631_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_v_631_);
if (v_isSharedCheck_649_ == 0)
{
v___x_643_ = v_v_631_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_inc(v_key_640_);
lean_dec(v_v_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
lean_inc(v_f_626_);
v___x_645_ = lean_apply_1(v_f_626_, v_val_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_key_640_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
v___y_635_ = v___x_647_;
goto v___jp_634_;
}
}
}
case 1:
{
lean_object* v_node_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_node_650_ = lean_ctor_get(v_v_631_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_v_631_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v_v_631_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_node_650_);
lean_dec(v_v_631_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
lean_inc(v_f_626_);
v___x_654_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_626_, v_node_650_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_635_ = v___x_656_;
goto v___jp_634_;
}
}
}
default: 
{
lean_object* v___x_659_; 
v___x_659_ = lean_box(2);
v___y_635_ = v___x_659_;
goto v___jp_634_;
}
}
v___jp_634_:
{
size_t v___x_636_; size_t v___x_637_; lean_object* v___x_638_; 
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_add(v_i_628_, v___x_636_);
v___x_638_ = lean_array_uset(v_bs_x27_633_, v_i_628_, v___y_635_);
v_i_628_ = v___x_637_;
v_bs_629_ = v___x_638_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(lean_object* v_f_660_, lean_object* v_n_661_){
_start:
{
if (lean_obj_tag(v_n_661_) == 0)
{
lean_object* v_es_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_672_; 
v_es_662_ = lean_ctor_get(v_n_661_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_n_661_);
if (v_isSharedCheck_672_ == 0)
{
v___x_664_ = v_n_661_;
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_es_662_);
lean_dec(v_n_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
size_t v_sz_666_; size_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_sz_666_ = lean_array_size(v_es_662_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_660_, v_sz_666_, v___x_667_, v_es_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_668_);
v___x_670_ = v___x_664_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v_ks_673_; lean_object* v_vs_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_ks_673_ = lean_ctor_get(v_n_661_, 0);
v_vs_674_ = lean_ctor_get(v_n_661_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_n_661_);
if (v_isSharedCheck_682_ == 0)
{
v___x_676_ = v_n_661_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_vs_674_);
lean_inc(v_ks_673_);
lean_dec(v_n_661_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_val_678_; lean_object* v___x_680_; 
v_val_678_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_660_, v_vs_674_);
lean_dec_ref(v_vs_674_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_val_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_ks_673_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_val_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_683_, lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_bs_686_){
_start:
{
size_t v_sz_boxed_687_; size_t v_i_boxed_688_; lean_object* v_res_689_; 
v_sz_boxed_687_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_688_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_683_, v_sz_boxed_687_, v_i_boxed_688_, v_bs_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(lean_object* v_d_690_, lean_object* v_f_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; 
v___f_692_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_692_, 0, v_f_691_);
v___x_693_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v___f_692_, v_d_690_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays___redArg(lean_object* v_d_694_, lean_object* v_f_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_mapArrays___redArg___lam__0), 2, 1);
lean_closure_set(v___f_696_, 0, v_f_695_);
v___x_697_ = l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(v_d_694_, v___f_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArrays(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_d_700_, lean_object* v_f_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_DiscrTree_mapArrays___redArg(v_d_700_, v_f_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_d_705_, lean_object* v_f_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0___redArg(v_d_705_, v_f_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_t_710_, lean_object* v_f_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0___redArg(v_t_710_, v_f_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1___redArg(lean_object* v_pm_713_, lean_object* v_f_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_714_, v_pm_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1(lean_object* v_00_u03b2_716_, lean_object* v_00_u03c3_717_, lean_object* v_pm_718_, lean_object* v_f_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_719_, v_pm_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_f_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_bs_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___redArg(v_f_723_, v_sz_724_, v_i_725_, v_bs_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_f_730_, lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_bs_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_735_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_Trie_mapArraysM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__0_spec__1(v_00_u03b1_728_, v_00_u03b2_729_, v_f_730_, v_sz_boxed_734_, v_i_boxed_735_, v_bs_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_00_u03c3_739_, lean_object* v_f_740_, lean_object* v_n_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3___redArg(v_f_740_, v_n_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_00_u03c3_745_, lean_object* v_f_746_, size_t v_sz_747_, size_t v_i_748_, lean_object* v_bs_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___redArg(v_f_746_, v_sz_747_, v_i_748_, v_bs_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_751_, lean_object* v_00_u03b2_752_, lean_object* v_00_u03c3_753_, lean_object* v_f_754_, lean_object* v_sz_755_, lean_object* v_i_756_, lean_object* v_bs_757_){
_start:
{
size_t v_sz_boxed_758_; size_t v_i_boxed_759_; lean_object* v_res_760_; 
v_sz_boxed_758_ = lean_unbox_usize(v_sz_755_);
lean_dec(v_sz_755_);
v_i_boxed_759_ = lean_unbox_usize(v_i_756_);
lean_dec(v_i_756_);
v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__4(v_00_u03b1_751_, v_00_u03b2_752_, v_00_u03c3_753_, v_f_754_, v_sz_boxed_758_, v_i_boxed_759_, v_bs_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_f_763_, lean_object* v_as_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___redArg(v_f_763_, v_as_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_766_, lean_object* v_00_u03b2_767_, lean_object* v_f_768_, lean_object* v_as_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_766_, v_00_u03b2_767_, v_f_768_, v_as_769_);
lean_dec_ref(v_as_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b1_771_, lean_object* v_00_u03b2_772_, lean_object* v_f_773_, lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_acc_776_, lean_object* v_hle_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_f_773_, v_as_774_, v_i_775_, v_acc_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_f_781_, lean_object* v_as_782_, lean_object* v_i_783_, lean_object* v_acc_784_, lean_object* v_hle_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_Meta_DiscrTree_mapArraysM___at___00Lean_Meta_DiscrTree_mapArrays_spec__0_spec__1_spec__3_spec__5_spec__6(v_00_u03b1_779_, v_00_u03b2_780_, v_f_781_, v_as_782_, v_i_783_, v_acc_784_, v_hle_785_);
lean_dec_ref(v_as_782_);
return v_res_786_;
}
}
lean_object* runtime_initialize_Lean_Meta_DiscrTree_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_DiscrTree_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
