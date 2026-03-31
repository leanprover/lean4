// Lean compiler output
// Module: Lean.Data.SMap
// Imports: public import Std.Data.HashMap.Basic public import Lean.Data.PersistentHashMap public import Std.Data.HashMap.Iterator public import Lean.Data.Iterators.Producers.PersistentHashMap public import Init.Data.Iterators.Combinators.Append
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_Zipper_prependNode___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__0;
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__1;
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__2;
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__3;
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__4;
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_findD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_findD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_SMap_find_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Data.SMap"};
static const lean_object* l_Lean_SMap_find_x21___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_find_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_SMap_find_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.SMap.find!"};
static const lean_object* l_Lean_SMap_find_x21___redArg___closed__1 = (const lean_object*)&l_Lean_SMap_find_x21___redArg___closed__1_value;
static const lean_string_object l_Lean_SMap_find_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_Lean_SMap_find_x21___redArg___closed__2 = (const lean_object*)&l_Lean_SMap_find_x21___redArg___closed__2_value;
static lean_once_cell_t l_Lean_SMap_find_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_find_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__0_value;
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__1 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__1_value;
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__2 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__2_value;
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__3 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__3_value;
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__4 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__4_value;
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__5 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__5_value;
static const lean_closure_object l_Lean_SMap_fold___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_fold___redArg___closed__6 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__6_value;
static const lean_ctor_object l_Lean_SMap_fold___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_SMap_fold___redArg___closed__0_value),((lean_object*)&l_Lean_SMap_fold___redArg___closed__1_value)}};
static const lean_object* l_Lean_SMap_fold___redArg___closed__7 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__7_value;
static const lean_ctor_object l_Lean_SMap_fold___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_SMap_fold___redArg___closed__7_value),((lean_object*)&l_Lean_SMap_fold___redArg___closed__2_value),((lean_object*)&l_Lean_SMap_fold___redArg___closed__3_value),((lean_object*)&l_Lean_SMap_fold___redArg___closed__4_value),((lean_object*)&l_Lean_SMap_fold___redArg___closed__5_value)}};
static const lean_object* l_Lean_SMap_fold___redArg___closed__8 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__8_value;
static const lean_ctor_object l_Lean_SMap_fold___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_SMap_fold___redArg___closed__8_value),((lean_object*)&l_Lean_SMap_fold___redArg___closed__6_value)}};
static const lean_object* l_Lean_SMap_fold___redArg___closed__9 = (const lean_object*)&l_Lean_SMap_fold___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprSMap___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".toSMap"};
static const lean_object* l_Lean_instReprSMap___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprSMap___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprSMap___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprSMap___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprSMap___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprSMap___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_SMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__0, &l_Lean_SMap_instInhabited___closed__0_once, _init_l_Lean_SMap_instInhabited___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__2(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_7_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__2, &l_Lean_SMap_instInhabited___closed__2_once, _init_l_Lean_SMap_instInhabited___closed__2);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__3, &l_Lean_SMap_instInhabited___closed__3_once, _init_l_Lean_SMap_instInhabited___closed__3);
v___x_11_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__1, &l_Lean_SMap_instInhabited___closed__1_once, _init_l_Lean_SMap_instInhabited___closed__1);
v___x_12_ = 1;
v___x_13_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_10_);
lean_ctor_set_uint8(v___x_13_, sizeof(void*)*2, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited(lean_object* v_00_u03b1_14_, lean_object* v_00_u03b2_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___boxed(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_SMap_instInhabited(v_00_u03b1_19_, v_00_u03b2_20_, v_inst_21_, v_inst_22_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_SMap_empty(v_00_u03b1_29_, v_00_u03b2_30_, v_inst_31_, v_inst_32_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg(lean_object* v_m_34_, uint8_t v_stage_u2081_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__3, &l_Lean_SMap_instInhabited___closed__3_once, _init_l_Lean_SMap_instInhabited___closed__3);
v___x_37_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_37_, 0, v_m_34_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*2, v_stage_u2081_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg___boxed(lean_object* v_m_38_, lean_object* v_stage_u2081_39_){
_start:
{
uint8_t v_stage_u2081_boxed_40_; lean_object* v_res_41_; 
v_stage_u2081_boxed_40_ = lean_unbox(v_stage_u2081_39_);
v_res_41_ = l_Lean_SMap_fromHashMap___redArg(v_m_38_, v_stage_u2081_boxed_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap(lean_object* v_00_u03b1_42_, lean_object* v_00_u03b2_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_m_46_, uint8_t v_stage_u2081_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__3, &l_Lean_SMap_instInhabited___closed__3_once, _init_l_Lean_SMap_instInhabited___closed__3);
v___x_49_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_49_, 0, v_m_46_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*2, v_stage_u2081_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___boxed(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_m_54_, lean_object* v_stage_u2081_55_){
_start:
{
uint8_t v_stage_u2081_boxed_56_; lean_object* v_res_57_; 
v_stage_u2081_boxed_56_ = lean_unbox(v_stage_u2081_55_);
v_res_57_ = l_Lean_SMap_fromHashMap(v_00_u03b1_50_, v_00_u03b2_51_, v_inst_52_, v_inst_53_, v_m_54_, v_stage_u2081_boxed_56_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___redArg(lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_stage_u2081_63_; 
v_stage_u2081_63_ = lean_ctor_get_uint8(v_x_60_, sizeof(void*)*2);
if (v_stage_u2081_63_ == 0)
{
lean_object* v_map_u2081_64_; lean_object* v_map_u2082_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_73_; 
v_map_u2081_64_ = lean_ctor_get(v_x_60_, 0);
v_map_u2082_65_ = lean_ctor_get(v_x_60_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_73_ == 0)
{
v___x_67_ = v_x_60_;
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_map_u2082_65_);
lean_inc(v_map_u2081_64_);
lean_dec(v_x_60_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_73_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_58_, v_inst_59_, v_map_u2082_65_, v_x_61_, v_x_62_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_69_);
v___x_71_ = v___x_67_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v_map_u2081_64_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_69_);
lean_ctor_set_uint8(v_reuseFailAlloc_72_, sizeof(void*)*2, v_stage_u2081_63_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
else
{
lean_object* v_map_u2081_74_; lean_object* v_map_u2082_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_83_; 
v_map_u2081_74_ = lean_ctor_get(v_x_60_, 0);
v_map_u2082_75_ = lean_ctor_get(v_x_60_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_83_ == 0)
{
v___x_77_ = v_x_60_;
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_map_u2082_75_);
lean_inc(v_map_u2081_74_);
lean_dec(v_x_60_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_58_, v_inst_59_, v_map_u2081_74_, v_x_61_, v_x_62_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_map_u2082_75_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*2, v_stage_u2081_63_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_SMap_insert___redArg(v_inst_86_, v_inst_87_, v_x_88_, v_x_89_, v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27___redArg(lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_stage_u2081_97_; 
v_stage_u2081_97_ = lean_ctor_get_uint8(v_x_94_, sizeof(void*)*2);
if (v_stage_u2081_97_ == 0)
{
lean_object* v_map_u2081_98_; lean_object* v_map_u2082_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_map_u2081_98_ = lean_ctor_get(v_x_94_, 0);
v_map_u2082_99_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v_x_94_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_map_u2082_99_);
lean_inc(v_map_u2081_98_);
lean_dec(v_x_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_92_, v_inst_93_, v_map_u2082_99_, v_x_95_, v_x_96_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_map_u2081_98_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
lean_ctor_set_uint8(v_reuseFailAlloc_106_, sizeof(void*)*2, v_stage_u2081_97_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
else
{
lean_object* v_map_u2081_108_; lean_object* v_map_u2082_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_map_u2081_108_ = lean_ctor_get(v_x_94_, 0);
v_map_u2082_109_ = lean_ctor_get(v_x_94_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v_x_94_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_map_u2082_109_);
lean_inc(v_map_u2081_108_);
lean_dec(v_x_94_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_92_, v_inst_93_, v_map_u2081_108_, v_x_95_, v_x_96_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_map_u2082_109_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*2, v_stage_u2081_97_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_SMap_insert_x27___redArg(v_inst_120_, v_inst_121_, v_x_122_, v_x_123_, v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_stage_u2081_130_; 
v_stage_u2081_130_ = lean_ctor_get_uint8(v_x_128_, sizeof(void*)*2);
if (v_stage_u2081_130_ == 0)
{
lean_object* v_map_u2081_131_; lean_object* v_map_u2082_132_; lean_object* v___x_133_; 
v_map_u2081_131_ = lean_ctor_get(v_x_128_, 0);
lean_inc_ref(v_map_u2081_131_);
v_map_u2082_132_ = lean_ctor_get(v_x_128_, 1);
lean_inc_ref(v_map_u2082_132_);
lean_dec_ref(v_x_128_);
lean_inc(v_x_129_);
lean_inc_ref(v_inst_127_);
lean_inc_ref(v_inst_126_);
v___x_133_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_126_, v_inst_127_, v_map_u2082_132_, v_x_129_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_126_, v_inst_127_, v_map_u2081_131_, v_x_129_);
lean_dec_ref(v_map_u2081_131_);
return v___x_134_;
}
else
{
lean_dec_ref(v_map_u2081_131_);
lean_dec(v_x_129_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
return v___x_133_;
}
}
else
{
lean_object* v_map_u2081_135_; lean_object* v___x_136_; 
v_map_u2081_135_ = lean_ctor_get(v_x_128_, 0);
lean_inc_ref(v_map_u2081_135_);
lean_dec_ref(v_x_128_);
v___x_136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_126_, v_inst_127_, v_map_u2081_135_, v_x_129_);
lean_dec_ref(v_map_u2081_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object* v_00_u03b1_137_, lean_object* v_00_u03b2_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_SMap_find_x3f___redArg(v_inst_139_, v_inst_140_, v_x_141_, v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_m_146_, lean_object* v_a_147_, lean_object* v_b_u2080_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_SMap_find_x3f___redArg(v_inst_144_, v_inst_145_, v_m_146_, v_a_147_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_inc(v_b_u2080_148_);
return v_b_u2080_148_;
}
else
{
lean_object* v_val_150_; 
v_val_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_150_);
lean_dec_ref(v___x_149_);
return v_val_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg___boxed(lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_m_153_, lean_object* v_a_154_, lean_object* v_b_u2080_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_SMap_findD___redArg(v_inst_151_, v_inst_152_, v_m_153_, v_a_154_, v_b_u2080_155_);
lean_dec(v_b_u2080_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_m_161_, lean_object* v_a_162_, lean_object* v_b_u2080_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_SMap_find_x3f___redArg(v_inst_159_, v_inst_160_, v_m_161_, v_a_162_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_inc(v_b_u2080_163_);
return v_b_u2080_163_;
}
else
{
lean_object* v_val_165_; 
v_val_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_val_165_);
lean_dec_ref(v___x_164_);
return v_val_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_m_170_, lean_object* v_a_171_, lean_object* v_b_u2080_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_SMap_findD(v_00_u03b1_166_, v_00_u03b2_167_, v_inst_168_, v_inst_169_, v_m_170_, v_a_171_, v_b_u2080_172_);
lean_dec(v_b_u2080_172_);
return v_res_173_;
}
}
static lean_object* _init_l_Lean_SMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__2));
v___x_178_ = lean_unsigned_to_nat(14u);
v___x_179_ = lean_unsigned_to_nat(70u);
v___x_180_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__1));
v___x_181_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__0));
v___x_182_ = l_mkPanicMessageWithDecl(v___x_181_, v___x_180_, v___x_179_, v___x_178_, v___x_177_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_m_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_SMap_find_x3f___redArg(v_inst_183_, v_inst_184_, v_m_186_, v_a_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_190_ = l_panic___redArg(v_inst_185_, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; 
v_val_191_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v___x_188_);
return v_val_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg___boxed(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_m_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_SMap_find_x21___redArg(v_inst_192_, v_inst_193_, v_inst_194_, v_m_195_, v_a_196_);
lean_dec(v_inst_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_m_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_SMap_find_x3f___redArg(v_inst_200_, v_inst_201_, v_m_203_, v_a_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_207_ = l_panic___redArg(v_inst_202_, v___x_206_);
return v___x_207_;
}
else
{
lean_object* v_val_208_; 
v_val_208_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_208_);
lean_dec_ref(v___x_205_);
return v_val_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___boxed(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_m_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_SMap_find_x21(v_00_u03b1_209_, v_00_u03b2_210_, v_inst_211_, v_inst_212_, v_inst_213_, v_m_214_, v_a_215_);
lean_dec(v_inst_213_);
return v_res_216_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___redArg(lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
uint8_t v_stage_u2081_221_; 
v_stage_u2081_221_ = lean_ctor_get_uint8(v_x_219_, sizeof(void*)*2);
if (v_stage_u2081_221_ == 0)
{
lean_object* v_map_u2081_222_; lean_object* v_map_u2082_223_; uint8_t v___x_224_; 
v_map_u2081_222_ = lean_ctor_get(v_x_219_, 0);
lean_inc_ref(v_map_u2081_222_);
v_map_u2082_223_ = lean_ctor_get(v_x_219_, 1);
lean_inc_ref(v_map_u2082_223_);
lean_dec_ref(v_x_219_);
lean_inc(v_x_220_);
lean_inc_ref(v_inst_218_);
lean_inc_ref(v_inst_217_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_217_, v_inst_218_, v_map_u2081_222_, v_x_220_);
lean_dec_ref(v_map_u2081_222_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_217_, v_inst_218_, v_map_u2082_223_, v_x_220_);
return v___x_225_;
}
else
{
lean_dec_ref(v_map_u2082_223_);
lean_dec(v_x_220_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_inst_217_);
return v___x_224_;
}
}
else
{
lean_object* v_map_u2081_226_; uint8_t v___x_227_; 
v_map_u2081_226_ = lean_ctor_get(v_x_219_, 0);
lean_inc_ref(v_map_u2081_226_);
lean_dec_ref(v_x_219_);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_217_, v_inst_218_, v_map_u2081_226_, v_x_220_);
lean_dec_ref(v_map_u2081_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Lean_SMap_contains___redArg(v_inst_228_, v_inst_229_, v_x_230_, v_x_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = l_Lean_SMap_contains___redArg(v_inst_236_, v_inst_237_, v_x_238_, v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_SMap_contains(v_00_u03b1_241_, v_00_u03b2_242_, v_inst_243_, v_inst_244_, v_x_245_, v_x_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_stage_u2081_253_; 
v_stage_u2081_253_ = lean_ctor_get_uint8(v_x_251_, sizeof(void*)*2);
if (v_stage_u2081_253_ == 0)
{
lean_object* v_map_u2081_254_; lean_object* v_map_u2082_255_; lean_object* v___x_256_; 
v_map_u2081_254_ = lean_ctor_get(v_x_251_, 0);
lean_inc_ref(v_map_u2081_254_);
v_map_u2082_255_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_map_u2082_255_);
lean_dec_ref(v_x_251_);
lean_inc(v_x_252_);
lean_inc_ref(v_inst_250_);
lean_inc_ref(v_inst_249_);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_249_, v_inst_250_, v_map_u2081_254_, v_x_252_);
lean_dec_ref(v_map_u2081_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_249_, v_inst_250_, v_map_u2082_255_, v_x_252_);
return v___x_257_;
}
else
{
lean_dec_ref(v_map_u2082_255_);
lean_dec(v_x_252_);
lean_dec_ref(v_inst_250_);
lean_dec_ref(v_inst_249_);
return v___x_256_;
}
}
else
{
lean_object* v_map_u2081_258_; lean_object* v___x_259_; 
v_map_u2081_258_ = lean_ctor_get(v_x_251_, 0);
lean_inc_ref(v_map_u2081_258_);
lean_dec_ref(v_x_251_);
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_249_, v_inst_250_, v_map_u2081_258_, v_x_252_);
lean_dec_ref(v_map_u2081_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object* v_00_u03b1_260_, lean_object* v_00_u03b2_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_262_, v_inst_263_, v_x_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object* v_inst_267_, lean_object* v_map_u2082_268_, lean_object* v_f_269_, lean_object* v_____r_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_267_, v_map_u2082_268_, v_f_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object* v_f_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_apply_2(v_f_272_, v___y_274_, v___y_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__2(lean_object* v_inst_277_, lean_object* v___f_278_, lean_object* v_x_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_box(0);
v___x_282_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_277_, v___f_278_, v___x_281_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object* v_inst_283_, lean_object* v_s_284_, lean_object* v_f_285_){
_start:
{
lean_object* v_map_u2081_286_; lean_object* v_toApplicative_287_; lean_object* v_toBind_288_; lean_object* v_map_u2082_289_; lean_object* v_buckets_290_; lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_map_u2081_286_ = lean_ctor_get(v_s_284_, 0);
lean_inc_ref(v_map_u2081_286_);
v_toApplicative_287_ = lean_ctor_get(v_inst_283_, 0);
v_toBind_288_ = lean_ctor_get(v_inst_283_, 1);
lean_inc(v_toBind_288_);
v_map_u2082_289_ = lean_ctor_get(v_s_284_, 1);
lean_inc_ref(v_map_u2082_289_);
lean_dec_ref(v_s_284_);
v_buckets_290_ = lean_ctor_get(v_map_u2081_286_, 1);
lean_inc_ref(v_buckets_290_);
lean_dec_ref(v_map_u2081_286_);
lean_inc(v_f_285_);
lean_inc_ref(v_inst_283_);
v___f_291_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_291_, 0, v_inst_283_);
lean_closure_set(v___f_291_, 1, v_map_u2082_289_);
lean_closure_set(v___f_291_, 2, v_f_285_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_buckets_290_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_295_ == 0)
{
lean_object* v_toPure_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_inc_ref(v_toApplicative_287_);
lean_dec_ref(v_buckets_290_);
lean_dec(v_f_285_);
lean_dec_ref(v_inst_283_);
v_toPure_296_ = lean_ctor_get(v_toApplicative_287_, 1);
lean_inc(v_toPure_296_);
lean_dec_ref(v_toApplicative_287_);
v___x_297_ = lean_apply_2(v_toPure_296_, lean_box(0), v___x_294_);
v___x_298_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_297_, v___f_291_);
return v___x_298_;
}
else
{
lean_object* v___f_299_; lean_object* v___f_300_; uint8_t v___x_301_; 
v___f_299_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 1);
lean_closure_set(v___f_299_, 0, v_f_285_);
lean_inc_ref(v_inst_283_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_300_, 0, v_inst_283_);
lean_closure_set(v___f_300_, 1, v___f_299_);
v___x_301_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_301_ == 0)
{
if (v___x_295_ == 0)
{
lean_object* v_toPure_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc_ref(v_toApplicative_287_);
lean_dec_ref(v___f_300_);
lean_dec_ref(v_buckets_290_);
lean_dec_ref(v_inst_283_);
v_toPure_302_ = lean_ctor_get(v_toApplicative_287_, 1);
lean_inc(v_toPure_302_);
lean_dec_ref(v_toApplicative_287_);
v___x_303_ = lean_apply_2(v_toPure_302_, lean_box(0), v___x_294_);
v___x_304_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_303_, v___f_291_);
return v___x_304_;
}
else
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_293_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_283_, v___f_300_, v_buckets_290_, v___x_305_, v___x_306_, v___x_294_);
v___x_308_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_307_, v___f_291_);
return v___x_308_;
}
}
else
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_293_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_283_, v___f_300_, v_buckets_290_, v___x_309_, v___x_310_, v___x_294_);
v___x_312_ = lean_apply_4(v_toBind_288_, lean_box(0), lean_box(0), v___x_311_, v___f_291_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_m_317_, lean_object* v_inst_318_, lean_object* v_s_319_, lean_object* v_f_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_SMap_forM___redArg(v_inst_318_, v_s_319_, v_f_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_m_326_, lean_object* v_inst_327_, lean_object* v_s_328_, lean_object* v_f_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_SMap_forM(v_00_u03b1_322_, v_00_u03b2_323_, v_inst_324_, v_inst_325_, v_m_326_, v_inst_327_, v_s_328_, v_f_329_);
lean_dec_ref(v_inst_325_);
lean_dec_ref(v_inst_324_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_331_, lean_object* v_x_332_, lean_object* v_y_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_x_332_);
lean_ctor_set(v___x_334_, 1, v_y_333_);
v___x_335_ = lean_apply_1(v_f_331_, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_336_, lean_object* v_s_337_, lean_object* v_f_338_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; 
v___f_339_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_339_, 0, v_f_338_);
v___x_340_ = l_Lean_SMap_forM___redArg(v_inst_336_, v_s_337_, v___f_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_341_){
_start:
{
lean_object* v___f_342_; 
v___f_342_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_342_, 0, v_inst_341_);
return v___f_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_m_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___f_349_; 
v___f_349_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_349_, 0, v_inst_348_);
return v___f_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_m_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_350_, v_00_u03b2_351_, v_inst_352_, v_inst_353_, v_m_354_, v_inst_355_);
lean_dec_ref(v_inst_353_);
lean_dec_ref(v_inst_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_357_, lean_object* v_____do__lift_358_){
_start:
{
if (lean_obj_tag(v_____do__lift_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v_____do__lift_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v_____do__lift_358_);
v___x_360_ = lean_apply_2(v_toPure_357_, lean_box(0), v_a_359_);
return v___x_360_;
}
else
{
lean_object* v_a_361_; lean_object* v_snd_362_; lean_object* v___x_363_; 
v_a_361_ = lean_ctor_get(v_____do__lift_358_, 0);
lean_inc(v_a_361_);
lean_dec_ref(v_____do__lift_358_);
v_snd_362_ = lean_ctor_get(v_a_361_, 1);
lean_inc(v_snd_362_);
lean_dec(v_a_361_);
v___x_363_ = lean_apply_2(v_toPure_357_, lean_box(0), v_snd_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_364_, lean_object* v_____do__lift_365_){
_start:
{
if (lean_obj_tag(v_____do__lift_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_a_366_ = lean_ctor_get(v_____do__lift_365_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v_____do__lift_365_);
if (v_isSharedCheck_374_ == 0)
{
v___x_368_ = v_____do__lift_365_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v_____do__lift_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_apply_2(v_toPure_364_, lean_box(0), v___x_371_);
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_385_; 
v_a_375_ = lean_ctor_get(v_____do__lift_365_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_____do__lift_365_);
if (v_isSharedCheck_385_ == 0)
{
v___x_377_ = v_____do__lift_365_;
v_isShared_378_ = v_isSharedCheck_385_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v_____do__lift_365_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_385_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_a_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_380_);
v___x_382_ = v___x_377_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_apply_2(v_toPure_364_, lean_box(0), v___x_382_);
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_386_, lean_object* v_toBind_387_, lean_object* v___f_388_, lean_object* v_x_389_, lean_object* v_y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_x_389_);
lean_ctor_set(v___x_392_, 1, v_y_390_);
v___x_393_ = lean_apply_2(v___y_386_, v___x_392_, v___y_391_);
v___x_394_ = lean_apply_4(v_toBind_387_, lean_box(0), lean_box(0), v___x_393_, v___f_388_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_395_, lean_object* v_00_u03b2_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___f_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_toApplicative_420_; lean_object* v_toBind_421_; lean_object* v_toPure_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___x_140__overap_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_inc_ref_n(v_inst_395_, 7);
v___f_400_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_400_, 0, v_inst_395_);
v___f_401_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_401_, 0, v_inst_395_);
v___f_402_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_402_, 0, v_inst_395_);
v___f_403_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_403_, 0, v_inst_395_);
v___x_404_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_404_, 0, lean_box(0));
lean_closure_set(v___x_404_, 1, lean_box(0));
lean_closure_set(v___x_404_, 2, v_inst_395_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___f_400_);
v___x_406_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_406_, 0, lean_box(0));
lean_closure_set(v___x_406_, 1, lean_box(0));
lean_closure_set(v___x_406_, 2, v_inst_395_);
v___x_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___f_401_);
lean_ctor_set(v___x_407_, 3, v___f_402_);
lean_ctor_set(v___x_407_, 4, v___f_403_);
v___x_408_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_408_, 0, lean_box(0));
lean_closure_set(v___x_408_, 1, lean_box(0));
lean_closure_set(v___x_408_, 2, v_inst_395_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_inc_ref_n(v___x_409_, 6);
v___f_410_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_410_, 0, v___x_409_);
v___f_411_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_411_, 0, v___x_409_);
v___f_412_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_412_, 0, v___x_409_);
v___f_413_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_413_, 0, v___x_409_);
v___x_414_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_414_, 0, lean_box(0));
lean_closure_set(v___x_414_, 1, lean_box(0));
lean_closure_set(v___x_414_, 2, v___x_409_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___f_410_);
v___x_416_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_416_, 0, lean_box(0));
lean_closure_set(v___x_416_, 1, lean_box(0));
lean_closure_set(v___x_416_, 2, v___x_409_);
v___x_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
lean_ctor_set(v___x_417_, 2, v___f_411_);
lean_ctor_set(v___x_417_, 3, v___f_412_);
lean_ctor_set(v___x_417_, 4, v___f_413_);
v___x_418_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_418_, 0, lean_box(0));
lean_closure_set(v___x_418_, 1, lean_box(0));
lean_closure_set(v___x_418_, 2, v___x_409_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v_toApplicative_420_ = lean_ctor_get(v_inst_395_, 0);
lean_inc_ref(v_toApplicative_420_);
v_toBind_421_ = lean_ctor_get(v_inst_395_, 1);
lean_inc_n(v_toBind_421_, 2);
lean_dec_ref(v_inst_395_);
v_toPure_422_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc_n(v_toPure_422_, 2);
lean_dec_ref(v_toApplicative_420_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_423_, 0, v_toPure_422_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_424_, 0, v_toPure_422_);
v___f_425_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_425_, 0, v___y_399_);
lean_closure_set(v___f_425_, 1, v_toBind_421_);
lean_closure_set(v___f_425_, 2, v___f_424_);
v___x_140__overap_426_ = l_Lean_SMap_forM___redArg(v___x_419_, v___y_397_, v___f_425_);
v___x_427_ = lean_apply_1(v___x_140__overap_426_, v___y_398_);
v___x_428_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_427_, v___f_423_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_429_){
_start:
{
lean_object* v___f_430_; 
v___f_430_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_430_, 0, v_inst_429_);
return v___f_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_m_435_, lean_object* v_inst_436_){
_start:
{
lean_object* v___f_437_; 
v___f_437_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_437_, 0, v_inst_436_);
return v___f_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_m_442_, lean_object* v_inst_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_438_, v_00_u03b2_439_, v_inst_440_, v_inst_441_, v_m_442_, v_inst_443_);
lean_dec_ref(v_inst_441_);
lean_dec_ref(v_inst_440_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object* v_s_445_){
_start:
{
lean_object* v_map_u2081_446_; lean_object* v_map_u2082_447_; lean_object* v_buckets_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_461_; 
v_map_u2081_446_ = lean_ctor_get(v_s_445_, 0);
lean_inc_ref(v_map_u2081_446_);
v_map_u2082_447_ = lean_ctor_get(v_s_445_, 1);
lean_inc_ref(v_map_u2082_447_);
lean_dec_ref(v_s_445_);
v_buckets_448_ = lean_ctor_get(v_map_u2081_446_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_map_u2081_446_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_map_u2081_446_, 0);
lean_dec(v_unused_462_);
v___x_450_ = v_map_u2081_446_;
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_buckets_448_);
lean_dec(v_map_u2081_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(0u);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_452_);
lean_ctor_set(v___x_450_, 0, v_buckets_448_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_buckets_448_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_460_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_box(0);
v___x_458_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_u2082_447_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_456_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_s_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_SMap_iter___redArg(v_s_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_s_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_SMap_iter(v_00_u03b1_469_, v_00_u03b2_470_, v_inst_471_, v_inst_472_, v_s_473_);
lean_dec_ref(v_inst_472_);
lean_dec_ref(v_inst_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_475_){
_start:
{
uint8_t v_stage_u2081_476_; 
v_stage_u2081_476_ = lean_ctor_get_uint8(v_m_475_, sizeof(void*)*2);
if (v_stage_u2081_476_ == 0)
{
return v_m_475_;
}
else
{
lean_object* v_map_u2081_477_; lean_object* v_map_u2082_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_486_; 
v_map_u2081_477_ = lean_ctor_get(v_m_475_, 0);
v_map_u2082_478_ = lean_ctor_get(v_m_475_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_m_475_);
if (v_isSharedCheck_486_ == 0)
{
v___x_480_ = v_m_475_;
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_map_u2082_478_);
lean_inc(v_map_u2081_477_);
lean_dec(v_m_475_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; lean_object* v___x_484_; 
v___x_482_ = 0;
if (v_isShared_481_ == 0)
{
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_map_u2081_477_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_map_u2082_478_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*2, v___x_482_);
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_487_, lean_object* v_00_u03b2_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_m_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_SMap_switch___redArg(v_m_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_m_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_SMap_switch(v_00_u03b1_493_, v_00_u03b2_494_, v_inst_495_, v_inst_496_, v_m_497_);
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_inst_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_499_, lean_object* v_s_500_, lean_object* v_m_501_){
_start:
{
lean_object* v_map_u2082_502_; lean_object* v___x_503_; 
v_map_u2082_502_ = lean_ctor_get(v_m_501_, 1);
lean_inc_ref(v_map_u2082_502_);
lean_dec_ref(v_m_501_);
v___x_503_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_502_, v_f_499_, v_s_500_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_00_u03c3_508_, lean_object* v_f_509_, lean_object* v_s_510_, lean_object* v_m_511_){
_start:
{
lean_object* v_map_u2082_512_; lean_object* v___x_513_; 
v_map_u2082_512_ = lean_ctor_get(v_m_511_, 1);
lean_inc_ref(v_map_u2082_512_);
lean_dec_ref(v_m_511_);
v___x_513_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_512_, v_f_509_, v_s_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_00_u03c3_518_, lean_object* v_f_519_, lean_object* v_s_520_, lean_object* v_m_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_SMap_foldStage2(v_00_u03b1_514_, v_00_u03b2_515_, v_inst_516_, v_inst_517_, v_00_u03c3_518_, v_f_519_, v_s_520_, v_m_521_);
lean_dec_ref(v_inst_517_);
lean_dec_ref(v_inst_516_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_523_, lean_object* v_f_524_, lean_object* v_map_u2082_525_, lean_object* v_____do__lift_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_523_, v_f_524_, v_map_u2082_525_, v_____do__lift_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object* v_inst_528_, lean_object* v_f_529_, lean_object* v_acc_530_, lean_object* v_l_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_528_, v_f_529_, v_acc_530_, v_l_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_533_, lean_object* v_f_534_, lean_object* v_init_535_, lean_object* v_map_536_){
_start:
{
lean_object* v_map_u2081_537_; lean_object* v_toApplicative_538_; lean_object* v_toBind_539_; lean_object* v_map_u2082_540_; lean_object* v_buckets_541_; lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_map_u2081_537_ = lean_ctor_get(v_map_536_, 0);
lean_inc_ref(v_map_u2081_537_);
v_toApplicative_538_ = lean_ctor_get(v_inst_533_, 0);
v_toBind_539_ = lean_ctor_get(v_inst_533_, 1);
lean_inc(v_toBind_539_);
v_map_u2082_540_ = lean_ctor_get(v_map_536_, 1);
lean_inc_ref(v_map_u2082_540_);
lean_dec_ref(v_map_536_);
v_buckets_541_ = lean_ctor_get(v_map_u2081_537_, 1);
lean_inc_ref(v_buckets_541_);
lean_dec_ref(v_map_u2081_537_);
lean_inc(v_f_534_);
lean_inc_ref(v_inst_533_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_542_, 0, v_inst_533_);
lean_closure_set(v___f_542_, 1, v_f_534_);
lean_closure_set(v___f_542_, 2, v_map_u2082_540_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_array_get_size(v_buckets_541_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v_toPure_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc_ref(v_toApplicative_538_);
lean_dec_ref(v_buckets_541_);
lean_dec(v_f_534_);
lean_dec_ref(v_inst_533_);
v_toPure_546_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_inc(v_toPure_546_);
lean_dec_ref(v_toApplicative_538_);
v___x_547_ = lean_apply_2(v_toPure_546_, lean_box(0), v_init_535_);
v___x_548_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_547_, v___f_542_);
return v___x_548_;
}
else
{
lean_object* v___f_549_; uint8_t v___x_550_; 
lean_inc_ref(v_inst_533_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_549_, 0, v_inst_533_);
lean_closure_set(v___f_549_, 1, v_f_534_);
v___x_550_ = lean_nat_dec_le(v___x_544_, v___x_544_);
if (v___x_550_ == 0)
{
if (v___x_545_ == 0)
{
lean_object* v_toPure_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_inc_ref(v_toApplicative_538_);
lean_dec_ref(v___f_549_);
lean_dec_ref(v_buckets_541_);
lean_dec_ref(v_inst_533_);
v_toPure_551_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_inc(v_toPure_551_);
lean_dec_ref(v_toApplicative_538_);
v___x_552_ = lean_apply_2(v_toPure_551_, lean_box(0), v_init_535_);
v___x_553_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_552_, v___f_542_);
return v___x_553_;
}
else
{
size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = ((size_t)0ULL);
v___x_555_ = lean_usize_of_nat(v___x_544_);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_533_, v___f_549_, v_buckets_541_, v___x_554_, v___x_555_, v_init_535_);
v___x_557_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_556_, v___f_542_);
return v___x_557_;
}
}
else
{
size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = ((size_t)0ULL);
v___x_559_ = lean_usize_of_nat(v___x_544_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_533_, v___f_549_, v_buckets_541_, v___x_558_, v___x_559_, v_init_535_);
v___x_561_ = lean_apply_4(v_toBind_539_, lean_box(0), lean_box(0), v___x_560_, v___f_542_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object* v_00_u03b1_562_, lean_object* v_00_u03b2_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_00_u03c3_566_, lean_object* v_m_567_, lean_object* v_inst_568_, lean_object* v_f_569_, lean_object* v_init_570_, lean_object* v_map_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_SMap_foldM___redArg(v_inst_568_, v_f_569_, v_init_570_, v_map_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_00_u03c3_577_, lean_object* v_m_578_, lean_object* v_inst_579_, lean_object* v_f_580_, lean_object* v_init_581_, lean_object* v_map_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_SMap_foldM(v_00_u03b1_573_, v_00_u03b2_574_, v_inst_575_, v_inst_576_, v_00_u03c3_577_, v_m_578_, v_inst_579_, v_f_580_, v_init_581_, v_map_582_);
lean_dec_ref(v_inst_576_);
lean_dec_ref(v_inst_575_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object* v_f_584_, lean_object* v_x1_585_, lean_object* v_x2_586_, lean_object* v_x3_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_apply_3(v_f_584_, v_x1_585_, v_x2_586_, v_x3_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__1(lean_object* v___x_589_, lean_object* v___f_590_, lean_object* v_acc_591_, lean_object* v_l_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_589_, v___f_590_, v_acc_591_, v_l_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object* v_f_613_, lean_object* v_init_614_, lean_object* v_m_615_){
_start:
{
lean_object* v_map_u2081_616_; lean_object* v_map_u2082_617_; lean_object* v___x_618_; lean_object* v_buckets_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_map_u2081_616_ = lean_ctor_get(v_m_615_, 0);
lean_inc_ref(v_map_u2081_616_);
v_map_u2082_617_ = lean_ctor_get(v_m_615_, 1);
lean_inc_ref(v_map_u2082_617_);
lean_dec_ref(v_m_615_);
v___x_618_ = ((lean_object*)(l_Lean_SMap_fold___redArg___closed__9));
v_buckets_619_ = lean_ctor_get(v_map_u2081_616_, 1);
lean_inc_ref(v_buckets_619_);
lean_dec_ref(v_map_u2081_616_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_array_get_size(v_buckets_619_);
v___x_622_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec_ref(v_buckets_619_);
v___x_623_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_617_, v_f_613_, v_init_614_);
return v___x_623_;
}
else
{
lean_object* v___f_624_; lean_object* v___f_625_; uint8_t v___x_626_; 
lean_inc(v_f_613_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_624_, 0, v_f_613_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_625_, 0, v___x_618_);
lean_closure_set(v___f_625_, 1, v___f_624_);
v___x_626_ = lean_nat_dec_le(v___x_621_, v___x_621_);
if (v___x_626_ == 0)
{
if (v___x_622_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v___f_625_);
lean_dec_ref(v_buckets_619_);
v___x_627_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_617_, v_f_613_, v_init_614_);
return v___x_627_;
}
else
{
size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = ((size_t)0ULL);
v___x_629_ = lean_usize_of_nat(v___x_621_);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_618_, v___f_625_, v_buckets_619_, v___x_628_, v___x_629_, v_init_614_);
v___x_631_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_617_, v_f_613_, v___x_630_);
return v___x_631_;
}
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_621_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_618_, v___f_625_, v_buckets_619_, v___x_632_, v___x_633_, v_init_614_);
v___x_635_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_617_, v_f_613_, v___x_634_);
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_00_u03c3_640_, lean_object* v_f_641_, lean_object* v_init_642_, lean_object* v_m_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_SMap_fold___redArg(v_f_641_, v_init_642_, v_m_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_00_u03c3_649_, lean_object* v_f_650_, lean_object* v_init_651_, lean_object* v_m_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_SMap_fold(v_00_u03b1_645_, v_00_u03b2_646_, v_inst_647_, v_inst_648_, v_00_u03c3_649_, v_f_650_, v_init_651_, v_m_652_);
lean_dec_ref(v_inst_648_);
lean_dec_ref(v_inst_647_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_654_){
_start:
{
lean_object* v_map_u2081_655_; lean_object* v___x_656_; 
v_map_u2081_655_ = lean_ctor_get(v_m_654_, 0);
v___x_656_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_SMap_numBuckets___redArg(v_m_657_);
lean_dec_ref(v_m_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_m_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_SMap_numBuckets___redArg(v_m_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_665_, lean_object* v_00_u03b2_666_, lean_object* v_inst_667_, lean_object* v_inst_668_, lean_object* v_m_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_SMap_numBuckets(v_00_u03b1_665_, v_00_u03b2_666_, v_inst_667_, v_inst_668_, v_m_669_);
lean_dec_ref(v_m_669_);
lean_dec_ref(v_inst_668_);
lean_dec_ref(v_inst_667_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_671_, lean_object* v_a_672_, lean_object* v_b_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v_a_672_);
lean_ctor_set(v___x_674_, 1, v_b_673_);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_es_671_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_677_){
_start:
{
lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___f_678_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_679_ = lean_box(0);
v___x_680_ = l_Lean_SMap_fold___redArg(v___f_678_, v___x_679_, v_m_677_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_681_, lean_object* v_00_u03b2_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_m_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_SMap_toList___redArg(v_m_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_m_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_SMap_toList(v_00_u03b1_687_, v_00_u03b2_688_, v_inst_689_, v_inst_690_, v_m_691_);
lean_dec_ref(v_inst_690_);
lean_dec_ref(v_inst_689_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap___redArg___lam__0(lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_s_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___x_699_; 
v_fst_697_ = lean_ctor_get(v_x_696_, 0);
lean_inc(v_fst_697_);
v_snd_698_ = lean_ctor_get(v_x_696_, 1);
lean_inc(v_snd_698_);
lean_dec_ref(v_x_696_);
v___x_699_ = l_Lean_SMap_insert___redArg(v_inst_693_, v_inst_694_, v_s_695_, v_fst_697_, v_snd_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap___redArg(lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_es_702_){
_start:
{
lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___f_703_ = lean_alloc_closure((void*)(l_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_703_, 0, v_inst_700_);
lean_closure_set(v___f_703_, 1, v_inst_701_);
v___x_704_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_705_ = l_List_foldl___redArg(v___f_703_, v___x_704_, v_es_702_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_es_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_List_toSMap___redArg(v_inst_708_, v_inst_709_, v_es_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_715_, lean_object* v_v_716_, lean_object* v_prec_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_718_ = l_Lean_SMap_toList___redArg(v_v_716_);
v___x_719_ = l_List_repr___redArg(v___x_715_, v___x_718_);
v___x_720_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Repr_addAppParen(v___x_721_, v_prec_717_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_723_, lean_object* v_v_724_, lean_object* v_prec_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_instReprSMap___redArg___lam__0(v___x_723_, v_v_724_, v_prec_725_);
lean_dec(v_prec_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___f_729_; lean_object* v___x_730_; lean_object* v___f_731_; 
v___f_729_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_729_, 0, v_inst_728_);
v___x_730_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_730_, 0, lean_box(0));
lean_closure_set(v___x_730_, 1, lean_box(0));
lean_closure_set(v___x_730_, 2, v_inst_727_);
lean_closure_set(v___x_730_, 3, v___f_729_);
v___f_731_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_731_, 0, v___x_730_);
return v___f_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_inst_736_, lean_object* v_inst_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_instReprSMap___redArg(v_inst_736_, v_inst_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_inst_743_, lean_object* v_inst_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_instReprSMap(v_00_u03b1_739_, v_00_u03b2_740_, v_x_741_, v_x_742_, v_inst_743_, v_inst_744_);
lean_dec_ref(v_x_742_);
lean_dec_ref(v_x_741_);
return v_res_745_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Append(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_SMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_SMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Iterator(uint8_t builtin);
lean_object* initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_Append(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_SMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_SMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_SMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_SMap(builtin);
}
#ifdef __cplusplus
}
#endif
