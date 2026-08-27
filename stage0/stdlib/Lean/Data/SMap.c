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
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toSMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_map_u2082_132_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_x_129_);
lean_inc_ref(v_inst_127_);
lean_inc_ref(v_inst_126_);
v___x_133_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_126_, v_inst_127_, v_map_u2082_132_, v_x_129_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_126_, v_inst_127_, v_map_u2081_131_, v_x_129_);
return v___x_134_;
}
else
{
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
v___x_136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_126_, v_inst_127_, v_map_u2081_135_, v_x_129_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg___boxed(lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_SMap_find_x3f___redArg(v_inst_137_, v_inst_138_, v_x_139_, v_x_140_);
lean_dec_ref(v_x_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_SMap_find_x3f___redArg(v_inst_144_, v_inst_145_, v_x_146_, v_x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___boxed(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_SMap_find_x3f(v_00_u03b1_149_, v_00_u03b2_150_, v_inst_151_, v_inst_152_, v_x_153_, v_x_154_);
lean_dec_ref(v_x_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_m_158_, lean_object* v_a_159_, lean_object* v_b_u2080_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_SMap_find_x3f___redArg(v_inst_156_, v_inst_157_, v_m_158_, v_a_159_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_inc(v_b_u2080_160_);
return v_b_u2080_160_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_161_, 1);
return v_val_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg___boxed(lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_m_165_, lean_object* v_a_166_, lean_object* v_b_u2080_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_SMap_findD___redArg(v_inst_163_, v_inst_164_, v_m_165_, v_a_166_, v_b_u2080_167_);
lean_dec(v_b_u2080_167_);
lean_dec_ref(v_m_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD(lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_m_173_, lean_object* v_a_174_, lean_object* v_b_u2080_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_SMap_find_x3f___redArg(v_inst_171_, v_inst_172_, v_m_173_, v_a_174_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_inc(v_b_u2080_175_);
return v_b_u2080_175_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_176_, 1);
return v_val_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___boxed(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_m_182_, lean_object* v_a_183_, lean_object* v_b_u2080_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_SMap_findD(v_00_u03b1_178_, v_00_u03b2_179_, v_inst_180_, v_inst_181_, v_m_182_, v_a_183_, v_b_u2080_184_);
lean_dec(v_b_u2080_184_);
lean_dec_ref(v_m_182_);
return v_res_185_;
}
}
static lean_object* _init_l_Lean_SMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_189_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__2));
v___x_190_ = lean_unsigned_to_nat(14u);
v___x_191_ = lean_unsigned_to_nat(70u);
v___x_192_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__1));
v___x_193_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__0));
v___x_194_ = l_mkPanicMessageWithDecl(v___x_193_, v___x_192_, v___x_191_, v___x_190_, v___x_189_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_SMap_find_x3f___redArg(v_inst_195_, v_inst_196_, v_m_198_, v_a_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_202_ = l_panic___redArg(v_inst_197_, v___x_201_);
return v___x_202_;
}
else
{
lean_object* v_val_203_; 
v_val_203_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_203_);
lean_dec_ref_known(v___x_200_, 1);
return v_val_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg___boxed(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_m_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_SMap_find_x21___redArg(v_inst_204_, v_inst_205_, v_inst_206_, v_m_207_, v_a_208_);
lean_dec_ref(v_m_207_);
lean_dec(v_inst_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_m_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_SMap_find_x3f___redArg(v_inst_212_, v_inst_213_, v_m_215_, v_a_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_219_ = l_panic___redArg(v_inst_214_, v___x_218_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; 
v_val_220_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v___x_217_, 1);
return v_val_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___boxed(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_m_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_SMap_find_x21(v_00_u03b1_221_, v_00_u03b2_222_, v_inst_223_, v_inst_224_, v_inst_225_, v_m_226_, v_a_227_);
lean_dec_ref(v_m_226_);
lean_dec(v_inst_225_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___redArg(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_stage_u2081_233_; 
v_stage_u2081_233_ = lean_ctor_get_uint8(v_x_231_, sizeof(void*)*2);
if (v_stage_u2081_233_ == 0)
{
lean_object* v_map_u2081_234_; lean_object* v_map_u2082_235_; uint8_t v___x_236_; 
v_map_u2081_234_ = lean_ctor_get(v_x_231_, 0);
lean_inc_ref(v_map_u2081_234_);
v_map_u2082_235_ = lean_ctor_get(v_x_231_, 1);
lean_inc_ref(v_map_u2082_235_);
lean_dec_ref(v_x_231_);
lean_inc(v_x_232_);
lean_inc_ref(v_inst_230_);
lean_inc_ref(v_inst_229_);
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_229_, v_inst_230_, v_map_u2081_234_, v_x_232_);
lean_dec_ref(v_map_u2081_234_);
if (v___x_236_ == 0)
{
uint8_t v___x_237_; 
v___x_237_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_229_, v_inst_230_, v_map_u2082_235_, v_x_232_);
return v___x_237_;
}
else
{
lean_dec_ref(v_map_u2082_235_);
lean_dec(v_x_232_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_inst_229_);
return v___x_236_;
}
}
else
{
lean_object* v_map_u2081_238_; uint8_t v___x_239_; 
v_map_u2081_238_ = lean_ctor_get(v_x_231_, 0);
lean_inc_ref(v_map_u2081_238_);
lean_dec_ref(v_x_231_);
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_229_, v_inst_230_, v_map_u2081_238_, v_x_232_);
lean_dec_ref(v_map_u2081_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Lean_SMap_contains___redArg(v_inst_240_, v_inst_241_, v_x_242_, v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = l_Lean_SMap_contains___redArg(v_inst_248_, v_inst_249_, v_x_250_, v_x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_SMap_contains(v_00_u03b1_253_, v_00_u03b2_254_, v_inst_255_, v_inst_256_, v_x_257_, v_x_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
uint8_t v_stage_u2081_265_; 
v_stage_u2081_265_ = lean_ctor_get_uint8(v_x_263_, sizeof(void*)*2);
if (v_stage_u2081_265_ == 0)
{
lean_object* v_map_u2081_266_; lean_object* v_map_u2082_267_; lean_object* v___x_268_; 
v_map_u2081_266_ = lean_ctor_get(v_x_263_, 0);
v_map_u2082_267_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_x_264_);
lean_inc_ref(v_inst_262_);
lean_inc_ref(v_inst_261_);
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_261_, v_inst_262_, v_map_u2081_266_, v_x_264_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_261_, v_inst_262_, v_map_u2082_267_, v_x_264_);
return v___x_269_;
}
else
{
lean_dec(v_x_264_);
lean_dec_ref(v_inst_262_);
lean_dec_ref(v_inst_261_);
return v___x_268_;
}
}
else
{
lean_object* v_map_u2081_270_; lean_object* v___x_271_; 
v_map_u2081_270_ = lean_ctor_get(v_x_263_, 0);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_261_, v_inst_262_, v_map_u2081_270_, v_x_264_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg___boxed(lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_272_, v_inst_273_, v_x_274_, v_x_275_);
lean_dec_ref(v_x_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_279_, v_inst_280_, v_x_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___boxed(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_SMap_find_x3f_x27(v_00_u03b1_284_, v_00_u03b2_285_, v_inst_286_, v_inst_287_, v_x_288_, v_x_289_);
lean_dec_ref(v_x_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object* v_inst_291_, lean_object* v_map_u2082_292_, lean_object* v_f_293_, lean_object* v_____r_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_291_, v_map_u2082_292_, v_f_293_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object* v_f_296_, lean_object* v_x_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_apply_2(v_f_296_, v___y_298_, v___y_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__2(lean_object* v_inst_301_, lean_object* v___f_302_, lean_object* v_x_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(0);
v___x_306_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_301_, v___f_302_, v___x_305_, v___y_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object* v_inst_307_, lean_object* v_s_308_, lean_object* v_f_309_){
_start:
{
lean_object* v_map_u2081_310_; lean_object* v_toApplicative_311_; lean_object* v_toBind_312_; lean_object* v_map_u2082_313_; lean_object* v_buckets_314_; lean_object* v_toPure_315_; lean_object* v___f_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_map_u2081_310_ = lean_ctor_get(v_s_308_, 0);
lean_inc_ref(v_map_u2081_310_);
v_toApplicative_311_ = lean_ctor_get(v_inst_307_, 0);
v_toBind_312_ = lean_ctor_get(v_inst_307_, 1);
lean_inc(v_toBind_312_);
v_map_u2082_313_ = lean_ctor_get(v_s_308_, 1);
lean_inc_ref(v_map_u2082_313_);
lean_dec_ref(v_s_308_);
v_buckets_314_ = lean_ctor_get(v_map_u2081_310_, 1);
lean_inc_ref(v_buckets_314_);
lean_dec_ref(v_map_u2081_310_);
v_toPure_315_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_inc(v_f_309_);
lean_inc_ref(v_inst_307_);
v___f_316_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_316_, 0, v_inst_307_);
lean_closure_set(v___f_316_, 1, v_map_u2082_313_);
lean_closure_set(v___f_316_, 2, v_f_309_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = lean_array_get_size(v_buckets_314_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_nat_dec_lt(v___x_317_, v___x_318_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc(v_toPure_315_);
lean_dec_ref(v_buckets_314_);
lean_dec(v_f_309_);
lean_dec_ref(v_inst_307_);
v___x_321_ = lean_apply_2(v_toPure_315_, lean_box(0), v___x_319_);
v___x_322_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_321_, v___f_316_);
return v___x_322_;
}
else
{
lean_object* v___f_323_; lean_object* v___f_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___f_323_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 1);
lean_closure_set(v___f_323_, 0, v_f_309_);
lean_inc_ref(v_inst_307_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_324_, 0, v_inst_307_);
lean_closure_set(v___f_324_, 1, v___f_323_);
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_318_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_307_, v___f_324_, v_buckets_314_, v___x_325_, v___x_326_, v___x_319_);
v___x_328_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_327_, v___f_316_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_m_333_, lean_object* v_inst_334_, lean_object* v_s_335_, lean_object* v_f_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_SMap_forM___redArg(v_inst_334_, v_s_335_, v_f_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_m_342_, lean_object* v_inst_343_, lean_object* v_s_344_, lean_object* v_f_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_SMap_forM(v_00_u03b1_338_, v_00_u03b2_339_, v_inst_340_, v_inst_341_, v_m_342_, v_inst_343_, v_s_344_, v_f_345_);
lean_dec_ref(v_inst_341_);
lean_dec_ref(v_inst_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_347_, lean_object* v_x_348_, lean_object* v_y_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v_x_348_);
lean_ctor_set(v___x_350_, 1, v_y_349_);
v___x_351_ = lean_apply_1(v_f_347_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_352_, lean_object* v_s_353_, lean_object* v_f_354_){
_start:
{
lean_object* v___f_355_; lean_object* v___x_356_; 
v___f_355_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_355_, 0, v_f_354_);
v___x_356_ = l_Lean_SMap_forM___redArg(v_inst_352_, v_s_353_, v___f_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_357_){
_start:
{
lean_object* v___f_358_; 
v___f_358_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_358_, 0, v_inst_357_);
return v___f_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b2_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_m_363_, lean_object* v_inst_364_){
_start:
{
lean_object* v___f_365_; 
v___f_365_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_365_, 0, v_inst_364_);
return v___f_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_366_, lean_object* v_00_u03b2_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_m_370_, lean_object* v_inst_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_366_, v_00_u03b2_367_, v_inst_368_, v_inst_369_, v_m_370_, v_inst_371_);
lean_dec_ref(v_inst_369_);
lean_dec_ref(v_inst_368_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_373_, lean_object* v_____do__lift_374_){
_start:
{
if (lean_obj_tag(v_____do__lift_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v_____do__lift_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v_____do__lift_374_, 1);
v___x_376_ = lean_apply_2(v_toPure_373_, lean_box(0), v_a_375_);
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v_snd_378_; lean_object* v___x_379_; 
v_a_377_ = lean_ctor_get(v_____do__lift_374_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v_____do__lift_374_, 1);
v_snd_378_ = lean_ctor_get(v_a_377_, 1);
lean_inc(v_snd_378_);
lean_dec(v_a_377_);
v___x_379_ = lean_apply_2(v_toPure_373_, lean_box(0), v_snd_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_380_, lean_object* v_____do__lift_381_){
_start:
{
if (lean_obj_tag(v_____do__lift_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v_____do__lift_381_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_____do__lift_381_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v_____do__lift_381_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v_____do__lift_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_389_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; 
v___x_388_ = lean_apply_2(v_toPure_380_, lean_box(0), v___x_387_);
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_401_; 
v_a_391_ = lean_ctor_get(v_____do__lift_381_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_____do__lift_381_);
if (v_isSharedCheck_401_ == 0)
{
v___x_393_ = v_____do__lift_381_;
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v_____do__lift_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_box(0);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_400_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; 
v___x_399_ = lean_apply_2(v_toPure_380_, lean_box(0), v___x_398_);
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_402_, lean_object* v_toBind_403_, lean_object* v___f_404_, lean_object* v_x_405_, lean_object* v_y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_x_405_);
lean_ctor_set(v___x_408_, 1, v_y_406_);
v___x_409_ = lean_apply_2(v___y_402_, v___x_408_, v___y_407_);
v___x_410_ = lean_apply_4(v_toBind_403_, lean_box(0), lean_box(0), v___x_409_, v___f_404_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_411_, lean_object* v_00_u03b2_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v_toApplicative_436_; lean_object* v_toBind_437_; lean_object* v_toPure_438_; lean_object* v___f_439_; lean_object* v___f_440_; lean_object* v___f_441_; lean_object* v___x_140__overap_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc_ref_n(v_inst_411_, 7);
v___f_416_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_416_, 0, v_inst_411_);
v___f_417_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_417_, 0, v_inst_411_);
v___f_418_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_418_, 0, v_inst_411_);
v___f_419_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_419_, 0, v_inst_411_);
v___x_420_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, lean_box(0));
lean_closure_set(v___x_420_, 2, v_inst_411_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___f_416_);
v___x_422_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_422_, 0, lean_box(0));
lean_closure_set(v___x_422_, 1, lean_box(0));
lean_closure_set(v___x_422_, 2, v_inst_411_);
v___x_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_ctor_set(v___x_423_, 2, v___f_417_);
lean_ctor_set(v___x_423_, 3, v___f_418_);
lean_ctor_set(v___x_423_, 4, v___f_419_);
v___x_424_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_424_, 0, lean_box(0));
lean_closure_set(v___x_424_, 1, lean_box(0));
lean_closure_set(v___x_424_, 2, v_inst_411_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_inc_ref_n(v___x_425_, 6);
v___f_426_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_426_, 0, v___x_425_);
v___f_427_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_427_, 0, v___x_425_);
v___f_428_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_428_, 0, v___x_425_);
v___f_429_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_429_, 0, v___x_425_);
v___x_430_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_430_, 0, lean_box(0));
lean_closure_set(v___x_430_, 1, lean_box(0));
lean_closure_set(v___x_430_, 2, v___x_425_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___f_426_);
v___x_432_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_432_, 0, lean_box(0));
lean_closure_set(v___x_432_, 1, lean_box(0));
lean_closure_set(v___x_432_, 2, v___x_425_);
v___x_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v___f_427_);
lean_ctor_set(v___x_433_, 3, v___f_428_);
lean_ctor_set(v___x_433_, 4, v___f_429_);
v___x_434_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_434_, 0, lean_box(0));
lean_closure_set(v___x_434_, 1, lean_box(0));
lean_closure_set(v___x_434_, 2, v___x_425_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v_toApplicative_436_ = lean_ctor_get(v_inst_411_, 0);
lean_inc_ref(v_toApplicative_436_);
v_toBind_437_ = lean_ctor_get(v_inst_411_, 1);
lean_inc_n(v_toBind_437_, 2);
lean_dec_ref(v_inst_411_);
v_toPure_438_ = lean_ctor_get(v_toApplicative_436_, 1);
lean_inc_n(v_toPure_438_, 2);
lean_dec_ref(v_toApplicative_436_);
v___f_439_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_439_, 0, v_toPure_438_);
v___f_440_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_440_, 0, v_toPure_438_);
v___f_441_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_441_, 0, v___y_415_);
lean_closure_set(v___f_441_, 1, v_toBind_437_);
lean_closure_set(v___f_441_, 2, v___f_440_);
v___x_140__overap_442_ = l_Lean_SMap_forM___redArg(v___x_435_, v___y_413_, v___f_441_);
v___x_443_ = lean_apply_1(v___x_140__overap_442_, v___y_414_);
v___x_444_ = lean_apply_4(v_toBind_437_, lean_box(0), lean_box(0), v___x_443_, v___f_439_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_445_){
_start:
{
lean_object* v___f_446_; 
v___f_446_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_446_, 0, v_inst_445_);
return v___f_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_m_451_, lean_object* v_inst_452_){
_start:
{
lean_object* v___f_453_; 
v___f_453_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_453_, 0, v_inst_452_);
return v___f_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_m_458_, lean_object* v_inst_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_454_, v_00_u03b2_455_, v_inst_456_, v_inst_457_, v_m_458_, v_inst_459_);
lean_dec_ref(v_inst_457_);
lean_dec_ref(v_inst_456_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object* v_s_461_){
_start:
{
lean_object* v_map_u2081_462_; lean_object* v_map_u2082_463_; lean_object* v_buckets_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_477_; 
v_map_u2081_462_ = lean_ctor_get(v_s_461_, 0);
lean_inc_ref(v_map_u2081_462_);
v_map_u2082_463_ = lean_ctor_get(v_s_461_, 1);
lean_inc_ref(v_map_u2082_463_);
lean_dec_ref(v_s_461_);
v_buckets_464_ = lean_ctor_get(v_map_u2081_462_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_map_u2081_462_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_map_u2081_462_, 0);
lean_dec(v_unused_478_);
v___x_466_ = v_map_u2081_462_;
v_isShared_467_ = v_isSharedCheck_477_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_buckets_464_);
lean_dec(v_map_u2081_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_477_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(0u);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_468_);
lean_ctor_set(v___x_466_, 0, v_buckets_464_);
v___x_470_ = v___x_466_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_buckets_464_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_476_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_471_ = lean_box(0);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_u2082_463_, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_472_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object* v_00_u03b1_479_, lean_object* v_00_u03b2_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_s_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_SMap_iter___redArg(v_s_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_s_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_SMap_iter(v_00_u03b1_485_, v_00_u03b2_486_, v_inst_487_, v_inst_488_, v_s_489_);
lean_dec_ref(v_inst_488_);
lean_dec_ref(v_inst_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_491_){
_start:
{
uint8_t v_stage_u2081_492_; 
v_stage_u2081_492_ = lean_ctor_get_uint8(v_m_491_, sizeof(void*)*2);
if (v_stage_u2081_492_ == 0)
{
return v_m_491_;
}
else
{
lean_object* v_map_u2081_493_; lean_object* v_map_u2082_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v_map_u2081_493_ = lean_ctor_get(v_m_491_, 0);
v_map_u2082_494_ = lean_ctor_get(v_m_491_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_m_491_);
if (v_isSharedCheck_502_ == 0)
{
v___x_496_ = v_m_491_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_map_u2082_494_);
lean_inc(v_map_u2081_493_);
lean_dec(v_m_491_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; lean_object* v___x_500_; 
v___x_498_ = 0;
if (v_isShared_497_ == 0)
{
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_map_u2081_493_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_map_u2082_494_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*2, v___x_498_);
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_503_, lean_object* v_00_u03b2_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_m_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_SMap_switch___redArg(v_m_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_m_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_SMap_switch(v_00_u03b1_509_, v_00_u03b2_510_, v_inst_511_, v_inst_512_, v_m_513_);
lean_dec_ref(v_inst_512_);
lean_dec_ref(v_inst_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_515_, lean_object* v_s_516_, lean_object* v_m_517_){
_start:
{
lean_object* v_map_u2082_518_; lean_object* v___x_519_; 
v_map_u2082_518_ = lean_ctor_get(v_m_517_, 1);
lean_inc_ref(v_map_u2082_518_);
lean_dec_ref(v_m_517_);
v___x_519_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_518_, v_f_515_, v_s_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_00_u03c3_524_, lean_object* v_f_525_, lean_object* v_s_526_, lean_object* v_m_527_){
_start:
{
lean_object* v_map_u2082_528_; lean_object* v___x_529_; 
v_map_u2082_528_ = lean_ctor_get(v_m_527_, 1);
lean_inc_ref(v_map_u2082_528_);
lean_dec_ref(v_m_527_);
v___x_529_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_528_, v_f_525_, v_s_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_00_u03c3_534_, lean_object* v_f_535_, lean_object* v_s_536_, lean_object* v_m_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_SMap_foldStage2(v_00_u03b1_530_, v_00_u03b2_531_, v_inst_532_, v_inst_533_, v_00_u03c3_534_, v_f_535_, v_s_536_, v_m_537_);
lean_dec_ref(v_inst_533_);
lean_dec_ref(v_inst_532_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_539_, lean_object* v_f_540_, lean_object* v_map_u2082_541_, lean_object* v_____do__lift_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_539_, v_f_540_, v_map_u2082_541_, v_____do__lift_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object* v_inst_544_, lean_object* v_f_545_, lean_object* v_acc_546_, lean_object* v_l_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_544_, v_f_545_, v_acc_546_, v_l_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_549_, lean_object* v_f_550_, lean_object* v_init_551_, lean_object* v_map_552_){
_start:
{
lean_object* v_map_u2081_553_; lean_object* v_toApplicative_554_; lean_object* v_toBind_555_; lean_object* v_map_u2082_556_; lean_object* v_buckets_557_; lean_object* v_toPure_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_map_u2081_553_ = lean_ctor_get(v_map_552_, 0);
lean_inc_ref(v_map_u2081_553_);
v_toApplicative_554_ = lean_ctor_get(v_inst_549_, 0);
v_toBind_555_ = lean_ctor_get(v_inst_549_, 1);
lean_inc(v_toBind_555_);
v_map_u2082_556_ = lean_ctor_get(v_map_552_, 1);
lean_inc_ref(v_map_u2082_556_);
lean_dec_ref(v_map_552_);
v_buckets_557_ = lean_ctor_get(v_map_u2081_553_, 1);
lean_inc_ref(v_buckets_557_);
lean_dec_ref(v_map_u2081_553_);
v_toPure_558_ = lean_ctor_get(v_toApplicative_554_, 1);
lean_inc(v_f_550_);
lean_inc_ref(v_inst_549_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_559_, 0, v_inst_549_);
lean_closure_set(v___f_559_, 1, v_f_550_);
lean_closure_set(v___f_559_, 2, v_map_u2082_556_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_array_get_size(v_buckets_557_);
v___x_562_ = lean_nat_dec_lt(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_inc(v_toPure_558_);
lean_dec_ref(v_buckets_557_);
lean_dec(v_f_550_);
lean_dec_ref(v_inst_549_);
v___x_563_ = lean_apply_2(v_toPure_558_, lean_box(0), v_init_551_);
v___x_564_ = lean_apply_4(v_toBind_555_, lean_box(0), lean_box(0), v___x_563_, v___f_559_);
return v___x_564_;
}
else
{
lean_object* v___f_565_; size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc_ref(v_inst_549_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_565_, 0, v_inst_549_);
lean_closure_set(v___f_565_, 1, v_f_550_);
v___x_566_ = ((size_t)0ULL);
v___x_567_ = lean_usize_of_nat(v___x_561_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_549_, v___f_565_, v_buckets_557_, v___x_566_, v___x_567_, v_init_551_);
v___x_569_ = lean_apply_4(v_toBind_555_, lean_box(0), lean_box(0), v___x_568_, v___f_559_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_00_u03c3_574_, lean_object* v_m_575_, lean_object* v_inst_576_, lean_object* v_f_577_, lean_object* v_init_578_, lean_object* v_map_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_SMap_foldM___redArg(v_inst_576_, v_f_577_, v_init_578_, v_map_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_00_u03c3_585_, lean_object* v_m_586_, lean_object* v_inst_587_, lean_object* v_f_588_, lean_object* v_init_589_, lean_object* v_map_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_SMap_foldM(v_00_u03b1_581_, v_00_u03b2_582_, v_inst_583_, v_inst_584_, v_00_u03c3_585_, v_m_586_, v_inst_587_, v_f_588_, v_init_589_, v_map_590_);
lean_dec_ref(v_inst_584_);
lean_dec_ref(v_inst_583_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object* v_f_592_, lean_object* v_x1_593_, lean_object* v_x2_594_, lean_object* v_x3_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_apply_3(v_f_592_, v_x1_593_, v_x2_594_, v_x3_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__1(lean_object* v___x_597_, lean_object* v___f_598_, lean_object* v_acc_599_, lean_object* v_l_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_597_, v___f_598_, v_acc_599_, v_l_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object* v_f_621_, lean_object* v_init_622_, lean_object* v_m_623_){
_start:
{
lean_object* v_map_u2081_624_; lean_object* v_map_u2082_625_; lean_object* v___x_626_; lean_object* v_buckets_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_map_u2081_624_ = lean_ctor_get(v_m_623_, 0);
lean_inc_ref(v_map_u2081_624_);
v_map_u2082_625_ = lean_ctor_get(v_m_623_, 1);
lean_inc_ref(v_map_u2082_625_);
lean_dec_ref(v_m_623_);
v___x_626_ = ((lean_object*)(l_Lean_SMap_fold___redArg___closed__9));
v_buckets_627_ = lean_ctor_get(v_map_u2081_624_, 1);
lean_inc_ref(v_buckets_627_);
lean_dec_ref(v_map_u2081_624_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_array_get_size(v_buckets_627_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v_buckets_627_);
v___x_631_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_625_, v_f_621_, v_init_622_);
return v___x_631_;
}
else
{
lean_object* v___f_632_; lean_object* v___f_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_inc(v_f_621_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_632_, 0, v_f_621_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_633_, 0, v___x_626_);
lean_closure_set(v___f_633_, 1, v___f_632_);
v___x_634_ = ((size_t)0ULL);
v___x_635_ = lean_usize_of_nat(v___x_629_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_626_, v___f_633_, v_buckets_627_, v___x_634_, v___x_635_, v_init_622_);
v___x_637_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_625_, v_f_621_, v___x_636_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_00_u03c3_642_, lean_object* v_f_643_, lean_object* v_init_644_, lean_object* v_m_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_SMap_fold___redArg(v_f_643_, v_init_644_, v_m_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_00_u03c3_651_, lean_object* v_f_652_, lean_object* v_init_653_, lean_object* v_m_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_SMap_fold(v_00_u03b1_647_, v_00_u03b2_648_, v_inst_649_, v_inst_650_, v_00_u03c3_651_, v_f_652_, v_init_653_, v_m_654_);
lean_dec_ref(v_inst_650_);
lean_dec_ref(v_inst_649_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_656_){
_start:
{
lean_object* v_map_u2081_657_; lean_object* v___x_658_; 
v_map_u2081_657_ = lean_ctor_get(v_m_656_, 0);
v___x_658_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_SMap_numBuckets___redArg(v_m_659_);
lean_dec_ref(v_m_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_m_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_SMap_numBuckets___redArg(v_m_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_m_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_SMap_numBuckets(v_00_u03b1_667_, v_00_u03b2_668_, v_inst_669_, v_inst_670_, v_m_671_);
lean_dec_ref(v_m_671_);
lean_dec_ref(v_inst_670_);
lean_dec_ref(v_inst_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_673_, lean_object* v_a_674_, lean_object* v_b_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_a_674_);
lean_ctor_set(v___x_676_, 1, v_b_675_);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_es_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_679_){
_start:
{
lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___f_680_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_681_ = lean_box(0);
v___x_682_ = l_Lean_SMap_fold___redArg(v___f_680_, v___x_681_, v_m_679_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_m_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_SMap_toList___redArg(v_m_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_m_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_SMap_toList(v_00_u03b1_689_, v_00_u03b2_690_, v_inst_691_, v_inst_692_, v_m_693_);
lean_dec_ref(v_inst_692_);
lean_dec_ref(v_inst_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg___lam__0(lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_s_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_fst_699_; lean_object* v_snd_700_; lean_object* v___x_701_; 
v_fst_699_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_fst_699_);
v_snd_700_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_snd_700_);
lean_dec_ref(v_x_698_);
v___x_701_ = l_Lean_SMap_insert___redArg(v_inst_695_, v_inst_696_, v_s_697_, v_fst_699_, v_snd_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg(lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_es_704_){
_start:
{
lean_object* v___f_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___f_705_ = lean_alloc_closure((void*)(l_Lean_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_705_, 0, v_inst_702_);
lean_closure_set(v___f_705_, 1, v_inst_703_);
v___x_706_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_707_ = l_List_foldl___redArg(v___f_705_, v___x_706_, v_es_704_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_es_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_List_toSMap___redArg(v_inst_710_, v_inst_711_, v_es_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_717_, lean_object* v_v_718_, lean_object* v_prec_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_720_ = l_Lean_SMap_toList___redArg(v_v_718_);
v___x_721_ = l_List_repr___redArg(v___x_717_, v___x_720_);
v___x_722_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Repr_addAppParen(v___x_723_, v_prec_719_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_725_, lean_object* v_v_726_, lean_object* v_prec_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_instReprSMap___redArg___lam__0(v___x_725_, v_v_726_, v_prec_727_);
lean_dec(v_prec_727_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_){
_start:
{
lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___f_733_; 
v___f_731_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_731_, 0, v_inst_730_);
v___x_732_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_732_, 0, lean_box(0));
lean_closure_set(v___x_732_, 1, lean_box(0));
lean_closure_set(v___x_732_, 2, v_inst_729_);
lean_closure_set(v___x_732_, 3, v___f_731_);
v___f_733_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v___x_732_);
return v___f_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_734_, lean_object* v_00_u03b2_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_inst_738_, lean_object* v_inst_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_instReprSMap___redArg(v_inst_738_, v_inst_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_inst_745_, lean_object* v_inst_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_instReprSMap(v_00_u03b1_741_, v_00_u03b2_742_, v_x_743_, v_x_744_, v_inst_745_, v_inst_746_);
lean_dec_ref(v_x_744_);
lean_dec_ref(v_x_743_);
return v_res_747_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Append(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_SMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
