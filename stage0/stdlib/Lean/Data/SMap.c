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
lean_dec_ref(v___x_161_);
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
lean_dec_ref(v___x_176_);
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
lean_dec_ref(v___x_200_);
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
lean_dec_ref(v___x_217_);
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
lean_object* v_map_u2081_310_; lean_object* v_toApplicative_311_; lean_object* v_toBind_312_; lean_object* v_map_u2082_313_; lean_object* v_buckets_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
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
lean_inc(v_f_309_);
lean_inc_ref(v_inst_307_);
v___f_315_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_315_, 0, v_inst_307_);
lean_closure_set(v___f_315_, 1, v_map_u2082_313_);
lean_closure_set(v___f_315_, 2, v_f_309_);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_array_get_size(v_buckets_314_);
v___x_318_ = lean_box(0);
v___x_319_ = lean_nat_dec_lt(v___x_316_, v___x_317_);
if (v___x_319_ == 0)
{
lean_object* v_toPure_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_inc_ref(v_toApplicative_311_);
lean_dec_ref(v_buckets_314_);
lean_dec(v_f_309_);
lean_dec_ref(v_inst_307_);
v_toPure_320_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_inc(v_toPure_320_);
lean_dec_ref(v_toApplicative_311_);
v___x_321_ = lean_apply_2(v_toPure_320_, lean_box(0), v___x_318_);
v___x_322_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_321_, v___f_315_);
return v___x_322_;
}
else
{
lean_object* v___f_323_; lean_object* v___f_324_; uint8_t v___x_325_; 
v___f_323_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 1);
lean_closure_set(v___f_323_, 0, v_f_309_);
lean_inc_ref(v_inst_307_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_324_, 0, v_inst_307_);
lean_closure_set(v___f_324_, 1, v___f_323_);
v___x_325_ = lean_nat_dec_le(v___x_317_, v___x_317_);
if (v___x_325_ == 0)
{
if (v___x_319_ == 0)
{
lean_object* v_toPure_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_inc_ref(v_toApplicative_311_);
lean_dec_ref(v___f_324_);
lean_dec_ref(v_buckets_314_);
lean_dec_ref(v_inst_307_);
v_toPure_326_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_inc(v_toPure_326_);
lean_dec_ref(v_toApplicative_311_);
v___x_327_ = lean_apply_2(v_toPure_326_, lean_box(0), v___x_318_);
v___x_328_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_327_, v___f_315_);
return v___x_328_;
}
else
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = ((size_t)0ULL);
v___x_330_ = lean_usize_of_nat(v___x_317_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_307_, v___f_324_, v_buckets_314_, v___x_329_, v___x_330_, v___x_318_);
v___x_332_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_331_, v___f_315_);
return v___x_332_;
}
}
else
{
size_t v___x_333_; size_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_333_ = ((size_t)0ULL);
v___x_334_ = lean_usize_of_nat(v___x_317_);
v___x_335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_307_, v___f_324_, v_buckets_314_, v___x_333_, v___x_334_, v___x_318_);
v___x_336_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_335_, v___f_315_);
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_m_341_, lean_object* v_inst_342_, lean_object* v_s_343_, lean_object* v_f_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_SMap_forM___redArg(v_inst_342_, v_s_343_, v_f_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_m_350_, lean_object* v_inst_351_, lean_object* v_s_352_, lean_object* v_f_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_SMap_forM(v_00_u03b1_346_, v_00_u03b2_347_, v_inst_348_, v_inst_349_, v_m_350_, v_inst_351_, v_s_352_, v_f_353_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_355_, lean_object* v_x_356_, lean_object* v_y_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_x_356_);
lean_ctor_set(v___x_358_, 1, v_y_357_);
v___x_359_ = lean_apply_1(v_f_355_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_360_, lean_object* v_s_361_, lean_object* v_f_362_){
_start:
{
lean_object* v___f_363_; lean_object* v___x_364_; 
v___f_363_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_363_, 0, v_f_362_);
v___x_364_ = l_Lean_SMap_forM___redArg(v_inst_360_, v_s_361_, v___f_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_365_){
_start:
{
lean_object* v___f_366_; 
v___f_366_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_366_, 0, v_inst_365_);
return v___f_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_m_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v___f_373_; 
v___f_373_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_373_, 0, v_inst_372_);
return v___f_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_m_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_374_, v_00_u03b2_375_, v_inst_376_, v_inst_377_, v_m_378_, v_inst_379_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_381_, lean_object* v_____do__lift_382_){
_start:
{
if (lean_obj_tag(v_____do__lift_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v_____do__lift_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v_____do__lift_382_);
v___x_384_ = lean_apply_2(v_toPure_381_, lean_box(0), v_a_383_);
return v___x_384_;
}
else
{
lean_object* v_a_385_; lean_object* v_snd_386_; lean_object* v___x_387_; 
v_a_385_ = lean_ctor_get(v_____do__lift_382_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v_____do__lift_382_);
v_snd_386_ = lean_ctor_get(v_a_385_, 1);
lean_inc(v_snd_386_);
lean_dec(v_a_385_);
v___x_387_ = lean_apply_2(v_toPure_381_, lean_box(0), v_snd_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_388_, lean_object* v_____do__lift_389_){
_start:
{
if (lean_obj_tag(v_____do__lift_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_a_390_ = lean_ctor_get(v_____do__lift_389_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_____do__lift_389_);
if (v_isSharedCheck_398_ == 0)
{
v___x_392_ = v_____do__lift_389_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v_____do__lift_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_397_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; 
v___x_396_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_395_);
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_409_; 
v_a_399_ = lean_ctor_get(v_____do__lift_389_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_____do__lift_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_401_ = v_____do__lift_389_;
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v_____do__lift_389_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_409_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_399_);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_404_);
v___x_406_ = v___x_401_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_apply_2(v_toPure_388_, lean_box(0), v___x_406_);
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_410_, lean_object* v_toBind_411_, lean_object* v___f_412_, lean_object* v_x_413_, lean_object* v_y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_x_413_);
lean_ctor_set(v___x_416_, 1, v_y_414_);
v___x_417_ = lean_apply_2(v___y_410_, v___x_416_, v___y_415_);
v___x_418_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v___x_417_, v___f_412_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_419_, lean_object* v_00_u03b2_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_toApplicative_444_; lean_object* v_toBind_445_; lean_object* v_toPure_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___x_140__overap_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc_ref_n(v_inst_419_, 7);
v___f_424_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_424_, 0, v_inst_419_);
v___f_425_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_425_, 0, v_inst_419_);
v___f_426_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_426_, 0, v_inst_419_);
v___f_427_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_427_, 0, v_inst_419_);
v___x_428_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_428_, 0, lean_box(0));
lean_closure_set(v___x_428_, 1, lean_box(0));
lean_closure_set(v___x_428_, 2, v_inst_419_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___f_424_);
v___x_430_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_430_, 0, lean_box(0));
lean_closure_set(v___x_430_, 1, lean_box(0));
lean_closure_set(v___x_430_, 2, v_inst_419_);
v___x_431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
lean_ctor_set(v___x_431_, 2, v___f_425_);
lean_ctor_set(v___x_431_, 3, v___f_426_);
lean_ctor_set(v___x_431_, 4, v___f_427_);
v___x_432_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_432_, 0, lean_box(0));
lean_closure_set(v___x_432_, 1, lean_box(0));
lean_closure_set(v___x_432_, 2, v_inst_419_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_inc_ref_n(v___x_433_, 6);
v___f_434_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_434_, 0, v___x_433_);
v___f_435_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_435_, 0, v___x_433_);
v___f_436_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_436_, 0, v___x_433_);
v___f_437_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_437_, 0, v___x_433_);
v___x_438_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_438_, 0, lean_box(0));
lean_closure_set(v___x_438_, 1, lean_box(0));
lean_closure_set(v___x_438_, 2, v___x_433_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___f_434_);
v___x_440_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_440_, 0, lean_box(0));
lean_closure_set(v___x_440_, 1, lean_box(0));
lean_closure_set(v___x_440_, 2, v___x_433_);
v___x_441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_ctor_set(v___x_441_, 2, v___f_435_);
lean_ctor_set(v___x_441_, 3, v___f_436_);
lean_ctor_set(v___x_441_, 4, v___f_437_);
v___x_442_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_442_, 0, lean_box(0));
lean_closure_set(v___x_442_, 1, lean_box(0));
lean_closure_set(v___x_442_, 2, v___x_433_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v_toApplicative_444_ = lean_ctor_get(v_inst_419_, 0);
lean_inc_ref(v_toApplicative_444_);
v_toBind_445_ = lean_ctor_get(v_inst_419_, 1);
lean_inc_n(v_toBind_445_, 2);
lean_dec_ref(v_inst_419_);
v_toPure_446_ = lean_ctor_get(v_toApplicative_444_, 1);
lean_inc_n(v_toPure_446_, 2);
lean_dec_ref(v_toApplicative_444_);
v___f_447_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_447_, 0, v_toPure_446_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_448_, 0, v_toPure_446_);
v___f_449_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_449_, 0, v___y_423_);
lean_closure_set(v___f_449_, 1, v_toBind_445_);
lean_closure_set(v___f_449_, 2, v___f_448_);
v___x_140__overap_450_ = l_Lean_SMap_forM___redArg(v___x_443_, v___y_421_, v___f_449_);
v___x_451_ = lean_apply_1(v___x_140__overap_450_, v___y_422_);
v___x_452_ = lean_apply_4(v_toBind_445_, lean_box(0), lean_box(0), v___x_451_, v___f_447_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_453_){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_454_, 0, v_inst_453_);
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_m_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; 
v___f_461_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_461_, 0, v_inst_460_);
return v___f_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_m_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_462_, v_00_u03b2_463_, v_inst_464_, v_inst_465_, v_m_466_, v_inst_467_);
lean_dec_ref(v_inst_465_);
lean_dec_ref(v_inst_464_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object* v_s_469_){
_start:
{
lean_object* v_map_u2081_470_; lean_object* v_map_u2082_471_; lean_object* v_buckets_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_485_; 
v_map_u2081_470_ = lean_ctor_get(v_s_469_, 0);
lean_inc_ref(v_map_u2081_470_);
v_map_u2082_471_ = lean_ctor_get(v_s_469_, 1);
lean_inc_ref(v_map_u2082_471_);
lean_dec_ref(v_s_469_);
v_buckets_472_ = lean_ctor_get(v_map_u2081_470_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_map_u2081_470_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_map_u2081_470_, 0);
lean_dec(v_unused_486_);
v___x_474_ = v_map_u2081_470_;
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_buckets_472_);
lean_dec(v_map_u2081_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(0u);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_476_);
lean_ctor_set(v___x_474_, 0, v_buckets_472_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_buckets_472_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_484_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_box(0);
v___x_482_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_u2082_471_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_480_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object* v_00_u03b1_487_, lean_object* v_00_u03b2_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_s_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_SMap_iter___redArg(v_s_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_s_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_SMap_iter(v_00_u03b1_493_, v_00_u03b2_494_, v_inst_495_, v_inst_496_, v_s_497_);
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_inst_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_499_){
_start:
{
uint8_t v_stage_u2081_500_; 
v_stage_u2081_500_ = lean_ctor_get_uint8(v_m_499_, sizeof(void*)*2);
if (v_stage_u2081_500_ == 0)
{
return v_m_499_;
}
else
{
lean_object* v_map_u2081_501_; lean_object* v_map_u2082_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_map_u2081_501_ = lean_ctor_get(v_m_499_, 0);
v_map_u2082_502_ = lean_ctor_get(v_m_499_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_m_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v_m_499_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_map_u2082_502_);
lean_inc(v_map_u2081_501_);
lean_dec(v_m_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; lean_object* v___x_508_; 
v___x_506_ = 0;
if (v_isShared_505_ == 0)
{
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_map_u2081_501_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_map_u2082_502_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*2, v___x_506_);
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_m_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_SMap_switch___redArg(v_m_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_m_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_SMap_switch(v_00_u03b1_517_, v_00_u03b2_518_, v_inst_519_, v_inst_520_, v_m_521_);
lean_dec_ref(v_inst_520_);
lean_dec_ref(v_inst_519_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_523_, lean_object* v_s_524_, lean_object* v_m_525_){
_start:
{
lean_object* v_map_u2082_526_; lean_object* v___x_527_; 
v_map_u2082_526_ = lean_ctor_get(v_m_525_, 1);
lean_inc_ref(v_map_u2082_526_);
lean_dec_ref(v_m_525_);
v___x_527_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_526_, v_f_523_, v_s_524_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_00_u03c3_532_, lean_object* v_f_533_, lean_object* v_s_534_, lean_object* v_m_535_){
_start:
{
lean_object* v_map_u2082_536_; lean_object* v___x_537_; 
v_map_u2082_536_ = lean_ctor_get(v_m_535_, 1);
lean_inc_ref(v_map_u2082_536_);
lean_dec_ref(v_m_535_);
v___x_537_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_536_, v_f_533_, v_s_534_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_00_u03c3_542_, lean_object* v_f_543_, lean_object* v_s_544_, lean_object* v_m_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_SMap_foldStage2(v_00_u03b1_538_, v_00_u03b2_539_, v_inst_540_, v_inst_541_, v_00_u03c3_542_, v_f_543_, v_s_544_, v_m_545_);
lean_dec_ref(v_inst_541_);
lean_dec_ref(v_inst_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_547_, lean_object* v_f_548_, lean_object* v_map_u2082_549_, lean_object* v_____do__lift_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_547_, v_f_548_, v_map_u2082_549_, v_____do__lift_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object* v_inst_552_, lean_object* v_f_553_, lean_object* v_acc_554_, lean_object* v_l_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_552_, v_f_553_, v_acc_554_, v_l_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_557_, lean_object* v_f_558_, lean_object* v_init_559_, lean_object* v_map_560_){
_start:
{
lean_object* v_map_u2081_561_; lean_object* v_toApplicative_562_; lean_object* v_toBind_563_; lean_object* v_map_u2082_564_; lean_object* v_buckets_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_map_u2081_561_ = lean_ctor_get(v_map_560_, 0);
lean_inc_ref(v_map_u2081_561_);
v_toApplicative_562_ = lean_ctor_get(v_inst_557_, 0);
v_toBind_563_ = lean_ctor_get(v_inst_557_, 1);
lean_inc(v_toBind_563_);
v_map_u2082_564_ = lean_ctor_get(v_map_560_, 1);
lean_inc_ref(v_map_u2082_564_);
lean_dec_ref(v_map_560_);
v_buckets_565_ = lean_ctor_get(v_map_u2081_561_, 1);
lean_inc_ref(v_buckets_565_);
lean_dec_ref(v_map_u2081_561_);
lean_inc(v_f_558_);
lean_inc_ref(v_inst_557_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_566_, 0, v_inst_557_);
lean_closure_set(v___f_566_, 1, v_f_558_);
lean_closure_set(v___f_566_, 2, v_map_u2082_564_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_array_get_size(v_buckets_565_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v_toPure_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_inc_ref(v_toApplicative_562_);
lean_dec_ref(v_buckets_565_);
lean_dec(v_f_558_);
lean_dec_ref(v_inst_557_);
v_toPure_570_ = lean_ctor_get(v_toApplicative_562_, 1);
lean_inc(v_toPure_570_);
lean_dec_ref(v_toApplicative_562_);
v___x_571_ = lean_apply_2(v_toPure_570_, lean_box(0), v_init_559_);
v___x_572_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_571_, v___f_566_);
return v___x_572_;
}
else
{
lean_object* v___f_573_; uint8_t v___x_574_; 
lean_inc_ref(v_inst_557_);
v___f_573_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_573_, 0, v_inst_557_);
lean_closure_set(v___f_573_, 1, v_f_558_);
v___x_574_ = lean_nat_dec_le(v___x_568_, v___x_568_);
if (v___x_574_ == 0)
{
if (v___x_569_ == 0)
{
lean_object* v_toPure_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_inc_ref(v_toApplicative_562_);
lean_dec_ref(v___f_573_);
lean_dec_ref(v_buckets_565_);
lean_dec_ref(v_inst_557_);
v_toPure_575_ = lean_ctor_get(v_toApplicative_562_, 1);
lean_inc(v_toPure_575_);
lean_dec_ref(v_toApplicative_562_);
v___x_576_ = lean_apply_2(v_toPure_575_, lean_box(0), v_init_559_);
v___x_577_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_576_, v___f_566_);
return v___x_577_;
}
else
{
size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_568_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_557_, v___f_573_, v_buckets_565_, v___x_578_, v___x_579_, v_init_559_);
v___x_581_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_580_, v___f_566_);
return v___x_581_;
}
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_568_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_557_, v___f_573_, v_buckets_565_, v___x_582_, v___x_583_, v_init_559_);
v___x_585_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_584_, v___f_566_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object* v_00_u03b1_586_, lean_object* v_00_u03b2_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_00_u03c3_590_, lean_object* v_m_591_, lean_object* v_inst_592_, lean_object* v_f_593_, lean_object* v_init_594_, lean_object* v_map_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_SMap_foldM___redArg(v_inst_592_, v_f_593_, v_init_594_, v_map_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_00_u03c3_601_, lean_object* v_m_602_, lean_object* v_inst_603_, lean_object* v_f_604_, lean_object* v_init_605_, lean_object* v_map_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_SMap_foldM(v_00_u03b1_597_, v_00_u03b2_598_, v_inst_599_, v_inst_600_, v_00_u03c3_601_, v_m_602_, v_inst_603_, v_f_604_, v_init_605_, v_map_606_);
lean_dec_ref(v_inst_600_);
lean_dec_ref(v_inst_599_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object* v_f_608_, lean_object* v_x1_609_, lean_object* v_x2_610_, lean_object* v_x3_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_apply_3(v_f_608_, v_x1_609_, v_x2_610_, v_x3_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__1(lean_object* v___x_613_, lean_object* v___f_614_, lean_object* v_acc_615_, lean_object* v_l_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_613_, v___f_614_, v_acc_615_, v_l_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object* v_f_637_, lean_object* v_init_638_, lean_object* v_m_639_){
_start:
{
lean_object* v_map_u2081_640_; lean_object* v_map_u2082_641_; lean_object* v___x_642_; lean_object* v_buckets_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_map_u2081_640_ = lean_ctor_get(v_m_639_, 0);
lean_inc_ref(v_map_u2081_640_);
v_map_u2082_641_ = lean_ctor_get(v_m_639_, 1);
lean_inc_ref(v_map_u2082_641_);
lean_dec_ref(v_m_639_);
v___x_642_ = ((lean_object*)(l_Lean_SMap_fold___redArg___closed__9));
v_buckets_643_ = lean_ctor_get(v_map_u2081_640_, 1);
lean_inc_ref(v_buckets_643_);
lean_dec_ref(v_map_u2081_640_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_array_get_size(v_buckets_643_);
v___x_646_ = lean_nat_dec_lt(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v_buckets_643_);
v___x_647_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_641_, v_f_637_, v_init_638_);
return v___x_647_;
}
else
{
lean_object* v___f_648_; lean_object* v___f_649_; uint8_t v___x_650_; 
lean_inc(v_f_637_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_648_, 0, v_f_637_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_649_, 0, v___x_642_);
lean_closure_set(v___f_649_, 1, v___f_648_);
v___x_650_ = lean_nat_dec_le(v___x_645_, v___x_645_);
if (v___x_650_ == 0)
{
if (v___x_646_ == 0)
{
lean_object* v___x_651_; 
lean_dec_ref(v___f_649_);
lean_dec_ref(v_buckets_643_);
v___x_651_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_641_, v_f_637_, v_init_638_);
return v___x_651_;
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_645_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_642_, v___f_649_, v_buckets_643_, v___x_652_, v___x_653_, v_init_638_);
v___x_655_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_641_, v_f_637_, v___x_654_);
return v___x_655_;
}
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_645_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_642_, v___f_649_, v_buckets_643_, v___x_656_, v___x_657_, v_init_638_);
v___x_659_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_641_, v_f_637_, v___x_658_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_660_, lean_object* v_00_u03b2_661_, lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_00_u03c3_664_, lean_object* v_f_665_, lean_object* v_init_666_, lean_object* v_m_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_SMap_fold___redArg(v_f_665_, v_init_666_, v_m_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_00_u03c3_673_, lean_object* v_f_674_, lean_object* v_init_675_, lean_object* v_m_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_SMap_fold(v_00_u03b1_669_, v_00_u03b2_670_, v_inst_671_, v_inst_672_, v_00_u03c3_673_, v_f_674_, v_init_675_, v_m_676_);
lean_dec_ref(v_inst_672_);
lean_dec_ref(v_inst_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_678_){
_start:
{
lean_object* v_map_u2081_679_; lean_object* v___x_680_; 
v_map_u2081_679_ = lean_ctor_get(v_m_678_, 0);
v___x_680_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_SMap_numBuckets___redArg(v_m_681_);
lean_dec_ref(v_m_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_m_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_SMap_numBuckets___redArg(v_m_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_689_, lean_object* v_00_u03b2_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_m_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_SMap_numBuckets(v_00_u03b1_689_, v_00_u03b2_690_, v_inst_691_, v_inst_692_, v_m_693_);
lean_dec_ref(v_m_693_);
lean_dec_ref(v_inst_692_);
lean_dec_ref(v_inst_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_695_, lean_object* v_a_696_, lean_object* v_b_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v_a_696_);
lean_ctor_set(v___x_698_, 1, v_b_697_);
v___x_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_es_695_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_701_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___f_702_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_703_ = lean_box(0);
v___x_704_ = l_Lean_SMap_fold___redArg(v___f_702_, v___x_703_, v_m_701_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_m_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_SMap_toList___redArg(v_m_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_m_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_SMap_toList(v_00_u03b1_711_, v_00_u03b2_712_, v_inst_713_, v_inst_714_, v_m_715_);
lean_dec_ref(v_inst_714_);
lean_dec_ref(v_inst_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap___redArg___lam__0(lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_s_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_723_; 
v_fst_721_ = lean_ctor_get(v_x_720_, 0);
lean_inc(v_fst_721_);
v_snd_722_ = lean_ctor_get(v_x_720_, 1);
lean_inc(v_snd_722_);
lean_dec_ref(v_x_720_);
v___x_723_ = l_Lean_SMap_insert___redArg(v_inst_717_, v_inst_718_, v_s_719_, v_fst_721_, v_snd_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap___redArg(lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_es_726_){
_start:
{
lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___f_727_ = lean_alloc_closure((void*)(l_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_727_, 0, v_inst_724_);
lean_closure_set(v___f_727_, 1, v_inst_725_);
v___x_728_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_729_ = l_List_foldl___redArg(v___f_727_, v___x_728_, v_es_726_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_es_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_List_toSMap___redArg(v_inst_732_, v_inst_733_, v_es_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_739_, lean_object* v_v_740_, lean_object* v_prec_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_742_ = l_Lean_SMap_toList___redArg(v_v_740_);
v___x_743_ = l_List_repr___redArg(v___x_739_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Repr_addAppParen(v___x_745_, v_prec_741_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_747_, lean_object* v_v_748_, lean_object* v_prec_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_instReprSMap___redArg___lam__0(v___x_747_, v_v_748_, v_prec_749_);
lean_dec(v_prec_749_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_751_, lean_object* v_inst_752_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___f_755_; 
v___f_753_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_753_, 0, v_inst_752_);
v___x_754_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_754_, 0, lean_box(0));
lean_closure_set(v___x_754_, 1, lean_box(0));
lean_closure_set(v___x_754_, 2, v_inst_751_);
lean_closure_set(v___x_754_, 3, v___f_753_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_755_, 0, v___x_754_);
return v___f_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_inst_760_, lean_object* v_inst_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_instReprSMap___redArg(v_inst_760_, v_inst_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_inst_767_, lean_object* v_inst_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_instReprSMap(v_00_u03b1_763_, v_00_u03b2_764_, v_x_765_, v_x_766_, v_inst_767_, v_inst_768_);
lean_dec_ref(v_x_766_);
lean_dec_ref(v_x_765_);
return v_res_769_;
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
