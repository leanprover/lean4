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
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__1, &l_Lean_SMap_instInhabited___closed__1_once, _init_l_Lean_SMap_instInhabited___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__0, &l_Lean_SMap_instInhabited___closed__0_once, _init_l_Lean_SMap_instInhabited___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__3(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_9_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__3, &l_Lean_SMap_instInhabited___closed__3_once, _init_l_Lean_SMap_instInhabited___closed__3);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__5(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_13_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__2, &l_Lean_SMap_instInhabited___closed__2_once, _init_l_Lean_SMap_instInhabited___closed__2);
v___x_14_ = 1;
v___x_15_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_12_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*2, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited(lean_object* v_00_u03b1_16_, lean_object* v_00_u03b2_17_, lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__5, &l_Lean_SMap_instInhabited___closed__5_once, _init_l_Lean_SMap_instInhabited___closed__5);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___boxed(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_SMap_instInhabited(v_00_u03b1_21_, v_00_u03b2_22_, v_inst_23_, v_inst_24_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__5, &l_Lean_SMap_instInhabited___closed__5_once, _init_l_Lean_SMap_instInhabited___closed__5);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___boxed(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_SMap_empty(v_00_u03b1_31_, v_00_u03b2_32_, v_inst_33_, v_inst_34_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg(lean_object* v_m_36_, uint8_t v_stage_u2081_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_39_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_39_, 0, v_m_36_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
lean_ctor_set_uint8(v___x_39_, sizeof(void*)*2, v_stage_u2081_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg___boxed(lean_object* v_m_40_, lean_object* v_stage_u2081_41_){
_start:
{
uint8_t v_stage_u2081_boxed_42_; lean_object* v_res_43_; 
v_stage_u2081_boxed_42_ = lean_unbox(v_stage_u2081_41_);
v_res_43_ = l_Lean_SMap_fromHashMap___redArg(v_m_40_, v_stage_u2081_boxed_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_m_48_, uint8_t v_stage_u2081_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_51_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_51_, 0, v_m_48_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*2, v_stage_u2081_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___boxed(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_m_56_, lean_object* v_stage_u2081_57_){
_start:
{
uint8_t v_stage_u2081_boxed_58_; lean_object* v_res_59_; 
v_stage_u2081_boxed_58_ = lean_unbox(v_stage_u2081_57_);
v_res_59_ = l_Lean_SMap_fromHashMap(v_00_u03b1_52_, v_00_u03b2_53_, v_inst_54_, v_inst_55_, v_m_56_, v_stage_u2081_boxed_58_);
lean_dec_ref(v_inst_55_);
lean_dec_ref(v_inst_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_stage_u2081_65_; lean_object* v_map_u2081_66_; lean_object* v_map_u2082_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_147_; 
v_stage_u2081_65_ = lean_ctor_get_uint8(v_x_62_, sizeof(void*)*2);
v_map_u2081_66_ = lean_ctor_get(v_x_62_, 0);
v_map_u2082_67_ = lean_ctor_get(v_x_62_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_62_);
if (v_isSharedCheck_147_ == 0)
{
v___x_69_ = v_x_62_;
v_isShared_70_ = v_isSharedCheck_147_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_map_u2082_67_);
lean_inc(v_map_u2081_66_);
lean_dec(v_x_62_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_147_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___y_72_; lean_object* v_i_73_; lean_object* v___y_82_; lean_object* v___y_94_; lean_object* v_i_95_; 
if (v_stage_u2081_65_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_del_object(v___x_69_);
v___x_113_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_60_, v_inst_61_, v_map_u2082_67_, v_x_63_, v_x_64_);
v___x_114_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_114_, 0, v_map_u2081_66_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; 
lean_inc(v_x_63_);
lean_inc_ref(v_inst_61_);
lean_inc_ref(v_inst_60_);
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_60_, v_inst_61_, v_map_u2081_66_, v_x_63_);
switch(lean_obj_tag(v___x_115_))
{
case 0:
{
lean_object* v_index_116_; lean_object* v_size_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_69_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
v_index_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_index_116_);
lean_dec_ref_known(v___x_115_, 3);
v_size_117_ = lean_ctor_get(v_map_u2081_66_, 0);
lean_inc(v_size_117_);
v___x_118_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_66_, v_size_117_, v_index_116_, v_x_63_, v_x_64_);
lean_dec(v_index_116_);
v___x_119_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_119_;
}
case 1:
{
lean_object* v_index_120_; lean_object* v_size_121_; lean_object* v_keyArray_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
lean_del_object(v___x_69_);
v_index_120_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_index_120_);
lean_dec_ref_known(v___x_115_, 1);
v_size_121_ = lean_ctor_get(v_map_u2081_66_, 0);
v_keyArray_122_ = lean_ctor_get(v_map_u2081_66_, 1);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_size_121_, v___x_123_);
v___x_125_ = lean_array_get_size(v_keyArray_122_);
v___x_126_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v___x_124_);
lean_dec(v_index_120_);
goto v___jp_101_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_127_ = lean_unsigned_to_nat(4u);
v___x_128_ = lean_nat_mul(v___x_124_, v___x_127_);
v___x_129_ = lean_unsigned_to_nat(3u);
v___x_130_ = lean_nat_mul(v___x_125_, v___x_129_);
v___x_131_ = lean_nat_dec_le(v___x_128_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v___x_128_);
if (v___x_131_ == 0)
{
lean_dec(v___x_124_);
lean_dec(v_index_120_);
goto v___jp_101_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
v___x_132_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_66_, v___x_124_, v_index_120_, v_x_63_, v_x_64_);
lean_dec(v_index_120_);
v___x_133_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_133_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_133_;
}
}
}
default: 
{
lean_object* v_size_134_; lean_object* v_keyArray_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_size_134_ = lean_ctor_get(v_map_u2081_66_, 0);
v_keyArray_135_ = lean_ctor_get(v_map_u2081_66_, 1);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_size_134_, v___x_136_);
v___x_138_ = lean_array_get_size(v_keyArray_135_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec(v___x_137_);
lean_inc_ref(v_inst_61_);
lean_inc_ref(v_inst_60_);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_60_, v_inst_61_, v_map_u2081_66_);
v___y_82_ = v___x_140_;
goto v___jp_81_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_nat_mul(v___x_137_, v___x_141_);
lean_dec(v___x_137_);
v___x_143_ = lean_unsigned_to_nat(3u);
v___x_144_ = lean_nat_mul(v___x_138_, v___x_143_);
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_144_);
lean_dec(v___x_144_);
lean_dec(v___x_142_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_inc_ref(v_inst_61_);
lean_inc_ref(v_inst_60_);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_60_, v_inst_61_, v_map_u2081_66_);
v___y_82_ = v___x_146_;
goto v___jp_81_;
}
else
{
v___y_82_ = v_map_u2081_66_;
goto v___jp_81_;
}
}
}
}
}
v___jp_71_:
{
lean_object* v_size_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v_size_74_ = lean_ctor_get(v___y_72_, 0);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_add(v_size_74_, v___x_75_);
v___x_77_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_72_, v___x_76_, v_i_73_, v_x_63_, v_x_64_);
lean_dec(v_i_73_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_77_);
v___x_79_ = v___x_69_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_80_, sizeof(void*)*2, v_stage_u2081_65_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
v___jp_81_:
{
lean_object* v___x_83_; 
lean_inc(v_x_63_);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_60_, v_inst_61_, v___y_82_, v_x_63_);
switch(lean_obj_tag(v___x_83_))
{
case 0:
{
lean_object* v_index_84_; lean_object* v_size_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
lean_del_object(v___x_69_);
v_index_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_index_84_);
lean_dec_ref_known(v___x_83_, 3);
v_size_85_ = lean_ctor_get(v___y_82_, 0);
lean_inc(v_size_85_);
v___x_86_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_82_, v_size_85_, v_index_84_, v_x_63_, v_x_64_);
lean_dec(v_index_84_);
v___x_87_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_87_;
}
case 1:
{
lean_object* v_index_88_; 
v_index_88_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_index_88_);
lean_dec_ref_known(v___x_83_, 1);
v___y_72_ = v___y_82_;
v_i_73_ = v_index_88_;
goto v___jp_71_;
}
default: 
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_82_, v___x_89_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_index_91_; 
v_index_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_index_91_);
lean_dec_ref_known(v___x_90_, 1);
v___y_72_ = v___y_82_;
v_i_73_ = v_index_91_;
goto v___jp_71_;
}
else
{
lean_object* v___x_92_; 
lean_del_object(v___x_69_);
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v___x_92_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_92_, 0, v___y_82_);
lean_ctor_set(v___x_92_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_92_;
}
}
}
}
v___jp_93_:
{
lean_object* v_size_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_size_96_ = lean_ctor_get(v___y_94_, 0);
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = lean_nat_add(v_size_96_, v___x_97_);
v___x_99_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_94_, v___x_98_, v_i_95_, v_x_63_, v_x_64_);
lean_dec(v_i_95_);
v___x_100_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_100_;
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_inc_ref(v_inst_61_);
lean_inc_ref(v_inst_60_);
v___x_102_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_60_, v_inst_61_, v_map_u2081_66_);
lean_inc(v_x_63_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_60_, v_inst_61_, v___x_102_, v_x_63_);
switch(lean_obj_tag(v___x_103_))
{
case 0:
{
lean_object* v_index_104_; lean_object* v_size_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_index_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_index_104_);
lean_dec_ref_known(v___x_103_, 3);
v_size_105_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_size_105_);
v___x_106_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_102_, v_size_105_, v_index_104_, v_x_63_, v_x_64_);
lean_dec(v_index_104_);
v___x_107_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_107_;
}
case 1:
{
lean_object* v_index_108_; 
v_index_108_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_index_108_);
lean_dec_ref_known(v___x_103_, 1);
v___y_94_ = v___x_102_;
v_i_95_ = v_index_108_;
goto v___jp_93_;
}
default: 
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_102_, v___x_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_index_111_; 
v_index_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_index_111_);
lean_dec_ref_known(v___x_110_, 1);
v___y_94_ = v___x_102_;
v_i_95_ = v_index_111_;
goto v___jp_93_;
}
else
{
lean_object* v___x_112_; 
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v___x_112_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_112_, 0, v___x_102_);
lean_ctor_set(v___x_112_, 1, v_map_u2082_67_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*2, v_stage_u2081_65_);
return v___x_112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_SMap_insert___redArg(v_inst_150_, v_inst_151_, v_x_152_, v_x_153_, v_x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27___redArg(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
uint8_t v_stage_u2081_161_; lean_object* v_map_u2081_162_; lean_object* v_map_u2082_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_243_; 
v_stage_u2081_161_ = lean_ctor_get_uint8(v_x_158_, sizeof(void*)*2);
v_map_u2081_162_ = lean_ctor_get(v_x_158_, 0);
v_map_u2082_163_ = lean_ctor_get(v_x_158_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_243_ == 0)
{
v___x_165_ = v_x_158_;
v_isShared_166_ = v_isSharedCheck_243_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_map_u2082_163_);
lean_inc(v_map_u2081_162_);
lean_dec(v_x_158_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_243_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___y_168_; lean_object* v_i_169_; lean_object* v___y_178_; lean_object* v___y_190_; lean_object* v_i_191_; 
if (v_stage_u2081_161_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_del_object(v___x_165_);
v___x_209_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_156_, v_inst_157_, v_map_u2082_163_, v_x_159_, v_x_160_);
v___x_210_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_210_, 0, v_map_u2081_162_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
lean_inc(v_x_159_);
lean_inc_ref(v_inst_157_);
lean_inc_ref(v_inst_156_);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_156_, v_inst_157_, v_map_u2081_162_, v_x_159_);
switch(lean_obj_tag(v___x_211_))
{
case 0:
{
lean_object* v_index_212_; lean_object* v_size_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_del_object(v___x_165_);
lean_dec_ref(v_inst_157_);
lean_dec_ref(v_inst_156_);
v_index_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_index_212_);
lean_dec_ref_known(v___x_211_, 3);
v_size_213_ = lean_ctor_get(v_map_u2081_162_, 0);
lean_inc(v_size_213_);
v___x_214_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_162_, v_size_213_, v_index_212_, v_x_159_, v_x_160_);
lean_dec(v_index_212_);
v___x_215_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_215_;
}
case 1:
{
lean_object* v_index_216_; lean_object* v_size_217_; lean_object* v_keyArray_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
lean_del_object(v___x_165_);
v_index_216_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_index_216_);
lean_dec_ref_known(v___x_211_, 1);
v_size_217_ = lean_ctor_get(v_map_u2081_162_, 0);
v_keyArray_218_ = lean_ctor_get(v_map_u2081_162_, 1);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_size_217_, v___x_219_);
v___x_221_ = lean_array_get_size(v_keyArray_218_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec(v___x_220_);
lean_dec(v_index_216_);
goto v___jp_197_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = lean_nat_mul(v___x_220_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(3u);
v___x_226_ = lean_nat_mul(v___x_221_, v___x_225_);
v___x_227_ = lean_nat_dec_le(v___x_224_, v___x_226_);
lean_dec(v___x_226_);
lean_dec(v___x_224_);
if (v___x_227_ == 0)
{
lean_dec(v___x_220_);
lean_dec(v_index_216_);
goto v___jp_197_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v_inst_157_);
lean_dec_ref(v_inst_156_);
v___x_228_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_162_, v___x_220_, v_index_216_, v_x_159_, v_x_160_);
lean_dec(v_index_216_);
v___x_229_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_229_;
}
}
}
default: 
{
lean_object* v_size_230_; lean_object* v_keyArray_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_size_230_ = lean_ctor_get(v_map_u2081_162_, 0);
v_keyArray_231_ = lean_ctor_get(v_map_u2081_162_, 1);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_size_230_, v___x_232_);
v___x_234_ = lean_array_get_size(v_keyArray_231_);
v___x_235_ = lean_nat_dec_lt(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v___x_233_);
lean_inc_ref(v_inst_157_);
lean_inc_ref(v_inst_156_);
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_156_, v_inst_157_, v_map_u2081_162_);
v___y_178_ = v___x_236_;
goto v___jp_177_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_237_ = lean_unsigned_to_nat(4u);
v___x_238_ = lean_nat_mul(v___x_233_, v___x_237_);
lean_dec(v___x_233_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = lean_nat_mul(v___x_234_, v___x_239_);
v___x_241_ = lean_nat_dec_le(v___x_238_, v___x_240_);
lean_dec(v___x_240_);
lean_dec(v___x_238_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
lean_inc_ref(v_inst_157_);
lean_inc_ref(v_inst_156_);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_156_, v_inst_157_, v_map_u2081_162_);
v___y_178_ = v___x_242_;
goto v___jp_177_;
}
else
{
v___y_178_ = v_map_u2081_162_;
goto v___jp_177_;
}
}
}
}
}
v___jp_167_:
{
lean_object* v_size_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v_size_170_ = lean_ctor_get(v___y_168_, 0);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_size_170_, v___x_171_);
v___x_173_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_168_, v___x_172_, v_i_169_, v_x_159_, v_x_160_);
lean_dec(v_i_169_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_173_);
v___x_175_ = v___x_165_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_176_, sizeof(void*)*2, v_stage_u2081_161_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
v___jp_177_:
{
lean_object* v___x_179_; 
lean_inc(v_x_159_);
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_156_, v_inst_157_, v___y_178_, v_x_159_);
switch(lean_obj_tag(v___x_179_))
{
case 0:
{
lean_object* v_index_180_; lean_object* v_size_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_del_object(v___x_165_);
v_index_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_index_180_);
lean_dec_ref_known(v___x_179_, 3);
v_size_181_ = lean_ctor_get(v___y_178_, 0);
lean_inc(v_size_181_);
v___x_182_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_178_, v_size_181_, v_index_180_, v_x_159_, v_x_160_);
lean_dec(v_index_180_);
v___x_183_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_183_;
}
case 1:
{
lean_object* v_index_184_; 
v_index_184_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_index_184_);
lean_dec_ref_known(v___x_179_, 1);
v___y_168_ = v___y_178_;
v_i_169_ = v_index_184_;
goto v___jp_167_;
}
default: 
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_178_, v___x_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_index_187_; 
v_index_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_index_187_);
lean_dec_ref_known(v___x_186_, 1);
v___y_168_ = v___y_178_;
v_i_169_ = v_index_187_;
goto v___jp_167_;
}
else
{
lean_object* v___x_188_; 
lean_del_object(v___x_165_);
lean_dec(v_x_160_);
lean_dec(v_x_159_);
v___x_188_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_188_, 0, v___y_178_);
lean_ctor_set(v___x_188_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_188_;
}
}
}
}
v___jp_189_:
{
lean_object* v_size_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_size_192_ = lean_ctor_get(v___y_190_, 0);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_add(v_size_192_, v___x_193_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_190_, v___x_194_, v_i_191_, v_x_159_, v_x_160_);
lean_dec(v_i_191_);
v___x_196_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_196_;
}
v___jp_197_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_inc_ref(v_inst_157_);
lean_inc_ref(v_inst_156_);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_156_, v_inst_157_, v_map_u2081_162_);
lean_inc(v_x_159_);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_156_, v_inst_157_, v___x_198_, v_x_159_);
switch(lean_obj_tag(v___x_199_))
{
case 0:
{
lean_object* v_index_200_; lean_object* v_size_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_index_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_199_, 3);
v_size_201_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_size_201_);
v___x_202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_198_, v_size_201_, v_index_200_, v_x_159_, v_x_160_);
lean_dec(v_index_200_);
v___x_203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_203_;
}
case 1:
{
lean_object* v_index_204_; 
v_index_204_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_204_);
lean_dec_ref_known(v___x_199_, 1);
v___y_190_ = v___x_198_;
v_i_191_ = v_index_204_;
goto v___jp_189_;
}
default: 
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_198_, v___x_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_index_207_; 
v_index_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_index_207_);
lean_dec_ref_known(v___x_206_, 1);
v___y_190_ = v___x_198_;
v_i_191_ = v_index_207_;
goto v___jp_189_;
}
else
{
lean_object* v___x_208_; 
lean_dec(v_x_160_);
lean_dec(v_x_159_);
v___x_208_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_208_, 0, v___x_198_);
lean_ctor_set(v___x_208_, 1, v_map_u2082_163_);
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*2, v_stage_u2081_161_);
return v___x_208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_SMap_insert_x27___redArg(v_inst_246_, v_inst_247_, v_x_248_, v_x_249_, v_x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg(lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_stage_u2081_256_; 
v_stage_u2081_256_ = lean_ctor_get_uint8(v_x_254_, sizeof(void*)*2);
if (v_stage_u2081_256_ == 0)
{
lean_object* v_map_u2081_257_; lean_object* v_map_u2082_258_; lean_object* v___x_259_; 
v_map_u2081_257_ = lean_ctor_get(v_x_254_, 0);
v_map_u2082_258_ = lean_ctor_get(v_x_254_, 1);
lean_inc(v_x_255_);
lean_inc_ref(v_inst_253_);
lean_inc_ref(v_inst_252_);
v___x_259_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_252_, v_inst_253_, v_map_u2082_258_, v_x_255_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_252_, v_inst_253_, v_map_u2081_257_, v_x_255_);
return v___x_260_;
}
else
{
lean_dec(v_x_255_);
lean_dec_ref(v_inst_253_);
lean_dec_ref(v_inst_252_);
return v___x_259_;
}
}
else
{
lean_object* v_map_u2081_261_; lean_object* v___x_262_; 
v_map_u2081_261_ = lean_ctor_get(v_x_254_, 0);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_252_, v_inst_253_, v_map_u2081_261_, v_x_255_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg___boxed(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_SMap_find_x3f___redArg(v_inst_263_, v_inst_264_, v_x_265_, v_x_266_);
lean_dec_ref(v_x_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_SMap_find_x3f___redArg(v_inst_270_, v_inst_271_, v_x_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___boxed(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_SMap_find_x3f(v_00_u03b1_275_, v_00_u03b2_276_, v_inst_277_, v_inst_278_, v_x_279_, v_x_280_);
lean_dec_ref(v_x_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg(lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_m_284_, lean_object* v_a_285_, lean_object* v_b_u2080_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_SMap_find_x3f___redArg(v_inst_282_, v_inst_283_, v_m_284_, v_a_285_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_inc(v_b_u2080_286_);
return v_b_u2080_286_;
}
else
{
lean_object* v_val_288_; 
v_val_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v___x_287_, 1);
return v_val_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg___boxed(lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_m_291_, lean_object* v_a_292_, lean_object* v_b_u2080_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_SMap_findD___redArg(v_inst_289_, v_inst_290_, v_m_291_, v_a_292_, v_b_u2080_293_);
lean_dec(v_b_u2080_293_);
lean_dec_ref(v_m_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_m_299_, lean_object* v_a_300_, lean_object* v_b_u2080_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_SMap_find_x3f___redArg(v_inst_297_, v_inst_298_, v_m_299_, v_a_300_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_inc(v_b_u2080_301_);
return v_b_u2080_301_;
}
else
{
lean_object* v_val_303_; 
v_val_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_val_303_);
lean_dec_ref_known(v___x_302_, 1);
return v_val_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___boxed(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_m_308_, lean_object* v_a_309_, lean_object* v_b_u2080_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_SMap_findD(v_00_u03b1_304_, v_00_u03b2_305_, v_inst_306_, v_inst_307_, v_m_308_, v_a_309_, v_b_u2080_310_);
lean_dec(v_b_u2080_310_);
lean_dec_ref(v_m_308_);
return v_res_311_;
}
}
static lean_object* _init_l_Lean_SMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_315_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__2));
v___x_316_ = lean_unsigned_to_nat(14u);
v___x_317_ = lean_unsigned_to_nat(70u);
v___x_318_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__1));
v___x_319_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__0));
v___x_320_ = l_mkPanicMessageWithDecl(v___x_319_, v___x_318_, v___x_317_, v___x_316_, v___x_315_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_m_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_SMap_find_x3f___redArg(v_inst_321_, v_inst_322_, v_m_324_, v_a_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_328_ = l_panic___redArg(v_inst_323_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v_val_329_; 
v_val_329_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v___x_326_, 1);
return v_val_329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg___boxed(lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_m_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_SMap_find_x21___redArg(v_inst_330_, v_inst_331_, v_inst_332_, v_m_333_, v_a_334_);
lean_dec_ref(v_m_333_);
lean_dec(v_inst_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_SMap_find_x3f___redArg(v_inst_338_, v_inst_339_, v_m_341_, v_a_342_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_345_ = l_panic___redArg(v_inst_340_, v___x_344_);
return v___x_345_;
}
else
{
lean_object* v_val_346_; 
v_val_346_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___x_343_, 1);
return v_val_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___boxed(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_m_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_SMap_find_x21(v_00_u03b1_347_, v_00_u03b2_348_, v_inst_349_, v_inst_350_, v_inst_351_, v_m_352_, v_a_353_);
lean_dec_ref(v_m_352_);
lean_dec(v_inst_351_);
return v_res_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___redArg(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_stage_u2081_359_; 
v_stage_u2081_359_ = lean_ctor_get_uint8(v_x_357_, sizeof(void*)*2);
if (v_stage_u2081_359_ == 0)
{
lean_object* v_map_u2081_360_; lean_object* v_map_u2082_361_; uint8_t v___x_362_; 
v_map_u2081_360_ = lean_ctor_get(v_x_357_, 0);
lean_inc_ref(v_map_u2081_360_);
v_map_u2082_361_ = lean_ctor_get(v_x_357_, 1);
lean_inc_ref(v_map_u2082_361_);
lean_dec_ref(v_x_357_);
lean_inc(v_x_358_);
lean_inc_ref(v_inst_356_);
lean_inc_ref(v_inst_355_);
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_355_, v_inst_356_, v_map_u2081_360_, v_x_358_);
lean_dec_ref(v_map_u2081_360_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_355_, v_inst_356_, v_map_u2082_361_, v_x_358_);
return v___x_363_;
}
else
{
lean_dec_ref(v_map_u2082_361_);
lean_dec(v_x_358_);
lean_dec_ref(v_inst_356_);
lean_dec_ref(v_inst_355_);
return v___x_362_;
}
}
else
{
lean_object* v_map_u2081_364_; uint8_t v___x_365_; 
v_map_u2081_364_ = lean_ctor_get(v_x_357_, 0);
lean_inc_ref(v_map_u2081_364_);
lean_dec_ref(v_x_357_);
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_355_, v_inst_356_, v_map_u2081_364_, v_x_358_);
lean_dec_ref(v_map_u2081_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Lean_SMap_contains___redArg(v_inst_366_, v_inst_367_, v_x_368_, v_x_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_SMap_contains___redArg(v_inst_374_, v_inst_375_, v_x_376_, v_x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_x_383_, lean_object* v_x_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_Lean_SMap_contains(v_00_u03b1_379_, v_00_u03b2_380_, v_inst_381_, v_inst_382_, v_x_383_, v_x_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
uint8_t v_stage_u2081_391_; 
v_stage_u2081_391_ = lean_ctor_get_uint8(v_x_389_, sizeof(void*)*2);
if (v_stage_u2081_391_ == 0)
{
lean_object* v_map_u2081_392_; lean_object* v_map_u2082_393_; lean_object* v___x_394_; 
v_map_u2081_392_ = lean_ctor_get(v_x_389_, 0);
v_map_u2082_393_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_x_390_);
lean_inc_ref(v_inst_388_);
lean_inc_ref(v_inst_387_);
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_387_, v_inst_388_, v_map_u2081_392_, v_x_390_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_387_, v_inst_388_, v_map_u2082_393_, v_x_390_);
return v___x_395_;
}
else
{
lean_dec(v_x_390_);
lean_dec_ref(v_inst_388_);
lean_dec_ref(v_inst_387_);
return v___x_394_;
}
}
else
{
lean_object* v_map_u2081_396_; lean_object* v___x_397_; 
v_map_u2081_396_ = lean_ctor_get(v_x_389_, 0);
v___x_397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_387_, v_inst_388_, v_map_u2081_396_, v_x_390_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg___boxed(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_398_, v_inst_399_, v_x_400_, v_x_401_);
lean_dec_ref(v_x_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_405_, v_inst_406_, v_x_407_, v_x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___boxed(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_SMap_find_x3f_x27(v_00_u03b1_410_, v_00_u03b2_411_, v_inst_412_, v_inst_413_, v_x_414_, v_x_415_);
lean_dec_ref(v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object* v_f_417_, lean_object* v_x_418_, lean_object* v_a_419_, lean_object* v_v_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_apply_2(v_f_417_, v_a_419_, v_v_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object* v_inst_422_, lean_object* v_map_u2082_423_, lean_object* v_f_424_, lean_object* v_____r_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_422_, v_map_u2082_423_, v_f_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object* v_inst_427_, lean_object* v_s_428_, lean_object* v_f_429_){
_start:
{
lean_object* v_toBind_430_; lean_object* v_map_u2081_431_; lean_object* v_map_u2082_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_toBind_430_ = lean_ctor_get(v_inst_427_, 1);
lean_inc(v_toBind_430_);
v_map_u2081_431_ = lean_ctor_get(v_s_428_, 0);
lean_inc_ref(v_map_u2081_431_);
v_map_u2082_432_ = lean_ctor_get(v_s_428_, 1);
lean_inc_ref(v_map_u2082_432_);
lean_dec_ref(v_s_428_);
lean_inc(v_f_429_);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_433_, 0, v_f_429_);
lean_inc_ref(v_inst_427_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_434_, 0, v_inst_427_);
lean_closure_set(v___f_434_, 1, v_map_u2082_432_);
lean_closure_set(v___f_434_, 2, v_f_429_);
v___x_435_ = lean_box(0);
v___x_436_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_427_, v___f_433_, v___x_435_, v_map_u2081_431_);
v___x_437_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v___x_436_, v___f_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b2_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_m_442_, lean_object* v_inst_443_, lean_object* v_s_444_, lean_object* v_f_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_SMap_forM___redArg(v_inst_443_, v_s_444_, v_f_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_m_451_, lean_object* v_inst_452_, lean_object* v_s_453_, lean_object* v_f_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_SMap_forM(v_00_u03b1_447_, v_00_u03b2_448_, v_inst_449_, v_inst_450_, v_m_451_, v_inst_452_, v_s_453_, v_f_454_);
lean_dec_ref(v_inst_450_);
lean_dec_ref(v_inst_449_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_456_, lean_object* v_x_457_, lean_object* v_y_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_x_457_);
lean_ctor_set(v___x_459_, 1, v_y_458_);
v___x_460_ = lean_apply_1(v_f_456_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_461_, lean_object* v_s_462_, lean_object* v_f_463_){
_start:
{
lean_object* v___f_464_; lean_object* v___x_465_; 
v___f_464_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_464_, 0, v_f_463_);
v___x_465_ = l_Lean_SMap_forM___redArg(v_inst_461_, v_s_462_, v___f_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_466_){
_start:
{
lean_object* v___f_467_; 
v___f_467_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_467_, 0, v_inst_466_);
return v___f_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_m_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v___f_474_; 
v___f_474_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_474_, 0, v_inst_473_);
return v___f_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_m_479_, lean_object* v_inst_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_475_, v_00_u03b2_476_, v_inst_477_, v_inst_478_, v_m_479_, v_inst_480_);
lean_dec_ref(v_inst_478_);
lean_dec_ref(v_inst_477_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_482_, lean_object* v_____do__lift_483_){
_start:
{
if (lean_obj_tag(v_____do__lift_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_ctor_get(v_____do__lift_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v_____do__lift_483_, 1);
v___x_485_ = lean_apply_2(v_toPure_482_, lean_box(0), v_a_484_);
return v___x_485_;
}
else
{
lean_object* v_a_486_; lean_object* v_snd_487_; lean_object* v___x_488_; 
v_a_486_ = lean_ctor_get(v_____do__lift_483_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v_____do__lift_483_, 1);
v_snd_487_ = lean_ctor_get(v_a_486_, 1);
lean_inc(v_snd_487_);
lean_dec(v_a_486_);
v___x_488_ = lean_apply_2(v_toPure_482_, lean_box(0), v_snd_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_489_, lean_object* v_____do__lift_490_){
_start:
{
if (lean_obj_tag(v_____do__lift_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_a_491_ = lean_ctor_get(v_____do__lift_490_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_____do__lift_490_);
if (v_isSharedCheck_499_ == 0)
{
v___x_493_ = v_____do__lift_490_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v_____do__lift_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_498_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; 
v___x_497_ = lean_apply_2(v_toPure_489_, lean_box(0), v___x_496_);
return v___x_497_;
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_510_; 
v_a_500_ = lean_ctor_get(v_____do__lift_490_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_____do__lift_490_);
if (v_isSharedCheck_510_ == 0)
{
v___x_502_ = v_____do__lift_490_;
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v_____do__lift_490_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_510_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_a_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_apply_2(v_toPure_489_, lean_box(0), v___x_507_);
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_511_, lean_object* v_toBind_512_, lean_object* v___f_513_, lean_object* v_x_514_, lean_object* v_y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_x_514_);
lean_ctor_set(v___x_517_, 1, v_y_515_);
v___x_518_ = lean_apply_2(v___y_511_, v___x_517_, v___y_516_);
v___x_519_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_518_, v___f_513_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_520_, lean_object* v_00_u03b2_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___f_537_; lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_toApplicative_545_; lean_object* v_toBind_546_; lean_object* v_toPure_547_; lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___f_550_; lean_object* v___x_140__overap_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_inc_ref_n(v_inst_520_, 7);
v___f_525_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_525_, 0, v_inst_520_);
v___f_526_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_526_, 0, v_inst_520_);
v___f_527_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_527_, 0, v_inst_520_);
v___f_528_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_528_, 0, v_inst_520_);
v___x_529_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_529_, 0, lean_box(0));
lean_closure_set(v___x_529_, 1, lean_box(0));
lean_closure_set(v___x_529_, 2, v_inst_520_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___f_525_);
v___x_531_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_531_, 0, lean_box(0));
lean_closure_set(v___x_531_, 1, lean_box(0));
lean_closure_set(v___x_531_, 2, v_inst_520_);
v___x_532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
lean_ctor_set(v___x_532_, 2, v___f_526_);
lean_ctor_set(v___x_532_, 3, v___f_527_);
lean_ctor_set(v___x_532_, 4, v___f_528_);
v___x_533_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_533_, 0, lean_box(0));
lean_closure_set(v___x_533_, 1, lean_box(0));
lean_closure_set(v___x_533_, 2, v_inst_520_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc_ref_n(v___x_534_, 6);
v___f_535_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_535_, 0, v___x_534_);
v___f_536_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_536_, 0, v___x_534_);
v___f_537_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_537_, 0, v___x_534_);
v___f_538_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_538_, 0, v___x_534_);
v___x_539_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_539_, 0, lean_box(0));
lean_closure_set(v___x_539_, 1, lean_box(0));
lean_closure_set(v___x_539_, 2, v___x_534_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___f_535_);
v___x_541_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_541_, 0, lean_box(0));
lean_closure_set(v___x_541_, 1, lean_box(0));
lean_closure_set(v___x_541_, 2, v___x_534_);
v___x_542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
lean_ctor_set(v___x_542_, 2, v___f_536_);
lean_ctor_set(v___x_542_, 3, v___f_537_);
lean_ctor_set(v___x_542_, 4, v___f_538_);
v___x_543_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_543_, 0, lean_box(0));
lean_closure_set(v___x_543_, 1, lean_box(0));
lean_closure_set(v___x_543_, 2, v___x_534_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v_toApplicative_545_ = lean_ctor_get(v_inst_520_, 0);
lean_inc_ref(v_toApplicative_545_);
v_toBind_546_ = lean_ctor_get(v_inst_520_, 1);
lean_inc_n(v_toBind_546_, 2);
lean_dec_ref(v_inst_520_);
v_toPure_547_ = lean_ctor_get(v_toApplicative_545_, 1);
lean_inc_n(v_toPure_547_, 2);
lean_dec_ref(v_toApplicative_545_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_548_, 0, v_toPure_547_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_549_, 0, v_toPure_547_);
v___f_550_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_550_, 0, v___y_524_);
lean_closure_set(v___f_550_, 1, v_toBind_546_);
lean_closure_set(v___f_550_, 2, v___f_549_);
v___x_140__overap_551_ = l_Lean_SMap_forM___redArg(v___x_544_, v___y_522_, v___f_550_);
v___x_552_ = lean_apply_1(v___x_140__overap_551_, v___y_523_);
v___x_553_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_552_, v___f_548_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_554_){
_start:
{
lean_object* v___f_555_; 
v___f_555_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_555_, 0, v_inst_554_);
return v___f_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_m_560_, lean_object* v_inst_561_){
_start:
{
lean_object* v___f_562_; 
v___f_562_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_562_, 0, v_inst_561_);
return v___f_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_m_567_, lean_object* v_inst_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_563_, v_00_u03b2_564_, v_inst_565_, v_inst_566_, v_m_567_, v_inst_568_);
lean_dec_ref(v_inst_566_);
lean_dec_ref(v_inst_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object* v_s_570_){
_start:
{
lean_object* v_map_u2081_571_; lean_object* v_map_u2082_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_map_u2081_571_ = lean_ctor_get(v_s_570_, 0);
lean_inc_ref(v_map_u2081_571_);
v_map_u2082_572_ = lean_ctor_get(v_s_570_, 1);
lean_inc_ref(v_map_u2082_572_);
lean_dec_ref(v_s_570_);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_map_u2081_571_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_box(0);
v___x_576_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_u2082_572_, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_574_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_s_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_SMap_iter___redArg(v_s_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_s_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_SMap_iter(v_00_u03b1_584_, v_00_u03b2_585_, v_inst_586_, v_inst_587_, v_s_588_);
lean_dec_ref(v_inst_587_);
lean_dec_ref(v_inst_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_590_){
_start:
{
uint8_t v_stage_u2081_591_; 
v_stage_u2081_591_ = lean_ctor_get_uint8(v_m_590_, sizeof(void*)*2);
if (v_stage_u2081_591_ == 0)
{
return v_m_590_;
}
else
{
lean_object* v_map_u2081_592_; lean_object* v_map_u2082_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_601_; 
v_map_u2081_592_ = lean_ctor_get(v_m_590_, 0);
v_map_u2082_593_ = lean_ctor_get(v_m_590_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_m_590_);
if (v_isSharedCheck_601_ == 0)
{
v___x_595_ = v_m_590_;
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_map_u2082_593_);
lean_inc(v_map_u2081_592_);
lean_dec(v_m_590_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_601_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_597_; lean_object* v___x_599_; 
v___x_597_ = 0;
if (v_isShared_596_ == 0)
{
v___x_599_ = v___x_595_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_map_u2081_592_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_map_u2082_593_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*2, v___x_597_);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_m_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_SMap_switch___redArg(v_m_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b2_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_m_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_SMap_switch(v_00_u03b1_608_, v_00_u03b2_609_, v_inst_610_, v_inst_611_, v_m_612_);
lean_dec_ref(v_inst_611_);
lean_dec_ref(v_inst_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_614_, lean_object* v_s_615_, lean_object* v_m_616_){
_start:
{
lean_object* v_map_u2082_617_; lean_object* v___x_618_; 
v_map_u2082_617_ = lean_ctor_get(v_m_616_, 1);
lean_inc_ref(v_map_u2082_617_);
lean_dec_ref(v_m_616_);
v___x_618_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_617_, v_f_614_, v_s_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_00_u03c3_623_, lean_object* v_f_624_, lean_object* v_s_625_, lean_object* v_m_626_){
_start:
{
lean_object* v_map_u2082_627_; lean_object* v___x_628_; 
v_map_u2082_627_ = lean_ctor_get(v_m_626_, 1);
lean_inc_ref(v_map_u2082_627_);
lean_dec_ref(v_m_626_);
v___x_628_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_627_, v_f_624_, v_s_625_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_00_u03c3_633_, lean_object* v_f_634_, lean_object* v_s_635_, lean_object* v_m_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_SMap_foldStage2(v_00_u03b1_629_, v_00_u03b2_630_, v_inst_631_, v_inst_632_, v_00_u03c3_633_, v_f_634_, v_s_635_, v_m_636_);
lean_dec_ref(v_inst_632_);
lean_dec_ref(v_inst_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_638_, lean_object* v_f_639_, lean_object* v_map_u2082_640_, lean_object* v_____do__lift_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_638_, v_f_639_, v_map_u2082_640_, v_____do__lift_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_643_, lean_object* v_f_644_, lean_object* v_init_645_, lean_object* v_map_646_){
_start:
{
lean_object* v_toBind_647_; lean_object* v_map_u2081_648_; lean_object* v_map_u2082_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_toBind_647_ = lean_ctor_get(v_inst_643_, 1);
lean_inc(v_toBind_647_);
v_map_u2081_648_ = lean_ctor_get(v_map_646_, 0);
lean_inc_ref(v_map_u2081_648_);
v_map_u2082_649_ = lean_ctor_get(v_map_646_, 1);
lean_inc_ref(v_map_u2082_649_);
lean_dec_ref(v_map_646_);
lean_inc(v_f_644_);
lean_inc_ref(v_inst_643_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_650_, 0, v_inst_643_);
lean_closure_set(v___f_650_, 1, v_f_644_);
lean_closure_set(v___f_650_, 2, v_map_u2082_649_);
v___x_651_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_643_, v_f_644_, v_init_645_, v_map_u2081_648_);
v___x_652_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v___x_651_, v___f_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_00_u03c3_657_, lean_object* v_m_658_, lean_object* v_inst_659_, lean_object* v_f_660_, lean_object* v_init_661_, lean_object* v_map_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_SMap_foldM___redArg(v_inst_659_, v_f_660_, v_init_661_, v_map_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_00_u03c3_668_, lean_object* v_m_669_, lean_object* v_inst_670_, lean_object* v_f_671_, lean_object* v_init_672_, lean_object* v_map_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_SMap_foldM(v_00_u03b1_664_, v_00_u03b2_665_, v_inst_666_, v_inst_667_, v_00_u03c3_668_, v_m_669_, v_inst_670_, v_f_671_, v_init_672_, v_map_673_);
lean_dec_ref(v_inst_667_);
lean_dec_ref(v_inst_666_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object* v_f_675_, lean_object* v_x1_676_, lean_object* v_x2_677_, lean_object* v_x3_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = lean_apply_3(v_f_675_, v_x1_676_, v_x2_677_, v_x3_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object* v_f_699_, lean_object* v_init_700_, lean_object* v_m_701_){
_start:
{
lean_object* v_map_u2081_702_; lean_object* v_map_u2082_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_map_u2081_702_ = lean_ctor_get(v_m_701_, 0);
lean_inc_ref(v_map_u2081_702_);
v_map_u2082_703_ = lean_ctor_get(v_m_701_, 1);
lean_inc_ref(v_map_u2082_703_);
lean_dec_ref(v_m_701_);
lean_inc(v_f_699_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_704_, 0, v_f_699_);
v___x_705_ = ((lean_object*)(l_Lean_SMap_fold___redArg___closed__9));
v___x_706_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_705_, v___f_704_, v_init_700_, v_map_u2081_702_);
v___x_707_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_703_, v_f_699_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_00_u03c3_712_, lean_object* v_f_713_, lean_object* v_init_714_, lean_object* v_m_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_SMap_fold___redArg(v_f_713_, v_init_714_, v_m_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_717_, lean_object* v_00_u03b2_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_00_u03c3_721_, lean_object* v_f_722_, lean_object* v_init_723_, lean_object* v_m_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_SMap_fold(v_00_u03b1_717_, v_00_u03b2_718_, v_inst_719_, v_inst_720_, v_00_u03c3_721_, v_f_722_, v_init_723_, v_m_724_);
lean_dec_ref(v_inst_720_);
lean_dec_ref(v_inst_719_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_726_){
_start:
{
lean_object* v_map_u2081_727_; lean_object* v___x_728_; 
v_map_u2081_727_ = lean_ctor_get(v_m_726_, 0);
v___x_728_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_SMap_numBuckets___redArg(v_m_729_);
lean_dec_ref(v_m_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_inst_733_, lean_object* v_inst_734_, lean_object* v_m_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_SMap_numBuckets___redArg(v_m_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_m_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_SMap_numBuckets(v_00_u03b1_737_, v_00_u03b2_738_, v_inst_739_, v_inst_740_, v_m_741_);
lean_dec_ref(v_m_741_);
lean_dec_ref(v_inst_740_);
lean_dec_ref(v_inst_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_a_744_);
lean_ctor_set(v___x_746_, 1, v_b_745_);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_es_743_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_749_){
_start:
{
lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___f_750_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_751_ = lean_box(0);
v___x_752_ = l_Lean_SMap_fold___redArg(v___f_750_, v___x_751_, v_m_749_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_753_, lean_object* v_00_u03b2_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_m_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_SMap_toList___redArg(v_m_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_m_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_SMap_toList(v_00_u03b1_759_, v_00_u03b2_760_, v_inst_761_, v_inst_762_, v_m_763_);
lean_dec_ref(v_inst_762_);
lean_dec_ref(v_inst_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg___lam__0(lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_s_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v___x_771_; 
v_fst_769_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_fst_769_);
v_snd_770_ = lean_ctor_get(v_x_768_, 1);
lean_inc(v_snd_770_);
lean_dec_ref(v_x_768_);
v___x_771_ = l_Lean_SMap_insert___redArg(v_inst_765_, v_inst_766_, v_s_767_, v_fst_769_, v_snd_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_es_774_){
_start:
{
lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___f_775_ = lean_alloc_closure((void*)(l_Lean_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_775_, 0, v_inst_772_);
lean_closure_set(v___f_775_, 1, v_inst_773_);
v___x_776_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__5, &l_Lean_SMap_instInhabited___closed__5_once, _init_l_Lean_SMap_instInhabited___closed__5);
v___x_777_ = l_List_foldl___redArg(v___f_775_, v___x_776_, v_es_774_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap(lean_object* v_00_u03b1_778_, lean_object* v_00_u03b2_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_es_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_List_toSMap___redArg(v_inst_780_, v_inst_781_, v_es_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_787_, lean_object* v_v_788_, lean_object* v_prec_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = l_Lean_SMap_toList___redArg(v_v_788_);
v___x_791_ = l_List_repr___redArg(v___x_787_, v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Repr_addAppParen(v___x_793_, v_prec_789_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_795_, lean_object* v_v_796_, lean_object* v_prec_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_instReprSMap___redArg___lam__0(v___x_795_, v_v_796_, v_prec_797_);
lean_dec(v_prec_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_799_, lean_object* v_inst_800_){
_start:
{
lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___f_803_; 
v___f_801_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_801_, 0, v_inst_800_);
v___x_802_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_802_, 0, lean_box(0));
lean_closure_set(v___x_802_, 1, lean_box(0));
lean_closure_set(v___x_802_, 2, v_inst_799_);
lean_closure_set(v___x_802_, 3, v___f_801_);
v___f_803_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_803_, 0, v___x_802_);
return v___f_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_inst_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_instReprSMap___redArg(v_inst_808_, v_inst_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_inst_815_, lean_object* v_inst_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_instReprSMap(v_00_u03b1_811_, v_00_u03b2_812_, v_x_813_, v_x_814_, v_inst_815_, v_inst_816_);
lean_dec_ref(v_x_814_);
lean_dec_ref(v_x_813_);
return v_res_817_;
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
