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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_SMap_instInhabited___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___redArg___closed__0;
static lean_once_cell_t l_Lean_SMap_instInhabited___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___redArg___closed__1;
static lean_once_cell_t l_Lean_SMap_instInhabited___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___redArg___closed__2;
static lean_once_cell_t l_Lean_SMap_instInhabited___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___redArg___closed__3;
static lean_once_cell_t l_Lean_SMap_instInhabited___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_SMap_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_SMap_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_SMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SMap_empty___closed__0;
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
static lean_object* _init_l_Lean_SMap_instInhabited___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__0, &l_Lean_SMap_instInhabited___redArg___closed__0_once, _init_l_Lean_SMap_instInhabited___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_7_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__2, &l_Lean_SMap_instInhabited___redArg___closed__2_once, _init_l_Lean_SMap_instInhabited___redArg___closed__2);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__3, &l_Lean_SMap_instInhabited___redArg___closed__3_once, _init_l_Lean_SMap_instInhabited___redArg___closed__3);
v___x_11_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__1, &l_Lean_SMap_instInhabited___redArg___closed__1_once, _init_l_Lean_SMap_instInhabited___redArg___closed__1);
v___x_12_ = 1;
v___x_13_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_10_);
lean_ctor_set_uint8(v___x_13_, sizeof(void*)*2, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__4, &l_Lean_SMap_instInhabited___redArg___closed__4_once, _init_l_Lean_SMap_instInhabited___redArg___closed__4);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_SMap_instInhabited___redArg();
return v_res_17_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_SMap_instInhabited___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__0, &l_Lean_SMap_instInhabited___closed__0_once, _init_l_Lean_SMap_instInhabited___closed__0);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___boxed(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_SMap_instInhabited(v_00_u03b1_24_, v_00_u03b2_25_, v_inst_26_, v_inst_27_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___redArg(){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__4, &l_Lean_SMap_instInhabited___redArg___closed__4_once, _init_l_Lean_SMap_instInhabited___redArg___closed__4);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_SMap_empty___redArg();
return v_res_32_;
}
}
static lean_object* _init_l_Lean_SMap_empty___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_SMap_empty___redArg();
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_inst_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Lean_SMap_empty___closed__0, &l_Lean_SMap_empty___closed__0_once, _init_l_Lean_SMap_empty___closed__0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___boxed(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_SMap_empty(v_00_u03b1_39_, v_00_u03b2_40_, v_inst_41_, v_inst_42_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg(lean_object* v_m_44_, uint8_t v_stage_u2081_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__3, &l_Lean_SMap_instInhabited___redArg___closed__3_once, _init_l_Lean_SMap_instInhabited___redArg___closed__3);
v___x_47_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_47_, 0, v_m_44_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*2, v_stage_u2081_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg___boxed(lean_object* v_m_48_, lean_object* v_stage_u2081_49_){
_start:
{
uint8_t v_stage_u2081_boxed_50_; lean_object* v_res_51_; 
v_stage_u2081_boxed_50_ = lean_unbox(v_stage_u2081_49_);
v_res_51_ = l_Lean_SMap_fromHashMap___redArg(v_m_48_, v_stage_u2081_boxed_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_m_56_, uint8_t v_stage_u2081_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__3, &l_Lean_SMap_instInhabited___redArg___closed__3_once, _init_l_Lean_SMap_instInhabited___redArg___closed__3);
v___x_59_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_59_, 0, v_m_56_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*2, v_stage_u2081_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___boxed(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_m_64_, lean_object* v_stage_u2081_65_){
_start:
{
uint8_t v_stage_u2081_boxed_66_; lean_object* v_res_67_; 
v_stage_u2081_boxed_66_ = lean_unbox(v_stage_u2081_65_);
v_res_67_ = l_Lean_SMap_fromHashMap(v_00_u03b1_60_, v_00_u03b2_61_, v_inst_62_, v_inst_63_, v_m_64_, v_stage_u2081_boxed_66_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_62_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_stage_u2081_73_; 
v_stage_u2081_73_ = lean_ctor_get_uint8(v_x_70_, sizeof(void*)*2);
if (v_stage_u2081_73_ == 0)
{
lean_object* v_map_u2081_74_; lean_object* v_map_u2082_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_83_; 
v_map_u2081_74_ = lean_ctor_get(v_x_70_, 0);
v_map_u2082_75_ = lean_ctor_get(v_x_70_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_83_ == 0)
{
v___x_77_ = v_x_70_;
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_map_u2082_75_);
lean_inc(v_map_u2081_74_);
lean_dec(v_x_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_68_, v_inst_69_, v_map_u2082_75_, v_x_71_, v_x_72_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_map_u2081_74_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_79_);
lean_ctor_set_uint8(v_reuseFailAlloc_82_, sizeof(void*)*2, v_stage_u2081_73_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
else
{
lean_object* v_map_u2081_84_; lean_object* v_map_u2082_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
v_map_u2081_84_ = lean_ctor_get(v_x_70_, 0);
v_map_u2082_85_ = lean_ctor_get(v_x_70_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_93_ == 0)
{
v___x_87_ = v_x_70_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_map_u2082_85_);
lean_inc(v_map_u2081_84_);
lean_dec(v_x_70_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_89_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_68_, v_inst_69_, v_map_u2081_84_, v_x_71_, v_x_72_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_map_u2082_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_92_, sizeof(void*)*2, v_stage_u2081_73_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_SMap_insert___redArg(v_inst_96_, v_inst_97_, v_x_98_, v_x_99_, v_x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27___redArg(lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v_stage_u2081_107_; 
v_stage_u2081_107_ = lean_ctor_get_uint8(v_x_104_, sizeof(void*)*2);
if (v_stage_u2081_107_ == 0)
{
lean_object* v_map_u2081_108_; lean_object* v_map_u2082_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_map_u2081_108_ = lean_ctor_get(v_x_104_, 0);
v_map_u2082_109_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v_x_104_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_map_u2082_109_);
lean_inc(v_map_u2081_108_);
lean_dec(v_x_104_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_102_, v_inst_103_, v_map_u2082_109_, v_x_105_, v_x_106_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_map_u2081_108_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*2, v_stage_u2081_107_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
else
{
lean_object* v_map_u2081_118_; lean_object* v_map_u2082_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_127_; 
v_map_u2081_118_ = lean_ctor_get(v_x_104_, 0);
v_map_u2082_119_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_127_ == 0)
{
v___x_121_ = v_x_104_;
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_map_u2082_119_);
lean_inc(v_map_u2081_118_);
lean_dec(v_x_104_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_123_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_102_, v_inst_103_, v_map_u2081_118_, v_x_105_, v_x_106_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_map_u2082_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_126_, sizeof(void*)*2, v_stage_u2081_107_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_SMap_insert_x27___redArg(v_inst_130_, v_inst_131_, v_x_132_, v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg(lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_stage_u2081_140_; 
v_stage_u2081_140_ = lean_ctor_get_uint8(v_x_138_, sizeof(void*)*2);
if (v_stage_u2081_140_ == 0)
{
lean_object* v_map_u2081_141_; lean_object* v_map_u2082_142_; lean_object* v___x_143_; 
v_map_u2081_141_ = lean_ctor_get(v_x_138_, 0);
v_map_u2082_142_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_x_139_);
lean_inc_ref(v_inst_137_);
lean_inc_ref(v_inst_136_);
v___x_143_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_136_, v_inst_137_, v_map_u2082_142_, v_x_139_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_136_, v_inst_137_, v_map_u2081_141_, v_x_139_);
return v___x_144_;
}
else
{
lean_dec(v_x_139_);
lean_dec_ref(v_inst_137_);
lean_dec_ref(v_inst_136_);
return v___x_143_;
}
}
else
{
lean_object* v_map_u2081_145_; lean_object* v___x_146_; 
v_map_u2081_145_ = lean_ctor_get(v_x_138_, 0);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_136_, v_inst_137_, v_map_u2081_145_, v_x_139_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg___boxed(lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_SMap_find_x3f___redArg(v_inst_147_, v_inst_148_, v_x_149_, v_x_150_);
lean_dec_ref(v_x_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object* v_00_u03b1_152_, lean_object* v_00_u03b2_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_SMap_find_x3f___redArg(v_inst_154_, v_inst_155_, v_x_156_, v_x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___boxed(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_SMap_find_x3f(v_00_u03b1_159_, v_00_u03b2_160_, v_inst_161_, v_inst_162_, v_x_163_, v_x_164_);
lean_dec_ref(v_x_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_m_168_, lean_object* v_a_169_, lean_object* v_b_u2080_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_SMap_find_x3f___redArg(v_inst_166_, v_inst_167_, v_m_168_, v_a_169_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_inc(v_b_u2080_170_);
return v_b_u2080_170_;
}
else
{
lean_object* v_val_172_; 
v_val_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v___x_171_, 1);
return v_val_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg___boxed(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_m_175_, lean_object* v_a_176_, lean_object* v_b_u2080_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_SMap_findD___redArg(v_inst_173_, v_inst_174_, v_m_175_, v_a_176_, v_b_u2080_177_);
lean_dec(v_b_u2080_177_);
lean_dec_ref(v_m_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_m_183_, lean_object* v_a_184_, lean_object* v_b_u2080_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_SMap_find_x3f___redArg(v_inst_181_, v_inst_182_, v_m_183_, v_a_184_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_inc(v_b_u2080_185_);
return v_b_u2080_185_;
}
else
{
lean_object* v_val_187_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_val_187_);
lean_dec_ref_known(v___x_186_, 1);
return v_val_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___boxed(lean_object* v_00_u03b1_188_, lean_object* v_00_u03b2_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_m_192_, lean_object* v_a_193_, lean_object* v_b_u2080_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_SMap_findD(v_00_u03b1_188_, v_00_u03b2_189_, v_inst_190_, v_inst_191_, v_m_192_, v_a_193_, v_b_u2080_194_);
lean_dec(v_b_u2080_194_);
lean_dec_ref(v_m_192_);
return v_res_195_;
}
}
static lean_object* _init_l_Lean_SMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_199_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__2));
v___x_200_ = lean_unsigned_to_nat(14u);
v___x_201_ = lean_unsigned_to_nat(70u);
v___x_202_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__1));
v___x_203_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__0));
v___x_204_ = l_mkPanicMessageWithDecl(v___x_203_, v___x_202_, v___x_201_, v___x_200_, v___x_199_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg(lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_m_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_SMap_find_x3f___redArg(v_inst_205_, v_inst_206_, v_m_208_, v_a_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_212_ = l_panic___redArg(v_inst_207_, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v_val_213_; 
v_val_213_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v___x_210_, 1);
return v_val_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg___boxed(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_m_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_SMap_find_x21___redArg(v_inst_214_, v_inst_215_, v_inst_216_, v_m_217_, v_a_218_);
lean_dec_ref(v_m_217_);
lean_dec(v_inst_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_SMap_find_x3f___redArg(v_inst_222_, v_inst_223_, v_m_225_, v_a_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_229_ = l_panic___redArg(v_inst_224_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_227_, 1);
return v_val_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___boxed(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_SMap_find_x21(v_00_u03b1_231_, v_00_u03b2_232_, v_inst_233_, v_inst_234_, v_inst_235_, v_m_236_, v_a_237_);
lean_dec_ref(v_m_236_);
lean_dec(v_inst_235_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___redArg(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint8_t v_stage_u2081_243_; 
v_stage_u2081_243_ = lean_ctor_get_uint8(v_x_241_, sizeof(void*)*2);
if (v_stage_u2081_243_ == 0)
{
lean_object* v_map_u2081_244_; lean_object* v_map_u2082_245_; uint8_t v___x_246_; 
v_map_u2081_244_ = lean_ctor_get(v_x_241_, 0);
lean_inc_ref(v_map_u2081_244_);
v_map_u2082_245_ = lean_ctor_get(v_x_241_, 1);
lean_inc_ref(v_map_u2082_245_);
lean_dec_ref(v_x_241_);
lean_inc(v_x_242_);
lean_inc_ref(v_inst_240_);
lean_inc_ref(v_inst_239_);
v___x_246_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_239_, v_inst_240_, v_map_u2081_244_, v_x_242_);
lean_dec_ref(v_map_u2081_244_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_239_, v_inst_240_, v_map_u2082_245_, v_x_242_);
return v___x_247_;
}
else
{
lean_dec_ref(v_map_u2082_245_);
lean_dec(v_x_242_);
lean_dec_ref(v_inst_240_);
lean_dec_ref(v_inst_239_);
return v___x_246_;
}
}
else
{
lean_object* v_map_u2081_248_; uint8_t v___x_249_; 
v_map_u2081_248_ = lean_ctor_get(v_x_241_, 0);
lean_inc_ref(v_map_u2081_248_);
lean_dec_ref(v_x_241_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_239_, v_inst_240_, v_map_u2081_248_, v_x_242_);
lean_dec_ref(v_map_u2081_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_SMap_contains___redArg(v_inst_250_, v_inst_251_, v_x_252_, v_x_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
uint8_t v___x_262_; 
v___x_262_ = l_Lean_SMap_contains___redArg(v_inst_258_, v_inst_259_, v_x_260_, v_x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object* v_00_u03b1_263_, lean_object* v_00_u03b2_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lean_SMap_contains(v_00_u03b1_263_, v_00_u03b2_264_, v_inst_265_, v_inst_266_, v_x_267_, v_x_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_stage_u2081_275_; 
v_stage_u2081_275_ = lean_ctor_get_uint8(v_x_273_, sizeof(void*)*2);
if (v_stage_u2081_275_ == 0)
{
lean_object* v_map_u2081_276_; lean_object* v_map_u2082_277_; lean_object* v___x_278_; 
v_map_u2081_276_ = lean_ctor_get(v_x_273_, 0);
v_map_u2082_277_ = lean_ctor_get(v_x_273_, 1);
lean_inc(v_x_274_);
lean_inc_ref(v_inst_272_);
lean_inc_ref(v_inst_271_);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_271_, v_inst_272_, v_map_u2081_276_, v_x_274_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_271_, v_inst_272_, v_map_u2082_277_, v_x_274_);
return v___x_279_;
}
else
{
lean_dec(v_x_274_);
lean_dec_ref(v_inst_272_);
lean_dec_ref(v_inst_271_);
return v___x_278_;
}
}
else
{
lean_object* v_map_u2081_280_; lean_object* v___x_281_; 
v_map_u2081_280_ = lean_ctor_get(v_x_273_, 0);
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_271_, v_inst_272_, v_map_u2081_280_, v_x_274_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg___boxed(lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_282_, v_inst_283_, v_x_284_, v_x_285_);
lean_dec_ref(v_x_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object* v_00_u03b1_287_, lean_object* v_00_u03b2_288_, lean_object* v_inst_289_, lean_object* v_inst_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_289_, v_inst_290_, v_x_291_, v_x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___boxed(lean_object* v_00_u03b1_294_, lean_object* v_00_u03b2_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_SMap_find_x3f_x27(v_00_u03b1_294_, v_00_u03b2_295_, v_inst_296_, v_inst_297_, v_x_298_, v_x_299_);
lean_dec_ref(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object* v_inst_301_, lean_object* v_map_u2082_302_, lean_object* v_f_303_, lean_object* v_____r_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_301_, v_map_u2082_302_, v_f_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object* v_f_306_, lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_apply_2(v_f_306_, v___y_308_, v___y_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__2(lean_object* v_inst_311_, lean_object* v___f_312_, lean_object* v_x_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_box(0);
v___x_316_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_311_, v___f_312_, v___x_315_, v___y_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object* v_inst_317_, lean_object* v_s_318_, lean_object* v_f_319_){
_start:
{
lean_object* v_map_u2081_320_; lean_object* v_toApplicative_321_; lean_object* v_toBind_322_; lean_object* v_map_u2082_323_; lean_object* v_buckets_324_; lean_object* v_toPure_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v_map_u2081_320_ = lean_ctor_get(v_s_318_, 0);
lean_inc_ref(v_map_u2081_320_);
v_toApplicative_321_ = lean_ctor_get(v_inst_317_, 0);
v_toBind_322_ = lean_ctor_get(v_inst_317_, 1);
lean_inc(v_toBind_322_);
v_map_u2082_323_ = lean_ctor_get(v_s_318_, 1);
lean_inc_ref(v_map_u2082_323_);
lean_dec_ref(v_s_318_);
v_buckets_324_ = lean_ctor_get(v_map_u2081_320_, 1);
lean_inc_ref(v_buckets_324_);
lean_dec_ref(v_map_u2081_320_);
v_toPure_325_ = lean_ctor_get(v_toApplicative_321_, 1);
lean_inc(v_f_319_);
lean_inc_ref(v_inst_317_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_326_, 0, v_inst_317_);
lean_closure_set(v___f_326_, 1, v_map_u2082_323_);
lean_closure_set(v___f_326_, 2, v_f_319_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get_size(v_buckets_324_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc(v_toPure_325_);
lean_dec_ref(v_buckets_324_);
lean_dec(v_f_319_);
lean_dec_ref(v_inst_317_);
v___x_331_ = lean_apply_2(v_toPure_325_, lean_box(0), v___x_329_);
v___x_332_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_331_, v___f_326_);
return v___x_332_;
}
else
{
lean_object* v___f_333_; lean_object* v___f_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___f_333_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 1);
lean_closure_set(v___f_333_, 0, v_f_319_);
lean_inc_ref(v_inst_317_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_334_, 0, v_inst_317_);
lean_closure_set(v___f_334_, 1, v___f_333_);
v___x_335_ = ((size_t)0ULL);
v___x_336_ = lean_usize_of_nat(v___x_328_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_317_, v___f_334_, v_buckets_324_, v___x_335_, v___x_336_, v___x_329_);
v___x_338_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_337_, v___f_326_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_m_343_, lean_object* v_inst_344_, lean_object* v_s_345_, lean_object* v_f_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_SMap_forM___redArg(v_inst_344_, v_s_345_, v_f_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_348_, lean_object* v_00_u03b2_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_m_352_, lean_object* v_inst_353_, lean_object* v_s_354_, lean_object* v_f_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_SMap_forM(v_00_u03b1_348_, v_00_u03b2_349_, v_inst_350_, v_inst_351_, v_m_352_, v_inst_353_, v_s_354_, v_f_355_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_357_, lean_object* v_x_358_, lean_object* v_y_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_x_358_);
lean_ctor_set(v___x_360_, 1, v_y_359_);
v___x_361_ = lean_apply_1(v_f_357_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_362_, lean_object* v_s_363_, lean_object* v_f_364_){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; 
v___f_365_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_365_, 0, v_f_364_);
v___x_366_ = l_Lean_SMap_forM___redArg(v_inst_362_, v_s_363_, v___f_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_367_){
_start:
{
lean_object* v___f_368_; 
v___f_368_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_368_, 0, v_inst_367_);
return v___f_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_m_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v___f_375_; 
v___f_375_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_375_, 0, v_inst_374_);
return v___f_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_m_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_376_, v_00_u03b2_377_, v_inst_378_, v_inst_379_, v_m_380_, v_inst_381_);
lean_dec_ref(v_inst_379_);
lean_dec_ref(v_inst_378_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_383_, lean_object* v_____do__lift_384_){
_start:
{
if (lean_obj_tag(v_____do__lift_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; 
v_a_385_ = lean_ctor_get(v_____do__lift_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v_____do__lift_384_, 1);
v___x_386_ = lean_apply_2(v_toPure_383_, lean_box(0), v_a_385_);
return v___x_386_;
}
else
{
lean_object* v_a_387_; lean_object* v_snd_388_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v_____do__lift_384_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v_____do__lift_384_, 1);
v_snd_388_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_snd_388_);
lean_dec(v_a_387_);
v___x_389_ = lean_apply_2(v_toPure_383_, lean_box(0), v_snd_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_390_, lean_object* v_____do__lift_391_){
_start:
{
if (lean_obj_tag(v_____do__lift_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_a_392_ = lean_ctor_get(v_____do__lift_391_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_____do__lift_391_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v_____do__lift_391_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v_____do__lift_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_399_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; 
v___x_398_ = lean_apply_2(v_toPure_390_, lean_box(0), v___x_397_);
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_411_; 
v_a_401_ = lean_ctor_get(v_____do__lift_391_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_____do__lift_391_);
if (v_isSharedCheck_411_ == 0)
{
v___x_403_ = v_____do__lift_391_;
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v_____do__lift_391_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_411_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; 
v___x_409_ = lean_apply_2(v_toPure_390_, lean_box(0), v___x_408_);
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_412_, lean_object* v_toBind_413_, lean_object* v___f_414_, lean_object* v_x_415_, lean_object* v_y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_x_415_);
lean_ctor_set(v___x_418_, 1, v_y_416_);
v___x_419_ = lean_apply_2(v___y_412_, v___x_418_, v___y_417_);
v___x_420_ = lean_apply_4(v_toBind_413_, lean_box(0), lean_box(0), v___x_419_, v___f_414_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_421_, lean_object* v_00_u03b2_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_toApplicative_446_; lean_object* v_toBind_447_; lean_object* v_toPure_448_; lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___f_451_; lean_object* v___x_142__overap_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref_n(v_inst_421_, 7);
v___f_426_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_426_, 0, v_inst_421_);
v___f_427_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_427_, 0, v_inst_421_);
v___f_428_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_428_, 0, v_inst_421_);
v___f_429_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_429_, 0, v_inst_421_);
v___x_430_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_430_, 0, lean_box(0));
lean_closure_set(v___x_430_, 1, lean_box(0));
lean_closure_set(v___x_430_, 2, v_inst_421_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___f_426_);
v___x_432_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_432_, 0, lean_box(0));
lean_closure_set(v___x_432_, 1, lean_box(0));
lean_closure_set(v___x_432_, 2, v_inst_421_);
v___x_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v___f_427_);
lean_ctor_set(v___x_433_, 3, v___f_428_);
lean_ctor_set(v___x_433_, 4, v___f_429_);
v___x_434_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_434_, 0, lean_box(0));
lean_closure_set(v___x_434_, 1, lean_box(0));
lean_closure_set(v___x_434_, 2, v_inst_421_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
lean_inc_ref_n(v___x_435_, 6);
v___f_436_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_436_, 0, v___x_435_);
v___f_437_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_437_, 0, v___x_435_);
v___f_438_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_438_, 0, v___x_435_);
v___f_439_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_439_, 0, v___x_435_);
v___x_440_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_440_, 0, lean_box(0));
lean_closure_set(v___x_440_, 1, lean_box(0));
lean_closure_set(v___x_440_, 2, v___x_435_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___f_436_);
v___x_442_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_442_, 0, lean_box(0));
lean_closure_set(v___x_442_, 1, lean_box(0));
lean_closure_set(v___x_442_, 2, v___x_435_);
v___x_443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
lean_ctor_set(v___x_443_, 2, v___f_437_);
lean_ctor_set(v___x_443_, 3, v___f_438_);
lean_ctor_set(v___x_443_, 4, v___f_439_);
v___x_444_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_444_, 0, lean_box(0));
lean_closure_set(v___x_444_, 1, lean_box(0));
lean_closure_set(v___x_444_, 2, v___x_435_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v_toApplicative_446_ = lean_ctor_get(v_inst_421_, 0);
lean_inc_ref(v_toApplicative_446_);
v_toBind_447_ = lean_ctor_get(v_inst_421_, 1);
lean_inc_n(v_toBind_447_, 2);
lean_dec_ref(v_inst_421_);
v_toPure_448_ = lean_ctor_get(v_toApplicative_446_, 1);
lean_inc_n(v_toPure_448_, 2);
lean_dec_ref(v_toApplicative_446_);
v___f_449_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_449_, 0, v_toPure_448_);
v___f_450_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_450_, 0, v_toPure_448_);
v___f_451_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_451_, 0, v___y_425_);
lean_closure_set(v___f_451_, 1, v_toBind_447_);
lean_closure_set(v___f_451_, 2, v___f_450_);
v___x_142__overap_452_ = l_Lean_SMap_forM___redArg(v___x_445_, v___y_423_, v___f_451_);
v___x_453_ = lean_apply_1(v___x_142__overap_452_, v___y_424_);
v___x_454_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v___x_453_, v___f_449_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_455_){
_start:
{
lean_object* v___f_456_; 
v___f_456_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_456_, 0, v_inst_455_);
return v___f_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_457_, lean_object* v_00_u03b2_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_m_461_, lean_object* v_inst_462_){
_start:
{
lean_object* v___f_463_; 
v___f_463_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_463_, 0, v_inst_462_);
return v___f_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_m_468_, lean_object* v_inst_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_464_, v_00_u03b2_465_, v_inst_466_, v_inst_467_, v_m_468_, v_inst_469_);
lean_dec_ref(v_inst_467_);
lean_dec_ref(v_inst_466_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object* v_s_471_){
_start:
{
lean_object* v_map_u2081_472_; lean_object* v_map_u2082_473_; lean_object* v_buckets_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_487_; 
v_map_u2081_472_ = lean_ctor_get(v_s_471_, 0);
lean_inc_ref(v_map_u2081_472_);
v_map_u2082_473_ = lean_ctor_get(v_s_471_, 1);
lean_inc_ref(v_map_u2082_473_);
lean_dec_ref(v_s_471_);
v_buckets_474_ = lean_ctor_get(v_map_u2081_472_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v_map_u2081_472_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_map_u2081_472_, 0);
lean_dec(v_unused_488_);
v___x_476_ = v_map_u2081_472_;
v_isShared_477_ = v_isSharedCheck_487_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_buckets_474_);
lean_dec(v_map_u2081_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_487_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(0u);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_478_);
lean_ctor_set(v___x_476_, 0, v_buckets_474_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_buckets_474_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_486_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_box(0);
v___x_484_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_u2082_473_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_482_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_s_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_SMap_iter___redArg(v_s_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_s_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_SMap_iter(v_00_u03b1_495_, v_00_u03b2_496_, v_inst_497_, v_inst_498_, v_s_499_);
lean_dec_ref(v_inst_498_);
lean_dec_ref(v_inst_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_501_){
_start:
{
uint8_t v_stage_u2081_502_; 
v_stage_u2081_502_ = lean_ctor_get_uint8(v_m_501_, sizeof(void*)*2);
if (v_stage_u2081_502_ == 0)
{
return v_m_501_;
}
else
{
lean_object* v_map_u2081_503_; lean_object* v_map_u2082_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_map_u2081_503_ = lean_ctor_get(v_m_501_, 0);
v_map_u2082_504_ = lean_ctor_get(v_m_501_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_m_501_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v_m_501_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_map_u2082_504_);
lean_inc(v_map_u2081_503_);
lean_dec(v_m_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; lean_object* v___x_510_; 
v___x_508_ = 0;
if (v_isShared_507_ == 0)
{
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_map_u2081_503_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_map_u2082_504_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*2, v___x_508_);
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_m_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_SMap_switch___redArg(v_m_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_m_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_SMap_switch(v_00_u03b1_519_, v_00_u03b2_520_, v_inst_521_, v_inst_522_, v_m_523_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_inst_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_525_, lean_object* v_s_526_, lean_object* v_m_527_){
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
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_00_u03c3_534_, lean_object* v_f_535_, lean_object* v_s_536_, lean_object* v_m_537_){
_start:
{
lean_object* v_map_u2082_538_; lean_object* v___x_539_; 
v_map_u2082_538_ = lean_ctor_get(v_m_537_, 1);
lean_inc_ref(v_map_u2082_538_);
lean_dec_ref(v_m_537_);
v___x_539_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_538_, v_f_535_, v_s_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_00_u03c3_544_, lean_object* v_f_545_, lean_object* v_s_546_, lean_object* v_m_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_SMap_foldStage2(v_00_u03b1_540_, v_00_u03b2_541_, v_inst_542_, v_inst_543_, v_00_u03c3_544_, v_f_545_, v_s_546_, v_m_547_);
lean_dec_ref(v_inst_543_);
lean_dec_ref(v_inst_542_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_549_, lean_object* v_f_550_, lean_object* v_map_u2082_551_, lean_object* v_____do__lift_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_549_, v_f_550_, v_map_u2082_551_, v_____do__lift_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object* v_inst_554_, lean_object* v_f_555_, lean_object* v_acc_556_, lean_object* v_l_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_554_, v_f_555_, v_acc_556_, v_l_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_559_, lean_object* v_f_560_, lean_object* v_init_561_, lean_object* v_map_562_){
_start:
{
lean_object* v_map_u2081_563_; lean_object* v_toApplicative_564_; lean_object* v_toBind_565_; lean_object* v_map_u2082_566_; lean_object* v_buckets_567_; lean_object* v_toPure_568_; lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_map_u2081_563_ = lean_ctor_get(v_map_562_, 0);
lean_inc_ref(v_map_u2081_563_);
v_toApplicative_564_ = lean_ctor_get(v_inst_559_, 0);
v_toBind_565_ = lean_ctor_get(v_inst_559_, 1);
lean_inc(v_toBind_565_);
v_map_u2082_566_ = lean_ctor_get(v_map_562_, 1);
lean_inc_ref(v_map_u2082_566_);
lean_dec_ref(v_map_562_);
v_buckets_567_ = lean_ctor_get(v_map_u2081_563_, 1);
lean_inc_ref(v_buckets_567_);
lean_dec_ref(v_map_u2081_563_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_564_, 1);
lean_inc(v_f_560_);
lean_inc_ref(v_inst_559_);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_569_, 0, v_inst_559_);
lean_closure_set(v___f_569_, 1, v_f_560_);
lean_closure_set(v___f_569_, 2, v_map_u2082_566_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_array_get_size(v_buckets_567_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_inc(v_toPure_568_);
lean_dec_ref(v_buckets_567_);
lean_dec(v_f_560_);
lean_dec_ref(v_inst_559_);
v___x_573_ = lean_apply_2(v_toPure_568_, lean_box(0), v_init_561_);
v___x_574_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_573_, v___f_569_);
return v___x_574_;
}
else
{
lean_object* v___f_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_inc_ref(v_inst_559_);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_575_, 0, v_inst_559_);
lean_closure_set(v___f_575_, 1, v_f_560_);
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_571_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_559_, v___f_575_, v_buckets_567_, v___x_576_, v___x_577_, v_init_561_);
v___x_579_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_578_, v___f_569_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_00_u03c3_584_, lean_object* v_m_585_, lean_object* v_inst_586_, lean_object* v_f_587_, lean_object* v_init_588_, lean_object* v_map_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_SMap_foldM___redArg(v_inst_586_, v_f_587_, v_init_588_, v_map_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object* v_00_u03b1_591_, lean_object* v_00_u03b2_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_00_u03c3_595_, lean_object* v_m_596_, lean_object* v_inst_597_, lean_object* v_f_598_, lean_object* v_init_599_, lean_object* v_map_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_SMap_foldM(v_00_u03b1_591_, v_00_u03b2_592_, v_inst_593_, v_inst_594_, v_00_u03c3_595_, v_m_596_, v_inst_597_, v_f_598_, v_init_599_, v_map_600_);
lean_dec_ref(v_inst_594_);
lean_dec_ref(v_inst_593_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object* v_f_602_, lean_object* v_x1_603_, lean_object* v_x2_604_, lean_object* v_x3_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_apply_3(v_f_602_, v_x1_603_, v_x2_604_, v_x3_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__1(lean_object* v___x_607_, lean_object* v___f_608_, lean_object* v_acc_609_, lean_object* v_l_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_607_, v___f_608_, v_acc_609_, v_l_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object* v_f_631_, lean_object* v_init_632_, lean_object* v_m_633_){
_start:
{
lean_object* v_map_u2081_634_; lean_object* v_map_u2082_635_; lean_object* v___x_636_; lean_object* v_buckets_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_map_u2081_634_ = lean_ctor_get(v_m_633_, 0);
lean_inc_ref(v_map_u2081_634_);
v_map_u2082_635_ = lean_ctor_get(v_m_633_, 1);
lean_inc_ref(v_map_u2082_635_);
lean_dec_ref(v_m_633_);
v___x_636_ = ((lean_object*)(l_Lean_SMap_fold___redArg___closed__9));
v_buckets_637_ = lean_ctor_get(v_map_u2081_634_, 1);
lean_inc_ref(v_buckets_637_);
lean_dec_ref(v_map_u2081_634_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_array_get_size(v_buckets_637_);
v___x_640_ = lean_nat_dec_lt(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_buckets_637_);
v___x_641_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_635_, v_f_631_, v_init_632_);
return v___x_641_;
}
else
{
lean_object* v___f_642_; lean_object* v___f_643_; size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc(v_f_631_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_642_, 0, v_f_631_);
v___f_643_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_643_, 0, v___x_636_);
lean_closure_set(v___f_643_, 1, v___f_642_);
v___x_644_ = ((size_t)0ULL);
v___x_645_ = lean_usize_of_nat(v___x_639_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_636_, v___f_643_, v_buckets_637_, v___x_644_, v___x_645_, v_init_632_);
v___x_647_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_635_, v_f_631_, v___x_646_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_00_u03c3_652_, lean_object* v_f_653_, lean_object* v_init_654_, lean_object* v_m_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_SMap_fold___redArg(v_f_653_, v_init_654_, v_m_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_00_u03c3_661_, lean_object* v_f_662_, lean_object* v_init_663_, lean_object* v_m_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_SMap_fold(v_00_u03b1_657_, v_00_u03b2_658_, v_inst_659_, v_inst_660_, v_00_u03c3_661_, v_f_662_, v_init_663_, v_m_664_);
lean_dec_ref(v_inst_660_);
lean_dec_ref(v_inst_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_666_){
_start:
{
lean_object* v_map_u2081_667_; lean_object* v___x_668_; 
v_map_u2081_667_ = lean_ctor_get(v_m_666_, 0);
v___x_668_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_SMap_numBuckets___redArg(v_m_669_);
lean_dec_ref(v_m_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_m_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_SMap_numBuckets___redArg(v_m_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_m_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_SMap_numBuckets(v_00_u03b1_677_, v_00_u03b2_678_, v_inst_679_, v_inst_680_, v_m_681_);
lean_dec_ref(v_m_681_);
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_683_, lean_object* v_a_684_, lean_object* v_b_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v_a_684_);
lean_ctor_set(v___x_686_, 1, v_b_685_);
v___x_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_es_683_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___f_690_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_691_ = lean_box(0);
v___x_692_ = l_Lean_SMap_fold___redArg(v___f_690_, v___x_691_, v_m_689_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_m_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_SMap_toList___redArg(v_m_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_m_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_SMap_toList(v_00_u03b1_699_, v_00_u03b2_700_, v_inst_701_, v_inst_702_, v_m_703_);
lean_dec_ref(v_inst_702_);
lean_dec_ref(v_inst_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg___lam__0(lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_s_707_, lean_object* v_x_708_){
_start:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_711_; 
v_fst_709_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_fst_709_);
v_snd_710_ = lean_ctor_get(v_x_708_, 1);
lean_inc(v_snd_710_);
lean_dec_ref(v_x_708_);
v___x_711_ = l_Lean_SMap_insert___redArg(v_inst_705_, v_inst_706_, v_s_707_, v_fst_709_, v_snd_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_es_714_){
_start:
{
lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___f_715_ = lean_alloc_closure((void*)(l_Lean_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_715_, 0, v_inst_712_);
lean_closure_set(v___f_715_, 1, v_inst_713_);
v___x_716_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__4, &l_Lean_SMap_instInhabited___redArg___closed__4_once, _init_l_Lean_SMap_instInhabited___redArg___closed__4);
v___x_717_ = l_List_foldl___redArg(v___f_715_, v___x_716_, v_es_714_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_es_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_List_toSMap___redArg(v_inst_720_, v_inst_721_, v_es_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_727_, lean_object* v_v_728_, lean_object* v_prec_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_730_ = l_Lean_SMap_toList___redArg(v_v_728_);
v___x_731_ = l_List_repr___redArg(v___x_727_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Repr_addAppParen(v___x_733_, v_prec_729_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_735_, lean_object* v_v_736_, lean_object* v_prec_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_instReprSMap___redArg___lam__0(v___x_735_, v_v_736_, v_prec_737_);
lean_dec(v_prec_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_739_, lean_object* v_inst_740_){
_start:
{
lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___f_743_; 
v___f_741_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_741_, 0, v_inst_740_);
v___x_742_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_742_, 0, lean_box(0));
lean_closure_set(v___x_742_, 1, lean_box(0));
lean_closure_set(v___x_742_, 2, v_inst_739_);
lean_closure_set(v___x_742_, 3, v___f_741_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_743_, 0, v___x_742_);
return v___f_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_inst_748_, lean_object* v_inst_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_instReprSMap___redArg(v_inst_748_, v_inst_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_751_, lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_inst_755_, lean_object* v_inst_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_instReprSMap(v_00_u03b1_751_, v_00_u03b2_752_, v_x_753_, v_x_754_, v_inst_755_, v_inst_756_);
lean_dec_ref(v_x_754_);
lean_dec_ref(v_x_753_);
return v_res_757_;
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
