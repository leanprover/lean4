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
lean_object* l_Lean_SMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__4, &l_Lean_SMap_instInhabited___redArg___closed__4_once, _init_l_Lean_SMap_instInhabited___redArg___closed__4);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_SMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l_Lean_SMap_instInhabited___redArg();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_SMap_instInhabited___redArg();
return v_res_18_;
}
}
static lean_object* _init_l_Lean_SMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_SMap_instInhabited___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__0, &l_Lean_SMap_instInhabited___closed__0_once, _init_l_Lean_SMap_instInhabited___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instInhabited___boxed(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_inst_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_SMap_instInhabited(v_00_u03b1_25_, v_00_u03b2_26_, v_inst_27_, v_inst_28_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
return v_res_29_;
}
}
lean_object* l_Lean_SMap_empty___redArg(){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__4, &l_Lean_SMap_instInhabited___redArg___closed__4_once, _init_l_Lean_SMap_instInhabited___redArg___closed__4);
return v___x_31_;
}
}
LEAN_EXPORT void l_Lean_SMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_32_;
v_res_32_ = l_Lean_SMap_empty___redArg();
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_SMap_empty___redArg();
return v_res_34_;
}
}
static lean_object* _init_l_Lean_SMap_empty___closed__0(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_SMap_empty___redArg();
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Lean_SMap_empty___closed__0, &l_Lean_SMap_empty___closed__0_once, _init_l_Lean_SMap_empty___closed__0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_empty___boxed(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_SMap_empty(v_00_u03b1_41_, v_00_u03b2_42_, v_inst_43_, v_inst_44_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
return v_res_45_;
}
}
lean_object* l_Lean_SMap_fromHashMap___redArg(lean_object* v_m_46_, uint8_t v_stage_u2081_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__3, &l_Lean_SMap_instInhabited___redArg___closed__3_once, _init_l_Lean_SMap_instInhabited___redArg___closed__3);
v___x_49_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_49_, 0, v_m_46_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*2, v_stage_u2081_47_);
return v___x_49_;
}
}
LEAN_EXPORT void l_Lean_SMap_fromHashMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_46_ = stack[0].m_obj;
uint8_t v_stage_u2081_47_ = stack[1].m_num;
lean_object* v_res_50_;
v_res_50_ = l_Lean_SMap_fromHashMap___redArg(v_m_46_, v_stage_u2081_47_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___redArg___boxed(lean_object* v_m_51_, lean_object* v_stage_u2081_52_){
_start:
{
uint8_t v_stage_u2081_boxed_53_; lean_object* v_res_54_; 
v_stage_u2081_boxed_53_ = lean_unbox(v_stage_u2081_52_);
v_res_54_ = l_Lean_SMap_fromHashMap___redArg(v_m_51_, v_stage_u2081_boxed_53_);
return v_res_54_;
}
}
lean_object* l_Lean_SMap_fromHashMap(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_m_59_, uint8_t v_stage_u2081_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__3, &l_Lean_SMap_instInhabited___redArg___closed__3_once, _init_l_Lean_SMap_instInhabited___redArg___closed__3);
v___x_62_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_62_, 0, v_m_59_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*2, v_stage_u2081_60_);
return v___x_62_;
}
}
LEAN_EXPORT void l_Lean_SMap_fromHashMap_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_57_ = stack[2].m_obj;
lean_object* v_inst_58_ = stack[3].m_obj;
lean_object* v_m_59_ = stack[4].m_obj;
uint8_t v_stage_u2081_60_ = stack[5].m_num;
lean_object* v_res_63_;
v_res_63_ = l_Lean_SMap_fromHashMap(lean_box(0), lean_box(0), v_inst_57_, v_inst_58_, v_m_59_, v_stage_u2081_60_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_fromHashMap___boxed(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_m_68_, lean_object* v_stage_u2081_69_){
_start:
{
uint8_t v_stage_u2081_boxed_70_; lean_object* v_res_71_; 
v_stage_u2081_boxed_70_ = lean_unbox(v_stage_u2081_69_);
v_res_71_ = l_Lean_SMap_fromHashMap(v_00_u03b1_64_, v_00_u03b2_65_, v_inst_66_, v_inst_67_, v_m_68_, v_stage_u2081_boxed_70_);
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_inst_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___redArg(lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_stage_u2081_77_; 
v_stage_u2081_77_ = lean_ctor_get_uint8(v_x_74_, sizeof(void*)*2);
if (v_stage_u2081_77_ == 0)
{
lean_object* v_map_u2081_78_; lean_object* v_map_u2082_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
v_map_u2081_78_ = lean_ctor_get(v_x_74_, 0);
v_map_u2082_79_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v_x_74_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_map_u2082_79_);
lean_inc(v_map_u2081_78_);
lean_dec(v_x_74_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_72_, v_inst_73_, v_map_u2082_79_, v_x_75_, v_x_76_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_map_u2081_78_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_83_);
lean_ctor_set_uint8(v_reuseFailAlloc_86_, sizeof(void*)*2, v_stage_u2081_77_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_map_u2081_88_; lean_object* v_map_u2082_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v_map_u2081_88_ = lean_ctor_get(v_x_74_, 0);
v_map_u2082_89_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v_x_74_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_map_u2082_89_);
lean_inc(v_map_u2081_88_);
lean_dec(v_x_74_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_72_, v_inst_73_, v_map_u2081_88_, v_x_75_, v_x_76_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_map_u2082_89_);
lean_ctor_set_uint8(v_reuseFailAlloc_96_, sizeof(void*)*2, v_stage_u2081_77_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_x_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_SMap_insert___redArg(v_inst_100_, v_inst_101_, v_x_102_, v_x_103_, v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27___redArg(lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_stage_u2081_111_; 
v_stage_u2081_111_ = lean_ctor_get_uint8(v_x_108_, sizeof(void*)*2);
if (v_stage_u2081_111_ == 0)
{
lean_object* v_map_u2081_112_; lean_object* v_map_u2082_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_121_; 
v_map_u2081_112_ = lean_ctor_get(v_x_108_, 0);
v_map_u2082_113_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_121_ == 0)
{
v___x_115_ = v_x_108_;
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_map_u2082_113_);
lean_inc(v_map_u2081_112_);
lean_dec(v_x_108_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_121_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = l_Lean_PersistentHashMap_insert___redArg(v_inst_106_, v_inst_107_, v_map_u2082_113_, v_x_109_, v_x_110_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_117_);
v___x_119_ = v___x_115_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_map_u2081_112_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_120_, sizeof(void*)*2, v_stage_u2081_111_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
lean_object* v_map_u2081_122_; lean_object* v_map_u2082_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_map_u2081_122_ = lean_ctor_get(v_x_108_, 0);
v_map_u2082_123_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v_x_108_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_map_u2082_123_);
lean_inc(v_map_u2081_122_);
lean_dec(v_x_108_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_106_, v_inst_107_, v_map_u2081_122_, v_x_109_, v_x_110_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_map_u2082_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_130_, sizeof(void*)*2, v_stage_u2081_111_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert_x27(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_SMap_insert_x27___redArg(v_inst_134_, v_inst_135_, v_x_136_, v_x_137_, v_x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg(lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
uint8_t v_stage_u2081_144_; 
v_stage_u2081_144_ = lean_ctor_get_uint8(v_x_142_, sizeof(void*)*2);
if (v_stage_u2081_144_ == 0)
{
lean_object* v_map_u2081_145_; lean_object* v_map_u2082_146_; lean_object* v___x_147_; 
v_map_u2081_145_ = lean_ctor_get(v_x_142_, 0);
v_map_u2082_146_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_x_143_);
lean_inc_ref(v_inst_141_);
lean_inc_ref(v_inst_140_);
v___x_147_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_140_, v_inst_141_, v_map_u2082_146_, v_x_143_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_140_, v_inst_141_, v_map_u2081_145_, v_x_143_);
return v___x_148_;
}
else
{
lean_dec(v_x_143_);
lean_dec_ref(v_inst_141_);
lean_dec_ref(v_inst_140_);
return v___x_147_;
}
}
else
{
lean_object* v_map_u2081_149_; lean_object* v___x_150_; 
v_map_u2081_149_ = lean_ctor_get(v_x_142_, 0);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_140_, v_inst_141_, v_map_u2081_149_, v_x_143_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___redArg___boxed(lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_SMap_find_x3f___redArg(v_inst_151_, v_inst_152_, v_x_153_, v_x_154_);
lean_dec_ref(v_x_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_SMap_find_x3f___redArg(v_inst_158_, v_inst_159_, v_x_160_, v_x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___boxed(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_SMap_find_x3f(v_00_u03b1_163_, v_00_u03b2_164_, v_inst_165_, v_inst_166_, v_x_167_, v_x_168_);
lean_dec_ref(v_x_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg(lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_m_172_, lean_object* v_a_173_, lean_object* v_b_u2080_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_SMap_find_x3f___redArg(v_inst_170_, v_inst_171_, v_m_172_, v_a_173_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_inc(v_b_u2080_174_);
return v_b_u2080_174_;
}
else
{
lean_object* v_val_176_; 
v_val_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_176_);
lean_dec_ref_known(v___x_175_, 1);
return v_val_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___redArg___boxed(lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_m_179_, lean_object* v_a_180_, lean_object* v_b_u2080_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_SMap_findD___redArg(v_inst_177_, v_inst_178_, v_m_179_, v_a_180_, v_b_u2080_181_);
lean_dec(v_b_u2080_181_);
lean_dec_ref(v_m_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_m_187_, lean_object* v_a_188_, lean_object* v_b_u2080_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_SMap_find_x3f___redArg(v_inst_185_, v_inst_186_, v_m_187_, v_a_188_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_inc(v_b_u2080_189_);
return v_b_u2080_189_;
}
else
{
lean_object* v_val_191_; 
v_val_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_191_);
lean_dec_ref_known(v___x_190_, 1);
return v_val_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_findD___boxed(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_u2080_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_SMap_findD(v_00_u03b1_192_, v_00_u03b2_193_, v_inst_194_, v_inst_195_, v_m_196_, v_a_197_, v_b_u2080_198_);
lean_dec(v_b_u2080_198_);
lean_dec_ref(v_m_196_);
return v_res_199_;
}
}
static lean_object* _init_l_Lean_SMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_203_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__2));
v___x_204_ = lean_unsigned_to_nat(14u);
v___x_205_ = lean_unsigned_to_nat(70u);
v___x_206_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__1));
v___x_207_ = ((lean_object*)(l_Lean_SMap_find_x21___redArg___closed__0));
v___x_208_ = l_mkPanicMessageWithDecl(v___x_207_, v___x_206_, v___x_205_, v___x_204_, v___x_203_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg(lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_m_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_SMap_find_x3f___redArg(v_inst_209_, v_inst_210_, v_m_212_, v_a_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_216_ = l_panic___redArg(v_inst_211_, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; 
v_val_217_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_214_, 1);
return v_val_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___redArg___boxed(lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_m_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_SMap_find_x21___redArg(v_inst_218_, v_inst_219_, v_inst_220_, v_m_221_, v_a_222_);
lean_dec_ref(v_m_221_);
lean_dec(v_inst_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_m_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_SMap_find_x3f___redArg(v_inst_226_, v_inst_227_, v_m_229_, v_a_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_233_ = l_panic___redArg(v_inst_228_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_231_, 1);
return v_val_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21___boxed(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_m_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_SMap_find_x21(v_00_u03b1_235_, v_00_u03b2_236_, v_inst_237_, v_inst_238_, v_inst_239_, v_m_240_, v_a_241_);
lean_dec_ref(v_m_240_);
lean_dec(v_inst_239_);
return v_res_242_;
}
}
uint8_t l_Lean_SMap_contains___redArg(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
uint8_t v_stage_u2081_247_; 
v_stage_u2081_247_ = lean_ctor_get_uint8(v_x_245_, sizeof(void*)*2);
if (v_stage_u2081_247_ == 0)
{
lean_object* v_map_u2081_248_; lean_object* v_map_u2082_249_; uint8_t v___x_250_; 
v_map_u2081_248_ = lean_ctor_get(v_x_245_, 0);
lean_inc_ref(v_map_u2081_248_);
v_map_u2082_249_ = lean_ctor_get(v_x_245_, 1);
lean_inc_ref(v_map_u2082_249_);
lean_dec_ref(v_x_245_);
lean_inc(v_x_246_);
lean_inc_ref(v_inst_244_);
lean_inc_ref(v_inst_243_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_243_, v_inst_244_, v_map_u2081_248_, v_x_246_);
lean_dec_ref(v_map_u2081_248_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_243_, v_inst_244_, v_map_u2082_249_, v_x_246_);
return v___x_251_;
}
else
{
lean_dec_ref(v_map_u2082_249_);
lean_dec(v_x_246_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
return v___x_250_;
}
}
else
{
lean_object* v_map_u2081_252_; uint8_t v___x_253_; 
v_map_u2081_252_ = lean_ctor_get(v_x_245_, 0);
lean_inc_ref(v_map_u2081_252_);
lean_dec_ref(v_x_245_);
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_243_, v_inst_244_, v_map_u2081_252_, v_x_246_);
lean_dec_ref(v_map_u2081_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT void l_Lean_SMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_243_ = stack[0].m_obj;
lean_object* v_inst_244_ = stack[1].m_obj;
lean_object* v_x_245_ = stack[2].m_obj;
lean_object* v_x_246_ = stack[3].m_obj;
uint8_t v_res_254_;
v_res_254_ = l_Lean_SMap_contains___redArg(v_inst_243_, v_inst_244_, v_x_245_, v_x_246_);
stack->m_num = v_res_254_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_SMap_contains___redArg(v_inst_255_, v_inst_256_, v_x_257_, v_x_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
uint8_t l_Lean_SMap_contains(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = l_Lean_SMap_contains___redArg(v_inst_263_, v_inst_264_, v_x_265_, v_x_266_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_SMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_263_ = stack[2].m_obj;
lean_object* v_inst_264_ = stack[3].m_obj;
lean_object* v_x_265_ = stack[4].m_obj;
lean_object* v_x_266_ = stack[5].m_obj;
uint8_t v_res_268_;
v_res_268_ = l_Lean_SMap_contains(lean_box(0), lean_box(0), v_inst_263_, v_inst_264_, v_x_265_, v_x_266_);
stack->m_num = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_Lean_SMap_contains(v_00_u03b1_269_, v_00_u03b2_270_, v_inst_271_, v_inst_272_, v_x_273_, v_x_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
uint8_t v_stage_u2081_281_; 
v_stage_u2081_281_ = lean_ctor_get_uint8(v_x_279_, sizeof(void*)*2);
if (v_stage_u2081_281_ == 0)
{
lean_object* v_map_u2081_282_; lean_object* v_map_u2082_283_; lean_object* v___x_284_; 
v_map_u2081_282_ = lean_ctor_get(v_x_279_, 0);
v_map_u2082_283_ = lean_ctor_get(v_x_279_, 1);
lean_inc(v_x_280_);
lean_inc_ref(v_inst_278_);
lean_inc_ref(v_inst_277_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_277_, v_inst_278_, v_map_u2081_282_, v_x_280_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_277_, v_inst_278_, v_map_u2082_283_, v_x_280_);
return v___x_285_;
}
else
{
lean_dec(v_x_280_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
return v___x_284_;
}
}
else
{
lean_object* v_map_u2081_286_; lean_object* v___x_287_; 
v_map_u2081_286_ = lean_ctor_get(v_x_279_, 0);
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_277_, v_inst_278_, v_map_u2081_286_, v_x_280_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg___boxed(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_288_, v_inst_289_, v_x_290_, v_x_291_);
lean_dec_ref(v_x_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_295_, v_inst_296_, v_x_297_, v_x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___boxed(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_SMap_find_x3f_x27(v_00_u03b1_300_, v_00_u03b2_301_, v_inst_302_, v_inst_303_, v_x_304_, v_x_305_);
lean_dec_ref(v_x_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object* v_inst_307_, lean_object* v_map_u2082_308_, lean_object* v_f_309_, lean_object* v_____r_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_307_, v_map_u2082_308_, v_f_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object* v_f_312_, lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_apply_2(v_f_312_, v___y_314_, v___y_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__2(lean_object* v_inst_317_, lean_object* v___f_318_, lean_object* v_x_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box(0);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_317_, v___f_318_, v___x_321_, v___y_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object* v_inst_323_, lean_object* v_s_324_, lean_object* v_f_325_){
_start:
{
lean_object* v_map_u2081_326_; lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_map_u2082_329_; lean_object* v_buckets_330_; lean_object* v_toPure_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_map_u2081_326_ = lean_ctor_get(v_s_324_, 0);
lean_inc_ref(v_map_u2081_326_);
v_toApplicative_327_ = lean_ctor_get(v_inst_323_, 0);
v_toBind_328_ = lean_ctor_get(v_inst_323_, 1);
lean_inc(v_toBind_328_);
v_map_u2082_329_ = lean_ctor_get(v_s_324_, 1);
lean_inc_ref(v_map_u2082_329_);
lean_dec_ref(v_s_324_);
v_buckets_330_ = lean_ctor_get(v_map_u2081_326_, 1);
lean_inc_ref(v_buckets_330_);
lean_dec_ref(v_map_u2081_326_);
v_toPure_331_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc(v_f_325_);
lean_inc_ref(v_inst_323_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_332_, 0, v_inst_323_);
lean_closure_set(v___f_332_, 1, v_map_u2082_329_);
lean_closure_set(v___f_332_, 2, v_f_325_);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_array_get_size(v_buckets_330_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_nat_dec_lt(v___x_333_, v___x_334_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_inc(v_toPure_331_);
lean_dec_ref(v_buckets_330_);
lean_dec(v_f_325_);
lean_dec_ref(v_inst_323_);
v___x_337_ = lean_apply_2(v_toPure_331_, lean_box(0), v___x_335_);
v___x_338_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_337_, v___f_332_);
return v___x_338_;
}
else
{
lean_object* v___f_339_; lean_object* v___f_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___f_339_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 1);
lean_closure_set(v___f_339_, 0, v_f_325_);
lean_inc_ref(v_inst_323_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_340_, 0, v_inst_323_);
lean_closure_set(v___f_340_, 1, v___f_339_);
v___x_341_ = ((size_t)0ULL);
v___x_342_ = lean_usize_of_nat(v___x_334_);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_323_, v___f_340_, v_buckets_330_, v___x_341_, v___x_342_, v___x_335_);
v___x_344_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_343_, v___f_332_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_m_349_, lean_object* v_inst_350_, lean_object* v_s_351_, lean_object* v_f_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_SMap_forM___redArg(v_inst_350_, v_s_351_, v_f_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_m_358_, lean_object* v_inst_359_, lean_object* v_s_360_, lean_object* v_f_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_SMap_forM(v_00_u03b1_354_, v_00_u03b2_355_, v_inst_356_, v_inst_357_, v_m_358_, v_inst_359_, v_s_360_, v_f_361_);
lean_dec_ref(v_inst_357_);
lean_dec_ref(v_inst_356_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_363_, lean_object* v_x_364_, lean_object* v_y_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_x_364_);
lean_ctor_set(v___x_366_, 1, v_y_365_);
v___x_367_ = lean_apply_1(v_f_363_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_368_, lean_object* v_s_369_, lean_object* v_f_370_){
_start:
{
lean_object* v___f_371_; lean_object* v___x_372_; 
v___f_371_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_371_, 0, v_f_370_);
v___x_372_ = l_Lean_SMap_forM___redArg(v_inst_368_, v_s_369_, v___f_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_373_){
_start:
{
lean_object* v___f_374_; 
v___f_374_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_374_, 0, v_inst_373_);
return v___f_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_m_379_, lean_object* v_inst_380_){
_start:
{
lean_object* v___f_381_; 
v___f_381_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_381_, 0, v_inst_380_);
return v___f_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_m_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_382_, v_00_u03b2_383_, v_inst_384_, v_inst_385_, v_m_386_, v_inst_387_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_inst_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_389_, lean_object* v_____do__lift_390_){
_start:
{
if (lean_obj_tag(v_____do__lift_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_ctor_get(v_____do__lift_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v_____do__lift_390_, 1);
v___x_392_ = lean_apply_2(v_toPure_389_, lean_box(0), v_a_391_);
return v___x_392_;
}
else
{
lean_object* v_a_393_; lean_object* v_snd_394_; lean_object* v___x_395_; 
v_a_393_ = lean_ctor_get(v_____do__lift_390_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v_____do__lift_390_, 1);
v_snd_394_ = lean_ctor_get(v_a_393_, 1);
lean_inc(v_snd_394_);
lean_dec(v_a_393_);
v___x_395_ = lean_apply_2(v_toPure_389_, lean_box(0), v_snd_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_396_, lean_object* v_____do__lift_397_){
_start:
{
if (lean_obj_tag(v_____do__lift_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_a_398_ = lean_ctor_get(v_____do__lift_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_____do__lift_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_____do__lift_397_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v_____do__lift_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_405_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; 
v___x_404_ = lean_apply_2(v_toPure_396_, lean_box(0), v___x_403_);
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_417_; 
v_a_407_ = lean_ctor_get(v_____do__lift_397_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_____do__lift_397_);
if (v_isSharedCheck_417_ == 0)
{
v___x_409_ = v_____do__lift_397_;
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v_____do__lift_397_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_417_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_a_407_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_416_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = lean_apply_2(v_toPure_396_, lean_box(0), v___x_414_);
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_418_, lean_object* v_toBind_419_, lean_object* v___f_420_, lean_object* v_x_421_, lean_object* v_y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_x_421_);
lean_ctor_set(v___x_424_, 1, v_y_422_);
v___x_425_ = lean_apply_2(v___y_418_, v___x_424_, v___y_423_);
v___x_426_ = lean_apply_4(v_toBind_419_, lean_box(0), lean_box(0), v___x_425_, v___f_420_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_427_, lean_object* v_00_u03b2_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; lean_object* v___f_443_; lean_object* v___f_444_; lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_toApplicative_452_; lean_object* v_toBind_453_; lean_object* v_toPure_454_; lean_object* v___f_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_142__overap_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_inc_ref_n(v_inst_427_, 7);
v___f_432_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_432_, 0, v_inst_427_);
v___f_433_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_433_, 0, v_inst_427_);
v___f_434_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_434_, 0, v_inst_427_);
v___f_435_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_435_, 0, v_inst_427_);
v___x_436_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_436_, 0, lean_box(0));
lean_closure_set(v___x_436_, 1, lean_box(0));
lean_closure_set(v___x_436_, 2, v_inst_427_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___f_432_);
v___x_438_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_438_, 0, lean_box(0));
lean_closure_set(v___x_438_, 1, lean_box(0));
lean_closure_set(v___x_438_, 2, v_inst_427_);
v___x_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
lean_ctor_set(v___x_439_, 2, v___f_433_);
lean_ctor_set(v___x_439_, 3, v___f_434_);
lean_ctor_set(v___x_439_, 4, v___f_435_);
v___x_440_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_440_, 0, lean_box(0));
lean_closure_set(v___x_440_, 1, lean_box(0));
lean_closure_set(v___x_440_, 2, v_inst_427_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_inc_ref_n(v___x_441_, 6);
v___f_442_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_442_, 0, v___x_441_);
v___f_443_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_443_, 0, v___x_441_);
v___f_444_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_444_, 0, v___x_441_);
v___f_445_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_445_, 0, v___x_441_);
v___x_446_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_446_, 0, lean_box(0));
lean_closure_set(v___x_446_, 1, lean_box(0));
lean_closure_set(v___x_446_, 2, v___x_441_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___f_442_);
v___x_448_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_448_, 0, lean_box(0));
lean_closure_set(v___x_448_, 1, lean_box(0));
lean_closure_set(v___x_448_, 2, v___x_441_);
v___x_449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_ctor_set(v___x_449_, 2, v___f_443_);
lean_ctor_set(v___x_449_, 3, v___f_444_);
lean_ctor_set(v___x_449_, 4, v___f_445_);
v___x_450_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_450_, 0, lean_box(0));
lean_closure_set(v___x_450_, 1, lean_box(0));
lean_closure_set(v___x_450_, 2, v___x_441_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v_toApplicative_452_ = lean_ctor_get(v_inst_427_, 0);
lean_inc_ref(v_toApplicative_452_);
v_toBind_453_ = lean_ctor_get(v_inst_427_, 1);
lean_inc_n(v_toBind_453_, 2);
lean_dec_ref(v_inst_427_);
v_toPure_454_ = lean_ctor_get(v_toApplicative_452_, 1);
lean_inc_n(v_toPure_454_, 2);
lean_dec_ref(v_toApplicative_452_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_455_, 0, v_toPure_454_);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_456_, 0, v_toPure_454_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_457_, 0, v___y_431_);
lean_closure_set(v___f_457_, 1, v_toBind_453_);
lean_closure_set(v___f_457_, 2, v___f_456_);
v___x_142__overap_458_ = l_Lean_SMap_forM___redArg(v___x_451_, v___y_429_, v___f_457_);
v___x_459_ = lean_apply_1(v___x_142__overap_458_, v___y_430_);
v___x_460_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v___x_459_, v___f_455_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_461_){
_start:
{
lean_object* v___f_462_; 
v___f_462_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_462_, 0, v_inst_461_);
return v___f_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_m_467_, lean_object* v_inst_468_){
_start:
{
lean_object* v___f_469_; 
v___f_469_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_469_, 0, v_inst_468_);
return v___f_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_m_474_, lean_object* v_inst_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_470_, v_00_u03b2_471_, v_inst_472_, v_inst_473_, v_m_474_, v_inst_475_);
lean_dec_ref(v_inst_473_);
lean_dec_ref(v_inst_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___redArg(lean_object* v_s_477_){
_start:
{
lean_object* v_map_u2081_478_; lean_object* v_map_u2082_479_; lean_object* v_buckets_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_493_; 
v_map_u2081_478_ = lean_ctor_get(v_s_477_, 0);
lean_inc_ref(v_map_u2081_478_);
v_map_u2082_479_ = lean_ctor_get(v_s_477_, 1);
lean_inc_ref(v_map_u2082_479_);
lean_dec_ref(v_s_477_);
v_buckets_480_ = lean_ctor_get(v_map_u2081_478_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_map_u2081_478_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_map_u2081_478_, 0);
lean_dec(v_unused_494_);
v___x_482_ = v_map_u2081_478_;
v_isShared_483_ = v_isSharedCheck_493_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_buckets_480_);
lean_dec(v_map_u2081_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_493_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_unsigned_to_nat(0u);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_484_);
lean_ctor_set(v___x_482_, 0, v_buckets_480_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_buckets_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_492_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_box(0);
v___x_490_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_u2082_479_, v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_488_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_s_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_SMap_iter___redArg(v_s_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_iter___boxed(lean_object* v_00_u03b1_501_, lean_object* v_00_u03b2_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_s_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_SMap_iter(v_00_u03b1_501_, v_00_u03b2_502_, v_inst_503_, v_inst_504_, v_s_505_);
lean_dec_ref(v_inst_504_);
lean_dec_ref(v_inst_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_507_){
_start:
{
uint8_t v_stage_u2081_508_; 
v_stage_u2081_508_ = lean_ctor_get_uint8(v_m_507_, sizeof(void*)*2);
if (v_stage_u2081_508_ == 0)
{
return v_m_507_;
}
else
{
lean_object* v_map_u2081_509_; lean_object* v_map_u2082_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_map_u2081_509_ = lean_ctor_get(v_m_507_, 0);
v_map_u2082_510_ = lean_ctor_get(v_m_507_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_m_507_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v_m_507_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_map_u2082_510_);
lean_inc(v_map_u2081_509_);
lean_dec(v_m_507_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; lean_object* v___x_516_; 
v___x_514_ = 0;
if (v_isShared_513_ == 0)
{
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_map_u2081_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_map_u2082_510_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*2, v___x_514_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_m_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_SMap_switch___redArg(v_m_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_m_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_SMap_switch(v_00_u03b1_525_, v_00_u03b2_526_, v_inst_527_, v_inst_528_, v_m_529_);
lean_dec_ref(v_inst_528_);
lean_dec_ref(v_inst_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_531_, lean_object* v_s_532_, lean_object* v_m_533_){
_start:
{
lean_object* v_map_u2082_534_; lean_object* v___x_535_; 
v_map_u2082_534_ = lean_ctor_get(v_m_533_, 1);
lean_inc_ref(v_map_u2082_534_);
lean_dec_ref(v_m_533_);
v___x_535_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_534_, v_f_531_, v_s_532_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_00_u03c3_540_, lean_object* v_f_541_, lean_object* v_s_542_, lean_object* v_m_543_){
_start:
{
lean_object* v_map_u2082_544_; lean_object* v___x_545_; 
v_map_u2082_544_ = lean_ctor_get(v_m_543_, 1);
lean_inc_ref(v_map_u2082_544_);
lean_dec_ref(v_m_543_);
v___x_545_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_544_, v_f_541_, v_s_542_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_00_u03c3_550_, lean_object* v_f_551_, lean_object* v_s_552_, lean_object* v_m_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_SMap_foldStage2(v_00_u03b1_546_, v_00_u03b2_547_, v_inst_548_, v_inst_549_, v_00_u03c3_550_, v_f_551_, v_s_552_, v_m_553_);
lean_dec_ref(v_inst_549_);
lean_dec_ref(v_inst_548_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_555_, lean_object* v_f_556_, lean_object* v_map_u2082_557_, lean_object* v_____do__lift_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_555_, v_f_556_, v_map_u2082_557_, v_____do__lift_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object* v_inst_560_, lean_object* v_f_561_, lean_object* v_acc_562_, lean_object* v_l_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_560_, v_f_561_, v_acc_562_, v_l_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_565_, lean_object* v_f_566_, lean_object* v_init_567_, lean_object* v_map_568_){
_start:
{
lean_object* v_map_u2081_569_; lean_object* v_toApplicative_570_; lean_object* v_toBind_571_; lean_object* v_map_u2082_572_; lean_object* v_buckets_573_; lean_object* v_toPure_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_map_u2081_569_ = lean_ctor_get(v_map_568_, 0);
lean_inc_ref(v_map_u2081_569_);
v_toApplicative_570_ = lean_ctor_get(v_inst_565_, 0);
v_toBind_571_ = lean_ctor_get(v_inst_565_, 1);
lean_inc(v_toBind_571_);
v_map_u2082_572_ = lean_ctor_get(v_map_568_, 1);
lean_inc_ref(v_map_u2082_572_);
lean_dec_ref(v_map_568_);
v_buckets_573_ = lean_ctor_get(v_map_u2081_569_, 1);
lean_inc_ref(v_buckets_573_);
lean_dec_ref(v_map_u2081_569_);
v_toPure_574_ = lean_ctor_get(v_toApplicative_570_, 1);
lean_inc(v_f_566_);
lean_inc_ref(v_inst_565_);
v___f_575_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_575_, 0, v_inst_565_);
lean_closure_set(v___f_575_, 1, v_f_566_);
lean_closure_set(v___f_575_, 2, v_map_u2082_572_);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_array_get_size(v_buckets_573_);
v___x_578_ = lean_nat_dec_lt(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_inc(v_toPure_574_);
lean_dec_ref(v_buckets_573_);
lean_dec(v_f_566_);
lean_dec_ref(v_inst_565_);
v___x_579_ = lean_apply_2(v_toPure_574_, lean_box(0), v_init_567_);
v___x_580_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_579_, v___f_575_);
return v___x_580_;
}
else
{
lean_object* v___f_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_inc_ref(v_inst_565_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_581_, 0, v_inst_565_);
lean_closure_set(v___f_581_, 1, v_f_566_);
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_577_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_565_, v___f_581_, v_buckets_573_, v___x_582_, v___x_583_, v_init_567_);
v___x_585_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_584_, v___f_575_);
return v___x_585_;
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
lean_object* v___f_648_; lean_object* v___f_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc(v_f_637_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_648_, 0, v_f_637_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_649_, 0, v___x_642_);
lean_closure_set(v___f_649_, 1, v___f_648_);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = lean_usize_of_nat(v___x_645_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_642_, v___f_649_, v_buckets_643_, v___x_650_, v___x_651_, v_init_638_);
v___x_653_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_641_, v_f_637_, v___x_652_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_00_u03c3_658_, lean_object* v_f_659_, lean_object* v_init_660_, lean_object* v_m_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_SMap_fold___redArg(v_f_659_, v_init_660_, v_m_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_663_, lean_object* v_00_u03b2_664_, lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_00_u03c3_667_, lean_object* v_f_668_, lean_object* v_init_669_, lean_object* v_m_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_SMap_fold(v_00_u03b1_663_, v_00_u03b2_664_, v_inst_665_, v_inst_666_, v_00_u03c3_667_, v_f_668_, v_init_669_, v_m_670_);
lean_dec_ref(v_inst_666_);
lean_dec_ref(v_inst_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_672_){
_start:
{
lean_object* v_map_u2081_673_; lean_object* v___x_674_; 
v_map_u2081_673_ = lean_ctor_get(v_m_672_, 0);
v___x_674_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_SMap_numBuckets___redArg(v_m_675_);
lean_dec_ref(v_m_675_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_m_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_SMap_numBuckets___redArg(v_m_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_m_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_SMap_numBuckets(v_00_u03b1_683_, v_00_u03b2_684_, v_inst_685_, v_inst_686_, v_m_687_);
lean_dec_ref(v_m_687_);
lean_dec_ref(v_inst_686_);
lean_dec_ref(v_inst_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_689_, lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_a_690_);
lean_ctor_set(v___x_692_, 1, v_b_691_);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v_es_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___f_696_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_697_ = lean_box(0);
v___x_698_ = l_Lean_SMap_fold___redArg(v___f_696_, v___x_697_, v_m_695_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_m_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_SMap_toList___redArg(v_m_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_m_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_SMap_toList(v_00_u03b1_705_, v_00_u03b2_706_, v_inst_707_, v_inst_708_, v_m_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_inst_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg___lam__0(lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_s_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_717_; 
v_fst_715_ = lean_ctor_get(v_x_714_, 0);
lean_inc(v_fst_715_);
v_snd_716_ = lean_ctor_get(v_x_714_, 1);
lean_inc(v_snd_716_);
lean_dec_ref(v_x_714_);
v___x_717_ = l_Lean_SMap_insert___redArg(v_inst_711_, v_inst_712_, v_s_713_, v_fst_715_, v_snd_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap___redArg(lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_es_720_){
_start:
{
lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___f_721_ = lean_alloc_closure((void*)(l_Lean_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_721_, 0, v_inst_718_);
lean_closure_set(v___f_721_, 1, v_inst_719_);
v___x_722_ = lean_obj_once(&l_Lean_SMap_instInhabited___redArg___closed__4, &l_Lean_SMap_instInhabited___redArg___closed__4_once, _init_l_Lean_SMap_instInhabited___redArg___closed__4);
v___x_723_ = l_List_foldl___redArg(v___f_721_, v___x_722_, v_es_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSMap(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_es_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_List_toSMap___redArg(v_inst_726_, v_inst_727_, v_es_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_733_, lean_object* v_v_734_, lean_object* v_prec_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_736_ = l_Lean_SMap_toList___redArg(v_v_734_);
v___x_737_ = l_List_repr___redArg(v___x_733_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Repr_addAppParen(v___x_739_, v_prec_735_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_741_, lean_object* v_v_742_, lean_object* v_prec_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_instReprSMap___redArg___lam__0(v___x_741_, v_v_742_, v_prec_743_);
lean_dec(v_prec_743_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_745_, lean_object* v_inst_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___f_749_; 
v___f_747_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_747_, 0, v_inst_746_);
v___x_748_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_748_, 0, lean_box(0));
lean_closure_set(v___x_748_, 1, lean_box(0));
lean_closure_set(v___x_748_, 2, v_inst_745_);
lean_closure_set(v___x_748_, 3, v___f_747_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_749_, 0, v___x_748_);
return v___f_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_inst_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_instReprSMap___redArg(v_inst_754_, v_inst_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_inst_761_, lean_object* v_inst_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_instReprSMap(v_00_u03b1_757_, v_00_u03b2_758_, v_x_759_, v_x_760_, v_inst_761_, v_inst_762_);
lean_dec_ref(v_x_760_);
lean_dec_ref(v_x_759_);
return v_res_763_;
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
