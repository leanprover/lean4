// Lean compiler output
// Module: Lean.Data.SMap
// Imports: public import Std.Data.HashMap.Basic public import Lean.Data.PersistentHashMap
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
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_179_ = lean_unsigned_to_nat(67u);
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
lean_dec(v_inst_185_);
v_val_191_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_val_191_);
lean_dec_ref(v___x_188_);
return v_val_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x21(lean_object* v_00_u03b1_192_, lean_object* v_00_u03b2_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_m_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_SMap_find_x3f___redArg(v_inst_194_, v_inst_195_, v_m_197_, v_a_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_obj_once(&l_Lean_SMap_find_x21___redArg___closed__3, &l_Lean_SMap_find_x21___redArg___closed__3_once, _init_l_Lean_SMap_find_x21___redArg___closed__3);
v___x_201_ = l_panic___redArg(v_inst_196_, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_val_202_; 
lean_dec(v_inst_196_);
v_val_202_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_202_);
lean_dec_ref(v___x_199_);
return v_val_202_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains___redArg(lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_stage_u2081_207_; 
v_stage_u2081_207_ = lean_ctor_get_uint8(v_x_205_, sizeof(void*)*2);
if (v_stage_u2081_207_ == 0)
{
lean_object* v_map_u2081_208_; lean_object* v_map_u2082_209_; uint8_t v___x_210_; 
v_map_u2081_208_ = lean_ctor_get(v_x_205_, 0);
lean_inc_ref(v_map_u2081_208_);
v_map_u2082_209_ = lean_ctor_get(v_x_205_, 1);
lean_inc_ref(v_map_u2082_209_);
lean_dec_ref(v_x_205_);
lean_inc(v_x_206_);
lean_inc_ref(v_inst_204_);
lean_inc_ref(v_inst_203_);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_203_, v_inst_204_, v_map_u2081_208_, v_x_206_);
lean_dec_ref(v_map_u2081_208_);
if (v___x_210_ == 0)
{
uint8_t v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_203_, v_inst_204_, v_map_u2082_209_, v_x_206_);
return v___x_211_;
}
else
{
lean_dec_ref(v_map_u2082_209_);
lean_dec(v_x_206_);
lean_dec_ref(v_inst_204_);
lean_dec_ref(v_inst_203_);
return v___x_210_;
}
}
else
{
lean_object* v_map_u2081_212_; uint8_t v___x_213_; 
v_map_u2081_212_ = lean_ctor_get(v_x_205_, 0);
lean_inc_ref(v_map_u2081_212_);
lean_dec_ref(v_x_205_);
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_203_, v_inst_204_, v_map_u2081_212_, v_x_206_);
lean_dec_ref(v_map_u2081_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___redArg___boxed(lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_SMap_contains___redArg(v_inst_214_, v_inst_215_, v_x_216_, v_x_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint8_t l_Lean_SMap_contains(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = l_Lean_SMap_contains___redArg(v_inst_222_, v_inst_223_, v_x_224_, v_x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_contains___boxed(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Lean_SMap_contains(v_00_u03b1_227_, v_00_u03b2_228_, v_inst_229_, v_inst_230_, v_x_231_, v_x_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint8_t v_stage_u2081_239_; 
v_stage_u2081_239_ = lean_ctor_get_uint8(v_x_237_, sizeof(void*)*2);
if (v_stage_u2081_239_ == 0)
{
lean_object* v_map_u2081_240_; lean_object* v_map_u2082_241_; lean_object* v___x_242_; 
v_map_u2081_240_ = lean_ctor_get(v_x_237_, 0);
lean_inc_ref(v_map_u2081_240_);
v_map_u2082_241_ = lean_ctor_get(v_x_237_, 1);
lean_inc_ref(v_map_u2082_241_);
lean_dec_ref(v_x_237_);
lean_inc(v_x_238_);
lean_inc_ref(v_inst_236_);
lean_inc_ref(v_inst_235_);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_235_, v_inst_236_, v_map_u2081_240_, v_x_238_);
lean_dec_ref(v_map_u2081_240_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_inst_235_, v_inst_236_, v_map_u2082_241_, v_x_238_);
return v___x_243_;
}
else
{
lean_dec_ref(v_map_u2082_241_);
lean_dec(v_x_238_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
return v___x_242_;
}
}
else
{
lean_object* v_map_u2081_244_; lean_object* v___x_245_; 
v_map_u2081_244_ = lean_ctor_get(v_x_237_, 0);
lean_inc_ref(v_map_u2081_244_);
lean_dec_ref(v_x_237_);
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_235_, v_inst_236_, v_map_u2081_244_, v_x_238_);
lean_dec_ref(v_map_u2081_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_SMap_find_x3f_x27___redArg(v_inst_248_, v_inst_249_, v_x_250_, v_x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__0(lean_object* v_inst_253_, lean_object* v_map_u2082_254_, lean_object* v_f_255_, lean_object* v_____r_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_253_, v_map_u2082_254_, v_f_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__1(lean_object* v_f_258_, lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_apply_2(v_f_258_, v___y_260_, v___y_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg___lam__2(lean_object* v_inst_263_, lean_object* v___f_264_, lean_object* v_x_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_box(0);
v___x_268_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_263_, v___f_264_, v___x_267_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___redArg(lean_object* v_inst_269_, lean_object* v_s_270_, lean_object* v_f_271_){
_start:
{
lean_object* v_map_u2081_272_; lean_object* v_toApplicative_273_; lean_object* v_toBind_274_; lean_object* v_map_u2082_275_; lean_object* v_buckets_276_; lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_map_u2081_272_ = lean_ctor_get(v_s_270_, 0);
lean_inc_ref(v_map_u2081_272_);
v_toApplicative_273_ = lean_ctor_get(v_inst_269_, 0);
v_toBind_274_ = lean_ctor_get(v_inst_269_, 1);
lean_inc(v_toBind_274_);
v_map_u2082_275_ = lean_ctor_get(v_s_270_, 1);
lean_inc_ref(v_map_u2082_275_);
lean_dec_ref(v_s_270_);
v_buckets_276_ = lean_ctor_get(v_map_u2081_272_, 1);
lean_inc_ref(v_buckets_276_);
lean_dec_ref(v_map_u2081_272_);
lean_inc(v_f_271_);
lean_inc_ref(v_inst_269_);
v___f_277_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_277_, 0, v_inst_269_);
lean_closure_set(v___f_277_, 1, v_map_u2082_275_);
lean_closure_set(v___f_277_, 2, v_f_271_);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_array_get_size(v_buckets_276_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_281_ == 0)
{
lean_object* v_toPure_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc_ref(v_toApplicative_273_);
lean_dec_ref(v_buckets_276_);
lean_dec(v_f_271_);
lean_dec_ref(v_inst_269_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_273_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_273_);
v___x_283_ = lean_apply_2(v_toPure_282_, lean_box(0), v___x_280_);
v___x_284_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_283_, v___f_277_);
return v___x_284_;
}
else
{
lean_object* v___f_285_; lean_object* v___f_286_; uint8_t v___x_287_; 
v___f_285_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__1), 4, 1);
lean_closure_set(v___f_285_, 0, v_f_271_);
lean_inc_ref(v_inst_269_);
v___f_286_ = lean_alloc_closure((void*)(l_Lean_SMap_forM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_286_, 0, v_inst_269_);
lean_closure_set(v___f_286_, 1, v___f_285_);
v___x_287_ = lean_nat_dec_le(v___x_279_, v___x_279_);
if (v___x_287_ == 0)
{
if (v___x_281_ == 0)
{
lean_object* v_toPure_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc_ref(v_toApplicative_273_);
lean_dec_ref(v___f_286_);
lean_dec_ref(v_buckets_276_);
lean_dec_ref(v_inst_269_);
v_toPure_288_ = lean_ctor_get(v_toApplicative_273_, 1);
lean_inc(v_toPure_288_);
lean_dec_ref(v_toApplicative_273_);
v___x_289_ = lean_apply_2(v_toPure_288_, lean_box(0), v___x_280_);
v___x_290_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_289_, v___f_277_);
return v___x_290_;
}
else
{
size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = ((size_t)0ULL);
v___x_292_ = lean_usize_of_nat(v___x_279_);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_269_, v___f_286_, v_buckets_276_, v___x_291_, v___x_292_, v___x_280_);
v___x_294_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_293_, v___f_277_);
return v___x_294_;
}
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_279_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_269_, v___f_286_, v_buckets_276_, v___x_295_, v___x_296_, v___x_280_);
v___x_298_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_297_, v___f_277_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM(lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_m_303_, lean_object* v_inst_304_, lean_object* v_s_305_, lean_object* v_f_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_SMap_forM___redArg(v_inst_304_, v_s_305_, v_f_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___boxed(lean_object* v_00_u03b1_308_, lean_object* v_00_u03b2_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_m_312_, lean_object* v_inst_313_, lean_object* v_s_314_, lean_object* v_f_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_SMap_forM(v_00_u03b1_308_, v_00_u03b2_309_, v_inst_310_, v_inst_311_, v_m_312_, v_inst_313_, v_s_314_, v_f_315_);
lean_dec_ref(v_inst_311_);
lean_dec_ref(v_inst_310_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_317_, lean_object* v_x_318_, lean_object* v_y_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_x_318_);
lean_ctor_set(v___x_320_, 1, v_y_319_);
v___x_321_ = lean_apply_1(v_f_317_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_322_, lean_object* v_s_323_, lean_object* v_f_324_){
_start:
{
lean_object* v___f_325_; lean_object* v___x_326_; 
v___f_325_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_325_, 0, v_f_324_);
v___x_326_ = l_Lean_SMap_forM___redArg(v_inst_322_, v_s_323_, v___f_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___redArg(lean_object* v_inst_327_){
_start:
{
lean_object* v___f_328_; 
v___f_328_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_328_, 0, v_inst_327_);
return v___f_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_m_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v___f_335_; 
v___f_335_ = lean_alloc_closure((void*)(l_Lean_SMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_335_, 0, v_inst_334_);
return v___f_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_m_340_, lean_object* v_inst_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_SMap_instForMProdOfMonad(v_00_u03b1_336_, v_00_u03b2_337_, v_inst_338_, v_inst_339_, v_m_340_, v_inst_341_);
lean_dec_ref(v_inst_339_);
lean_dec_ref(v_inst_338_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_toPure_343_, lean_object* v_____do__lift_344_){
_start:
{
if (lean_obj_tag(v_____do__lift_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_346_; 
v_a_345_ = lean_ctor_get(v_____do__lift_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v_____do__lift_344_);
v___x_346_ = lean_apply_2(v_toPure_343_, lean_box(0), v_a_345_);
return v___x_346_;
}
else
{
lean_object* v_a_347_; lean_object* v_snd_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v_____do__lift_344_, 0);
lean_inc(v_a_347_);
lean_dec_ref(v_____do__lift_344_);
v_snd_348_ = lean_ctor_get(v_a_347_, 1);
lean_inc(v_snd_348_);
lean_dec(v_a_347_);
v___x_349_ = lean_apply_2(v_toPure_343_, lean_box(0), v_snd_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_toPure_350_, lean_object* v_____do__lift_351_){
_start:
{
if (lean_obj_tag(v_____do__lift_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
v_a_352_ = lean_ctor_get(v_____do__lift_351_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v_____do__lift_351_);
if (v_isSharedCheck_360_ == 0)
{
v___x_354_ = v_____do__lift_351_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v_____do__lift_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_apply_2(v_toPure_350_, lean_box(0), v___x_357_);
return v___x_358_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_a_361_ = lean_ctor_get(v_____do__lift_351_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_____do__lift_351_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v_____do__lift_351_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v_____do__lift_351_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_box(0);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_370_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; 
v___x_369_ = lean_apply_2(v_toPure_350_, lean_box(0), v___x_368_);
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__2(lean_object* v___y_372_, lean_object* v_toBind_373_, lean_object* v___f_374_, lean_object* v_x_375_, lean_object* v_y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_x_375_);
lean_ctor_set(v___x_378_, 1, v_y_376_);
v___x_379_ = lean_apply_2(v___y_372_, v___x_378_, v___y_377_);
v___x_380_ = lean_apply_4(v_toBind_373_, lean_box(0), lean_box(0), v___x_379_, v___f_374_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg___lam__3(lean_object* v_inst_381_, lean_object* v_00_u03b2_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___f_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___f_398_; lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_toApplicative_406_; lean_object* v_toBind_407_; lean_object* v_toPure_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___x_140__overap_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_inc_ref(v_inst_381_);
v___f_386_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_386_, 0, v_inst_381_);
lean_inc_ref(v_inst_381_);
v___f_387_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_387_, 0, v_inst_381_);
lean_inc_ref(v_inst_381_);
v___f_388_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_388_, 0, v_inst_381_);
lean_inc_ref(v_inst_381_);
v___f_389_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_389_, 0, v_inst_381_);
lean_inc_ref(v_inst_381_);
v___x_390_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_390_, 0, lean_box(0));
lean_closure_set(v___x_390_, 1, lean_box(0));
lean_closure_set(v___x_390_, 2, v_inst_381_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___f_386_);
lean_inc_ref(v_inst_381_);
v___x_392_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_392_, 0, lean_box(0));
lean_closure_set(v___x_392_, 1, lean_box(0));
lean_closure_set(v___x_392_, 2, v_inst_381_);
v___x_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
lean_ctor_set(v___x_393_, 2, v___f_387_);
lean_ctor_set(v___x_393_, 3, v___f_388_);
lean_ctor_set(v___x_393_, 4, v___f_389_);
lean_inc_ref(v_inst_381_);
v___x_394_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_394_, 0, lean_box(0));
lean_closure_set(v___x_394_, 1, lean_box(0));
lean_closure_set(v___x_394_, 2, v_inst_381_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_inc_ref(v___x_395_);
v___f_396_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_396_, 0, v___x_395_);
lean_inc_ref(v___x_395_);
v___f_397_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_397_, 0, v___x_395_);
lean_inc_ref(v___x_395_);
v___f_398_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_398_, 0, v___x_395_);
lean_inc_ref(v___x_395_);
v___f_399_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_399_, 0, v___x_395_);
lean_inc_ref(v___x_395_);
v___x_400_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_400_, 0, lean_box(0));
lean_closure_set(v___x_400_, 1, lean_box(0));
lean_closure_set(v___x_400_, 2, v___x_395_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
lean_ctor_set(v___x_401_, 1, v___f_396_);
lean_inc_ref(v___x_395_);
v___x_402_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_402_, 0, lean_box(0));
lean_closure_set(v___x_402_, 1, lean_box(0));
lean_closure_set(v___x_402_, 2, v___x_395_);
v___x_403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v___f_397_);
lean_ctor_set(v___x_403_, 3, v___f_398_);
lean_ctor_set(v___x_403_, 4, v___f_399_);
v___x_404_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_404_, 0, lean_box(0));
lean_closure_set(v___x_404_, 1, lean_box(0));
lean_closure_set(v___x_404_, 2, v___x_395_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v_toApplicative_406_ = lean_ctor_get(v_inst_381_, 0);
lean_inc_ref(v_toApplicative_406_);
v_toBind_407_ = lean_ctor_get(v_inst_381_, 1);
lean_inc(v_toBind_407_);
lean_dec_ref(v_inst_381_);
v_toPure_408_ = lean_ctor_get(v_toApplicative_406_, 1);
lean_inc(v_toPure_408_);
lean_dec_ref(v_toApplicative_406_);
lean_inc(v_toPure_408_);
v___f_409_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_409_, 0, v_toPure_408_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_410_, 0, v_toPure_408_);
lean_inc(v_toBind_407_);
v___f_411_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_411_, 0, v___y_385_);
lean_closure_set(v___f_411_, 1, v_toBind_407_);
lean_closure_set(v___f_411_, 2, v___f_410_);
v___x_140__overap_412_ = l_Lean_SMap_forM___redArg(v___x_405_, v___y_383_, v___f_411_);
v___x_413_ = lean_apply_1(v___x_140__overap_412_, v___y_384_);
v___x_414_ = lean_apply_4(v_toBind_407_, lean_box(0), lean_box(0), v___x_413_, v___f_409_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___redArg(lean_object* v_inst_415_){
_start:
{
lean_object* v___f_416_; 
v___f_416_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_416_, 0, v_inst_415_);
return v___f_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad(lean_object* v_00_u03b1_417_, lean_object* v_00_u03b2_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_m_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v___f_423_; 
v___f_423_ = lean_alloc_closure((void*)(l_Lean_SMap_instForInProdOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_423_, 0, v_inst_422_);
return v___f_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_SMap_instForInProdOfMonad(v_00_u03b1_424_, v_00_u03b2_425_, v_inst_426_, v_inst_427_, v_m_428_, v_inst_429_);
lean_dec_ref(v_inst_427_);
lean_dec_ref(v_inst_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___redArg(lean_object* v_m_431_){
_start:
{
uint8_t v_stage_u2081_432_; 
v_stage_u2081_432_ = lean_ctor_get_uint8(v_m_431_, sizeof(void*)*2);
if (v_stage_u2081_432_ == 0)
{
return v_m_431_;
}
else
{
lean_object* v_map_u2081_433_; lean_object* v_map_u2082_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
v_map_u2081_433_ = lean_ctor_get(v_m_431_, 0);
v_map_u2082_434_ = lean_ctor_get(v_m_431_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_m_431_);
if (v_isSharedCheck_442_ == 0)
{
v___x_436_ = v_m_431_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_map_u2082_434_);
lean_inc(v_map_u2081_433_);
lean_dec(v_m_431_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
uint8_t v___x_438_; lean_object* v___x_440_; 
v___x_438_ = 0;
if (v_isShared_437_ == 0)
{
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_map_u2081_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_map_u2082_434_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*2, v___x_438_);
return v___x_440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch(lean_object* v_00_u03b1_443_, lean_object* v_00_u03b2_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_m_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_SMap_switch___redArg(v_m_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___boxed(lean_object* v_00_u03b1_449_, lean_object* v_00_u03b2_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_m_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_SMap_switch(v_00_u03b1_449_, v_00_u03b2_450_, v_inst_451_, v_inst_452_, v_m_453_);
lean_dec_ref(v_inst_452_);
lean_dec_ref(v_inst_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___redArg(lean_object* v_f_455_, lean_object* v_s_456_, lean_object* v_m_457_){
_start:
{
lean_object* v_map_u2082_458_; lean_object* v___x_459_; 
v_map_u2082_458_ = lean_ctor_get(v_m_457_, 1);
lean_inc_ref(v_map_u2082_458_);
lean_dec_ref(v_m_457_);
v___x_459_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_458_, v_f_455_, v_s_456_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2(lean_object* v_00_u03b1_460_, lean_object* v_00_u03b2_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_00_u03c3_464_, lean_object* v_f_465_, lean_object* v_s_466_, lean_object* v_m_467_){
_start:
{
lean_object* v_map_u2082_468_; lean_object* v___x_469_; 
v_map_u2082_468_ = lean_ctor_get(v_m_467_, 1);
lean_inc_ref(v_map_u2082_468_);
lean_dec_ref(v_m_467_);
v___x_469_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_468_, v_f_465_, v_s_466_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_00_u03c3_474_, lean_object* v_f_475_, lean_object* v_s_476_, lean_object* v_m_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_SMap_foldStage2(v_00_u03b1_470_, v_00_u03b2_471_, v_inst_472_, v_inst_473_, v_00_u03c3_474_, v_f_475_, v_s_476_, v_m_477_);
lean_dec_ref(v_inst_473_);
lean_dec_ref(v_inst_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__0(lean_object* v_inst_479_, lean_object* v_f_480_, lean_object* v_map_u2082_481_, lean_object* v_____do__lift_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_479_, v_f_480_, v_map_u2082_481_, v_____do__lift_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg___lam__1(lean_object* v_inst_484_, lean_object* v_f_485_, lean_object* v_acc_486_, lean_object* v_l_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_484_, v_f_485_, v_acc_486_, v_l_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___redArg(lean_object* v_inst_489_, lean_object* v_f_490_, lean_object* v_init_491_, lean_object* v_map_492_){
_start:
{
lean_object* v_map_u2081_493_; lean_object* v_toApplicative_494_; lean_object* v_toBind_495_; lean_object* v_map_u2082_496_; lean_object* v_buckets_497_; lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_map_u2081_493_ = lean_ctor_get(v_map_492_, 0);
lean_inc_ref(v_map_u2081_493_);
v_toApplicative_494_ = lean_ctor_get(v_inst_489_, 0);
v_toBind_495_ = lean_ctor_get(v_inst_489_, 1);
lean_inc(v_toBind_495_);
v_map_u2082_496_ = lean_ctor_get(v_map_492_, 1);
lean_inc_ref(v_map_u2082_496_);
lean_dec_ref(v_map_492_);
v_buckets_497_ = lean_ctor_get(v_map_u2081_493_, 1);
lean_inc_ref(v_buckets_497_);
lean_dec_ref(v_map_u2081_493_);
lean_inc(v_f_490_);
lean_inc_ref(v_inst_489_);
v___f_498_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_498_, 0, v_inst_489_);
lean_closure_set(v___f_498_, 1, v_f_490_);
lean_closure_set(v___f_498_, 2, v_map_u2082_496_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_array_get_size(v_buckets_497_);
v___x_501_ = lean_nat_dec_lt(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v_toPure_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc_ref(v_toApplicative_494_);
lean_dec_ref(v_buckets_497_);
lean_dec(v_f_490_);
lean_dec_ref(v_inst_489_);
v_toPure_502_ = lean_ctor_get(v_toApplicative_494_, 1);
lean_inc(v_toPure_502_);
lean_dec_ref(v_toApplicative_494_);
v___x_503_ = lean_apply_2(v_toPure_502_, lean_box(0), v_init_491_);
v___x_504_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v___x_503_, v___f_498_);
return v___x_504_;
}
else
{
lean_object* v___f_505_; uint8_t v___x_506_; 
lean_inc_ref(v_inst_489_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_SMap_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_505_, 0, v_inst_489_);
lean_closure_set(v___f_505_, 1, v_f_490_);
v___x_506_ = lean_nat_dec_le(v___x_500_, v___x_500_);
if (v___x_506_ == 0)
{
if (v___x_501_ == 0)
{
lean_object* v_toPure_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_inc_ref(v_toApplicative_494_);
lean_dec_ref(v___f_505_);
lean_dec_ref(v_buckets_497_);
lean_dec_ref(v_inst_489_);
v_toPure_507_ = lean_ctor_get(v_toApplicative_494_, 1);
lean_inc(v_toPure_507_);
lean_dec_ref(v_toApplicative_494_);
v___x_508_ = lean_apply_2(v_toPure_507_, lean_box(0), v_init_491_);
v___x_509_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v___x_508_, v___f_498_);
return v___x_509_;
}
else
{
size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = ((size_t)0ULL);
v___x_511_ = lean_usize_of_nat(v___x_500_);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_489_, v___f_505_, v_buckets_497_, v___x_510_, v___x_511_, v_init_491_);
v___x_513_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v___x_512_, v___f_498_);
return v___x_513_;
}
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_514_ = ((size_t)0ULL);
v___x_515_ = lean_usize_of_nat(v___x_500_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_489_, v___f_505_, v_buckets_497_, v___x_514_, v___x_515_, v_init_491_);
v___x_517_ = lean_apply_4(v_toBind_495_, lean_box(0), lean_box(0), v___x_516_, v___f_498_);
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_00_u03c3_522_, lean_object* v_m_523_, lean_object* v_inst_524_, lean_object* v_f_525_, lean_object* v_init_526_, lean_object* v_map_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_SMap_foldM___redArg(v_inst_524_, v_f_525_, v_init_526_, v_map_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_foldM___boxed(lean_object* v_00_u03b1_529_, lean_object* v_00_u03b2_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_00_u03c3_533_, lean_object* v_m_534_, lean_object* v_inst_535_, lean_object* v_f_536_, lean_object* v_init_537_, lean_object* v_map_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_SMap_foldM(v_00_u03b1_529_, v_00_u03b2_530_, v_inst_531_, v_inst_532_, v_00_u03c3_533_, v_m_534_, v_inst_535_, v_f_536_, v_init_537_, v_map_538_);
lean_dec_ref(v_inst_532_);
lean_dec_ref(v_inst_531_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__0(lean_object* v_f_540_, lean_object* v_x1_541_, lean_object* v_x2_542_, lean_object* v_x3_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = lean_apply_3(v_f_540_, v_x1_541_, v_x2_542_, v_x3_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg___lam__1(lean_object* v___x_545_, lean_object* v___f_546_, lean_object* v_acc_547_, lean_object* v_l_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_545_, v___f_546_, v_acc_547_, v_l_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___redArg(lean_object* v_f_569_, lean_object* v_init_570_, lean_object* v_m_571_){
_start:
{
lean_object* v_map_u2081_572_; lean_object* v_map_u2082_573_; lean_object* v___x_574_; lean_object* v_buckets_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_map_u2081_572_ = lean_ctor_get(v_m_571_, 0);
lean_inc_ref(v_map_u2081_572_);
v_map_u2082_573_ = lean_ctor_get(v_m_571_, 1);
lean_inc_ref(v_map_u2082_573_);
lean_dec_ref(v_m_571_);
v___x_574_ = ((lean_object*)(l_Lean_SMap_fold___redArg___closed__9));
v_buckets_575_ = lean_ctor_get(v_map_u2081_572_, 1);
lean_inc_ref(v_buckets_575_);
lean_dec_ref(v_map_u2081_572_);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_array_get_size(v_buckets_575_);
v___x_578_ = lean_nat_dec_lt(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec_ref(v_buckets_575_);
v___x_579_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_573_, v_f_569_, v_init_570_);
return v___x_579_;
}
else
{
lean_object* v___f_580_; lean_object* v___f_581_; uint8_t v___x_582_; 
lean_inc(v_f_569_);
v___f_580_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_580_, 0, v_f_569_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_SMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_581_, 0, v___x_574_);
lean_closure_set(v___f_581_, 1, v___f_580_);
v___x_582_ = lean_nat_dec_le(v___x_577_, v___x_577_);
if (v___x_582_ == 0)
{
if (v___x_578_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v___f_581_);
lean_dec_ref(v_buckets_575_);
v___x_583_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_573_, v_f_569_, v_init_570_);
return v___x_583_;
}
else
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = ((size_t)0ULL);
v___x_585_ = lean_usize_of_nat(v___x_577_);
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_574_, v___f_581_, v_buckets_575_, v___x_584_, v___x_585_, v_init_570_);
v___x_587_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_573_, v_f_569_, v___x_586_);
return v___x_587_;
}
}
else
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = ((size_t)0ULL);
v___x_589_ = lean_usize_of_nat(v___x_577_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_574_, v___f_581_, v_buckets_575_, v___x_588_, v___x_589_, v_init_570_);
v___x_591_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_573_, v_f_569_, v___x_590_);
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_00_u03c3_596_, lean_object* v_f_597_, lean_object* v_init_598_, lean_object* v_m_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_SMap_fold___redArg(v_f_597_, v_init_598_, v_m_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___boxed(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_00_u03c3_605_, lean_object* v_f_606_, lean_object* v_init_607_, lean_object* v_m_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_SMap_fold(v_00_u03b1_601_, v_00_u03b2_602_, v_inst_603_, v_inst_604_, v_00_u03c3_605_, v_f_606_, v_init_607_, v_m_608_);
lean_dec_ref(v_inst_604_);
lean_dec_ref(v_inst_603_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg(lean_object* v_m_610_){
_start:
{
lean_object* v_map_u2081_611_; lean_object* v___x_612_; 
v_map_u2081_611_ = lean_ctor_get(v_m_610_, 0);
v___x_612_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_map_u2081_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___redArg___boxed(lean_object* v_m_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_SMap_numBuckets___redArg(v_m_613_);
lean_dec_ref(v_m_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_m_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_SMap_numBuckets___redArg(v_m_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_m_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_SMap_numBuckets(v_00_u03b1_621_, v_00_u03b2_622_, v_inst_623_, v_inst_624_, v_m_625_);
lean_dec_ref(v_m_625_);
lean_dec_ref(v_inst_624_);
lean_dec_ref(v_inst_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg___lam__0(lean_object* v_es_627_, lean_object* v_a_628_, lean_object* v_b_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_a_628_);
lean_ctor_set(v___x_630_, 1, v_b_629_);
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_es_627_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___redArg(lean_object* v_m_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___f_634_ = ((lean_object*)(l_Lean_SMap_toList___redArg___closed__0));
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_SMap_fold___redArg(v___f_634_, v___x_635_, v_m_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_m_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_SMap_toList___redArg(v_m_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___boxed(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_m_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_SMap_toList(v_00_u03b1_643_, v_00_u03b2_644_, v_inst_645_, v_inst_646_, v_m_647_);
lean_dec_ref(v_inst_646_);
lean_dec_ref(v_inst_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap___redArg___lam__0(lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_s_651_, lean_object* v_x_652_){
_start:
{
lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; 
v_fst_653_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_snd_654_);
lean_dec_ref(v_x_652_);
v___x_655_ = l_Lean_SMap_insert___redArg(v_inst_649_, v_inst_650_, v_s_651_, v_fst_653_, v_snd_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap___redArg(lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_es_658_){
_start:
{
lean_object* v___f_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___f_659_ = lean_alloc_closure((void*)(l_List_toSMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_659_, 0, v_inst_656_);
lean_closure_set(v___f_659_, 1, v_inst_657_);
v___x_660_ = lean_obj_once(&l_Lean_SMap_instInhabited___closed__4, &l_Lean_SMap_instInhabited___closed__4_once, _init_l_Lean_SMap_instInhabited___closed__4);
v___x_661_ = l_List_foldl___redArg(v___f_659_, v___x_660_, v_es_658_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_List_toSMap(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_es_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_List_toSMap___redArg(v_inst_664_, v_inst_665_, v_es_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0(lean_object* v___x_671_, lean_object* v_v_672_, lean_object* v_prec_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_674_ = l_Lean_SMap_toList___redArg(v_v_672_);
v___x_675_ = l_List_repr___redArg(v___x_671_, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_instReprSMap___redArg___lam__0___closed__1));
v___x_677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Repr_addAppParen(v___x_677_, v_prec_673_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg___lam__0___boxed(lean_object* v___x_679_, lean_object* v_v_680_, lean_object* v_prec_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_instReprSMap___redArg___lam__0(v___x_679_, v_v_680_, v_prec_681_);
lean_dec(v_prec_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___redArg(lean_object* v_inst_683_, lean_object* v_inst_684_){
_start:
{
lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___f_687_; 
v___f_685_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_685_, 0, v_inst_684_);
v___x_686_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_686_, 0, lean_box(0));
lean_closure_set(v___x_686_, 1, lean_box(0));
lean_closure_set(v___x_686_, 2, v_inst_683_);
lean_closure_set(v___x_686_, 3, v___f_685_);
v___f_687_ = lean_alloc_closure((void*)(l_Lean_instReprSMap___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_687_, 0, v___x_686_);
return v___f_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_inst_692_, lean_object* v_inst_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_instReprSMap___redArg(v_inst_692_, v_inst_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSMap___boxed(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_inst_699_, lean_object* v_inst_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_instReprSMap(v_00_u03b1_695_, v_00_u03b2_696_, v_x_697_, v_x_698_, v_inst_699_, v_inst_700_);
lean_dec_ref(v_x_698_);
lean_dec_ref(v_x_697_);
return v_res_701_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
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
