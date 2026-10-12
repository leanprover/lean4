// Lean compiler output
// Module: Init.Data.List.Impl
// Imports: public import Init.Ext import Init.Data.Array.Bootstrap import Init.Data.Bool import Init.Data.List.Lemmas import Init.Data.Option.Lemmas
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_setTR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_setTR___redArg___closed__0 = (const lean_object*)&l_List_setTR___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_setTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_setTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_reduceOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_reduceOption___redArg___closed__0 = (const lean_object*)&l_List_reduceOption___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_reduceOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_foldrTR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__0 = (const lean_object*)&l_List_foldrTR___redArg___closed__0_value;
static const lean_closure_object l_List_foldrTR___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__1 = (const lean_object*)&l_List_foldrTR___redArg___closed__1_value;
static const lean_closure_object l_List_foldrTR___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__2 = (const lean_object*)&l_List_foldrTR___redArg___closed__2_value;
static const lean_closure_object l_List_foldrTR___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__3 = (const lean_object*)&l_List_foldrTR___redArg___closed__3_value;
static const lean_closure_object l_List_foldrTR___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__4 = (const lean_object*)&l_List_foldrTR___redArg___closed__4_value;
static const lean_closure_object l_List_foldrTR___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__5 = (const lean_object*)&l_List_foldrTR___redArg___closed__5_value;
static const lean_closure_object l_List_foldrTR___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_foldrTR___redArg___closed__6 = (const lean_object*)&l_List_foldrTR___redArg___closed__6_value;
static const lean_ctor_object l_List_foldrTR___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_foldrTR___redArg___closed__0_value),((lean_object*)&l_List_foldrTR___redArg___closed__1_value)}};
static const lean_object* l_List_foldrTR___redArg___closed__7 = (const lean_object*)&l_List_foldrTR___redArg___closed__7_value;
static const lean_ctor_object l_List_foldrTR___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_foldrTR___redArg___closed__7_value),((lean_object*)&l_List_foldrTR___redArg___closed__2_value),((lean_object*)&l_List_foldrTR___redArg___closed__3_value),((lean_object*)&l_List_foldrTR___redArg___closed__4_value),((lean_object*)&l_List_foldrTR___redArg___closed__5_value)}};
static const lean_object* l_List_foldrTR___redArg___closed__8 = (const lean_object*)&l_List_foldrTR___redArg___closed__8_value;
static const lean_ctor_object l_List_foldrTR___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_foldrTR___redArg___closed__8_value),((lean_object*)&l_List_foldrTR___redArg___closed__6_value)}};
static const lean_object* l_List_foldrTR___redArg___closed__9 = (const lean_object*)&l_List_foldrTR___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_flattenTR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_flattenTR___redArg___closed__0 = (const lean_object*)&l_List_flattenTR___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_flattenTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_flattenTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_dropLastTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_dropLastTR(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_5_ == 0)
{
size_t v___x_6_; size_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_6_ = ((size_t)1ULL);
v___x_7_ = lean_usize_sub(v_i_2_, v___x_6_);
v___x_8_ = lean_array_uget_borrowed(v_as_1_, v___x_7_);
lean_inc(v___x_8_);
v___x_9_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v_b_4_);
v_i_2_ = v___x_7_;
v_b_4_ = v___x_9_;
goto _start;
}
else
{
return v_b_4_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_11_;
v_res_11_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_1_, v_i_2_, v_stop_3_, v_b_4_);
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg___boxed(lean_object* v_as_12_, lean_object* v_i_13_, lean_object* v_stop_14_, lean_object* v_b_15_){
_start:
{
size_t v_i_boxed_16_; size_t v_stop_boxed_17_; lean_object* v_res_18_; 
v_i_boxed_16_ = lean_unbox_usize(v_i_13_);
lean_dec(v_i_13_);
v_stop_boxed_17_ = lean_unbox_usize(v_stop_14_);
lean_dec(v_stop_14_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_12_, v_i_boxed_16_, v_stop_boxed_17_, v_b_15_);
lean_dec_ref(v_as_12_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(lean_object* v_l_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
if (lean_obj_tag(v_a_21_) == 0)
{
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec(v_a_20_);
lean_inc(v_l_19_);
return v_l_19_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_43_; 
v_head_24_ = lean_ctor_get(v_a_21_, 0);
v_tail_25_ = lean_ctor_get(v_a_21_, 1);
v_isSharedCheck_43_ = !lean_is_exclusive(v_a_21_);
if (v_isSharedCheck_43_ == 0)
{
v___x_27_ = v_a_21_;
v_isShared_28_ = v_isSharedCheck_43_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_tail_25_);
lean_inc(v_head_24_);
lean_dec(v_a_21_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_43_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_zero_29_; uint8_t v_isZero_30_; 
v_zero_29_ = lean_unsigned_to_nat(0u);
v_isZero_30_ = lean_nat_dec_eq(v_a_22_, v_zero_29_);
if (v_isZero_30_ == 1)
{
lean_object* v___x_32_; 
lean_dec(v_head_24_);
lean_dec(v_a_22_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v_a_20_);
v___x_32_ = v___x_27_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_20_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_tail_25_);
v___x_32_ = v_reuseFailAlloc_38_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_33_ = lean_array_get_size(v_a_23_);
v___x_34_ = lean_nat_dec_lt(v_zero_29_, v___x_33_);
if (v___x_34_ == 0)
{
lean_dec_ref(v_a_23_);
return v___x_32_;
}
else
{
size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = lean_usize_of_nat(v___x_33_);
v___x_36_ = ((size_t)0ULL);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_23_, v___x_35_, v___x_36_, v___x_32_);
lean_dec_ref(v_a_23_);
return v___x_37_;
}
}
}
else
{
lean_object* v_one_39_; lean_object* v_n_40_; lean_object* v___x_41_; 
lean_del_object(v___x_27_);
v_one_39_ = lean_unsigned_to_nat(1u);
v_n_40_ = lean_nat_sub(v_a_22_, v_one_39_);
lean_dec(v_a_22_);
v___x_41_ = lean_array_push(v_a_23_, v_head_24_);
v_a_21_ = v_tail_25_;
v_a_22_ = v_n_40_;
v_a_23_ = v___x_41_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg___boxed(lean_object* v_l_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
lean_dec(v_l_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go(lean_object* v_00_u03b1_50_, lean_object* v_l_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___boxed(lean_object* v_00_u03b1_57_, lean_object* v_l_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Init_Data_List_Impl_0__List_setTR_go(v_00_u03b1_57_, v_l_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_l_58_);
return v_res_63_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(lean_object* v_00_u03b1_64_, lean_object* v_as_65_, size_t v_i_66_, size_t v_stop_67_, lean_object* v_b_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_65_, v_i_66_, v_stop_67_, v_b_68_);
return v___x_69_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_65_ = stack[1].m_obj;
size_t v_i_66_ = stack[2].m_num;
size_t v_stop_67_ = stack[3].m_num;
lean_object* v_b_68_ = stack[4].m_obj;
lean_object* v_res_70_;
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(lean_box(0), v_as_65_, v_i_66_, v_stop_67_, v_b_68_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___boxed(lean_object* v_00_u03b1_71_, lean_object* v_as_72_, lean_object* v_i_73_, lean_object* v_stop_74_, lean_object* v_b_75_){
_start:
{
size_t v_i_boxed_76_; size_t v_stop_boxed_77_; lean_object* v_res_78_; 
v_i_boxed_76_ = lean_unbox_usize(v_i_73_);
lean_dec(v_i_73_);
v_stop_boxed_77_ = lean_unbox_usize(v_stop_74_);
lean_dec(v_stop_74_);
v_res_78_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(v_00_u03b1_71_, v_as_72_, v_i_boxed_76_, v_stop_boxed_77_, v_b_75_);
lean_dec_ref(v_as_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_List_setTR___redArg(lean_object* v_l_81_, lean_object* v_n_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_81_);
v___x_85_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_81_, v_a_83_, v_l_81_, v_n_82_, v___x_84_);
lean_dec(v_l_81_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_List_setTR(lean_object* v_00_u03b1_86_, lean_object* v_l_87_, lean_object* v_n_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_87_);
v___x_91_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_87_, v_a_89_, v_l_87_, v_n_88_, v___x_90_);
lean_dec(v_l_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___redArg(lean_object* v_f_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
if (lean_obj_tag(v_a_93_) == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v_f_92_);
v___x_95_ = lean_array_to_list(v_a_94_);
return v___x_95_;
}
else
{
lean_object* v_head_96_; lean_object* v_tail_97_; lean_object* v___x_98_; 
v_head_96_ = lean_ctor_get(v_a_93_, 0);
lean_inc(v_head_96_);
v_tail_97_ = lean_ctor_get(v_a_93_, 1);
lean_inc(v_tail_97_);
lean_dec_ref_known(v_a_93_, 2);
lean_inc_ref(v_f_92_);
v___x_98_ = lean_apply_1(v_f_92_, v_head_96_);
if (lean_obj_tag(v___x_98_) == 0)
{
v_a_93_ = v_tail_97_;
goto _start;
}
else
{
lean_object* v_val_100_; lean_object* v___x_101_; 
v_val_100_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_val_100_);
lean_dec_ref_known(v___x_98_, 1);
v___x_101_ = lean_array_push(v_a_94_, v_val_100_);
v_a_93_ = v_tail_97_;
v_a_94_ = v___x_101_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_f_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_List_filterMapTR_go___redArg(v_f_105_, v_a_106_, v_a_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR___redArg(lean_object* v_f_109_, lean_object* v_l_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_112_ = l_List_filterMapTR_go___redArg(v_f_109_, v_l_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_f_115_, lean_object* v_l_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_118_ = l_List_filterMapTR_go___redArg(v_f_115_, v_l_116_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(lean_object* v_x_119_, lean_object* v_h__1_120_, lean_object* v_h__2_121_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_h__2_121_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_apply_1(v_h__1_120_, v___x_122_);
return v___x_123_;
}
else
{
lean_object* v_val_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_120_);
v_val_124_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v_x_119_, 1);
v___x_125_ = lean_apply_1(v_h__2_121_, v_val_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(lean_object* v_00_u03b2_126_, lean_object* v_motive_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_130_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_apply_1(v_h__1_129_, v___x_131_);
return v___x_132_;
}
else
{
lean_object* v_val_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_129_);
v_val_133_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v_x_128_, 1);
v___x_134_ = lean_apply_1(v_h__2_130_, v_val_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__2_137_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__1_136_, v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_val_140_; lean_object* v___x_141_; 
lean_dec(v_h__1_136_);
v_val_140_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_val_140_);
lean_dec_ref_known(v_x_135_, 1);
v___x_141_ = lean_apply_1(v_h__2_137_, v_val_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_142_, lean_object* v_motive_143_, lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__2_146_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__1_145_, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_145_);
v_val_149_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v_x_144_, 1);
v___x_150_ = lean_apply_1(v_h__2_146_, v_val_149_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_List_reduceOption___redArg(lean_object* v_a_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_154_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_155_ = l_List_filterMapTR_go___redArg(v___x_153_, v_a_152_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object* v_00_u03b1_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_159_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_160_ = l_List_filterMapTR_go___redArg(v___x_158_, v_a_157_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg___lam__0(lean_object* v_f_161_, lean_object* v_x1_162_, lean_object* v_x2_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_apply_2(v_f_161_, v_x1_162_, v_x2_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg(lean_object* v_f_184_, lean_object* v_init_185_, lean_object* v_l_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_187_ = lean_array_mk(v_l_186_);
v___x_188_ = lean_array_get_size(v___x_187_);
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_191_ = lean_nat_dec_lt(v___x_189_, v___x_188_);
if (v___x_191_ == 0)
{
lean_dec_ref(v___x_187_);
lean_dec(v_f_184_);
return v_init_185_;
}
else
{
lean_object* v___f_192_; size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; 
v___f_192_ = lean_alloc_closure((void*)(l_List_foldrTR___redArg___lam__0), 3, 1);
lean_closure_set(v___f_192_, 0, v_f_184_);
v___x_193_ = lean_usize_of_nat(v___x_188_);
v___x_194_ = ((size_t)0ULL);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_190_, v___f_192_, v___x_187_, v___x_193_, v___x_194_, v_init_185_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_f_198_, lean_object* v_init_199_, lean_object* v_l_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_List_foldrTR___redArg(v_f_198_, v_init_199_, v_l_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object* v_f_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
if (lean_obj_tag(v_a_203_) == 0)
{
lean_object* v___x_205_; 
lean_dec_ref(v_f_202_);
v___x_205_ = lean_array_to_list(v_a_204_);
return v___x_205_;
}
else
{
lean_object* v_head_206_; lean_object* v_tail_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_head_206_ = lean_ctor_get(v_a_203_, 0);
lean_inc(v_head_206_);
v_tail_207_ = lean_ctor_get(v_a_203_, 1);
lean_inc(v_tail_207_);
lean_dec_ref_known(v_a_203_, 2);
lean_inc_ref(v_f_202_);
v___x_208_ = lean_apply_1(v_f_202_, v_head_206_);
v___x_209_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_204_, v___x_208_);
v_a_203_ = v_tail_207_;
v_a_204_ = v___x_209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_f_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_213_, v_a_214_, v_a_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR___redArg(lean_object* v_f_217_, lean_object* v_as_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_220_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_217_, v_as_218_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_f_223_, lean_object* v_as_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_226_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_223_, v_as_224_, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR___redArg(lean_object* v_l_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_230_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_231_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_229_, v_l_228_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR(lean_object* v_00_u03b1_232_, lean_object* v_l_233_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_235_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_236_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_234_, v_l_233_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object* v_l_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
if (lean_obj_tag(v_a_238_) == 0)
{
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_inc(v_l_237_);
return v_l_237_;
}
else
{
lean_object* v_head_241_; lean_object* v_tail_242_; lean_object* v_zero_243_; uint8_t v_isZero_244_; 
v_head_241_ = lean_ctor_get(v_a_238_, 0);
lean_inc(v_head_241_);
v_tail_242_ = lean_ctor_get(v_a_238_, 1);
lean_inc(v_tail_242_);
lean_dec_ref_known(v_a_238_, 2);
v_zero_243_ = lean_unsigned_to_nat(0u);
v_isZero_244_ = lean_nat_dec_eq(v_a_239_, v_zero_243_);
if (v_isZero_244_ == 1)
{
lean_object* v___x_245_; 
lean_dec(v_tail_242_);
lean_dec(v_head_241_);
lean_dec(v_a_239_);
v___x_245_ = lean_array_to_list(v_a_240_);
return v___x_245_;
}
else
{
lean_object* v_one_246_; lean_object* v_n_247_; lean_object* v___x_248_; 
v_one_246_ = lean_unsigned_to_nat(1u);
v_n_247_ = lean_nat_sub(v_a_239_, v_one_246_);
lean_dec(v_a_239_);
v___x_248_ = lean_array_push(v_a_240_, v_head_241_);
v_a_238_ = v_tail_242_;
v_a_239_ = v_n_247_;
v_a_240_ = v___x_248_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(lean_object* v_l_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_l_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object* v_00_u03b1_255_, lean_object* v_l_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_256_, v_a_257_, v_a_258_, v_a_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(lean_object* v_00_u03b1_261_, lean_object* v_l_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(v_00_u03b1_261_, v_l_262_, v_a_263_, v_a_264_, v_a_265_);
lean_dec(v_l_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR___redArg(lean_object* v_n_267_, lean_object* v_l_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_268_);
v___x_270_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_268_, v_l_268_, v_n_267_, v___x_269_);
lean_dec(v_l_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR(lean_object* v_00_u03b1_271_, lean_object* v_n_272_, lean_object* v_l_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_273_);
v___x_275_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_273_, v_l_273_, v_n_272_, v___x_274_);
lean_dec(v_l_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object* v_p_276_, lean_object* v_l_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
if (lean_obj_tag(v_a_278_) == 0)
{
lean_dec_ref(v_a_279_);
lean_dec_ref(v_p_276_);
lean_inc(v_l_277_);
return v_l_277_;
}
else
{
lean_object* v_head_280_; lean_object* v_tail_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_head_280_ = lean_ctor_get(v_a_278_, 0);
lean_inc_n(v_head_280_, 2);
v_tail_281_ = lean_ctor_get(v_a_278_, 1);
lean_inc(v_tail_281_);
lean_dec_ref_known(v_a_278_, 2);
lean_inc_ref(v_p_276_);
v___x_282_ = lean_apply_1(v_p_276_, v_head_280_);
v___x_283_ = lean_unbox(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_tail_281_);
lean_dec(v_head_280_);
lean_dec_ref(v_p_276_);
v___x_284_ = lean_array_to_list(v_a_279_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_array_push(v_a_279_, v_head_280_);
v_a_278_ = v_tail_281_;
v_a_279_ = v___x_285_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object* v_p_287_, lean_object* v_l_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_287_, v_l_288_, v_a_289_, v_a_290_);
lean_dec(v_l_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object* v_00_u03b1_292_, lean_object* v_p_293_, lean_object* v_l_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_293_, v_l_294_, v_a_295_, v_a_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object* v_00_u03b1_298_, lean_object* v_p_299_, lean_object* v_l_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(v_00_u03b1_298_, v_p_299_, v_l_300_, v_a_301_, v_a_302_);
lean_dec(v_l_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object* v_p_304_, lean_object* v_l_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_305_);
v___x_307_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_304_, v_l_305_, v_l_305_, v___x_306_);
lean_dec(v_l_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object* v_00_u03b1_308_, lean_object* v_p_309_, lean_object* v_l_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_310_);
v___x_312_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_309_, v_l_310_, v_l_310_, v___x_311_);
lean_dec(v_l_310_);
return v___x_312_;
}
}
lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (v_x_313_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_h__1_314_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v_h__2_315_, v___x_316_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_h__2_315_);
v___x_318_ = lean_box(0);
v___x_319_ = lean_apply_1(v_h__1_314_, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_313_ = stack[0].m_num;
lean_object* v_h__1_314_ = stack[1].m_obj;
lean_object* v_h__2_315_ = stack[2].m_obj;
lean_object* v_res_320_;
v_res_320_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_313_, v_h__1_314_, v_h__2_315_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_){
_start:
{
uint8_t v_x_24__boxed_324_; lean_object* v_res_325_; 
v_x_24__boxed_324_ = lean_unbox(v_x_321_);
v_res_325_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_324_, v_h__1_322_, v_h__2_323_);
return v_res_325_;
}
}
lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object* v_motive_326_, uint8_t v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (v_x_327_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_328_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__2_329_, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_h__2_329_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_1(v_h__1_328_, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_327_ = stack[1].m_num;
lean_object* v_h__1_328_ = stack[2].m_obj;
lean_object* v_h__2_329_ = stack[3].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_box(0), v_x_327_, v_h__1_328_, v_h__2_329_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_h__1_337_, lean_object* v_h__2_338_){
_start:
{
uint8_t v_x_41__boxed_339_; lean_object* v_res_340_; 
v_x_41__boxed_339_ = lean_unbox(v_x_336_);
v_res_340_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(v_motive_335_, v_x_41__boxed_339_, v_h__1_337_, v_h__2_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR___redArg(lean_object* v_l_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_array_mk(v_l_341_);
v___x_343_ = lean_array_pop(v___x_342_);
v___x_344_ = lean_array_to_list(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR(lean_object* v_00_u03b1_345_, lean_object* v_l_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = lean_array_mk(v_l_346_);
v___x_348_ = lean_array_pop(v___x_347_);
v___x_349_ = lean_array_to_list(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(lean_object* v_p_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v_p_350_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v_head_353_; lean_object* v_tail_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_head_353_ = lean_ctor_get(v_x_351_, 0);
lean_inc_n(v_head_353_, 2);
v_tail_354_ = lean_ctor_get(v_x_351_, 1);
lean_inc(v_tail_354_);
lean_dec_ref_known(v_x_351_, 2);
lean_inc_ref(v_p_350_);
v___x_355_ = lean_apply_1(v_p_350_, v_head_353_);
v___x_356_ = lean_unbox(v___x_355_);
if (v___x_356_ == 0)
{
lean_dec(v_head_353_);
v_x_351_ = v_tail_354_;
goto _start;
}
else
{
lean_object* v___x_358_; 
lean_dec(v_tail_354_);
lean_dec_ref(v_p_350_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_head_353_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object* v_p_359_, lean_object* v_l_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = l_List_reverse___redArg(v_l_360_);
v___x_362_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_359_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object* v_00_u03b1_363_, lean_object* v_p_364_, lean_object* v_l_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_List_findRev_x3fTR___redArg(v_p_364_, v_l_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(lean_object* v_00_u03b1_367_, lean_object* v_p_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_368_, v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_371_, lean_object* v_h__1_372_, lean_object* v_h__2_373_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec(v_h__1_372_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_apply_1(v_h__2_373_, v___x_374_);
return v___x_375_;
}
else
{
lean_object* v_val_376_; lean_object* v___x_377_; 
lean_dec(v_h__2_373_);
v_val_376_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_x_371_, 1);
v___x_377_ = lean_apply_1(v_h__1_372_, v_val_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_378_, lean_object* v_motive_379_, lean_object* v_x_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v_h__1_381_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_apply_1(v_h__2_382_, v___x_383_);
return v___x_384_;
}
else
{
lean_object* v_val_385_; lean_object* v___x_386_; 
lean_dec(v_h__2_382_);
v_val_385_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v_x_380_, 1);
v___x_386_ = lean_apply_1(v_h__1_381_, v_val_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(lean_object* v_f_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v___x_389_; 
lean_dec_ref(v_f_387_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v_head_390_; lean_object* v_tail_391_; lean_object* v___x_392_; 
v_head_390_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_head_390_);
v_tail_391_ = lean_ctor_get(v_x_388_, 1);
lean_inc(v_tail_391_);
lean_dec_ref_known(v_x_388_, 2);
lean_inc_ref(v_f_387_);
v___x_392_ = lean_apply_1(v_f_387_, v_head_390_);
if (lean_obj_tag(v___x_392_) == 0)
{
v_x_388_ = v_tail_391_;
goto _start;
}
else
{
lean_dec(v_tail_391_);
lean_dec_ref(v_f_387_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object* v_f_394_, lean_object* v_l_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l_List_reverse___redArg(v_l_395_);
v___x_397_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_394_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v_f_400_, lean_object* v_l_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_List_findSomeRev_x3fTR___redArg(v_f_400_, v_l_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_f_405_, lean_object* v_x_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_405_, v_x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object* v_x1_408_, lean_object* v_x2_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v_x1_408_);
lean_ctor_set(v___x_410_, 1, v_x2_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object* v_inst_412_, lean_object* v_l_413_, lean_object* v_b_414_, lean_object* v_c_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
if (lean_obj_tag(v_a_416_) == 0)
{
lean_dec_ref(v_a_417_);
lean_dec(v_c_415_);
lean_dec(v_b_414_);
lean_dec_ref(v_inst_412_);
lean_inc(v_l_413_);
return v_l_413_;
}
else
{
lean_object* v_head_418_; lean_object* v_tail_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_438_; 
v_head_418_ = lean_ctor_get(v_a_416_, 0);
v_tail_419_ = lean_ctor_get(v_a_416_, 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_438_ == 0)
{
v___x_421_ = v_a_416_;
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_tail_419_);
lean_inc(v_head_418_);
lean_dec(v_a_416_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_438_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
lean_inc_ref(v_inst_412_);
lean_inc(v_head_418_);
lean_inc(v_b_414_);
v___x_423_ = lean_apply_2(v_inst_412_, v_b_414_, v_head_418_);
v___x_424_ = lean_unbox(v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_del_object(v___x_421_);
v___x_425_ = lean_array_push(v_a_417_, v_head_418_);
v_a_416_ = v_tail_419_;
v_a_417_ = v___x_425_;
goto _start;
}
else
{
lean_object* v___x_428_; 
lean_dec(v_head_418_);
lean_dec(v_b_414_);
lean_dec_ref(v_inst_412_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_c_415_);
v___x_428_ = v___x_421_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_c_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_tail_419_);
v___x_428_ = v_reuseFailAlloc_437_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_429_ = lean_array_get_size(v_a_417_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_432_ = lean_nat_dec_lt(v___x_430_, v___x_429_);
if (v___x_432_ == 0)
{
lean_dec_ref(v_a_417_);
return v___x_428_;
}
else
{
lean_object* v___f_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___f_433_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_434_ = lean_usize_of_nat(v___x_429_);
v___x_435_ = ((size_t)0ULL);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_431_, v___f_433_, v_a_417_, v___x_434_, v___x_435_, v___x_428_);
return v___x_436_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object* v_inst_439_, lean_object* v_l_440_, lean_object* v_b_441_, lean_object* v_c_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_439_, v_l_440_, v_b_441_, v_c_442_, v_a_443_, v_a_444_);
lean_dec(v_l_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object* v_00_u03b1_446_, lean_object* v_inst_447_, lean_object* v_l_448_, lean_object* v_b_449_, lean_object* v_c_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_447_, v_l_448_, v_b_449_, v_c_450_, v_a_451_, v_a_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object* v_00_u03b1_454_, lean_object* v_inst_455_, lean_object* v_l_456_, lean_object* v_b_457_, lean_object* v_c_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(v_00_u03b1_454_, v_inst_455_, v_l_456_, v_b_457_, v_c_458_, v_a_459_, v_a_460_);
lean_dec(v_l_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object* v_inst_462_, lean_object* v_l_463_, lean_object* v_b_464_, lean_object* v_c_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_463_);
v___x_467_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_462_, v_l_463_, v_b_464_, v_c_465_, v_l_463_, v___x_466_);
lean_dec(v_l_463_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object* v_00_u03b1_468_, lean_object* v_inst_469_, lean_object* v_l_470_, lean_object* v_b_471_, lean_object* v_c_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_470_);
v___x_474_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_469_, v_l_470_, v_b_471_, v_c_472_, v_l_470_, v___x_473_);
lean_dec(v_l_470_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object* v_f_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
if (lean_obj_tag(v_a_476_) == 0)
{
lean_object* v___x_479_; 
lean_dec(v_a_477_);
lean_dec(v_f_475_);
v___x_479_ = lean_array_to_list(v_a_478_);
return v___x_479_;
}
else
{
lean_object* v_head_480_; lean_object* v_tail_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_500_; 
v_head_480_ = lean_ctor_get(v_a_476_, 0);
v_tail_481_ = lean_ctor_get(v_a_476_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_476_);
if (v_isSharedCheck_500_ == 0)
{
v___x_483_ = v_a_476_;
v_isShared_484_ = v_isSharedCheck_500_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_tail_481_);
lean_inc(v_head_480_);
lean_dec(v_a_476_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_500_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_zero_485_; uint8_t v_isZero_486_; 
v_zero_485_ = lean_unsigned_to_nat(0u);
v_isZero_486_ = lean_nat_dec_eq(v_a_477_, v_zero_485_);
if (v_isZero_486_ == 1)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v_a_477_);
v___x_487_ = lean_apply_1(v_f_475_, v_head_480_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_487_);
v___x_489_ = v___x_483_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_tail_481_);
v___x_489_ = v_reuseFailAlloc_495_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v_a_478_);
v___x_491_ = lean_nat_dec_lt(v_zero_485_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec_ref(v_a_478_);
return v___x_489_;
}
else
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_usize_of_nat(v___x_490_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_478_, v___x_492_, v___x_493_, v___x_489_);
lean_dec_ref(v_a_478_);
return v___x_494_;
}
}
}
else
{
lean_object* v_one_496_; lean_object* v_n_497_; lean_object* v___x_498_; 
lean_del_object(v___x_483_);
v_one_496_ = lean_unsigned_to_nat(1u);
v_n_497_ = lean_nat_sub(v_a_477_, v_one_496_);
lean_dec(v_a_477_);
v___x_498_ = lean_array_push(v_a_478_, v_head_480_);
v_a_476_ = v_tail_481_;
v_a_477_ = v_n_497_;
v_a_478_ = v___x_498_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object* v_00_u03b1_501_, lean_object* v_f_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object* v_l_507_, lean_object* v_i_508_, lean_object* v_f_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_511_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_509_, v_l_507_, v_i_508_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object* v_00_u03b1_512_, lean_object* v_l_513_, lean_object* v_i_514_, lean_object* v_f_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_List_modifyTR___redArg(v_l_513_, v_i_514_, v_f_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_zero_521_; uint8_t v_isZero_522_; 
v_zero_521_ = lean_unsigned_to_nat(0u);
v_isZero_522_ = lean_nat_dec_eq(v_a_518_, v_zero_521_);
if (v_isZero_522_ == 1)
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
lean_dec(v_a_518_);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v_a_517_);
lean_ctor_set(v___x_523_, 1, v_a_519_);
v___x_524_ = lean_array_get_size(v_a_520_);
v___x_525_ = lean_nat_dec_lt(v_zero_521_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec_ref(v_a_520_);
return v___x_523_;
}
else
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_usize_of_nat(v___x_524_);
v___x_527_ = ((size_t)0ULL);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_520_, v___x_526_, v___x_527_, v___x_523_);
lean_dec_ref(v_a_520_);
return v___x_528_;
}
}
else
{
if (lean_obj_tag(v_a_519_) == 0)
{
lean_object* v___x_529_; 
lean_dec(v_a_518_);
lean_dec(v_a_517_);
v___x_529_ = lean_array_to_list(v_a_520_);
return v___x_529_;
}
else
{
lean_object* v_head_530_; lean_object* v_tail_531_; lean_object* v_one_532_; lean_object* v_n_533_; lean_object* v___x_534_; 
v_head_530_ = lean_ctor_get(v_a_519_, 0);
lean_inc(v_head_530_);
v_tail_531_ = lean_ctor_get(v_a_519_, 1);
lean_inc(v_tail_531_);
lean_dec_ref_known(v_a_519_, 2);
v_one_532_ = lean_unsigned_to_nat(1u);
v_n_533_ = lean_nat_sub(v_a_518_, v_one_532_);
lean_dec(v_a_518_);
v___x_534_ = lean_array_push(v_a_520_, v_head_530_);
v_a_518_ = v_n_533_;
v_a_519_ = v_tail_531_;
v_a_520_ = v___x_534_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object* v_00_u03b1_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object* v_l_542_, lean_object* v_n_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_546_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_544_, v_n_543_, v_l_542_, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object* v_00_u03b1_547_, lean_object* v_l_548_, lean_object* v_n_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_552_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_550_, v_n_549_, v_l_548_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_h__1_556_, lean_object* v_h__2_557_, lean_object* v_h__3_558_){
_start:
{
lean_object* v_zero_559_; uint8_t v_isZero_560_; 
v_zero_559_ = lean_unsigned_to_nat(0u);
v_isZero_560_ = lean_nat_dec_eq(v_x_553_, v_zero_559_);
if (v_isZero_560_ == 1)
{
lean_object* v___x_561_; 
lean_dec(v_h__3_558_);
lean_dec(v_h__2_557_);
lean_dec(v_x_553_);
v___x_561_ = lean_apply_2(v_h__1_556_, v_x_554_, v_x_555_);
return v___x_561_;
}
else
{
lean_dec(v_h__1_556_);
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v___x_562_; 
lean_dec(v_h__3_558_);
v___x_562_ = lean_apply_3(v_h__2_557_, v_x_553_, v_x_555_, lean_box(0));
return v___x_562_;
}
else
{
lean_object* v_head_563_; lean_object* v_tail_564_; lean_object* v_one_565_; lean_object* v_n_566_; lean_object* v___x_567_; 
lean_dec(v_h__2_557_);
v_head_563_ = lean_ctor_get(v_x_554_, 0);
lean_inc(v_head_563_);
v_tail_564_ = lean_ctor_get(v_x_554_, 1);
lean_inc(v_tail_564_);
lean_dec_ref_known(v_x_554_, 2);
v_one_565_ = lean_unsigned_to_nat(1u);
v_n_566_ = lean_nat_sub(v_x_553_, v_one_565_);
lean_dec(v_x_553_);
v___x_567_ = lean_apply_4(v_h__3_558_, v_n_566_, v_head_563_, v_tail_564_, v_x_555_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object* v_00_u03b1_568_, lean_object* v_motive_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_, lean_object* v_h__3_575_){
_start:
{
lean_object* v_zero_576_; uint8_t v_isZero_577_; 
v_zero_576_ = lean_unsigned_to_nat(0u);
v_isZero_577_ = lean_nat_dec_eq(v_x_570_, v_zero_576_);
if (v_isZero_577_ == 1)
{
lean_object* v___x_578_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__2_574_);
lean_dec(v_x_570_);
v___x_578_ = lean_apply_2(v_h__1_573_, v_x_571_, v_x_572_);
return v___x_578_;
}
else
{
lean_dec(v_h__1_573_);
if (lean_obj_tag(v_x_571_) == 0)
{
lean_object* v___x_579_; 
lean_dec(v_h__3_575_);
v___x_579_ = lean_apply_3(v_h__2_574_, v_x_570_, v_x_572_, lean_box(0));
return v___x_579_;
}
else
{
lean_object* v_head_580_; lean_object* v_tail_581_; lean_object* v_one_582_; lean_object* v_n_583_; lean_object* v___x_584_; 
lean_dec(v_h__2_574_);
v_head_580_ = lean_ctor_get(v_x_571_, 0);
lean_inc(v_head_580_);
v_tail_581_ = lean_ctor_get(v_x_571_, 1);
lean_inc(v_tail_581_);
lean_dec_ref_known(v_x_571_, 2);
v_one_582_ = lean_unsigned_to_nat(1u);
v_n_583_ = lean_nat_sub(v_x_570_, v_one_582_);
lean_dec(v_x_570_);
v___x_584_ = lean_apply_4(v_h__3_575_, v_n_583_, v_head_580_, v_tail_581_, v_x_572_);
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object* v_inst_585_, lean_object* v_l_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
if (lean_obj_tag(v_a_588_) == 0)
{
lean_dec_ref(v_a_589_);
lean_dec(v_a_587_);
lean_dec_ref(v_inst_585_);
lean_inc(v_l_586_);
return v_l_586_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_head_590_ = lean_ctor_get(v_a_588_, 0);
lean_inc_n(v_head_590_, 2);
v_tail_591_ = lean_ctor_get(v_a_588_, 1);
lean_inc(v_tail_591_);
lean_dec_ref_known(v_a_588_, 2);
lean_inc_ref(v_inst_585_);
lean_inc(v_a_587_);
v___x_592_ = lean_apply_2(v_inst_585_, v_head_590_, v_a_587_);
v___x_593_ = lean_unbox(v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_push(v_a_589_, v_head_590_);
v_a_588_ = v_tail_591_;
v_a_589_ = v___x_594_;
goto _start;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
lean_dec(v_head_590_);
lean_dec(v_a_587_);
lean_dec_ref(v_inst_585_);
v___x_596_ = lean_array_get_size(v_a_589_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_596_);
if (v___x_599_ == 0)
{
lean_dec_ref(v_a_589_);
return v_tail_591_;
}
else
{
lean_object* v___f_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
v___f_600_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_601_ = lean_usize_of_nat(v___x_596_);
v___x_602_ = ((size_t)0ULL);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_598_, v___f_600_, v_a_589_, v___x_601_, v___x_602_, v_tail_591_);
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object* v_inst_604_, lean_object* v_l_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_604_, v_l_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_l_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_l_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_611_, v_l_612_, v_a_613_, v_a_614_, v_a_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object* v_00_u03b1_617_, lean_object* v_inst_618_, lean_object* v_l_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(v_00_u03b1_617_, v_inst_618_, v_l_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_l_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object* v_inst_624_, lean_object* v_l_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_625_);
v___x_628_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_624_, v_l_625_, v_a_626_, v_l_625_, v___x_627_);
lean_dec(v_l_625_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object* v_00_u03b1_629_, lean_object* v_inst_630_, lean_object* v_l_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_631_);
v___x_634_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_630_, v_l_631_, v_a_632_, v_l_631_, v___x_633_);
lean_dec(v_l_631_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object* v_p_635_, lean_object* v_l_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
if (lean_obj_tag(v_a_637_) == 0)
{
lean_dec_ref(v_a_638_);
lean_dec_ref(v_p_635_);
lean_inc(v_l_636_);
return v_l_636_;
}
else
{
lean_object* v_head_639_; lean_object* v_tail_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_head_639_ = lean_ctor_get(v_a_637_, 0);
lean_inc_n(v_head_639_, 2);
v_tail_640_ = lean_ctor_get(v_a_637_, 1);
lean_inc(v_tail_640_);
lean_dec_ref_known(v_a_637_, 2);
lean_inc_ref(v_p_635_);
v___x_641_ = lean_apply_1(v_p_635_, v_head_639_);
v___x_642_ = lean_unbox(v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_array_push(v_a_638_, v_head_639_);
v_a_637_ = v_tail_640_;
v_a_638_ = v___x_643_;
goto _start;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_dec(v_head_639_);
lean_dec_ref(v_p_635_);
v___x_645_ = lean_array_get_size(v_a_638_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_648_ = lean_nat_dec_lt(v___x_646_, v___x_645_);
if (v___x_648_ == 0)
{
lean_dec_ref(v_a_638_);
return v_tail_640_;
}
else
{
lean_object* v___f_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___f_649_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_650_ = lean_usize_of_nat(v___x_645_);
v___x_651_ = ((size_t)0ULL);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_647_, v___f_649_, v_a_638_, v___x_650_, v___x_651_, v_tail_640_);
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object* v_p_653_, lean_object* v_l_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_653_, v_l_654_, v_a_655_, v_a_656_);
lean_dec(v_l_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object* v_00_u03b1_658_, lean_object* v_p_659_, lean_object* v_l_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_659_, v_l_660_, v_a_661_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object* v_00_u03b1_664_, lean_object* v_p_665_, lean_object* v_l_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(v_00_u03b1_664_, v_p_665_, v_l_666_, v_a_667_, v_a_668_);
lean_dec(v_l_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object* v_p_670_, lean_object* v_l_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_671_);
v___x_673_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_670_, v_l_671_, v_l_671_, v___x_672_);
lean_dec(v_l_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object* v_00_u03b1_674_, lean_object* v_p_675_, lean_object* v_l_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_676_);
v___x_678_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_675_, v_l_676_, v_l_676_, v___x_677_);
lean_dec(v_l_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object* v_l_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
if (lean_obj_tag(v_a_680_) == 0)
{
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_inc(v_l_679_);
return v_l_679_;
}
else
{
lean_object* v_head_683_; lean_object* v_tail_684_; lean_object* v_zero_685_; uint8_t v_isZero_686_; 
v_head_683_ = lean_ctor_get(v_a_680_, 0);
lean_inc(v_head_683_);
v_tail_684_ = lean_ctor_get(v_a_680_, 1);
lean_inc(v_tail_684_);
lean_dec_ref_known(v_a_680_, 2);
v_zero_685_ = lean_unsigned_to_nat(0u);
v_isZero_686_ = lean_nat_dec_eq(v_a_681_, v_zero_685_);
if (v_isZero_686_ == 1)
{
lean_object* v___x_687_; uint8_t v___x_688_; 
lean_dec(v_head_683_);
lean_dec(v_a_681_);
v___x_687_ = lean_array_get_size(v_a_682_);
v___x_688_ = lean_nat_dec_lt(v_zero_685_, v___x_687_);
if (v___x_688_ == 0)
{
lean_dec_ref(v_a_682_);
return v_tail_684_;
}
else
{
size_t v___x_689_; size_t v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_usize_of_nat(v___x_687_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_682_, v___x_689_, v___x_690_, v_tail_684_);
lean_dec_ref(v_a_682_);
return v___x_691_;
}
}
else
{
lean_object* v_one_692_; lean_object* v_n_693_; lean_object* v___x_694_; 
v_one_692_ = lean_unsigned_to_nat(1u);
v_n_693_ = lean_nat_sub(v_a_681_, v_one_692_);
lean_dec(v_a_681_);
v___x_694_ = lean_array_push(v_a_682_, v_head_683_);
v_a_680_ = v_tail_684_;
v_a_681_ = v_n_693_;
v_a_682_ = v___x_694_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object* v_l_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_l_696_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object* v_00_u03b1_701_, lean_object* v_l_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_702_, v_a_703_, v_a_704_, v_a_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object* v_00_u03b1_707_, lean_object* v_l_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(v_00_u03b1_707_, v_l_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_l_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object* v_l_713_, lean_object* v_n_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_713_);
v___x_716_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_713_, v_l_713_, v_n_714_, v___x_715_);
lean_dec(v_l_713_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object* v_00_u03b1_717_, lean_object* v_l_718_, lean_object* v_n_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_718_);
v___x_721_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_718_, v_l_718_, v_n_719_, v___x_720_);
lean_dec(v_l_718_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object* v_f_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
if (lean_obj_tag(v_a_723_) == 1)
{
if (lean_obj_tag(v_a_724_) == 1)
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v_head_728_; lean_object* v_tail_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_head_726_ = lean_ctor_get(v_a_723_, 0);
lean_inc(v_head_726_);
v_tail_727_ = lean_ctor_get(v_a_723_, 1);
lean_inc(v_tail_727_);
lean_dec_ref_known(v_a_723_, 2);
v_head_728_ = lean_ctor_get(v_a_724_, 0);
lean_inc(v_head_728_);
v_tail_729_ = lean_ctor_get(v_a_724_, 1);
lean_inc(v_tail_729_);
lean_dec_ref_known(v_a_724_, 2);
lean_inc(v_f_722_);
v___x_730_ = lean_apply_2(v_f_722_, v_head_726_, v_head_728_);
v___x_731_ = lean_array_push(v_a_725_, v___x_730_);
v_a_723_ = v_tail_727_;
v_a_724_ = v_tail_729_;
v_a_725_ = v___x_731_;
goto _start;
}
else
{
lean_object* v___x_733_; 
lean_dec_ref_known(v_a_723_, 2);
lean_dec(v_a_724_);
lean_dec(v_f_722_);
v___x_733_ = lean_array_to_list(v_a_725_);
return v___x_733_;
}
}
else
{
lean_object* v___x_734_; 
lean_dec(v_a_724_);
lean_dec(v_a_723_);
lean_dec(v_f_722_);
v___x_734_ = lean_array_to_list(v_a_725_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_00_u03b3_737_, lean_object* v_f_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_738_, v_a_739_, v_a_740_, v_a_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object* v_f_743_, lean_object* v_as_744_, lean_object* v_bs_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_747_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_743_, v_as_744_, v_bs_745_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_00_u03b3_750_, lean_object* v_f_751_, lean_object* v_as_752_, lean_object* v_bs_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_755_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_751_, v_as_752_, v_bs_753_, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_h__1_759_, lean_object* v_h__2_760_){
_start:
{
if (lean_obj_tag(v_x_756_) == 1)
{
if (lean_obj_tag(v_x_757_) == 1)
{
lean_object* v_head_761_; lean_object* v_tail_762_; lean_object* v_head_763_; lean_object* v_tail_764_; lean_object* v___x_765_; 
lean_dec(v_h__2_760_);
v_head_761_ = lean_ctor_get(v_x_756_, 0);
lean_inc(v_head_761_);
v_tail_762_ = lean_ctor_get(v_x_756_, 1);
lean_inc(v_tail_762_);
lean_dec_ref_known(v_x_756_, 2);
v_head_763_ = lean_ctor_get(v_x_757_, 0);
lean_inc(v_head_763_);
v_tail_764_ = lean_ctor_get(v_x_757_, 1);
lean_inc(v_tail_764_);
lean_dec_ref_known(v_x_757_, 2);
v___x_765_ = lean_apply_5(v_h__1_759_, v_head_761_, v_tail_762_, v_head_763_, v_tail_764_, v_x_758_);
return v___x_765_;
}
else
{
lean_object* v___x_766_; 
lean_dec(v_h__1_759_);
v___x_766_ = lean_apply_4(v_h__2_760_, v_x_756_, v_x_757_, v_x_758_, lean_box(0));
return v___x_766_;
}
}
else
{
lean_object* v___x_767_; 
lean_dec(v_h__1_759_);
v___x_767_ = lean_apply_4(v_h__2_760_, v_x_756_, v_x_757_, v_x_758_, lean_box(0));
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_00_u03b3_770_, lean_object* v_motive_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_h__1_775_, lean_object* v_h__2_776_){
_start:
{
if (lean_obj_tag(v_x_772_) == 1)
{
if (lean_obj_tag(v_x_773_) == 1)
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v_head_779_; lean_object* v_tail_780_; lean_object* v___x_781_; 
lean_dec(v_h__2_776_);
v_head_777_ = lean_ctor_get(v_x_772_, 0);
lean_inc(v_head_777_);
v_tail_778_ = lean_ctor_get(v_x_772_, 1);
lean_inc(v_tail_778_);
lean_dec_ref_known(v_x_772_, 2);
v_head_779_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_head_779_);
v_tail_780_ = lean_ctor_get(v_x_773_, 1);
lean_inc(v_tail_780_);
lean_dec_ref_known(v_x_773_, 2);
v___x_781_ = lean_apply_5(v_h__1_775_, v_head_777_, v_tail_778_, v_head_779_, v_tail_780_, v_x_774_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; 
lean_dec(v_h__1_775_);
v___x_782_ = lean_apply_4(v_h__2_776_, v_x_772_, v_x_773_, v_x_774_, lean_box(0));
return v___x_782_;
}
}
else
{
lean_object* v___x_783_; 
lean_dec(v_h__1_775_);
v___x_783_ = lean_apply_4(v_h__2_776_, v_x_772_, v_x_773_, v_x_774_, lean_box(0));
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWith_match__1_splitter___redArg(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_h__1_786_, lean_object* v_h__2_787_){
_start:
{
if (lean_obj_tag(v_x_784_) == 1)
{
if (lean_obj_tag(v_x_785_) == 1)
{
lean_object* v_head_788_; lean_object* v_tail_789_; lean_object* v_head_790_; lean_object* v_tail_791_; lean_object* v___x_792_; 
lean_dec(v_h__2_787_);
v_head_788_ = lean_ctor_get(v_x_784_, 0);
lean_inc(v_head_788_);
v_tail_789_ = lean_ctor_get(v_x_784_, 1);
lean_inc(v_tail_789_);
lean_dec_ref_known(v_x_784_, 2);
v_head_790_ = lean_ctor_get(v_x_785_, 0);
lean_inc(v_head_790_);
v_tail_791_ = lean_ctor_get(v_x_785_, 1);
lean_inc(v_tail_791_);
lean_dec_ref_known(v_x_785_, 2);
v___x_792_ = lean_apply_4(v_h__1_786_, v_head_788_, v_tail_789_, v_head_790_, v_tail_791_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; 
lean_dec(v_h__1_786_);
v___x_793_ = lean_apply_3(v_h__2_787_, v_x_784_, v_x_785_, lean_box(0));
return v___x_793_;
}
}
else
{
lean_object* v___x_794_; 
lean_dec(v_h__1_786_);
v___x_794_ = lean_apply_3(v_h__2_787_, v_x_784_, v_x_785_, lean_box(0));
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWith_match__1_splitter(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_motive_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_h__1_800_, lean_object* v_h__2_801_){
_start:
{
if (lean_obj_tag(v_x_798_) == 1)
{
if (lean_obj_tag(v_x_799_) == 1)
{
lean_object* v_head_802_; lean_object* v_tail_803_; lean_object* v_head_804_; lean_object* v_tail_805_; lean_object* v___x_806_; 
lean_dec(v_h__2_801_);
v_head_802_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_head_802_);
v_tail_803_ = lean_ctor_get(v_x_798_, 1);
lean_inc(v_tail_803_);
lean_dec_ref_known(v_x_798_, 2);
v_head_804_ = lean_ctor_get(v_x_799_, 0);
lean_inc(v_head_804_);
v_tail_805_ = lean_ctor_get(v_x_799_, 1);
lean_inc(v_tail_805_);
lean_dec_ref_known(v_x_799_, 2);
v___x_806_ = lean_apply_4(v_h__1_800_, v_head_802_, v_tail_803_, v_head_804_, v_tail_805_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; 
lean_dec(v_h__1_800_);
v___x_807_ = lean_apply_3(v_h__2_801_, v_x_798_, v_x_799_, lean_box(0));
return v___x_807_;
}
}
else
{
lean_object* v___x_808_; 
lean_dec(v_h__1_800_);
v___x_808_ = lean_apply_3(v_h__2_801_, v_x_798_, v_x_799_, lean_box(0));
return v___x_808_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object* v_as_809_, size_t v_i_810_, size_t v_stop_811_, lean_object* v_b_812_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = lean_usize_dec_eq(v_i_810_, v_stop_811_);
if (v___x_813_ == 0)
{
lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_830_; 
v_fst_814_ = lean_ctor_get(v_b_812_, 0);
v_snd_815_ = lean_ctor_get(v_b_812_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_b_812_);
if (v_isSharedCheck_830_ == 0)
{
v___x_817_ = v_b_812_;
v_isShared_818_ = v_isSharedCheck_830_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v_b_812_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_830_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_sub(v_i_810_, v___x_819_);
v___x_821_ = lean_array_uget_borrowed(v_as_809_, v___x_820_);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_sub(v_fst_814_, v___x_822_);
lean_dec(v_fst_814_);
lean_inc(v___x_823_);
lean_inc(v___x_821_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_823_);
lean_ctor_set(v___x_817_, 0, v___x_821_);
v___x_825_ = v___x_817_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_snd_815_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_823_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v_i_810_ = v___x_820_;
v_b_812_ = v___x_827_;
goto _start;
}
}
}
else
{
return v_b_812_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_809_ = stack[0].m_obj;
size_t v_i_810_ = stack[1].m_num;
size_t v_stop_811_ = stack[2].m_num;
lean_object* v_b_812_ = stack[3].m_obj;
lean_object* v_res_831_;
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_809_, v_i_810_, v_stop_811_, v_b_812_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object* v_as_832_, lean_object* v_i_833_, lean_object* v_stop_834_, lean_object* v_b_835_){
_start:
{
size_t v_i_boxed_836_; size_t v_stop_boxed_837_; lean_object* v_res_838_; 
v_i_boxed_836_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_stop_boxed_837_ = lean_unbox_usize(v_stop_834_);
lean_dec(v_stop_834_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_832_, v_i_boxed_836_, v_stop_boxed_837_, v_b_835_);
lean_dec_ref(v_as_832_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object* v_l_839_, lean_object* v_n_840_){
_start:
{
lean_object* v_as_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_as_841_ = lean_array_mk(v_l_839_);
v___x_842_ = lean_array_get_size(v_as_841_);
v___x_843_ = lean_box(0);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_nat_dec_lt(v___x_844_, v___x_842_);
if (v___x_845_ == 0)
{
lean_dec_ref(v_as_841_);
return v___x_843_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; lean_object* v_snd_851_; 
v___x_846_ = lean_nat_add(v_n_840_, v___x_842_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_843_);
v___x_848_ = lean_usize_of_nat(v___x_842_);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_841_, v___x_848_, v___x_849_, v___x_847_);
lean_dec_ref(v_as_841_);
v_snd_851_ = lean_ctor_get(v___x_850_, 1);
lean_inc(v_snd_851_);
lean_dec_ref(v___x_850_);
return v_snd_851_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object* v_l_852_, lean_object* v_n_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_List_zipIdxTR___redArg(v_l_852_, v_n_853_);
lean_dec(v_n_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object* v_00_u03b1_855_, lean_object* v_l_856_, lean_object* v_n_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_List_zipIdxTR___redArg(v_l_856_, v_n_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object* v_00_u03b1_859_, lean_object* v_l_860_, lean_object* v_n_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_List_zipIdxTR(v_00_u03b1_859_, v_l_860_, v_n_861_);
lean_dec(v_n_861_);
return v_res_862_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object* v_00_u03b1_863_, lean_object* v_as_864_, size_t v_i_865_, size_t v_stop_866_, lean_object* v_b_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_864_, v_i_865_, v_stop_866_, v_b_867_);
return v___x_868_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_864_ = stack[1].m_obj;
size_t v_i_865_ = stack[2].m_num;
size_t v_stop_866_ = stack[3].m_num;
lean_object* v_b_867_ = stack[4].m_obj;
lean_object* v_res_869_;
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_box(0), v_as_864_, v_i_865_, v_stop_866_, v_b_867_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object* v_00_u03b1_870_, lean_object* v_as_871_, lean_object* v_i_872_, lean_object* v_stop_873_, lean_object* v_b_874_){
_start:
{
size_t v_i_boxed_875_; size_t v_stop_boxed_876_; lean_object* v_res_877_; 
v_i_boxed_875_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_stop_boxed_876_ = lean_unbox_usize(v_stop_873_);
lean_dec(v_stop_873_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(v_00_u03b1_870_, v_as_871_, v_i_boxed_875_, v_stop_boxed_876_, v_b_874_);
lean_dec_ref(v_as_871_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object* v_sep_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
if (lean_obj_tag(v_a_880_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_882_ = lean_array_get_size(v_a_881_);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_nat_dec_lt(v___x_883_, v___x_882_);
if (v___x_884_ == 0)
{
lean_dec_ref(v_a_881_);
return v_a_879_;
}
else
{
size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_usize_of_nat(v___x_882_);
v___x_886_ = ((size_t)0ULL);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_881_, v___x_885_, v___x_886_, v_a_879_);
lean_dec_ref(v_a_881_);
return v___x_887_;
}
}
else
{
lean_object* v_head_888_; lean_object* v_tail_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_head_888_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_head_888_);
v_tail_889_ = lean_ctor_get(v_a_880_, 1);
lean_inc(v_tail_889_);
lean_dec_ref_known(v_a_880_, 2);
v___x_890_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_881_, v_a_879_);
v___x_891_ = l_Array_append___redArg(v___x_890_, v_sep_878_);
v_a_879_ = v_head_888_;
v_a_880_ = v_tail_889_;
v_a_881_ = v___x_891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object* v_sep_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec_ref(v_sep_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object* v_00_u03b1_898_, lean_object* v_sep_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object* v_00_u03b1_904_, lean_object* v_sep_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(v_00_u03b1_904_, v_sep_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec_ref(v_sep_905_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object* v_sep_910_, lean_object* v_x_911_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_object* v___x_912_; 
lean_dec(v_sep_910_);
v___x_912_ = lean_box(0);
return v___x_912_;
}
else
{
lean_object* v_tail_913_; 
v_tail_913_ = lean_ctor_get(v_x_911_, 1);
if (lean_obj_tag(v_tail_913_) == 0)
{
lean_object* v_head_914_; 
lean_dec(v_sep_910_);
v_head_914_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_head_914_);
lean_dec_ref_known(v_x_911_, 2);
return v_head_914_;
}
else
{
lean_object* v_head_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_inc(v_tail_913_);
v_head_915_ = lean_ctor_get(v_x_911_, 0);
lean_inc(v_head_915_);
lean_dec_ref_known(v_x_911_, 2);
v___x_916_ = lean_array_mk(v_sep_910_);
v___x_917_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_918_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v___x_916_, v_head_915_, v_tail_913_, v___x_917_);
lean_dec_ref(v___x_916_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object* v_00_u03b1_919_, lean_object* v_sep_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_List_intercalateTR___redArg(v_sep_920_, v_x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object* v_x_923_, lean_object* v_h__1_924_, lean_object* v_h__2_925_, lean_object* v_h__3_926_){
_start:
{
if (lean_obj_tag(v_x_923_) == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_h__3_926_);
lean_dec(v_h__2_925_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_apply_1(v_h__1_924_, v___x_927_);
return v___x_928_;
}
else
{
lean_object* v_tail_929_; 
lean_dec(v_h__1_924_);
v_tail_929_ = lean_ctor_get(v_x_923_, 1);
if (lean_obj_tag(v_tail_929_) == 0)
{
lean_object* v_head_930_; lean_object* v___x_931_; 
lean_dec(v_h__3_926_);
v_head_930_ = lean_ctor_get(v_x_923_, 0);
lean_inc(v_head_930_);
lean_dec_ref_known(v_x_923_, 2);
v___x_931_ = lean_apply_1(v_h__2_925_, v_head_930_);
return v___x_931_;
}
else
{
lean_object* v_head_932_; lean_object* v___x_933_; 
lean_inc(v_tail_929_);
lean_dec(v_h__2_925_);
v_head_932_ = lean_ctor_get(v_x_923_, 0);
lean_inc(v_head_932_);
lean_dec_ref_known(v_x_923_, 2);
v___x_933_ = lean_apply_3(v_h__3_926_, v_head_932_, v_tail_929_, lean_box(0));
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object* v_00_u03b1_934_, lean_object* v_motive_935_, lean_object* v_x_936_, lean_object* v_h__1_937_, lean_object* v_h__2_938_, lean_object* v_h__3_939_){
_start:
{
if (lean_obj_tag(v_x_936_) == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec(v_h__3_939_);
lean_dec(v_h__2_938_);
v___x_940_ = lean_box(0);
v___x_941_ = lean_apply_1(v_h__1_937_, v___x_940_);
return v___x_941_;
}
else
{
lean_object* v_tail_942_; 
lean_dec(v_h__1_937_);
v_tail_942_ = lean_ctor_get(v_x_936_, 1);
if (lean_obj_tag(v_tail_942_) == 0)
{
lean_object* v_head_943_; lean_object* v___x_944_; 
lean_dec(v_h__3_939_);
v_head_943_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_head_943_);
lean_dec_ref_known(v_x_936_, 2);
v___x_944_ = lean_apply_1(v_h__2_938_, v_head_943_);
return v___x_944_;
}
else
{
lean_object* v_head_945_; lean_object* v___x_946_; 
lean_inc(v_tail_942_);
lean_dec(v_h__2_938_);
v_head_945_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_head_945_);
lean_dec_ref_known(v_x_936_, 2);
v___x_946_ = lean_apply_3(v_h__3_939_, v_head_945_, v_tail_942_, lean_box(0));
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_947_, lean_object* v_h__1_948_, lean_object* v_h__2_949_, lean_object* v_h__3_950_){
_start:
{
if (lean_obj_tag(v_x_947_) == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_h__3_950_);
lean_dec(v_h__2_949_);
v___x_951_ = lean_box(0);
v___x_952_ = lean_apply_1(v_h__1_948_, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v_tail_953_; 
lean_dec(v_h__1_948_);
v_tail_953_ = lean_ctor_get(v_x_947_, 1);
if (lean_obj_tag(v_tail_953_) == 0)
{
lean_object* v_head_954_; lean_object* v___x_955_; 
lean_dec(v_h__3_950_);
v_head_954_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_head_954_);
lean_dec_ref_known(v_x_947_, 2);
v___x_955_ = lean_apply_1(v_h__2_949_, v_head_954_);
return v___x_955_;
}
else
{
lean_object* v_head_956_; lean_object* v___x_957_; 
lean_inc(v_tail_953_);
lean_dec(v_h__2_949_);
v_head_956_ = lean_ctor_get(v_x_947_, 0);
lean_inc(v_head_956_);
lean_dec_ref_known(v_x_947_, 2);
v___x_957_ = lean_apply_3(v_h__3_950_, v_head_956_, v_tail_953_, lean_box(0));
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_958_, lean_object* v_motive_959_, lean_object* v_x_960_, lean_object* v_h__1_961_, lean_object* v_h__2_962_, lean_object* v_h__3_963_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_h__3_963_);
lean_dec(v_h__2_962_);
v___x_964_ = lean_box(0);
v___x_965_ = lean_apply_1(v_h__1_961_, v___x_964_);
return v___x_965_;
}
else
{
lean_object* v_tail_966_; 
lean_dec(v_h__1_961_);
v_tail_966_ = lean_ctor_get(v_x_960_, 1);
if (lean_obj_tag(v_tail_966_) == 0)
{
lean_object* v_head_967_; lean_object* v___x_968_; 
lean_dec(v_h__3_963_);
v_head_967_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_head_967_);
lean_dec_ref_known(v_x_960_, 2);
v___x_968_ = lean_apply_1(v_h__2_962_, v_head_967_);
return v___x_968_;
}
else
{
lean_object* v_head_969_; lean_object* v___x_970_; 
lean_inc(v_tail_966_);
lean_dec(v_h__2_962_);
v_head_969_ = lean_ctor_get(v_x_960_, 0);
lean_inc(v_head_969_);
lean_dec_ref_known(v_x_960_, 2);
v___x_970_ = lean_apply_3(v_h__3_963_, v_head_969_, v_tail_966_, lean_box(0));
return v___x_970_;
}
}
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Impl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Impl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Impl(builtin);
}
#ifdef __cplusplus
}
#endif
