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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg___boxed(lean_object* v_as_11_, lean_object* v_i_12_, lean_object* v_stop_13_, lean_object* v_b_14_){
_start:
{
size_t v_i_boxed_15_; size_t v_stop_boxed_16_; lean_object* v_res_17_; 
v_i_boxed_15_ = lean_unbox_usize(v_i_12_);
lean_dec(v_i_12_);
v_stop_boxed_16_ = lean_unbox_usize(v_stop_13_);
lean_dec(v_stop_13_);
v_res_17_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_11_, v_i_boxed_15_, v_stop_boxed_16_, v_b_14_);
lean_dec_ref(v_as_11_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(lean_object* v_l_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
if (lean_obj_tag(v_a_20_) == 0)
{
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec(v_a_19_);
lean_inc(v_l_18_);
return v_l_18_;
}
else
{
lean_object* v_head_23_; lean_object* v_tail_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_42_; 
v_head_23_ = lean_ctor_get(v_a_20_, 0);
v_tail_24_ = lean_ctor_get(v_a_20_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_a_20_);
if (v_isSharedCheck_42_ == 0)
{
v___x_26_ = v_a_20_;
v_isShared_27_ = v_isSharedCheck_42_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_tail_24_);
lean_inc(v_head_23_);
lean_dec(v_a_20_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_42_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_a_21_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_31_; 
lean_dec(v_head_23_);
lean_dec(v_a_21_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v_a_19_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_19_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_tail_24_);
v___x_31_ = v_reuseFailAlloc_37_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v_a_22_);
v___x_33_ = lean_nat_dec_lt(v_zero_28_, v___x_32_);
if (v___x_33_ == 0)
{
lean_dec_ref(v_a_22_);
return v___x_31_;
}
else
{
size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_usize_of_nat(v___x_32_);
v___x_35_ = ((size_t)0ULL);
v___x_36_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_22_, v___x_34_, v___x_35_, v___x_31_);
lean_dec_ref(v_a_22_);
return v___x_36_;
}
}
}
else
{
lean_object* v_one_38_; lean_object* v_n_39_; lean_object* v___x_40_; 
lean_del_object(v___x_26_);
v_one_38_ = lean_unsigned_to_nat(1u);
v_n_39_ = lean_nat_sub(v_a_21_, v_one_38_);
lean_dec(v_a_21_);
v___x_40_ = lean_array_push(v_a_22_, v_head_23_);
v_a_20_ = v_tail_24_;
v_a_21_ = v_n_39_;
v_a_22_ = v___x_40_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___redArg___boxed(lean_object* v_l_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
lean_dec(v_l_43_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go(lean_object* v_00_u03b1_49_, lean_object* v_l_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go___boxed(lean_object* v_00_u03b1_56_, lean_object* v_l_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Init_Data_List_Impl_0__List_setTR_go(v_00_u03b1_56_, v_l_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_l_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(lean_object* v_00_u03b1_63_, lean_object* v_as_64_, size_t v_i_65_, size_t v_stop_66_, lean_object* v_b_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_as_64_, v_i_65_, v_stop_66_, v_b_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_as_70_, lean_object* v_i_71_, lean_object* v_stop_72_, lean_object* v_b_73_){
_start:
{
size_t v_i_boxed_74_; size_t v_stop_boxed_75_; lean_object* v_res_76_; 
v_i_boxed_74_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_stop_boxed_75_ = lean_unbox_usize(v_stop_72_);
lean_dec(v_stop_72_);
v_res_76_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0(v_00_u03b1_69_, v_as_70_, v_i_boxed_74_, v_stop_boxed_75_, v_b_73_);
lean_dec_ref(v_as_70_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_List_setTR___redArg(lean_object* v_l_79_, lean_object* v_n_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_79_);
v___x_83_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_79_, v_a_81_, v_l_79_, v_n_80_, v___x_82_);
lean_dec(v_l_79_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_List_setTR(lean_object* v_00_u03b1_84_, lean_object* v_l_85_, lean_object* v_n_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_85_);
v___x_89_ = l___private_Init_Data_List_Impl_0__List_setTR_go___redArg(v_l_85_, v_a_87_, v_l_85_, v_n_86_, v___x_88_);
lean_dec(v_l_85_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___redArg(lean_object* v_f_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
if (lean_obj_tag(v_a_91_) == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_f_90_);
v___x_93_ = lean_array_to_list(v_a_92_);
return v___x_93_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; lean_object* v___x_96_; 
v_head_94_ = lean_ctor_get(v_a_91_, 0);
lean_inc(v_head_94_);
v_tail_95_ = lean_ctor_get(v_a_91_, 1);
lean_inc(v_tail_95_);
lean_dec_ref_known(v_a_91_, 2);
lean_inc_ref(v_f_90_);
v___x_96_ = lean_apply_1(v_f_90_, v_head_94_);
if (lean_obj_tag(v___x_96_) == 0)
{
v_a_91_ = v_tail_95_;
goto _start;
}
else
{
lean_object* v_val_98_; lean_object* v___x_99_; 
v_val_98_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_val_98_);
lean_dec_ref_known(v___x_96_, 1);
v___x_99_ = lean_array_push(v_a_92_, v_val_98_);
v_a_91_ = v_tail_95_;
v_a_92_ = v___x_99_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_f_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_List_filterMapTR_go___redArg(v_f_103_, v_a_104_, v_a_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR___redArg(lean_object* v_f_107_, lean_object* v_l_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_110_ = l_List_filterMapTR_go___redArg(v_f_107_, v_l_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_f_113_, lean_object* v_l_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_116_ = l_List_filterMapTR_go___redArg(v_f_113_, v_l_114_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_119_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__1_118_, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_118_);
v_val_122_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v_x_117_, 1);
v___x_123_ = lean_apply_1(v_h__2_119_, v_val_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(lean_object* v_00_u03b2_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_128_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_1(v_h__1_127_, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_127_);
v_val_131_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v_x_126_, 1);
v___x_132_ = lean_apply_1(v_h__2_128_, v_val_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec(v_h__2_135_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_1(v_h__1_134_, v___x_136_);
return v___x_137_;
}
else
{
lean_object* v_val_138_; lean_object* v___x_139_; 
lean_dec(v_h__1_134_);
v_val_138_ = lean_ctor_get(v_x_133_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v_x_133_, 1);
v___x_139_ = lean_apply_1(v_h__2_135_, v_val_138_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_h__2_144_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_1(v_h__1_143_, v___x_145_);
return v___x_146_;
}
else
{
lean_object* v_val_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v_val_147_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v_x_142_, 1);
v___x_148_ = lean_apply_1(v_h__2_144_, v_val_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_List_reduceOption___redArg(lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_152_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_153_ = l_List_filterMapTR_go___redArg(v___x_151_, v_a_150_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object* v_00_u03b1_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_157_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_158_ = l_List_filterMapTR_go___redArg(v___x_156_, v_a_155_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg___lam__0(lean_object* v_f_159_, lean_object* v_x1_160_, lean_object* v_x2_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_2(v_f_159_, v_x1_160_, v_x2_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg(lean_object* v_f_182_, lean_object* v_init_183_, lean_object* v_l_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v___x_185_ = lean_array_mk(v_l_184_);
v___x_186_ = lean_array_get_size(v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_189_ = lean_nat_dec_lt(v___x_187_, v___x_186_);
if (v___x_189_ == 0)
{
lean_dec_ref(v___x_185_);
lean_dec(v_f_182_);
return v_init_183_;
}
else
{
lean_object* v___f_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; 
v___f_190_ = lean_alloc_closure((void*)(l_List_foldrTR___redArg___lam__0), 3, 1);
lean_closure_set(v___f_190_, 0, v_f_182_);
v___x_191_ = lean_usize_of_nat(v___x_186_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_188_, v___f_190_, v___x_185_, v___x_191_, v___x_192_, v_init_183_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR(lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_f_196_, lean_object* v_init_197_, lean_object* v_l_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_List_foldrTR___redArg(v_f_196_, v_init_197_, v_l_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object* v_f_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_203_; 
lean_dec_ref(v_f_200_);
v___x_203_ = lean_array_to_list(v_a_202_);
return v___x_203_;
}
else
{
lean_object* v_head_204_; lean_object* v_tail_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_head_204_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_head_204_);
v_tail_205_ = lean_ctor_get(v_a_201_, 1);
lean_inc(v_tail_205_);
lean_dec_ref_known(v_a_201_, 2);
lean_inc_ref(v_f_200_);
v___x_206_ = lean_apply_1(v_f_200_, v_head_204_);
v___x_207_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_202_, v___x_206_);
v_a_201_ = v_tail_205_;
v_a_202_ = v___x_207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_f_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_211_, v_a_212_, v_a_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR___redArg(lean_object* v_f_215_, lean_object* v_as_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_218_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_215_, v_as_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_f_221_, lean_object* v_as_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_224_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_221_, v_as_222_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR___redArg(lean_object* v_l_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_228_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_229_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_227_, v_l_226_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR(lean_object* v_00_u03b1_230_, lean_object* v_l_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_233_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_234_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_232_, v_l_231_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object* v_l_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
if (lean_obj_tag(v_a_236_) == 0)
{
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_inc(v_l_235_);
return v_l_235_;
}
else
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v_zero_241_; uint8_t v_isZero_242_; 
v_head_239_ = lean_ctor_get(v_a_236_, 0);
lean_inc(v_head_239_);
v_tail_240_ = lean_ctor_get(v_a_236_, 1);
lean_inc(v_tail_240_);
lean_dec_ref_known(v_a_236_, 2);
v_zero_241_ = lean_unsigned_to_nat(0u);
v_isZero_242_ = lean_nat_dec_eq(v_a_237_, v_zero_241_);
if (v_isZero_242_ == 1)
{
lean_object* v___x_243_; 
lean_dec(v_tail_240_);
lean_dec(v_head_239_);
lean_dec(v_a_237_);
v___x_243_ = lean_array_to_list(v_a_238_);
return v___x_243_;
}
else
{
lean_object* v_one_244_; lean_object* v_n_245_; lean_object* v___x_246_; 
v_one_244_ = lean_unsigned_to_nat(1u);
v_n_245_ = lean_nat_sub(v_a_237_, v_one_244_);
lean_dec(v_a_237_);
v___x_246_ = lean_array_push(v_a_238_, v_head_239_);
v_a_236_ = v_tail_240_;
v_a_237_ = v_n_245_;
v_a_238_ = v___x_246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(lean_object* v_l_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_l_248_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object* v_00_u03b1_253_, lean_object* v_l_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_254_, v_a_255_, v_a_256_, v_a_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(lean_object* v_00_u03b1_259_, lean_object* v_l_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(v_00_u03b1_259_, v_l_260_, v_a_261_, v_a_262_, v_a_263_);
lean_dec(v_l_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR___redArg(lean_object* v_n_265_, lean_object* v_l_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_266_);
v___x_268_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_266_, v_l_266_, v_n_265_, v___x_267_);
lean_dec(v_l_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR(lean_object* v_00_u03b1_269_, lean_object* v_n_270_, lean_object* v_l_271_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_271_);
v___x_273_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_271_, v_l_271_, v_n_270_, v___x_272_);
lean_dec(v_l_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object* v_p_274_, lean_object* v_l_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
if (lean_obj_tag(v_a_276_) == 0)
{
lean_dec_ref(v_a_277_);
lean_dec_ref(v_p_274_);
lean_inc(v_l_275_);
return v_l_275_;
}
else
{
lean_object* v_head_278_; lean_object* v_tail_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_head_278_ = lean_ctor_get(v_a_276_, 0);
lean_inc_n(v_head_278_, 2);
v_tail_279_ = lean_ctor_get(v_a_276_, 1);
lean_inc(v_tail_279_);
lean_dec_ref_known(v_a_276_, 2);
lean_inc_ref(v_p_274_);
v___x_280_ = lean_apply_1(v_p_274_, v_head_278_);
v___x_281_ = lean_unbox(v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_dec(v_tail_279_);
lean_dec(v_head_278_);
lean_dec_ref(v_p_274_);
v___x_282_ = lean_array_to_list(v_a_277_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
v___x_283_ = lean_array_push(v_a_277_, v_head_278_);
v_a_276_ = v_tail_279_;
v_a_277_ = v___x_283_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object* v_p_285_, lean_object* v_l_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_285_, v_l_286_, v_a_287_, v_a_288_);
lean_dec(v_l_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object* v_00_u03b1_290_, lean_object* v_p_291_, lean_object* v_l_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_291_, v_l_292_, v_a_293_, v_a_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object* v_00_u03b1_296_, lean_object* v_p_297_, lean_object* v_l_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(v_00_u03b1_296_, v_p_297_, v_l_298_, v_a_299_, v_a_300_);
lean_dec(v_l_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object* v_p_302_, lean_object* v_l_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_303_);
v___x_305_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_302_, v_l_303_, v_l_303_, v___x_304_);
lean_dec(v_l_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object* v_00_u03b1_306_, lean_object* v_p_307_, lean_object* v_l_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_308_);
v___x_310_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_307_, v_l_308_, v_l_308_, v___x_309_);
lean_dec(v_l_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t v_x_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
if (v_x_311_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_h__1_312_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_1(v_h__2_313_, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_h__2_313_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v_h__1_312_, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_318_, lean_object* v_h__1_319_, lean_object* v_h__2_320_){
_start:
{
uint8_t v_x_24__boxed_321_; lean_object* v_res_322_; 
v_x_24__boxed_321_ = lean_unbox(v_x_318_);
v_res_322_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_321_, v_h__1_319_, v_h__2_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object* v_motive_323_, uint8_t v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_){
_start:
{
if (v_x_324_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_h__1_325_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_1(v_h__2_326_, v___x_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_h__2_326_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_h__1_325_, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_331_, lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
uint8_t v_x_35__boxed_335_; lean_object* v_res_336_; 
v_x_35__boxed_335_ = lean_unbox(v_x_332_);
v_res_336_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(v_motive_331_, v_x_35__boxed_335_, v_h__1_333_, v_h__2_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR___redArg(lean_object* v_l_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_array_mk(v_l_337_);
v___x_339_ = lean_array_pop(v___x_338_);
v___x_340_ = lean_array_to_list(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR(lean_object* v_00_u03b1_341_, lean_object* v_l_342_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_array_mk(v_l_342_);
v___x_344_ = lean_array_pop(v___x_343_);
v___x_345_ = lean_array_to_list(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(lean_object* v_p_346_, lean_object* v_x_347_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_348_; 
lean_dec_ref(v_p_346_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v_head_349_; lean_object* v_tail_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_head_349_ = lean_ctor_get(v_x_347_, 0);
lean_inc_n(v_head_349_, 2);
v_tail_350_ = lean_ctor_get(v_x_347_, 1);
lean_inc(v_tail_350_);
lean_dec_ref_known(v_x_347_, 2);
lean_inc_ref(v_p_346_);
v___x_351_ = lean_apply_1(v_p_346_, v_head_349_);
v___x_352_ = lean_unbox(v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_head_349_);
v_x_347_ = v_tail_350_;
goto _start;
}
else
{
lean_object* v___x_354_; 
lean_dec(v_tail_350_);
lean_dec_ref(v_p_346_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_head_349_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object* v_p_355_, lean_object* v_l_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_List_reverse___redArg(v_l_356_);
v___x_358_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_355_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object* v_00_u03b1_359_, lean_object* v_p_360_, lean_object* v_l_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_List_findRev_x3fTR___redArg(v_p_360_, v_l_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(lean_object* v_00_u03b1_363_, lean_object* v_p_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_364_, v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v_h__1_368_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_apply_1(v_h__2_369_, v___x_370_);
return v___x_371_;
}
else
{
lean_object* v_val_372_; lean_object* v___x_373_; 
lean_dec(v_h__2_369_);
v_val_372_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v_x_367_, 1);
v___x_373_ = lean_apply_1(v_h__1_368_, v_val_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_374_, lean_object* v_motive_375_, lean_object* v_x_376_, lean_object* v_h__1_377_, lean_object* v_h__2_378_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_h__1_377_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_apply_1(v_h__2_378_, v___x_379_);
return v___x_380_;
}
else
{
lean_object* v_val_381_; lean_object* v___x_382_; 
lean_dec(v_h__2_378_);
v_val_381_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v_x_376_, 1);
v___x_382_ = lean_apply_1(v_h__1_377_, v_val_381_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(lean_object* v_f_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_385_; 
lean_dec_ref(v_f_383_);
v___x_385_ = lean_box(0);
return v___x_385_;
}
else
{
lean_object* v_head_386_; lean_object* v_tail_387_; lean_object* v___x_388_; 
v_head_386_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_head_386_);
v_tail_387_ = lean_ctor_get(v_x_384_, 1);
lean_inc(v_tail_387_);
lean_dec_ref_known(v_x_384_, 2);
lean_inc_ref(v_f_383_);
v___x_388_ = lean_apply_1(v_f_383_, v_head_386_);
if (lean_obj_tag(v___x_388_) == 0)
{
v_x_384_ = v_tail_387_;
goto _start;
}
else
{
lean_dec(v_tail_387_);
lean_dec_ref(v_f_383_);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object* v_f_390_, lean_object* v_l_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = l_List_reverse___redArg(v_l_391_);
v___x_393_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_390_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_f_396_, lean_object* v_l_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_List_findSomeRev_x3fTR___redArg(v_f_396_, v_l_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_f_401_, lean_object* v_x_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_401_, v_x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object* v_x1_404_, lean_object* v_x2_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v_x1_404_);
lean_ctor_set(v___x_406_, 1, v_x2_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object* v_inst_408_, lean_object* v_l_409_, lean_object* v_b_410_, lean_object* v_c_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
if (lean_obj_tag(v_a_412_) == 0)
{
lean_dec_ref(v_a_413_);
lean_dec(v_c_411_);
lean_dec(v_b_410_);
lean_dec_ref(v_inst_408_);
lean_inc(v_l_409_);
return v_l_409_;
}
else
{
lean_object* v_head_414_; lean_object* v_tail_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_434_; 
v_head_414_ = lean_ctor_get(v_a_412_, 0);
v_tail_415_ = lean_ctor_get(v_a_412_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_412_);
if (v_isSharedCheck_434_ == 0)
{
v___x_417_ = v_a_412_;
v_isShared_418_ = v_isSharedCheck_434_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_tail_415_);
lean_inc(v_head_414_);
lean_dec(v_a_412_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_434_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
lean_inc_ref(v_inst_408_);
lean_inc(v_head_414_);
lean_inc(v_b_410_);
v___x_419_ = lean_apply_2(v_inst_408_, v_b_410_, v_head_414_);
v___x_420_ = lean_unbox(v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_del_object(v___x_417_);
v___x_421_ = lean_array_push(v_a_413_, v_head_414_);
v_a_412_ = v_tail_415_;
v_a_413_ = v___x_421_;
goto _start;
}
else
{
lean_object* v___x_424_; 
lean_dec(v_head_414_);
lean_dec(v_b_410_);
lean_dec_ref(v_inst_408_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v_c_411_);
v___x_424_ = v___x_417_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_c_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_tail_415_);
v___x_424_ = v_reuseFailAlloc_433_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_425_ = lean_array_get_size(v_a_413_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_428_ = lean_nat_dec_lt(v___x_426_, v___x_425_);
if (v___x_428_ == 0)
{
lean_dec_ref(v_a_413_);
return v___x_424_;
}
else
{
lean_object* v___f_429_; size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___f_429_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_430_ = lean_usize_of_nat(v___x_425_);
v___x_431_ = ((size_t)0ULL);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_427_, v___f_429_, v_a_413_, v___x_430_, v___x_431_, v___x_424_);
return v___x_432_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object* v_inst_435_, lean_object* v_l_436_, lean_object* v_b_437_, lean_object* v_c_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_435_, v_l_436_, v_b_437_, v_c_438_, v_a_439_, v_a_440_);
lean_dec(v_l_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object* v_00_u03b1_442_, lean_object* v_inst_443_, lean_object* v_l_444_, lean_object* v_b_445_, lean_object* v_c_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_443_, v_l_444_, v_b_445_, v_c_446_, v_a_447_, v_a_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object* v_00_u03b1_450_, lean_object* v_inst_451_, lean_object* v_l_452_, lean_object* v_b_453_, lean_object* v_c_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(v_00_u03b1_450_, v_inst_451_, v_l_452_, v_b_453_, v_c_454_, v_a_455_, v_a_456_);
lean_dec(v_l_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object* v_inst_458_, lean_object* v_l_459_, lean_object* v_b_460_, lean_object* v_c_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_459_);
v___x_463_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_458_, v_l_459_, v_b_460_, v_c_461_, v_l_459_, v___x_462_);
lean_dec(v_l_459_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object* v_00_u03b1_464_, lean_object* v_inst_465_, lean_object* v_l_466_, lean_object* v_b_467_, lean_object* v_c_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_466_);
v___x_470_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_465_, v_l_466_, v_b_467_, v_c_468_, v_l_466_, v___x_469_);
lean_dec(v_l_466_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object* v_f_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_object* v___x_475_; 
lean_dec(v_a_473_);
lean_dec(v_f_471_);
v___x_475_ = lean_array_to_list(v_a_474_);
return v___x_475_;
}
else
{
lean_object* v_head_476_; lean_object* v_tail_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_496_; 
v_head_476_ = lean_ctor_get(v_a_472_, 0);
v_tail_477_ = lean_ctor_get(v_a_472_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_496_ == 0)
{
v___x_479_ = v_a_472_;
v_isShared_480_ = v_isSharedCheck_496_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_tail_477_);
lean_inc(v_head_476_);
lean_dec(v_a_472_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_496_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_zero_481_; uint8_t v_isZero_482_; 
v_zero_481_ = lean_unsigned_to_nat(0u);
v_isZero_482_ = lean_nat_dec_eq(v_a_473_, v_zero_481_);
if (v_isZero_482_ == 1)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_a_473_);
v___x_483_ = lean_apply_1(v_f_471_, v_head_476_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_483_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_tail_477_);
v___x_485_ = v_reuseFailAlloc_491_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_array_get_size(v_a_474_);
v___x_487_ = lean_nat_dec_lt(v_zero_481_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec_ref(v_a_474_);
return v___x_485_;
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_usize_of_nat(v___x_486_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_474_, v___x_488_, v___x_489_, v___x_485_);
lean_dec_ref(v_a_474_);
return v___x_490_;
}
}
}
else
{
lean_object* v_one_492_; lean_object* v_n_493_; lean_object* v___x_494_; 
lean_del_object(v___x_479_);
v_one_492_ = lean_unsigned_to_nat(1u);
v_n_493_ = lean_nat_sub(v_a_473_, v_one_492_);
lean_dec(v_a_473_);
v___x_494_ = lean_array_push(v_a_474_, v_head_476_);
v_a_472_ = v_tail_477_;
v_a_473_ = v_n_493_;
v_a_474_ = v___x_494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object* v_00_u03b1_497_, lean_object* v_f_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object* v_l_503_, lean_object* v_i_504_, lean_object* v_f_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_507_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_505_, v_l_503_, v_i_504_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object* v_00_u03b1_508_, lean_object* v_l_509_, lean_object* v_i_510_, lean_object* v_f_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_List_modifyTR___redArg(v_l_509_, v_i_510_, v_f_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_zero_517_; uint8_t v_isZero_518_; 
v_zero_517_ = lean_unsigned_to_nat(0u);
v_isZero_518_ = lean_nat_dec_eq(v_a_514_, v_zero_517_);
if (v_isZero_518_ == 1)
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
lean_dec(v_a_514_);
v___x_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_519_, 0, v_a_513_);
lean_ctor_set(v___x_519_, 1, v_a_515_);
v___x_520_ = lean_array_get_size(v_a_516_);
v___x_521_ = lean_nat_dec_lt(v_zero_517_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec_ref(v_a_516_);
return v___x_519_;
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_usize_of_nat(v___x_520_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_516_, v___x_522_, v___x_523_, v___x_519_);
lean_dec_ref(v_a_516_);
return v___x_524_;
}
}
else
{
if (lean_obj_tag(v_a_515_) == 0)
{
lean_object* v___x_525_; 
lean_dec(v_a_514_);
lean_dec(v_a_513_);
v___x_525_ = lean_array_to_list(v_a_516_);
return v___x_525_;
}
else
{
lean_object* v_head_526_; lean_object* v_tail_527_; lean_object* v_one_528_; lean_object* v_n_529_; lean_object* v___x_530_; 
v_head_526_ = lean_ctor_get(v_a_515_, 0);
lean_inc(v_head_526_);
v_tail_527_ = lean_ctor_get(v_a_515_, 1);
lean_inc(v_tail_527_);
lean_dec_ref_known(v_a_515_, 2);
v_one_528_ = lean_unsigned_to_nat(1u);
v_n_529_ = lean_nat_sub(v_a_514_, v_one_528_);
lean_dec(v_a_514_);
v___x_530_ = lean_array_push(v_a_516_, v_head_526_);
v_a_514_ = v_n_529_;
v_a_515_ = v_tail_527_;
v_a_516_ = v___x_530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object* v_00_u03b1_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object* v_l_538_, lean_object* v_n_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_542_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_540_, v_n_539_, v_l_538_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object* v_00_u03b1_543_, lean_object* v_l_544_, lean_object* v_n_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_548_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_546_, v_n_545_, v_l_544_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_h__1_552_, lean_object* v_h__2_553_, lean_object* v_h__3_554_){
_start:
{
lean_object* v_zero_555_; uint8_t v_isZero_556_; 
v_zero_555_ = lean_unsigned_to_nat(0u);
v_isZero_556_ = lean_nat_dec_eq(v_x_549_, v_zero_555_);
if (v_isZero_556_ == 1)
{
lean_object* v___x_557_; 
lean_dec(v_h__3_554_);
lean_dec(v_h__2_553_);
lean_dec(v_x_549_);
v___x_557_ = lean_apply_2(v_h__1_552_, v_x_550_, v_x_551_);
return v___x_557_;
}
else
{
lean_dec(v_h__1_552_);
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v___x_558_; 
lean_dec(v_h__3_554_);
v___x_558_ = lean_apply_3(v_h__2_553_, v_x_549_, v_x_551_, lean_box(0));
return v___x_558_;
}
else
{
lean_object* v_head_559_; lean_object* v_tail_560_; lean_object* v_one_561_; lean_object* v_n_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_553_);
v_head_559_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_head_559_);
v_tail_560_ = lean_ctor_get(v_x_550_, 1);
lean_inc(v_tail_560_);
lean_dec_ref_known(v_x_550_, 2);
v_one_561_ = lean_unsigned_to_nat(1u);
v_n_562_ = lean_nat_sub(v_x_549_, v_one_561_);
lean_dec(v_x_549_);
v___x_563_ = lean_apply_4(v_h__3_554_, v_n_562_, v_head_559_, v_tail_560_, v_x_551_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object* v_00_u03b1_564_, lean_object* v_motive_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_, lean_object* v_h__3_571_){
_start:
{
lean_object* v_zero_572_; uint8_t v_isZero_573_; 
v_zero_572_ = lean_unsigned_to_nat(0u);
v_isZero_573_ = lean_nat_dec_eq(v_x_566_, v_zero_572_);
if (v_isZero_573_ == 1)
{
lean_object* v___x_574_; 
lean_dec(v_h__3_571_);
lean_dec(v_h__2_570_);
lean_dec(v_x_566_);
v___x_574_ = lean_apply_2(v_h__1_569_, v_x_567_, v_x_568_);
return v___x_574_;
}
else
{
lean_dec(v_h__1_569_);
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v___x_575_; 
lean_dec(v_h__3_571_);
v___x_575_ = lean_apply_3(v_h__2_570_, v_x_566_, v_x_568_, lean_box(0));
return v___x_575_;
}
else
{
lean_object* v_head_576_; lean_object* v_tail_577_; lean_object* v_one_578_; lean_object* v_n_579_; lean_object* v___x_580_; 
lean_dec(v_h__2_570_);
v_head_576_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_head_576_);
v_tail_577_ = lean_ctor_get(v_x_567_, 1);
lean_inc(v_tail_577_);
lean_dec_ref_known(v_x_567_, 2);
v_one_578_ = lean_unsigned_to_nat(1u);
v_n_579_ = lean_nat_sub(v_x_566_, v_one_578_);
lean_dec(v_x_566_);
v___x_580_ = lean_apply_4(v_h__3_571_, v_n_579_, v_head_576_, v_tail_577_, v_x_568_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object* v_inst_581_, lean_object* v_l_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
if (lean_obj_tag(v_a_584_) == 0)
{
lean_dec_ref(v_a_585_);
lean_dec(v_a_583_);
lean_dec_ref(v_inst_581_);
lean_inc(v_l_582_);
return v_l_582_;
}
else
{
lean_object* v_head_586_; lean_object* v_tail_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_head_586_ = lean_ctor_get(v_a_584_, 0);
lean_inc_n(v_head_586_, 2);
v_tail_587_ = lean_ctor_get(v_a_584_, 1);
lean_inc(v_tail_587_);
lean_dec_ref_known(v_a_584_, 2);
lean_inc_ref(v_inst_581_);
lean_inc(v_a_583_);
v___x_588_ = lean_apply_2(v_inst_581_, v_head_586_, v_a_583_);
v___x_589_ = lean_unbox(v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_array_push(v_a_585_, v_head_586_);
v_a_584_ = v_tail_587_;
v_a_585_ = v___x_590_;
goto _start;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
lean_dec(v_head_586_);
lean_dec(v_a_583_);
lean_dec_ref(v_inst_581_);
v___x_592_ = lean_array_get_size(v_a_585_);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_595_ = lean_nat_dec_lt(v___x_593_, v___x_592_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_a_585_);
return v_tail_587_;
}
else
{
lean_object* v___f_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___f_596_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_597_ = lean_usize_of_nat(v___x_592_);
v___x_598_ = ((size_t)0ULL);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_594_, v___f_596_, v_a_585_, v___x_597_, v___x_598_, v_tail_587_);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object* v_inst_600_, lean_object* v_l_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_600_, v_l_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_l_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object* v_00_u03b1_606_, lean_object* v_inst_607_, lean_object* v_l_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_607_, v_l_608_, v_a_609_, v_a_610_, v_a_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object* v_00_u03b1_613_, lean_object* v_inst_614_, lean_object* v_l_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(v_00_u03b1_613_, v_inst_614_, v_l_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_l_615_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object* v_inst_620_, lean_object* v_l_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_621_);
v___x_624_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_620_, v_l_621_, v_a_622_, v_l_621_, v___x_623_);
lean_dec(v_l_621_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object* v_00_u03b1_625_, lean_object* v_inst_626_, lean_object* v_l_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_627_);
v___x_630_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_626_, v_l_627_, v_a_628_, v_l_627_, v___x_629_);
lean_dec(v_l_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object* v_p_631_, lean_object* v_l_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
if (lean_obj_tag(v_a_633_) == 0)
{
lean_dec_ref(v_a_634_);
lean_dec_ref(v_p_631_);
lean_inc(v_l_632_);
return v_l_632_;
}
else
{
lean_object* v_head_635_; lean_object* v_tail_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_head_635_ = lean_ctor_get(v_a_633_, 0);
lean_inc_n(v_head_635_, 2);
v_tail_636_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_tail_636_);
lean_dec_ref_known(v_a_633_, 2);
lean_inc_ref(v_p_631_);
v___x_637_ = lean_apply_1(v_p_631_, v_head_635_);
v___x_638_ = lean_unbox(v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = lean_array_push(v_a_634_, v_head_635_);
v_a_633_ = v_tail_636_;
v_a_634_ = v___x_639_;
goto _start;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_dec(v_head_635_);
lean_dec_ref(v_p_631_);
v___x_641_ = lean_array_get_size(v_a_634_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_641_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_a_634_);
return v_tail_636_;
}
else
{
lean_object* v___f_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___f_645_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_646_ = lean_usize_of_nat(v___x_641_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_643_, v___f_645_, v_a_634_, v___x_646_, v___x_647_, v_tail_636_);
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object* v_p_649_, lean_object* v_l_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_649_, v_l_650_, v_a_651_, v_a_652_);
lean_dec(v_l_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object* v_00_u03b1_654_, lean_object* v_p_655_, lean_object* v_l_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_655_, v_l_656_, v_a_657_, v_a_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object* v_00_u03b1_660_, lean_object* v_p_661_, lean_object* v_l_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(v_00_u03b1_660_, v_p_661_, v_l_662_, v_a_663_, v_a_664_);
lean_dec(v_l_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object* v_p_666_, lean_object* v_l_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_667_);
v___x_669_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_666_, v_l_667_, v_l_667_, v___x_668_);
lean_dec(v_l_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object* v_00_u03b1_670_, lean_object* v_p_671_, lean_object* v_l_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_672_);
v___x_674_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_671_, v_l_672_, v_l_672_, v___x_673_);
lean_dec(v_l_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object* v_l_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
if (lean_obj_tag(v_a_676_) == 0)
{
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_inc(v_l_675_);
return v_l_675_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v_zero_681_; uint8_t v_isZero_682_; 
v_head_679_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_head_679_);
v_tail_680_ = lean_ctor_get(v_a_676_, 1);
lean_inc(v_tail_680_);
lean_dec_ref_known(v_a_676_, 2);
v_zero_681_ = lean_unsigned_to_nat(0u);
v_isZero_682_ = lean_nat_dec_eq(v_a_677_, v_zero_681_);
if (v_isZero_682_ == 1)
{
lean_object* v___x_683_; uint8_t v___x_684_; 
lean_dec(v_head_679_);
lean_dec(v_a_677_);
v___x_683_ = lean_array_get_size(v_a_678_);
v___x_684_ = lean_nat_dec_lt(v_zero_681_, v___x_683_);
if (v___x_684_ == 0)
{
lean_dec_ref(v_a_678_);
return v_tail_680_;
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_usize_of_nat(v___x_683_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_678_, v___x_685_, v___x_686_, v_tail_680_);
lean_dec_ref(v_a_678_);
return v___x_687_;
}
}
else
{
lean_object* v_one_688_; lean_object* v_n_689_; lean_object* v___x_690_; 
v_one_688_ = lean_unsigned_to_nat(1u);
v_n_689_ = lean_nat_sub(v_a_677_, v_one_688_);
lean_dec(v_a_677_);
v___x_690_ = lean_array_push(v_a_678_, v_head_679_);
v_a_676_ = v_tail_680_;
v_a_677_ = v_n_689_;
v_a_678_ = v___x_690_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object* v_l_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_l_692_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object* v_00_u03b1_697_, lean_object* v_l_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_698_, v_a_699_, v_a_700_, v_a_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object* v_00_u03b1_703_, lean_object* v_l_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(v_00_u03b1_703_, v_l_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_l_704_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object* v_l_709_, lean_object* v_n_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_709_);
v___x_712_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_709_, v_l_709_, v_n_710_, v___x_711_);
lean_dec(v_l_709_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object* v_00_u03b1_713_, lean_object* v_l_714_, lean_object* v_n_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_714_);
v___x_717_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_714_, v_l_714_, v_n_715_, v___x_716_);
lean_dec(v_l_714_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object* v_f_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
if (lean_obj_tag(v_a_719_) == 1)
{
if (lean_obj_tag(v_a_720_) == 1)
{
lean_object* v_head_722_; lean_object* v_tail_723_; lean_object* v_head_724_; lean_object* v_tail_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_head_722_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_head_722_);
v_tail_723_ = lean_ctor_get(v_a_719_, 1);
lean_inc(v_tail_723_);
lean_dec_ref_known(v_a_719_, 2);
v_head_724_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_head_724_);
v_tail_725_ = lean_ctor_get(v_a_720_, 1);
lean_inc(v_tail_725_);
lean_dec_ref_known(v_a_720_, 2);
lean_inc(v_f_718_);
v___x_726_ = lean_apply_2(v_f_718_, v_head_722_, v_head_724_);
v___x_727_ = lean_array_push(v_a_721_, v___x_726_);
v_a_719_ = v_tail_723_;
v_a_720_ = v_tail_725_;
v_a_721_ = v___x_727_;
goto _start;
}
else
{
lean_object* v___x_729_; 
lean_dec_ref_known(v_a_719_, 2);
lean_dec(v_a_720_);
lean_dec(v_f_718_);
v___x_729_ = lean_array_to_list(v_a_721_);
return v___x_729_;
}
}
else
{
lean_object* v___x_730_; 
lean_dec(v_a_720_);
lean_dec(v_a_719_);
lean_dec(v_f_718_);
v___x_730_ = lean_array_to_list(v_a_721_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_00_u03b3_733_, lean_object* v_f_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object* v_f_739_, lean_object* v_as_740_, lean_object* v_bs_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_743_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_739_, v_as_740_, v_bs_741_, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_00_u03b3_746_, lean_object* v_f_747_, lean_object* v_as_748_, lean_object* v_bs_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_751_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_747_, v_as_748_, v_bs_749_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_h__1_755_, lean_object* v_h__2_756_){
_start:
{
if (lean_obj_tag(v_x_752_) == 1)
{
if (lean_obj_tag(v_x_753_) == 1)
{
lean_object* v_head_757_; lean_object* v_tail_758_; lean_object* v_head_759_; lean_object* v_tail_760_; lean_object* v___x_761_; 
lean_dec(v_h__2_756_);
v_head_757_ = lean_ctor_get(v_x_752_, 0);
lean_inc(v_head_757_);
v_tail_758_ = lean_ctor_get(v_x_752_, 1);
lean_inc(v_tail_758_);
lean_dec_ref_known(v_x_752_, 2);
v_head_759_ = lean_ctor_get(v_x_753_, 0);
lean_inc(v_head_759_);
v_tail_760_ = lean_ctor_get(v_x_753_, 1);
lean_inc(v_tail_760_);
lean_dec_ref_known(v_x_753_, 2);
v___x_761_ = lean_apply_5(v_h__1_755_, v_head_757_, v_tail_758_, v_head_759_, v_tail_760_, v_x_754_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; 
lean_dec(v_h__1_755_);
v___x_762_ = lean_apply_4(v_h__2_756_, v_x_752_, v_x_753_, v_x_754_, lean_box(0));
return v___x_762_;
}
}
else
{
lean_object* v___x_763_; 
lean_dec(v_h__1_755_);
v___x_763_ = lean_apply_4(v_h__2_756_, v_x_752_, v_x_753_, v_x_754_, lean_box(0));
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object* v_00_u03b1_764_, lean_object* v_00_u03b2_765_, lean_object* v_00_u03b3_766_, lean_object* v_motive_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_h__1_771_, lean_object* v_h__2_772_){
_start:
{
if (lean_obj_tag(v_x_768_) == 1)
{
if (lean_obj_tag(v_x_769_) == 1)
{
lean_object* v_head_773_; lean_object* v_tail_774_; lean_object* v_head_775_; lean_object* v_tail_776_; lean_object* v___x_777_; 
lean_dec(v_h__2_772_);
v_head_773_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_head_773_);
v_tail_774_ = lean_ctor_get(v_x_768_, 1);
lean_inc(v_tail_774_);
lean_dec_ref_known(v_x_768_, 2);
v_head_775_ = lean_ctor_get(v_x_769_, 0);
lean_inc(v_head_775_);
v_tail_776_ = lean_ctor_get(v_x_769_, 1);
lean_inc(v_tail_776_);
lean_dec_ref_known(v_x_769_, 2);
v___x_777_ = lean_apply_5(v_h__1_771_, v_head_773_, v_tail_774_, v_head_775_, v_tail_776_, v_x_770_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; 
lean_dec(v_h__1_771_);
v___x_778_ = lean_apply_4(v_h__2_772_, v_x_768_, v_x_769_, v_x_770_, lean_box(0));
return v___x_778_;
}
}
else
{
lean_object* v___x_779_; 
lean_dec(v_h__1_771_);
v___x_779_ = lean_apply_4(v_h__2_772_, v_x_768_, v_x_769_, v_x_770_, lean_box(0));
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object* v_as_780_, size_t v_i_781_, size_t v_stop_782_, lean_object* v_b_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_eq(v_i_781_, v_stop_782_);
if (v___x_784_ == 0)
{
lean_object* v_fst_785_; lean_object* v_snd_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_801_; 
v_fst_785_ = lean_ctor_get(v_b_783_, 0);
v_snd_786_ = lean_ctor_get(v_b_783_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_783_);
if (v_isSharedCheck_801_ == 0)
{
v___x_788_ = v_b_783_;
v_isShared_789_ = v_isSharedCheck_801_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snd_786_);
lean_inc(v_fst_785_);
lean_dec(v_b_783_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_801_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
size_t v___x_790_; size_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_sub(v_i_781_, v___x_790_);
v___x_792_ = lean_array_uget_borrowed(v_as_780_, v___x_791_);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_sub(v_fst_785_, v___x_793_);
lean_dec(v_fst_785_);
lean_inc(v___x_794_);
lean_inc(v___x_792_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_794_);
lean_ctor_set(v___x_788_, 0, v___x_792_);
v___x_796_ = v___x_788_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_800_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_snd_786_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_794_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v_i_781_ = v___x_791_;
v_b_783_ = v___x_798_;
goto _start;
}
}
}
else
{
return v_b_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object* v_as_802_, lean_object* v_i_803_, lean_object* v_stop_804_, lean_object* v_b_805_){
_start:
{
size_t v_i_boxed_806_; size_t v_stop_boxed_807_; lean_object* v_res_808_; 
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_stop_boxed_807_ = lean_unbox_usize(v_stop_804_);
lean_dec(v_stop_804_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_802_, v_i_boxed_806_, v_stop_boxed_807_, v_b_805_);
lean_dec_ref(v_as_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object* v_l_809_, lean_object* v_n_810_){
_start:
{
lean_object* v_as_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_as_811_ = lean_array_mk(v_l_809_);
v___x_812_ = lean_array_get_size(v_as_811_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_nat_dec_lt(v___x_814_, v___x_812_);
if (v___x_815_ == 0)
{
lean_dec_ref(v_as_811_);
return v___x_813_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v___x_820_; lean_object* v_snd_821_; 
v___x_816_ = lean_nat_add(v_n_810_, v___x_812_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_813_);
v___x_818_ = lean_usize_of_nat(v___x_812_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_811_, v___x_818_, v___x_819_, v___x_817_);
lean_dec_ref(v_as_811_);
v_snd_821_ = lean_ctor_get(v___x_820_, 1);
lean_inc(v_snd_821_);
lean_dec_ref(v___x_820_);
return v_snd_821_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object* v_l_822_, lean_object* v_n_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_List_zipIdxTR___redArg(v_l_822_, v_n_823_);
lean_dec(v_n_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object* v_00_u03b1_825_, lean_object* v_l_826_, lean_object* v_n_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_List_zipIdxTR___redArg(v_l_826_, v_n_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object* v_00_u03b1_829_, lean_object* v_l_830_, lean_object* v_n_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_List_zipIdxTR(v_00_u03b1_829_, v_l_830_, v_n_831_);
lean_dec(v_n_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object* v_00_u03b1_833_, lean_object* v_as_834_, size_t v_i_835_, size_t v_stop_836_, lean_object* v_b_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_834_, v_i_835_, v_stop_836_, v_b_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object* v_00_u03b1_839_, lean_object* v_as_840_, lean_object* v_i_841_, lean_object* v_stop_842_, lean_object* v_b_843_){
_start:
{
size_t v_i_boxed_844_; size_t v_stop_boxed_845_; lean_object* v_res_846_; 
v_i_boxed_844_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_stop_boxed_845_ = lean_unbox_usize(v_stop_842_);
lean_dec(v_stop_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(v_00_u03b1_839_, v_as_840_, v_i_boxed_844_, v_stop_boxed_845_, v_b_843_);
lean_dec_ref(v_as_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object* v_sep_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
if (lean_obj_tag(v_a_849_) == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_851_ = lean_array_get_size(v_a_850_);
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v___x_851_);
if (v___x_853_ == 0)
{
lean_dec_ref(v_a_850_);
return v_a_848_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_usize_of_nat(v___x_851_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_850_, v___x_854_, v___x_855_, v_a_848_);
lean_dec_ref(v_a_850_);
return v___x_856_;
}
}
else
{
lean_object* v_head_857_; lean_object* v_tail_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_head_857_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_head_857_);
v_tail_858_ = lean_ctor_get(v_a_849_, 1);
lean_inc(v_tail_858_);
lean_dec_ref_known(v_a_849_, 2);
v___x_859_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_850_, v_a_848_);
v___x_860_ = l_Array_append___redArg(v___x_859_, v_sep_847_);
v_a_848_ = v_head_857_;
v_a_849_ = v_tail_858_;
v_a_850_ = v___x_860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object* v_sep_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec_ref(v_sep_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object* v_00_u03b1_867_, lean_object* v_sep_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_868_, v_a_869_, v_a_870_, v_a_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object* v_00_u03b1_873_, lean_object* v_sep_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(v_00_u03b1_873_, v_sep_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec_ref(v_sep_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object* v_sep_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_object* v___x_881_; 
lean_dec(v_sep_879_);
v___x_881_ = lean_box(0);
return v___x_881_;
}
else
{
lean_object* v_tail_882_; 
v_tail_882_ = lean_ctor_get(v_x_880_, 1);
if (lean_obj_tag(v_tail_882_) == 0)
{
lean_object* v_head_883_; 
lean_dec(v_sep_879_);
v_head_883_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_head_883_);
lean_dec_ref_known(v_x_880_, 2);
return v_head_883_;
}
else
{
lean_object* v_head_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_inc(v_tail_882_);
v_head_884_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_head_884_);
lean_dec_ref_known(v_x_880_, 2);
v___x_885_ = lean_array_mk(v_sep_879_);
v___x_886_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_887_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v___x_885_, v_head_884_, v_tail_882_, v___x_886_);
lean_dec_ref(v___x_885_);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object* v_00_u03b1_888_, lean_object* v_sep_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_List_intercalateTR___redArg(v_sep_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object* v_x_892_, lean_object* v_h__1_893_, lean_object* v_h__2_894_, lean_object* v_h__3_895_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_h__3_895_);
lean_dec(v_h__2_894_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_apply_1(v_h__1_893_, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_tail_898_; 
lean_dec(v_h__1_893_);
v_tail_898_ = lean_ctor_get(v_x_892_, 1);
if (lean_obj_tag(v_tail_898_) == 0)
{
lean_object* v_head_899_; lean_object* v___x_900_; 
lean_dec(v_h__3_895_);
v_head_899_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_head_899_);
lean_dec_ref_known(v_x_892_, 2);
v___x_900_ = lean_apply_1(v_h__2_894_, v_head_899_);
return v___x_900_;
}
else
{
lean_object* v_head_901_; lean_object* v___x_902_; 
lean_inc(v_tail_898_);
lean_dec(v_h__2_894_);
v_head_901_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_head_901_);
lean_dec_ref_known(v_x_892_, 2);
v___x_902_ = lean_apply_3(v_h__3_895_, v_head_901_, v_tail_898_, lean_box(0));
return v___x_902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object* v_00_u03b1_903_, lean_object* v_motive_904_, lean_object* v_x_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_, lean_object* v_h__3_908_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_h__3_908_);
lean_dec(v_h__2_907_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_apply_1(v_h__1_906_, v___x_909_);
return v___x_910_;
}
else
{
lean_object* v_tail_911_; 
lean_dec(v_h__1_906_);
v_tail_911_ = lean_ctor_get(v_x_905_, 1);
if (lean_obj_tag(v_tail_911_) == 0)
{
lean_object* v_head_912_; lean_object* v___x_913_; 
lean_dec(v_h__3_908_);
v_head_912_ = lean_ctor_get(v_x_905_, 0);
lean_inc(v_head_912_);
lean_dec_ref_known(v_x_905_, 2);
v___x_913_ = lean_apply_1(v_h__2_907_, v_head_912_);
return v___x_913_;
}
else
{
lean_object* v_head_914_; lean_object* v___x_915_; 
lean_inc(v_tail_911_);
lean_dec(v_h__2_907_);
v_head_914_ = lean_ctor_get(v_x_905_, 0);
lean_inc(v_head_914_);
lean_dec_ref_known(v_x_905_, 2);
v___x_915_ = lean_apply_3(v_h__3_908_, v_head_914_, v_tail_911_, lean_box(0));
return v___x_915_;
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
