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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter___redArg(lean_object* v_x_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_h__3_95_);
lean_dec(v_h__2_94_);
v___x_96_ = lean_apply_2(v_h__1_93_, v_x_91_, v_x_92_);
return v___x_96_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v_zero_99_; uint8_t v_isZero_100_; 
lean_dec(v_h__1_93_);
v_head_97_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_head_97_);
v_tail_98_ = lean_ctor_get(v_x_90_, 1);
lean_inc(v_tail_98_);
lean_dec_ref(v_x_90_);
v_zero_99_ = lean_unsigned_to_nat(0u);
v_isZero_100_ = lean_nat_dec_eq(v_x_91_, v_zero_99_);
if (v_isZero_100_ == 1)
{
lean_object* v___x_101_; 
lean_dec(v_h__3_95_);
lean_dec(v_x_91_);
v___x_101_ = lean_apply_3(v_h__2_94_, v_head_97_, v_tail_98_, v_x_92_);
return v___x_101_;
}
else
{
lean_object* v_one_102_; lean_object* v_n_103_; lean_object* v___x_104_; 
lean_dec(v_h__2_94_);
v_one_102_ = lean_unsigned_to_nat(1u);
v_n_103_ = lean_nat_sub(v_x_91_, v_one_102_);
lean_dec(v_x_91_);
v___x_104_ = lean_apply_4(v_h__3_95_, v_head_97_, v_tail_98_, v_n_103_, v_x_92_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter(lean_object* v_00_u03b1_105_, lean_object* v_motive_106_, lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_, lean_object* v_h__3_112_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_113_; 
lean_dec(v_h__3_112_);
lean_dec(v_h__2_111_);
v___x_113_ = lean_apply_2(v_h__1_110_, v_x_108_, v_x_109_);
return v___x_113_;
}
else
{
lean_object* v_head_114_; lean_object* v_tail_115_; lean_object* v_zero_116_; uint8_t v_isZero_117_; 
lean_dec(v_h__1_110_);
v_head_114_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_head_114_);
v_tail_115_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_tail_115_);
lean_dec_ref(v_x_107_);
v_zero_116_ = lean_unsigned_to_nat(0u);
v_isZero_117_ = lean_nat_dec_eq(v_x_108_, v_zero_116_);
if (v_isZero_117_ == 1)
{
lean_object* v___x_118_; 
lean_dec(v_h__3_112_);
lean_dec(v_x_108_);
v___x_118_ = lean_apply_3(v_h__2_111_, v_head_114_, v_tail_115_, v_x_109_);
return v___x_118_;
}
else
{
lean_object* v_one_119_; lean_object* v_n_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_111_);
v_one_119_ = lean_unsigned_to_nat(1u);
v_n_120_ = lean_nat_sub(v_x_108_, v_one_119_);
lean_dec(v_x_108_);
v___x_121_ = lean_apply_4(v_h__3_112_, v_head_114_, v_tail_115_, v_n_120_, v_x_109_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___redArg(lean_object* v_f_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
if (lean_obj_tag(v_a_123_) == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v_f_122_);
v___x_125_ = lean_array_to_list(v_a_124_);
return v___x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_128_; 
v_head_126_ = lean_ctor_get(v_a_123_, 0);
lean_inc(v_head_126_);
v_tail_127_ = lean_ctor_get(v_a_123_, 1);
lean_inc(v_tail_127_);
lean_dec_ref(v_a_123_);
lean_inc_ref(v_f_122_);
v___x_128_ = lean_apply_1(v_f_122_, v_head_126_);
if (lean_obj_tag(v___x_128_) == 0)
{
v_a_123_ = v_tail_127_;
goto _start;
}
else
{
lean_object* v_val_130_; lean_object* v___x_131_; 
v_val_130_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_val_130_);
lean_dec_ref(v___x_128_);
v___x_131_ = lean_array_push(v_a_124_, v_val_130_);
v_a_123_ = v_tail_127_;
v_a_124_ = v___x_131_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_f_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_List_filterMapTR_go___redArg(v_f_135_, v_a_136_, v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR___redArg(lean_object* v_f_139_, lean_object* v_l_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_142_ = l_List_filterMapTR_go___redArg(v_f_139_, v_l_140_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_f_145_, lean_object* v_l_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_148_ = l_List_filterMapTR_go___redArg(v_f_145_, v_l_146_, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_153_; 
lean_dec(v_h__2_152_);
v___x_153_ = lean_apply_1(v_h__1_151_, v_x_150_);
return v___x_153_;
}
else
{
lean_object* v_head_154_; lean_object* v_tail_155_; lean_object* v___x_156_; 
lean_dec(v_h__1_151_);
v_head_154_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_head_154_);
v_tail_155_ = lean_ctor_get(v_x_149_, 1);
lean_inc(v_tail_155_);
lean_dec_ref(v_x_149_);
v___x_156_ = lean_apply_3(v_h__2_152_, v_head_154_, v_tail_155_, v_x_150_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_motive_159_, lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_h__1_162_, lean_object* v_h__2_163_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_164_; 
lean_dec(v_h__2_163_);
v___x_164_ = lean_apply_1(v_h__1_162_, v_x_161_);
return v___x_164_;
}
else
{
lean_object* v_head_165_; lean_object* v_tail_166_; lean_object* v___x_167_; 
lean_dec(v_h__1_162_);
v_head_165_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_head_165_);
v_tail_166_ = lean_ctor_get(v_x_160_, 1);
lean_inc(v_tail_166_);
lean_dec_ref(v_x_160_);
v___x_167_ = lean_apply_3(v_h__2_163_, v_head_165_, v_tail_166_, v_x_161_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(lean_object* v_x_168_, lean_object* v_h__1_169_, lean_object* v_h__2_170_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_h__2_170_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_1(v_h__1_169_, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v___x_174_; 
lean_dec(v_h__1_169_);
v_val_173_ = lean_ctor_get(v_x_168_, 0);
lean_inc(v_val_173_);
lean_dec_ref(v_x_168_);
v___x_174_ = lean_apply_1(v_h__2_170_, v_val_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(lean_object* v_00_u03b2_175_, lean_object* v_motive_176_, lean_object* v_x_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec(v_h__2_179_);
v___x_180_ = lean_box(0);
v___x_181_ = lean_apply_1(v_h__1_178_, v___x_180_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_183_; 
lean_dec(v_h__1_178_);
v_val_182_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v_x_177_);
v___x_183_ = lean_apply_1(v_h__2_179_, v_val_182_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_184_, lean_object* v_h__1_185_, lean_object* v_h__2_186_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_h__2_186_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_1(v_h__1_185_, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v_val_189_; lean_object* v___x_190_; 
lean_dec(v_h__1_185_);
v_val_189_ = lean_ctor_get(v_x_184_, 0);
lean_inc(v_val_189_);
lean_dec_ref(v_x_184_);
v___x_190_ = lean_apply_1(v_h__2_186_, v_val_189_);
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_191_, lean_object* v_motive_192_, lean_object* v_x_193_, lean_object* v_h__1_194_, lean_object* v_h__2_195_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec(v_h__2_195_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_apply_1(v_h__1_194_, v___x_196_);
return v___x_197_;
}
else
{
lean_object* v_val_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_194_);
v_val_198_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_val_198_);
lean_dec_ref(v_x_193_);
v___x_199_ = lean_apply_1(v_h__2_195_, v_val_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_List_reduceOption___redArg(lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_203_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_204_ = l_List_filterMapTR_go___redArg(v___x_202_, v_a_201_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object* v_00_u03b1_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_208_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_209_ = l_List_filterMapTR_go___redArg(v___x_207_, v_a_206_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg___lam__0(lean_object* v_f_210_, lean_object* v_x1_211_, lean_object* v_x2_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_apply_2(v_f_210_, v_x1_211_, v_x2_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg(lean_object* v_f_233_, lean_object* v_init_234_, lean_object* v_l_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_236_ = lean_array_mk(v_l_235_);
v___x_237_ = lean_array_get_size(v___x_236_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_240_ = lean_nat_dec_lt(v___x_238_, v___x_237_);
if (v___x_240_ == 0)
{
lean_dec_ref(v___x_236_);
lean_dec(v_f_233_);
return v_init_234_;
}
else
{
lean_object* v___f_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; 
v___f_241_ = lean_alloc_closure((void*)(l_List_foldrTR___redArg___lam__0), 3, 1);
lean_closure_set(v___f_241_, 0, v_f_233_);
v___x_242_ = lean_usize_of_nat(v___x_237_);
v___x_243_ = ((size_t)0ULL);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_239_, v___f_241_, v___x_236_, v___x_242_, v___x_243_, v_init_234_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_f_247_, lean_object* v_init_248_, lean_object* v_l_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_List_foldrTR___redArg(v_f_247_, v_init_248_, v_l_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object* v_f_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
if (lean_obj_tag(v_a_252_) == 0)
{
lean_object* v___x_254_; 
lean_dec_ref(v_f_251_);
v___x_254_ = lean_array_to_list(v_a_253_);
return v___x_254_;
}
else
{
lean_object* v_head_255_; lean_object* v_tail_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_head_255_ = lean_ctor_get(v_a_252_, 0);
lean_inc(v_head_255_);
v_tail_256_ = lean_ctor_get(v_a_252_, 1);
lean_inc(v_tail_256_);
lean_dec_ref(v_a_252_);
lean_inc_ref(v_f_251_);
v___x_257_ = lean_apply_1(v_f_251_, v_head_255_);
v___x_258_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_253_, v___x_257_);
v_a_252_ = v_tail_256_;
v_a_253_ = v___x_258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object* v_00_u03b1_260_, lean_object* v_00_u03b2_261_, lean_object* v_f_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_262_, v_a_263_, v_a_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR___redArg(lean_object* v_f_266_, lean_object* v_as_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_269_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_266_, v_as_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_f_272_, lean_object* v_as_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_275_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_272_, v_as_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR___redArg(lean_object* v_l_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_279_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_280_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_278_, v_l_277_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR(lean_object* v_00_u03b1_281_, lean_object* v_l_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_284_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_285_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_283_, v_l_282_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object* v_l_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
if (lean_obj_tag(v_a_287_) == 0)
{
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_inc(v_l_286_);
return v_l_286_;
}
else
{
lean_object* v_head_290_; lean_object* v_tail_291_; lean_object* v_zero_292_; uint8_t v_isZero_293_; 
v_head_290_ = lean_ctor_get(v_a_287_, 0);
lean_inc(v_head_290_);
v_tail_291_ = lean_ctor_get(v_a_287_, 1);
lean_inc(v_tail_291_);
lean_dec_ref(v_a_287_);
v_zero_292_ = lean_unsigned_to_nat(0u);
v_isZero_293_ = lean_nat_dec_eq(v_a_288_, v_zero_292_);
if (v_isZero_293_ == 1)
{
lean_object* v___x_294_; 
lean_dec(v_tail_291_);
lean_dec(v_head_290_);
lean_dec(v_a_288_);
v___x_294_ = lean_array_to_list(v_a_289_);
return v___x_294_;
}
else
{
lean_object* v_one_295_; lean_object* v_n_296_; lean_object* v___x_297_; 
v_one_295_ = lean_unsigned_to_nat(1u);
v_n_296_ = lean_nat_sub(v_a_288_, v_one_295_);
lean_dec(v_a_288_);
v___x_297_ = lean_array_push(v_a_289_, v_head_290_);
v_a_287_ = v_tail_291_;
v_a_288_ = v_n_296_;
v_a_289_ = v___x_297_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(lean_object* v_l_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_l_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object* v_00_u03b1_304_, lean_object* v_l_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_305_, v_a_306_, v_a_307_, v_a_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(lean_object* v_00_u03b1_310_, lean_object* v_l_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(v_00_u03b1_310_, v_l_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_l_311_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR___redArg(lean_object* v_n_316_, lean_object* v_l_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_317_);
v___x_319_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_317_, v_l_317_, v_n_316_, v___x_318_);
lean_dec(v_l_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR(lean_object* v_00_u03b1_320_, lean_object* v_n_321_, lean_object* v_l_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_322_);
v___x_324_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_322_, v_l_322_, v_n_321_, v___x_323_);
lean_dec(v_l_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_h__1_327_, lean_object* v_h__2_328_, lean_object* v_h__3_329_){
_start:
{
lean_object* v_zero_330_; uint8_t v_isZero_331_; 
v_zero_330_ = lean_unsigned_to_nat(0u);
v_isZero_331_ = lean_nat_dec_eq(v_x_325_, v_zero_330_);
if (v_isZero_331_ == 1)
{
lean_object* v___x_332_; 
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
v___x_332_ = lean_apply_1(v_h__1_327_, v_x_326_);
return v___x_332_;
}
else
{
lean_object* v_one_333_; lean_object* v_n_334_; 
lean_dec(v_h__1_327_);
v_one_333_ = lean_unsigned_to_nat(1u);
v_n_334_ = lean_nat_sub(v_x_325_, v_one_333_);
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v___x_335_; 
lean_dec(v_h__3_329_);
v___x_335_ = lean_apply_1(v_h__2_328_, v_n_334_);
return v___x_335_;
}
else
{
lean_object* v_head_336_; lean_object* v_tail_337_; lean_object* v___x_338_; 
lean_dec(v_h__2_328_);
v_head_336_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_head_336_);
v_tail_337_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_tail_337_);
lean_dec_ref(v_x_326_);
v___x_338_ = lean_apply_3(v_h__3_329_, v_n_334_, v_head_336_, v_tail_337_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_, lean_object* v_h__3_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(v_x_339_, v_x_340_, v_h__1_341_, v_h__2_342_, v_h__3_343_);
lean_dec(v_x_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(lean_object* v_00_u03b1_345_, lean_object* v_motive_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_h__1_349_, lean_object* v_h__2_350_, lean_object* v_h__3_351_){
_start:
{
lean_object* v_zero_352_; uint8_t v_isZero_353_; 
v_zero_352_ = lean_unsigned_to_nat(0u);
v_isZero_353_ = lean_nat_dec_eq(v_x_347_, v_zero_352_);
if (v_isZero_353_ == 1)
{
lean_object* v___x_354_; 
lean_dec(v_h__3_351_);
lean_dec(v_h__2_350_);
v___x_354_ = lean_apply_1(v_h__1_349_, v_x_348_);
return v___x_354_;
}
else
{
lean_object* v_one_355_; lean_object* v_n_356_; 
lean_dec(v_h__1_349_);
v_one_355_ = lean_unsigned_to_nat(1u);
v_n_356_ = lean_nat_sub(v_x_347_, v_one_355_);
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v___x_357_; 
lean_dec(v_h__3_351_);
v___x_357_ = lean_apply_1(v_h__2_350_, v_n_356_);
return v___x_357_;
}
else
{
lean_object* v_head_358_; lean_object* v_tail_359_; lean_object* v___x_360_; 
lean_dec(v_h__2_350_);
v_head_358_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_head_358_);
v_tail_359_ = lean_ctor_get(v_x_348_, 1);
lean_inc(v_tail_359_);
lean_dec_ref(v_x_348_);
v___x_360_ = lean_apply_3(v_h__3_351_, v_n_356_, v_head_358_, v_tail_359_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_361_, lean_object* v_motive_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_, lean_object* v_h__3_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(v_00_u03b1_361_, v_motive_362_, v_x_363_, v_x_364_, v_h__1_365_, v_h__2_366_, v_h__3_367_);
lean_dec(v_x_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object* v_p_369_, lean_object* v_l_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
if (lean_obj_tag(v_a_371_) == 0)
{
lean_dec_ref(v_a_372_);
lean_dec_ref(v_p_369_);
lean_inc(v_l_370_);
return v_l_370_;
}
else
{
lean_object* v_head_373_; lean_object* v_tail_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_head_373_ = lean_ctor_get(v_a_371_, 0);
lean_inc_n(v_head_373_, 2);
v_tail_374_ = lean_ctor_get(v_a_371_, 1);
lean_inc(v_tail_374_);
lean_dec_ref(v_a_371_);
lean_inc_ref(v_p_369_);
v___x_375_ = lean_apply_1(v_p_369_, v_head_373_);
v___x_376_ = lean_unbox(v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_tail_374_);
lean_dec(v_head_373_);
lean_dec_ref(v_p_369_);
v___x_377_ = lean_array_to_list(v_a_372_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_array_push(v_a_372_, v_head_373_);
v_a_371_ = v_tail_374_;
v_a_372_ = v___x_378_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object* v_p_380_, lean_object* v_l_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_380_, v_l_381_, v_a_382_, v_a_383_);
lean_dec(v_l_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object* v_00_u03b1_385_, lean_object* v_p_386_, lean_object* v_l_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_386_, v_l_387_, v_a_388_, v_a_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object* v_00_u03b1_391_, lean_object* v_p_392_, lean_object* v_l_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(v_00_u03b1_391_, v_p_392_, v_l_393_, v_a_394_, v_a_395_);
lean_dec(v_l_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object* v_p_397_, lean_object* v_l_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_398_);
v___x_400_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_397_, v_l_398_, v_l_398_, v___x_399_);
lean_dec(v_l_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object* v_00_u03b1_401_, lean_object* v_p_402_, lean_object* v_l_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_403_);
v___x_405_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_402_, v_l_403_, v_l_403_, v___x_404_);
lean_dec(v_l_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_406_, lean_object* v_h__1_407_, lean_object* v_h__2_408_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_h__2_408_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_1(v_h__1_407_, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v_head_411_; lean_object* v_tail_412_; lean_object* v___x_413_; 
lean_dec(v_h__1_407_);
v_head_411_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_head_411_);
v_tail_412_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_tail_412_);
lean_dec_ref(v_x_406_);
v___x_413_ = lean_apply_2(v_h__2_408_, v_head_411_, v_tail_412_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_414_, lean_object* v_motive_415_, lean_object* v_x_416_, lean_object* v_h__1_417_, lean_object* v_h__2_418_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_h__2_418_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_apply_1(v_h__1_417_, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v_head_421_; lean_object* v_tail_422_; lean_object* v___x_423_; 
lean_dec(v_h__1_417_);
v_head_421_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_head_421_);
v_tail_422_ = lean_ctor_get(v_x_416_, 1);
lean_inc(v_tail_422_);
lean_dec_ref(v_x_416_);
v___x_423_ = lean_apply_2(v_h__2_418_, v_head_421_, v_tail_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t v_x_424_, lean_object* v_h__1_425_, lean_object* v_h__2_426_){
_start:
{
if (v_x_424_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_h__1_425_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_apply_1(v_h__2_426_, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_h__2_426_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_1(v_h__1_425_, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_){
_start:
{
uint8_t v_x_26__boxed_434_; lean_object* v_res_435_; 
v_x_26__boxed_434_ = lean_unbox(v_x_431_);
v_res_435_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_434_, v_h__1_432_, v_h__2_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object* v_motive_436_, uint8_t v_x_437_, lean_object* v_h__1_438_, lean_object* v_h__2_439_){
_start:
{
if (v_x_437_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_h__1_438_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_apply_1(v_h__2_439_, v___x_440_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_h__2_439_);
v___x_442_ = lean_box(0);
v___x_443_ = lean_apply_1(v_h__1_438_, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_444_, lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
uint8_t v_x_37__boxed_448_; lean_object* v_res_449_; 
v_x_37__boxed_448_ = lean_unbox(v_x_445_);
v_res_449_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(v_motive_444_, v_x_37__boxed_448_, v_h__1_446_, v_h__2_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v___x_454_; 
lean_dec(v_h__2_453_);
v___x_454_ = lean_apply_1(v_h__1_452_, v_x_451_);
return v___x_454_;
}
else
{
lean_object* v_head_455_; lean_object* v_tail_456_; lean_object* v___x_457_; 
lean_dec(v_h__1_452_);
v_head_455_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_head_455_);
v_tail_456_ = lean_ctor_get(v_x_450_, 1);
lean_inc(v_tail_456_);
lean_dec_ref(v_x_450_);
v___x_457_ = lean_apply_3(v_h__2_453_, v_head_455_, v_tail_456_, v_x_451_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(lean_object* v_00_u03b1_458_, lean_object* v_motive_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_h__1_462_, lean_object* v_h__2_463_){
_start:
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v___x_464_; 
lean_dec(v_h__2_463_);
v___x_464_ = lean_apply_1(v_h__1_462_, v_x_461_);
return v___x_464_;
}
else
{
lean_object* v_head_465_; lean_object* v_tail_466_; lean_object* v___x_467_; 
lean_dec(v_h__1_462_);
v_head_465_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_head_465_);
v_tail_466_ = lean_ctor_get(v_x_460_, 1);
lean_inc(v_tail_466_);
lean_dec_ref(v_x_460_);
v___x_467_ = lean_apply_3(v_h__2_463_, v_head_465_, v_tail_466_, v_x_461_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR___redArg(lean_object* v_l_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_array_mk(v_l_468_);
v___x_470_ = lean_array_pop(v___x_469_);
v___x_471_ = lean_array_to_list(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR(lean_object* v_00_u03b1_472_, lean_object* v_l_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_array_mk(v_l_473_);
v___x_475_ = lean_array_pop(v___x_474_);
v___x_476_ = lean_array_to_list(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(lean_object* v_p_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v___x_479_; 
lean_dec_ref(v_p_477_);
v___x_479_ = lean_box(0);
return v___x_479_;
}
else
{
lean_object* v_head_480_; lean_object* v_tail_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_head_480_ = lean_ctor_get(v_x_478_, 0);
lean_inc_n(v_head_480_, 2);
v_tail_481_ = lean_ctor_get(v_x_478_, 1);
lean_inc(v_tail_481_);
lean_dec_ref(v_x_478_);
lean_inc_ref(v_p_477_);
v___x_482_ = lean_apply_1(v_p_477_, v_head_480_);
v___x_483_ = lean_unbox(v___x_482_);
if (v___x_483_ == 0)
{
lean_dec(v_head_480_);
v_x_478_ = v_tail_481_;
goto _start;
}
else
{
lean_object* v___x_485_; 
lean_dec(v_tail_481_);
lean_dec_ref(v_p_477_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_head_480_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object* v_p_486_, lean_object* v_l_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = l_List_reverse___redArg(v_l_487_);
v___x_489_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_486_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object* v_00_u03b1_490_, lean_object* v_p_491_, lean_object* v_l_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_List_findRev_x3fTR___redArg(v_p_491_, v_l_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(lean_object* v_00_u03b1_494_, lean_object* v_p_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_495_, v_x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v_h__1_499_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_apply_1(v_h__2_500_, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_500_);
v_val_503_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_val_503_);
lean_dec_ref(v_x_498_);
v___x_504_ = lean_apply_1(v_h__1_499_, v_val_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_505_, lean_object* v_motive_506_, lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_h__1_508_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_apply_1(v_h__2_509_, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v_val_512_; lean_object* v___x_513_; 
lean_dec(v_h__2_509_);
v_val_512_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_val_512_);
lean_dec_ref(v_x_507_);
v___x_513_ = lean_apply_1(v_h__1_508_, v_val_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(lean_object* v_f_514_, lean_object* v_x_515_){
_start:
{
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v___x_516_; 
lean_dec_ref(v_f_514_);
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
lean_object* v_head_517_; lean_object* v_tail_518_; lean_object* v___x_519_; 
v_head_517_ = lean_ctor_get(v_x_515_, 0);
lean_inc(v_head_517_);
v_tail_518_ = lean_ctor_get(v_x_515_, 1);
lean_inc(v_tail_518_);
lean_dec_ref(v_x_515_);
lean_inc_ref(v_f_514_);
v___x_519_ = lean_apply_1(v_f_514_, v_head_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
v_x_515_ = v_tail_518_;
goto _start;
}
else
{
lean_dec(v_tail_518_);
lean_dec_ref(v_f_514_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object* v_f_521_, lean_object* v_l_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = l_List_reverse___redArg(v_l_522_);
v___x_524_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_521_, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_, lean_object* v_f_527_, lean_object* v_l_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_List_findSomeRev_x3fTR___redArg(v_f_527_, v_l_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_f_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_532_, v_x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object* v_x1_535_, lean_object* v_x2_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v_x1_535_);
lean_ctor_set(v___x_537_, 1, v_x2_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object* v_inst_539_, lean_object* v_l_540_, lean_object* v_b_541_, lean_object* v_c_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
if (lean_obj_tag(v_a_543_) == 0)
{
lean_dec_ref(v_a_544_);
lean_dec(v_c_542_);
lean_dec(v_b_541_);
lean_dec_ref(v_inst_539_);
lean_inc(v_l_540_);
return v_l_540_;
}
else
{
lean_object* v_head_545_; lean_object* v_tail_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_565_; 
v_head_545_ = lean_ctor_get(v_a_543_, 0);
v_tail_546_ = lean_ctor_get(v_a_543_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_565_ == 0)
{
v___x_548_ = v_a_543_;
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_tail_546_);
lean_inc(v_head_545_);
lean_dec(v_a_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
lean_inc_ref(v_inst_539_);
lean_inc(v_head_545_);
lean_inc(v_b_541_);
v___x_550_ = lean_apply_2(v_inst_539_, v_b_541_, v_head_545_);
v___x_551_ = lean_unbox(v___x_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_del_object(v___x_548_);
v___x_552_ = lean_array_push(v_a_544_, v_head_545_);
v_a_543_ = v_tail_546_;
v_a_544_ = v___x_552_;
goto _start;
}
else
{
lean_object* v___x_555_; 
lean_dec(v_head_545_);
lean_dec(v_b_541_);
lean_dec_ref(v_inst_539_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v_c_542_);
v___x_555_ = v___x_548_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_c_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_tail_546_);
v___x_555_ = v_reuseFailAlloc_564_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_array_get_size(v_a_544_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_559_ = lean_nat_dec_lt(v___x_557_, v___x_556_);
if (v___x_559_ == 0)
{
lean_dec_ref(v_a_544_);
return v___x_555_;
}
else
{
lean_object* v___f_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___f_560_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_561_ = lean_usize_of_nat(v___x_556_);
v___x_562_ = ((size_t)0ULL);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_558_, v___f_560_, v_a_544_, v___x_561_, v___x_562_, v___x_555_);
return v___x_563_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object* v_inst_566_, lean_object* v_l_567_, lean_object* v_b_568_, lean_object* v_c_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_566_, v_l_567_, v_b_568_, v_c_569_, v_a_570_, v_a_571_);
lean_dec(v_l_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object* v_00_u03b1_573_, lean_object* v_inst_574_, lean_object* v_l_575_, lean_object* v_b_576_, lean_object* v_c_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_574_, v_l_575_, v_b_576_, v_c_577_, v_a_578_, v_a_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object* v_00_u03b1_581_, lean_object* v_inst_582_, lean_object* v_l_583_, lean_object* v_b_584_, lean_object* v_c_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(v_00_u03b1_581_, v_inst_582_, v_l_583_, v_b_584_, v_c_585_, v_a_586_, v_a_587_);
lean_dec(v_l_583_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object* v_inst_589_, lean_object* v_l_590_, lean_object* v_b_591_, lean_object* v_c_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_590_);
v___x_594_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_589_, v_l_590_, v_b_591_, v_c_592_, v_l_590_, v___x_593_);
lean_dec(v_l_590_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object* v_00_u03b1_595_, lean_object* v_inst_596_, lean_object* v_l_597_, lean_object* v_b_598_, lean_object* v_c_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_597_);
v___x_601_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_596_, v_l_597_, v_b_598_, v_c_599_, v_l_597_, v___x_600_);
lean_dec(v_l_597_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v___x_607_; 
lean_dec(v_h__2_606_);
v___x_607_ = lean_apply_2(v_h__1_605_, v_x_603_, v_x_604_);
return v___x_607_;
}
else
{
lean_object* v_head_608_; lean_object* v_tail_609_; lean_object* v___x_610_; 
lean_dec(v_h__1_605_);
v_head_608_ = lean_ctor_get(v_x_602_, 0);
lean_inc(v_head_608_);
v_tail_609_ = lean_ctor_get(v_x_602_, 1);
lean_inc(v_tail_609_);
lean_dec_ref(v_x_602_);
v___x_610_ = lean_apply_4(v_h__2_606_, v_head_608_, v_tail_609_, v_x_603_, v_x_604_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter(lean_object* v_00_u03b1_611_, lean_object* v_motive_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_618_; 
lean_dec(v_h__2_617_);
v___x_618_ = lean_apply_2(v_h__1_616_, v_x_614_, v_x_615_);
return v___x_618_;
}
else
{
lean_object* v_head_619_; lean_object* v_tail_620_; lean_object* v___x_621_; 
lean_dec(v_h__1_616_);
v_head_619_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_head_619_);
v_tail_620_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_tail_620_);
lean_dec_ref(v_x_613_);
v___x_621_ = lean_apply_4(v_h__2_617_, v_head_619_, v_tail_620_, v_x_614_, v_x_615_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object* v_f_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
if (lean_obj_tag(v_a_623_) == 0)
{
lean_object* v___x_626_; 
lean_dec(v_a_624_);
lean_dec(v_f_622_);
v___x_626_ = lean_array_to_list(v_a_625_);
return v___x_626_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_647_; 
v_head_627_ = lean_ctor_get(v_a_623_, 0);
v_tail_628_ = lean_ctor_get(v_a_623_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_647_ == 0)
{
v___x_630_ = v_a_623_;
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_tail_628_);
lean_inc(v_head_627_);
lean_dec(v_a_623_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_zero_632_; uint8_t v_isZero_633_; 
v_zero_632_ = lean_unsigned_to_nat(0u);
v_isZero_633_ = lean_nat_dec_eq(v_a_624_, v_zero_632_);
if (v_isZero_633_ == 1)
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_a_624_);
v___x_634_ = lean_apply_1(v_f_622_, v_head_627_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_634_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_tail_628_);
v___x_636_ = v_reuseFailAlloc_642_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_a_625_);
v___x_638_ = lean_nat_dec_lt(v_zero_632_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec_ref(v_a_625_);
return v___x_636_;
}
else
{
size_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_usize_of_nat(v___x_637_);
v___x_640_ = ((size_t)0ULL);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_625_, v___x_639_, v___x_640_, v___x_636_);
lean_dec_ref(v_a_625_);
return v___x_641_;
}
}
}
else
{
lean_object* v_one_643_; lean_object* v_n_644_; lean_object* v___x_645_; 
lean_del_object(v___x_630_);
v_one_643_ = lean_unsigned_to_nat(1u);
v_n_644_ = lean_nat_sub(v_a_624_, v_one_643_);
lean_dec(v_a_624_);
v___x_645_ = lean_array_push(v_a_625_, v_head_627_);
v_a_623_ = v_tail_628_;
v_a_624_ = v_n_644_;
v_a_625_ = v___x_645_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object* v_00_u03b1_648_, lean_object* v_f_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_649_, v_a_650_, v_a_651_, v_a_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object* v_l_654_, lean_object* v_i_655_, lean_object* v_f_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_658_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_656_, v_l_654_, v_i_655_, v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object* v_00_u03b1_659_, lean_object* v_l_660_, lean_object* v_i_661_, lean_object* v_f_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_List_modifyTR___redArg(v_l_660_, v_i_661_, v_f_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_zero_668_; uint8_t v_isZero_669_; 
v_zero_668_ = lean_unsigned_to_nat(0u);
v_isZero_669_ = lean_nat_dec_eq(v_a_665_, v_zero_668_);
if (v_isZero_669_ == 1)
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
lean_dec(v_a_665_);
v___x_670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_670_, 0, v_a_664_);
lean_ctor_set(v___x_670_, 1, v_a_666_);
v___x_671_ = lean_array_get_size(v_a_667_);
v___x_672_ = lean_nat_dec_lt(v_zero_668_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_a_667_);
return v___x_670_;
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_usize_of_nat(v___x_671_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_667_, v___x_673_, v___x_674_, v___x_670_);
lean_dec_ref(v_a_667_);
return v___x_675_;
}
}
else
{
if (lean_obj_tag(v_a_666_) == 0)
{
lean_object* v___x_676_; 
lean_dec(v_a_665_);
lean_dec(v_a_664_);
v___x_676_ = lean_array_to_list(v_a_667_);
return v___x_676_;
}
else
{
lean_object* v_head_677_; lean_object* v_tail_678_; lean_object* v_one_679_; lean_object* v_n_680_; lean_object* v___x_681_; 
v_head_677_ = lean_ctor_get(v_a_666_, 0);
lean_inc(v_head_677_);
v_tail_678_ = lean_ctor_get(v_a_666_, 1);
lean_inc(v_tail_678_);
lean_dec_ref(v_a_666_);
v_one_679_ = lean_unsigned_to_nat(1u);
v_n_680_ = lean_nat_sub(v_a_665_, v_one_679_);
lean_dec(v_a_665_);
v___x_681_ = lean_array_push(v_a_667_, v_head_677_);
v_a_665_ = v_n_680_;
v_a_666_ = v_tail_678_;
v_a_667_ = v___x_681_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object* v_00_u03b1_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_684_, v_a_685_, v_a_686_, v_a_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object* v_l_689_, lean_object* v_n_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_693_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_691_, v_n_690_, v_l_689_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object* v_00_u03b1_694_, lean_object* v_l_695_, lean_object* v_n_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_699_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_697_, v_n_696_, v_l_695_, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_h__1_703_, lean_object* v_h__2_704_, lean_object* v_h__3_705_){
_start:
{
lean_object* v_zero_706_; uint8_t v_isZero_707_; 
v_zero_706_ = lean_unsigned_to_nat(0u);
v_isZero_707_ = lean_nat_dec_eq(v_x_700_, v_zero_706_);
if (v_isZero_707_ == 1)
{
lean_object* v___x_708_; 
lean_dec(v_h__3_705_);
lean_dec(v_h__2_704_);
lean_dec(v_x_700_);
v___x_708_ = lean_apply_2(v_h__1_703_, v_x_701_, v_x_702_);
return v___x_708_;
}
else
{
lean_dec(v_h__1_703_);
if (lean_obj_tag(v_x_701_) == 0)
{
lean_object* v___x_709_; 
lean_dec(v_h__3_705_);
v___x_709_ = lean_apply_3(v_h__2_704_, v_x_700_, v_x_702_, lean_box(0));
return v___x_709_;
}
else
{
lean_object* v_head_710_; lean_object* v_tail_711_; lean_object* v_one_712_; lean_object* v_n_713_; lean_object* v___x_714_; 
lean_dec(v_h__2_704_);
v_head_710_ = lean_ctor_get(v_x_701_, 0);
lean_inc(v_head_710_);
v_tail_711_ = lean_ctor_get(v_x_701_, 1);
lean_inc(v_tail_711_);
lean_dec_ref(v_x_701_);
v_one_712_ = lean_unsigned_to_nat(1u);
v_n_713_ = lean_nat_sub(v_x_700_, v_one_712_);
lean_dec(v_x_700_);
v___x_714_ = lean_apply_4(v_h__3_705_, v_n_713_, v_head_710_, v_tail_711_, v_x_702_);
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object* v_00_u03b1_715_, lean_object* v_motive_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_h__1_720_, lean_object* v_h__2_721_, lean_object* v_h__3_722_){
_start:
{
lean_object* v_zero_723_; uint8_t v_isZero_724_; 
v_zero_723_ = lean_unsigned_to_nat(0u);
v_isZero_724_ = lean_nat_dec_eq(v_x_717_, v_zero_723_);
if (v_isZero_724_ == 1)
{
lean_object* v___x_725_; 
lean_dec(v_h__3_722_);
lean_dec(v_h__2_721_);
lean_dec(v_x_717_);
v___x_725_ = lean_apply_2(v_h__1_720_, v_x_718_, v_x_719_);
return v___x_725_;
}
else
{
lean_dec(v_h__1_720_);
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v___x_726_; 
lean_dec(v_h__3_722_);
v___x_726_ = lean_apply_3(v_h__2_721_, v_x_717_, v_x_719_, lean_box(0));
return v___x_726_;
}
else
{
lean_object* v_head_727_; lean_object* v_tail_728_; lean_object* v_one_729_; lean_object* v_n_730_; lean_object* v___x_731_; 
lean_dec(v_h__2_721_);
v_head_727_ = lean_ctor_get(v_x_718_, 0);
lean_inc(v_head_727_);
v_tail_728_ = lean_ctor_get(v_x_718_, 1);
lean_inc(v_tail_728_);
lean_dec_ref(v_x_718_);
v_one_729_ = lean_unsigned_to_nat(1u);
v_n_730_ = lean_nat_sub(v_x_717_, v_one_729_);
lean_dec(v_x_717_);
v___x_731_ = lean_apply_4(v_h__3_722_, v_n_730_, v_head_727_, v_tail_728_, v_x_719_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object* v_inst_732_, lean_object* v_l_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
if (lean_obj_tag(v_a_735_) == 0)
{
lean_dec_ref(v_a_736_);
lean_dec(v_a_734_);
lean_dec_ref(v_inst_732_);
lean_inc(v_l_733_);
return v_l_733_;
}
else
{
lean_object* v_head_737_; lean_object* v_tail_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_head_737_ = lean_ctor_get(v_a_735_, 0);
lean_inc_n(v_head_737_, 2);
v_tail_738_ = lean_ctor_get(v_a_735_, 1);
lean_inc(v_tail_738_);
lean_dec_ref(v_a_735_);
lean_inc_ref(v_inst_732_);
lean_inc(v_a_734_);
v___x_739_ = lean_apply_2(v_inst_732_, v_head_737_, v_a_734_);
v___x_740_ = lean_unbox(v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
v___x_741_ = lean_array_push(v_a_736_, v_head_737_);
v_a_735_ = v_tail_738_;
v_a_736_ = v___x_741_;
goto _start;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
lean_dec(v_head_737_);
lean_dec(v_a_734_);
lean_dec_ref(v_inst_732_);
v___x_743_ = lean_array_get_size(v_a_736_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_746_ = lean_nat_dec_lt(v___x_744_, v___x_743_);
if (v___x_746_ == 0)
{
lean_dec_ref(v_a_736_);
return v_tail_738_;
}
else
{
lean_object* v___f_747_; size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___f_747_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_748_ = lean_usize_of_nat(v___x_743_);
v___x_749_ = ((size_t)0ULL);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_745_, v___f_747_, v_a_736_, v___x_748_, v___x_749_, v_tail_738_);
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object* v_inst_751_, lean_object* v_l_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_751_, v_l_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_l_752_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object* v_00_u03b1_757_, lean_object* v_inst_758_, lean_object* v_l_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_758_, v_l_759_, v_a_760_, v_a_761_, v_a_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object* v_00_u03b1_764_, lean_object* v_inst_765_, lean_object* v_l_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(v_00_u03b1_764_, v_inst_765_, v_l_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_l_766_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object* v_inst_771_, lean_object* v_l_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_772_);
v___x_775_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_771_, v_l_772_, v_a_773_, v_l_772_, v___x_774_);
lean_dec(v_l_772_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object* v_00_u03b1_776_, lean_object* v_inst_777_, lean_object* v_l_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_778_);
v___x_781_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_777_, v_l_778_, v_a_779_, v_l_778_, v___x_780_);
lean_dec(v_l_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object* v_p_782_, lean_object* v_l_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
if (lean_obj_tag(v_a_784_) == 0)
{
lean_dec_ref(v_a_785_);
lean_dec_ref(v_p_782_);
lean_inc(v_l_783_);
return v_l_783_;
}
else
{
lean_object* v_head_786_; lean_object* v_tail_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_head_786_ = lean_ctor_get(v_a_784_, 0);
lean_inc_n(v_head_786_, 2);
v_tail_787_ = lean_ctor_get(v_a_784_, 1);
lean_inc(v_tail_787_);
lean_dec_ref(v_a_784_);
lean_inc_ref(v_p_782_);
v___x_788_ = lean_apply_1(v_p_782_, v_head_786_);
v___x_789_ = lean_unbox(v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_array_push(v_a_785_, v_head_786_);
v_a_784_ = v_tail_787_;
v_a_785_ = v___x_790_;
goto _start;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
lean_dec(v_head_786_);
lean_dec_ref(v_p_782_);
v___x_792_ = lean_array_get_size(v_a_785_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_792_);
if (v___x_795_ == 0)
{
lean_dec_ref(v_a_785_);
return v_tail_787_;
}
else
{
lean_object* v___f_796_; size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___f_796_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_797_ = lean_usize_of_nat(v___x_792_);
v___x_798_ = ((size_t)0ULL);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_794_, v___f_796_, v_a_785_, v___x_797_, v___x_798_, v_tail_787_);
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object* v_p_800_, lean_object* v_l_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_800_, v_l_801_, v_a_802_, v_a_803_);
lean_dec(v_l_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object* v_00_u03b1_805_, lean_object* v_p_806_, lean_object* v_l_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_806_, v_l_807_, v_a_808_, v_a_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object* v_00_u03b1_811_, lean_object* v_p_812_, lean_object* v_l_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(v_00_u03b1_811_, v_p_812_, v_l_813_, v_a_814_, v_a_815_);
lean_dec(v_l_813_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object* v_p_817_, lean_object* v_l_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_818_);
v___x_820_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_817_, v_l_818_, v_l_818_, v___x_819_);
lean_dec(v_l_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object* v_00_u03b1_821_, lean_object* v_p_822_, lean_object* v_l_823_){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_823_);
v___x_825_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_822_, v_l_823_, v_l_823_, v___x_824_);
lean_dec(v_l_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object* v_l_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
if (lean_obj_tag(v_a_827_) == 0)
{
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_inc(v_l_826_);
return v_l_826_;
}
else
{
lean_object* v_head_830_; lean_object* v_tail_831_; lean_object* v_zero_832_; uint8_t v_isZero_833_; 
v_head_830_ = lean_ctor_get(v_a_827_, 0);
lean_inc(v_head_830_);
v_tail_831_ = lean_ctor_get(v_a_827_, 1);
lean_inc(v_tail_831_);
lean_dec_ref(v_a_827_);
v_zero_832_ = lean_unsigned_to_nat(0u);
v_isZero_833_ = lean_nat_dec_eq(v_a_828_, v_zero_832_);
if (v_isZero_833_ == 1)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
lean_dec(v_head_830_);
lean_dec(v_a_828_);
v___x_834_ = lean_array_get_size(v_a_829_);
v___x_835_ = lean_nat_dec_lt(v_zero_832_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v_a_829_);
return v_tail_831_;
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_usize_of_nat(v___x_834_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_829_, v___x_836_, v___x_837_, v_tail_831_);
lean_dec_ref(v_a_829_);
return v___x_838_;
}
}
else
{
lean_object* v_one_839_; lean_object* v_n_840_; lean_object* v___x_841_; 
v_one_839_ = lean_unsigned_to_nat(1u);
v_n_840_ = lean_nat_sub(v_a_828_, v_one_839_);
lean_dec(v_a_828_);
v___x_841_ = lean_array_push(v_a_829_, v_head_830_);
v_a_827_ = v_tail_831_;
v_a_828_ = v_n_840_;
v_a_829_ = v___x_841_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object* v_l_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_l_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object* v_00_u03b1_848_, lean_object* v_l_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object* v_00_u03b1_854_, lean_object* v_l_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(v_00_u03b1_854_, v_l_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_l_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object* v_l_860_, lean_object* v_n_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_860_);
v___x_863_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_860_, v_l_860_, v_n_861_, v___x_862_);
lean_dec(v_l_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object* v_00_u03b1_864_, lean_object* v_l_865_, lean_object* v_n_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_865_);
v___x_868_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_865_, v_l_865_, v_n_866_, v___x_867_);
lean_dec(v_l_865_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_h__1_871_, lean_object* v_h__2_872_, lean_object* v_h__3_873_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
lean_object* v___x_874_; 
lean_dec(v_h__3_873_);
lean_dec(v_h__2_872_);
v___x_874_ = lean_apply_1(v_h__1_871_, v_x_870_);
return v___x_874_;
}
else
{
lean_object* v_head_875_; lean_object* v_tail_876_; lean_object* v_zero_877_; uint8_t v_isZero_878_; 
lean_dec(v_h__1_871_);
v_head_875_ = lean_ctor_get(v_x_869_, 0);
lean_inc(v_head_875_);
v_tail_876_ = lean_ctor_get(v_x_869_, 1);
lean_inc(v_tail_876_);
lean_dec_ref(v_x_869_);
v_zero_877_ = lean_unsigned_to_nat(0u);
v_isZero_878_ = lean_nat_dec_eq(v_x_870_, v_zero_877_);
if (v_isZero_878_ == 1)
{
lean_object* v___x_879_; 
lean_dec(v_h__3_873_);
lean_dec(v_x_870_);
v___x_879_ = lean_apply_2(v_h__2_872_, v_head_875_, v_tail_876_);
return v___x_879_;
}
else
{
lean_object* v_one_880_; lean_object* v_n_881_; lean_object* v___x_882_; 
lean_dec(v_h__2_872_);
v_one_880_ = lean_unsigned_to_nat(1u);
v_n_881_ = lean_nat_sub(v_x_870_, v_one_880_);
lean_dec(v_x_870_);
v___x_882_ = lean_apply_3(v_h__3_873_, v_head_875_, v_tail_876_, v_n_881_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_883_, lean_object* v_motive_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_h__1_887_, lean_object* v_h__2_888_, lean_object* v_h__3_889_){
_start:
{
if (lean_obj_tag(v_x_885_) == 0)
{
lean_object* v___x_890_; 
lean_dec(v_h__3_889_);
lean_dec(v_h__2_888_);
v___x_890_ = lean_apply_1(v_h__1_887_, v_x_886_);
return v___x_890_;
}
else
{
lean_object* v_head_891_; lean_object* v_tail_892_; lean_object* v_zero_893_; uint8_t v_isZero_894_; 
lean_dec(v_h__1_887_);
v_head_891_ = lean_ctor_get(v_x_885_, 0);
lean_inc(v_head_891_);
v_tail_892_ = lean_ctor_get(v_x_885_, 1);
lean_inc(v_tail_892_);
lean_dec_ref(v_x_885_);
v_zero_893_ = lean_unsigned_to_nat(0u);
v_isZero_894_ = lean_nat_dec_eq(v_x_886_, v_zero_893_);
if (v_isZero_894_ == 1)
{
lean_object* v___x_895_; 
lean_dec(v_h__3_889_);
lean_dec(v_x_886_);
v___x_895_ = lean_apply_2(v_h__2_888_, v_head_891_, v_tail_892_);
return v___x_895_;
}
else
{
lean_object* v_one_896_; lean_object* v_n_897_; lean_object* v___x_898_; 
lean_dec(v_h__2_888_);
v_one_896_ = lean_unsigned_to_nat(1u);
v_n_897_ = lean_nat_sub(v_x_886_, v_one_896_);
lean_dec(v_x_886_);
v___x_898_ = lean_apply_3(v_h__3_889_, v_head_891_, v_tail_892_, v_n_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object* v_f_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_a_900_) == 1)
{
if (lean_obj_tag(v_a_901_) == 1)
{
lean_object* v_head_903_; lean_object* v_tail_904_; lean_object* v_head_905_; lean_object* v_tail_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_head_903_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_head_903_);
v_tail_904_ = lean_ctor_get(v_a_900_, 1);
lean_inc(v_tail_904_);
lean_dec_ref(v_a_900_);
v_head_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_head_905_);
v_tail_906_ = lean_ctor_get(v_a_901_, 1);
lean_inc(v_tail_906_);
lean_dec_ref(v_a_901_);
lean_inc(v_f_899_);
v___x_907_ = lean_apply_2(v_f_899_, v_head_903_, v_head_905_);
v___x_908_ = lean_array_push(v_a_902_, v___x_907_);
v_a_900_ = v_tail_904_;
v_a_901_ = v_tail_906_;
v_a_902_ = v___x_908_;
goto _start;
}
else
{
lean_object* v___x_910_; 
lean_dec_ref(v_a_900_);
lean_dec(v_a_901_);
lean_dec(v_f_899_);
v___x_910_ = lean_array_to_list(v_a_902_);
return v___x_910_;
}
}
else
{
lean_object* v___x_911_; 
lean_dec(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_f_899_);
v___x_911_ = lean_array_to_list(v_a_902_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_00_u03b3_914_, lean_object* v_f_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_915_, v_a_916_, v_a_917_, v_a_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object* v_f_920_, lean_object* v_as_921_, lean_object* v_bs_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_924_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_920_, v_as_921_, v_bs_922_, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_00_u03b3_927_, lean_object* v_f_928_, lean_object* v_as_929_, lean_object* v_bs_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_932_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_928_, v_as_929_, v_bs_930_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_h__1_936_, lean_object* v_h__2_937_){
_start:
{
if (lean_obj_tag(v_x_933_) == 1)
{
if (lean_obj_tag(v_x_934_) == 1)
{
lean_object* v_head_938_; lean_object* v_tail_939_; lean_object* v_head_940_; lean_object* v_tail_941_; lean_object* v___x_942_; 
lean_dec(v_h__2_937_);
v_head_938_ = lean_ctor_get(v_x_933_, 0);
lean_inc(v_head_938_);
v_tail_939_ = lean_ctor_get(v_x_933_, 1);
lean_inc(v_tail_939_);
lean_dec_ref(v_x_933_);
v_head_940_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_head_940_);
v_tail_941_ = lean_ctor_get(v_x_934_, 1);
lean_inc(v_tail_941_);
lean_dec_ref(v_x_934_);
v___x_942_ = lean_apply_5(v_h__1_936_, v_head_938_, v_tail_939_, v_head_940_, v_tail_941_, v_x_935_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
lean_dec(v_h__1_936_);
v___x_943_ = lean_apply_4(v_h__2_937_, v_x_933_, v_x_934_, v_x_935_, lean_box(0));
return v___x_943_;
}
}
else
{
lean_object* v___x_944_; 
lean_dec(v_h__1_936_);
v___x_944_ = lean_apply_4(v_h__2_937_, v_x_933_, v_x_934_, v_x_935_, lean_box(0));
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_00_u03b3_947_, lean_object* v_motive_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_h__1_952_, lean_object* v_h__2_953_){
_start:
{
if (lean_obj_tag(v_x_949_) == 1)
{
if (lean_obj_tag(v_x_950_) == 1)
{
lean_object* v_head_954_; lean_object* v_tail_955_; lean_object* v_head_956_; lean_object* v_tail_957_; lean_object* v___x_958_; 
lean_dec(v_h__2_953_);
v_head_954_ = lean_ctor_get(v_x_949_, 0);
lean_inc(v_head_954_);
v_tail_955_ = lean_ctor_get(v_x_949_, 1);
lean_inc(v_tail_955_);
lean_dec_ref(v_x_949_);
v_head_956_ = lean_ctor_get(v_x_950_, 0);
lean_inc(v_head_956_);
v_tail_957_ = lean_ctor_get(v_x_950_, 1);
lean_inc(v_tail_957_);
lean_dec_ref(v_x_950_);
v___x_958_ = lean_apply_5(v_h__1_952_, v_head_954_, v_tail_955_, v_head_956_, v_tail_957_, v_x_951_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_h__1_952_);
v___x_959_ = lean_apply_4(v_h__2_953_, v_x_949_, v_x_950_, v_x_951_, lean_box(0));
return v___x_959_;
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v_h__1_952_);
v___x_960_ = lean_apply_4(v_h__2_953_, v_x_949_, v_x_950_, v_x_951_, lean_box(0));
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object* v_as_961_, size_t v_i_962_, size_t v_stop_963_, lean_object* v_b_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = lean_usize_dec_eq(v_i_962_, v_stop_963_);
if (v___x_965_ == 0)
{
lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_982_; 
v_fst_966_ = lean_ctor_get(v_b_964_, 0);
v_snd_967_ = lean_ctor_get(v_b_964_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_b_964_);
if (v_isSharedCheck_982_ == 0)
{
v___x_969_ = v_b_964_;
v_isShared_970_ = v_isSharedCheck_982_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v_b_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_982_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_sub(v_i_962_, v___x_971_);
v___x_973_ = lean_array_uget_borrowed(v_as_961_, v___x_972_);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = lean_nat_sub(v_fst_966_, v___x_974_);
lean_dec(v_fst_966_);
lean_inc(v___x_975_);
lean_inc(v___x_973_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_975_);
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_977_ = v___x_969_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_975_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_snd_967_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_975_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v_i_962_ = v___x_972_;
v_b_964_ = v___x_979_;
goto _start;
}
}
}
else
{
return v_b_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; lean_object* v_res_989_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_983_, v_i_boxed_987_, v_stop_boxed_988_, v_b_986_);
lean_dec_ref(v_as_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object* v_l_990_, lean_object* v_n_991_){
_start:
{
lean_object* v_as_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_as_992_ = lean_array_mk(v_l_990_);
v___x_993_ = lean_array_get_size(v_as_992_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_nat_dec_lt(v___x_995_, v___x_993_);
if (v___x_996_ == 0)
{
lean_dec_ref(v_as_992_);
return v___x_994_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; lean_object* v_snd_1002_; 
v___x_997_ = lean_nat_add(v_n_991_, v___x_993_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_994_);
v___x_999_ = lean_usize_of_nat(v___x_993_);
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_992_, v___x_999_, v___x_1000_, v___x_998_);
lean_dec_ref(v_as_992_);
v_snd_1002_ = lean_ctor_get(v___x_1001_, 1);
lean_inc(v_snd_1002_);
lean_dec_ref(v___x_1001_);
return v_snd_1002_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object* v_l_1003_, lean_object* v_n_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_List_zipIdxTR___redArg(v_l_1003_, v_n_1004_);
lean_dec(v_n_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object* v_00_u03b1_1006_, lean_object* v_l_1007_, lean_object* v_n_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_List_zipIdxTR___redArg(v_l_1007_, v_n_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_l_1011_, lean_object* v_n_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_List_zipIdxTR(v_00_u03b1_1010_, v_l_1011_, v_n_1012_);
lean_dec(v_n_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object* v_00_u03b1_1014_, lean_object* v_as_1015_, size_t v_i_1016_, size_t v_stop_1017_, lean_object* v_b_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_1015_, v_i_1016_, v_stop_1017_, v_b_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_as_1021_, lean_object* v_i_1022_, lean_object* v_stop_1023_, lean_object* v_b_1024_){
_start:
{
size_t v_i_boxed_1025_; size_t v_stop_boxed_1026_; lean_object* v_res_1027_; 
v_i_boxed_1025_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_stop_boxed_1026_ = lean_unbox_usize(v_stop_1023_);
lean_dec(v_stop_1023_);
v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(v_00_u03b1_1020_, v_as_1021_, v_i_boxed_1025_, v_stop_boxed_1026_, v_b_1024_);
lean_dec_ref(v_as_1021_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_1028_, lean_object* v_x_1029_, lean_object* v_h__1_1030_, lean_object* v_h__2_1031_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
lean_object* v___x_1032_; 
lean_dec(v_h__2_1031_);
v___x_1032_ = lean_apply_1(v_h__1_1030_, v_x_1029_);
return v___x_1032_;
}
else
{
lean_object* v_head_1033_; lean_object* v_tail_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__1_1030_);
v_head_1033_ = lean_ctor_get(v_x_1028_, 0);
lean_inc(v_head_1033_);
v_tail_1034_ = lean_ctor_get(v_x_1028_, 1);
lean_inc(v_tail_1034_);
lean_dec_ref(v_x_1028_);
v___x_1035_ = lean_apply_3(v_h__2_1031_, v_head_1033_, v_tail_1034_, v_x_1029_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_1036_, lean_object* v_motive_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_h__1_1040_, lean_object* v_h__2_1041_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v___x_1042_; 
lean_dec(v_h__2_1041_);
v___x_1042_ = lean_apply_1(v_h__1_1040_, v_x_1039_);
return v___x_1042_;
}
else
{
lean_object* v_head_1043_; lean_object* v_tail_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__1_1040_);
v_head_1043_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_head_1043_);
v_tail_1044_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_tail_1044_);
lean_dec_ref(v_x_1038_);
v___x_1045_ = lean_apply_3(v_h__2_1041_, v_head_1043_, v_tail_1044_, v_x_1039_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object* v_sep_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
if (lean_obj_tag(v_a_1048_) == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_array_get_size(v_a_1049_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_nat_dec_lt(v___x_1051_, v___x_1050_);
if (v___x_1052_ == 0)
{
lean_dec_ref(v_a_1049_);
return v_a_1047_;
}
else
{
size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_usize_of_nat(v___x_1050_);
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1049_, v___x_1053_, v___x_1054_, v_a_1047_);
lean_dec_ref(v_a_1049_);
return v___x_1055_;
}
}
else
{
lean_object* v_head_1056_; lean_object* v_tail_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_head_1056_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_head_1056_);
v_tail_1057_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_tail_1057_);
lean_dec_ref(v_a_1048_);
v___x_1058_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1049_, v_a_1047_);
v___x_1059_ = l_Array_append___redArg(v___x_1058_, v_sep_1046_);
v_a_1047_ = v_head_1056_;
v_a_1048_ = v_tail_1057_;
v_a_1049_ = v___x_1059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object* v_sep_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec_ref(v_sep_1061_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object* v_00_u03b1_1066_, lean_object* v_sep_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object* v_00_u03b1_1072_, lean_object* v_sep_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(v_00_u03b1_1072_, v_sep_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec_ref(v_sep_1073_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object* v_sep_1078_, lean_object* v_x_1079_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v___x_1080_; 
lean_dec(v_sep_1078_);
v___x_1080_ = lean_box(0);
return v___x_1080_;
}
else
{
lean_object* v_tail_1081_; 
v_tail_1081_ = lean_ctor_get(v_x_1079_, 1);
if (lean_obj_tag(v_tail_1081_) == 0)
{
lean_object* v_head_1082_; 
lean_dec(v_sep_1078_);
v_head_1082_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_head_1082_);
lean_dec_ref(v_x_1079_);
return v_head_1082_;
}
else
{
lean_object* v_head_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc(v_tail_1081_);
v_head_1083_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_head_1083_);
lean_dec_ref(v_x_1079_);
v___x_1084_ = lean_array_mk(v_sep_1078_);
v___x_1085_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_1086_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v___x_1084_, v_head_1083_, v_tail_1081_, v___x_1085_);
lean_dec_ref(v___x_1084_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object* v_00_u03b1_1087_, lean_object* v_sep_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_List_intercalateTR___redArg(v_sep_1088_, v_x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object* v_x_1091_, lean_object* v_h__1_1092_, lean_object* v_h__2_1093_, lean_object* v_h__3_1094_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__3_1094_);
lean_dec(v_h__2_1093_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_apply_1(v_h__1_1092_, v___x_1095_);
return v___x_1096_;
}
else
{
lean_object* v_tail_1097_; 
lean_dec(v_h__1_1092_);
v_tail_1097_ = lean_ctor_get(v_x_1091_, 1);
if (lean_obj_tag(v_tail_1097_) == 0)
{
lean_object* v_head_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__3_1094_);
v_head_1098_ = lean_ctor_get(v_x_1091_, 0);
lean_inc(v_head_1098_);
lean_dec_ref(v_x_1091_);
v___x_1099_ = lean_apply_1(v_h__2_1093_, v_head_1098_);
return v___x_1099_;
}
else
{
lean_object* v_head_1100_; lean_object* v___x_1101_; 
lean_inc(v_tail_1097_);
lean_dec(v_h__2_1093_);
v_head_1100_ = lean_ctor_get(v_x_1091_, 0);
lean_inc(v_head_1100_);
lean_dec_ref(v_x_1091_);
v___x_1101_ = lean_apply_3(v_h__3_1094_, v_head_1100_, v_tail_1097_, lean_box(0));
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object* v_00_u03b1_1102_, lean_object* v_motive_1103_, lean_object* v_x_1104_, lean_object* v_h__1_1105_, lean_object* v_h__2_1106_, lean_object* v_h__3_1107_){
_start:
{
if (lean_obj_tag(v_x_1104_) == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__3_1107_);
lean_dec(v_h__2_1106_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_apply_1(v_h__1_1105_, v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v_tail_1110_; 
lean_dec(v_h__1_1105_);
v_tail_1110_ = lean_ctor_get(v_x_1104_, 1);
if (lean_obj_tag(v_tail_1110_) == 0)
{
lean_object* v_head_1111_; lean_object* v___x_1112_; 
lean_dec(v_h__3_1107_);
v_head_1111_ = lean_ctor_get(v_x_1104_, 0);
lean_inc(v_head_1111_);
lean_dec_ref(v_x_1104_);
v___x_1112_ = lean_apply_1(v_h__2_1106_, v_head_1111_);
return v___x_1112_;
}
else
{
lean_object* v_head_1113_; lean_object* v___x_1114_; 
lean_inc(v_tail_1110_);
lean_dec(v_h__2_1106_);
v_head_1113_ = lean_ctor_get(v_x_1104_, 0);
lean_inc(v_head_1113_);
lean_dec_ref(v_x_1104_);
v___x_1114_ = lean_apply_3(v_h__3_1107_, v_head_1113_, v_tail_1110_, lean_box(0));
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_h__1_1118_, lean_object* v_h__2_1119_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
lean_object* v___x_1120_; 
lean_dec(v_h__2_1119_);
v___x_1120_ = lean_apply_2(v_h__1_1118_, v_x_1115_, v_x_1117_);
return v___x_1120_;
}
else
{
lean_object* v_head_1121_; lean_object* v_tail_1122_; lean_object* v___x_1123_; 
lean_dec(v_h__1_1118_);
v_head_1121_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_head_1121_);
v_tail_1122_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_tail_1122_);
lean_dec_ref(v_x_1116_);
v___x_1123_ = lean_apply_4(v_h__2_1119_, v_x_1115_, v_head_1121_, v_tail_1122_, v_x_1117_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter(lean_object* v_00_u03b1_1124_, lean_object* v_motive_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_h__1_1129_, lean_object* v_h__2_1130_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_object* v___x_1131_; 
lean_dec(v_h__2_1130_);
v___x_1131_ = lean_apply_2(v_h__1_1129_, v_x_1126_, v_x_1128_);
return v___x_1131_;
}
else
{
lean_object* v_head_1132_; lean_object* v_tail_1133_; lean_object* v___x_1134_; 
lean_dec(v_h__1_1129_);
v_head_1132_ = lean_ctor_get(v_x_1127_, 0);
lean_inc(v_head_1132_);
v_tail_1133_ = lean_ctor_get(v_x_1127_, 1);
lean_inc(v_tail_1133_);
lean_dec_ref(v_x_1127_);
v___x_1134_ = lean_apply_4(v_h__2_1130_, v_x_1126_, v_head_1132_, v_tail_1133_, v_x_1128_);
return v___x_1134_;
}
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
