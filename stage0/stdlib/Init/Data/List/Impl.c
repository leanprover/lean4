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
lean_object* l_List_findSome_x3f___redArg(lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_Data_List_Impl_0__List_setTR_go_match__1_splitter___redArg(v_x_107_, v_x_108_, v_x_109_, v_h__1_110_, v_h__2_111_, v_h__3_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___redArg(lean_object* v_f_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
if (lean_obj_tag(v_a_115_) == 0)
{
lean_object* v___x_117_; 
lean_dec_ref(v_f_114_);
v___x_117_ = lean_array_to_list(v_a_116_);
return v___x_117_;
}
else
{
lean_object* v_head_118_; lean_object* v_tail_119_; lean_object* v___x_120_; 
v_head_118_ = lean_ctor_get(v_a_115_, 0);
lean_inc(v_head_118_);
v_tail_119_ = lean_ctor_get(v_a_115_, 1);
lean_inc(v_tail_119_);
lean_dec_ref(v_a_115_);
lean_inc_ref(v_f_114_);
v___x_120_ = lean_apply_1(v_f_114_, v_head_118_);
if (lean_obj_tag(v___x_120_) == 0)
{
v_a_115_ = v_tail_119_;
goto _start;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
v_val_122_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_array_push(v_a_116_, v_val_122_);
v_a_115_ = v_tail_119_;
v_a_116_ = v___x_123_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_f_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_List_filterMapTR_go___redArg(v_f_127_, v_a_128_, v_a_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR___redArg(lean_object* v_f_131_, lean_object* v_l_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_134_ = l_List_filterMapTR_go___redArg(v_f_131_, v_l_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_f_137_, lean_object* v_l_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_140_ = l_List_filterMapTR_go___redArg(v_f_137_, v_l_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v___x_145_; 
lean_dec(v_h__2_144_);
v___x_145_ = lean_apply_1(v_h__1_143_, v_x_142_);
return v___x_145_;
}
else
{
lean_object* v_head_146_; lean_object* v_tail_147_; lean_object* v___x_148_; 
lean_dec(v_h__1_143_);
v_head_146_ = lean_ctor_get(v_x_141_, 0);
lean_inc(v_head_146_);
v_tail_147_ = lean_ctor_get(v_x_141_, 1);
lean_inc(v_tail_147_);
lean_dec_ref(v_x_141_);
v___x_148_ = lean_apply_3(v_h__2_144_, v_head_146_, v_tail_147_, v_x_142_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_motive_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__3_splitter___redArg(v_x_152_, v_x_153_, v_h__1_154_, v_h__2_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(lean_object* v_x_157_, lean_object* v_h__1_158_, lean_object* v_h__2_159_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_h__2_159_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_1(v_h__1_158_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_163_; 
lean_dec(v_h__1_158_);
v_val_162_ = lean_ctor_get(v_x_157_, 0);
lean_inc(v_val_162_);
lean_dec_ref(v_x_157_);
v___x_163_ = lean_apply_1(v_h__2_159_, v_val_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter(lean_object* v_00_u03b2_164_, lean_object* v_motive_165_, lean_object* v_x_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Init_Data_List_Impl_0__List_filterMapTR_go_match__1_splitter___redArg(v_x_166_, v_h__1_167_, v_h__2_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_170_, lean_object* v_h__1_171_, lean_object* v_h__2_172_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v_h__2_172_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_apply_1(v_h__1_171_, v___x_173_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_176_; 
lean_dec(v_h__1_171_);
v_val_175_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_val_175_);
lean_dec_ref(v_x_170_);
v___x_176_ = lean_apply_1(v_h__2_172_, v_val_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_177_, lean_object* v_motive_178_, lean_object* v_x_179_, lean_object* v_h__1_180_, lean_object* v_h__2_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Init_Data_List_Impl_0__List_filterMap_match__1_splitter___redArg(v_x_179_, v_h__1_180_, v_h__2_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption___redArg(lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_186_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_187_ = l_List_filterMapTR_go___redArg(v___x_185_, v_a_184_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_List_reduceOption(lean_object* v_00_u03b1_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l_List_reduceOption___redArg___closed__0));
v___x_191_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_192_ = l_List_filterMapTR_go___redArg(v___x_190_, v_a_189_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg___lam__0(lean_object* v_f_193_, lean_object* v_x1_194_, lean_object* v_x2_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_apply_2(v_f_193_, v_x1_194_, v_x2_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___redArg(lean_object* v_f_216_, lean_object* v_init_217_, lean_object* v_l_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_219_ = lean_array_mk(v_l_218_);
v___x_220_ = lean_array_get_size(v___x_219_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_220_);
if (v___x_223_ == 0)
{
lean_dec_ref(v___x_219_);
lean_dec(v_f_216_);
return v_init_217_;
}
else
{
lean_object* v___f_224_; size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; 
v___f_224_ = lean_alloc_closure((void*)(l_List_foldrTR___redArg___lam__0), 3, 1);
lean_closure_set(v___f_224_, 0, v_f_216_);
v___x_225_ = lean_usize_of_nat(v___x_220_);
v___x_226_ = ((size_t)0ULL);
v___x_227_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_222_, v___f_224_, v___x_219_, v___x_225_, v___x_226_, v_init_217_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_f_230_, lean_object* v_init_231_, lean_object* v_l_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_List_foldrTR___redArg(v_f_230_, v_init_231_, v_l_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object* v_f_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
if (lean_obj_tag(v_a_235_) == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v_f_234_);
v___x_237_ = lean_array_to_list(v_a_236_);
return v___x_237_;
}
else
{
lean_object* v_head_238_; lean_object* v_tail_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_head_238_ = lean_ctor_get(v_a_235_, 0);
lean_inc(v_head_238_);
v_tail_239_ = lean_ctor_get(v_a_235_, 1);
lean_inc(v_tail_239_);
lean_dec_ref(v_a_235_);
lean_inc_ref(v_f_234_);
v___x_240_ = lean_apply_1(v_f_234_, v_head_238_);
v___x_241_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_236_, v___x_240_);
v_a_235_ = v_tail_239_;
v_a_236_ = v___x_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_f_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_245_, v_a_246_, v_a_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR___redArg(lean_object* v_f_249_, lean_object* v_as_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_252_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_249_, v_as_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_f_255_, lean_object* v_as_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_258_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_255_, v_as_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR___redArg(lean_object* v_l_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_262_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_263_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_261_, v_l_260_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR(lean_object* v_00_u03b1_264_, lean_object* v_l_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_267_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_268_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_266_, v_l_265_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object* v_l_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
if (lean_obj_tag(v_a_270_) == 0)
{
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_inc(v_l_269_);
return v_l_269_;
}
else
{
lean_object* v_head_273_; lean_object* v_tail_274_; lean_object* v_zero_275_; uint8_t v_isZero_276_; 
v_head_273_ = lean_ctor_get(v_a_270_, 0);
lean_inc(v_head_273_);
v_tail_274_ = lean_ctor_get(v_a_270_, 1);
lean_inc(v_tail_274_);
lean_dec_ref(v_a_270_);
v_zero_275_ = lean_unsigned_to_nat(0u);
v_isZero_276_ = lean_nat_dec_eq(v_a_271_, v_zero_275_);
if (v_isZero_276_ == 1)
{
lean_object* v___x_277_; 
lean_dec(v_tail_274_);
lean_dec(v_head_273_);
lean_dec(v_a_271_);
v___x_277_ = lean_array_to_list(v_a_272_);
return v___x_277_;
}
else
{
lean_object* v_one_278_; lean_object* v_n_279_; lean_object* v___x_280_; 
v_one_278_ = lean_unsigned_to_nat(1u);
v_n_279_ = lean_nat_sub(v_a_271_, v_one_278_);
lean_dec(v_a_271_);
v___x_280_ = lean_array_push(v_a_272_, v_head_273_);
v_a_270_ = v_tail_274_;
v_a_271_ = v_n_279_;
v_a_272_ = v___x_280_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(lean_object* v_l_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_l_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object* v_00_u03b1_287_, lean_object* v_l_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(lean_object* v_00_u03b1_293_, lean_object* v_l_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(v_00_u03b1_293_, v_l_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_l_294_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR___redArg(lean_object* v_n_299_, lean_object* v_l_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_300_);
v___x_302_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_300_, v_l_300_, v_n_299_, v___x_301_);
lean_dec(v_l_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR(lean_object* v_00_u03b1_303_, lean_object* v_n_304_, lean_object* v_l_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_305_);
v___x_307_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_305_, v_l_305_, v_n_304_, v___x_306_);
lean_dec(v_l_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_h__1_310_, lean_object* v_h__2_311_, lean_object* v_h__3_312_){
_start:
{
lean_object* v_zero_313_; uint8_t v_isZero_314_; 
v_zero_313_ = lean_unsigned_to_nat(0u);
v_isZero_314_ = lean_nat_dec_eq(v_x_308_, v_zero_313_);
if (v_isZero_314_ == 1)
{
lean_object* v___x_315_; 
lean_dec(v_h__3_312_);
lean_dec(v_h__2_311_);
v___x_315_ = lean_apply_1(v_h__1_310_, v_x_309_);
return v___x_315_;
}
else
{
lean_object* v_one_316_; lean_object* v_n_317_; 
lean_dec(v_h__1_310_);
v_one_316_ = lean_unsigned_to_nat(1u);
v_n_317_ = lean_nat_sub(v_x_308_, v_one_316_);
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v___x_318_; 
lean_dec(v_h__3_312_);
v___x_318_ = lean_apply_1(v_h__2_311_, v_n_317_);
return v___x_318_;
}
else
{
lean_object* v_head_319_; lean_object* v_tail_320_; lean_object* v___x_321_; 
lean_dec(v_h__2_311_);
v_head_319_ = lean_ctor_get(v_x_309_, 0);
lean_inc(v_head_319_);
v_tail_320_ = lean_ctor_get(v_x_309_, 1);
lean_inc(v_tail_320_);
lean_dec_ref(v_x_309_);
v___x_321_ = lean_apply_3(v_h__3_312_, v_n_317_, v_head_319_, v_tail_320_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_, lean_object* v_h__3_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(v_x_322_, v_x_323_, v_h__1_324_, v_h__2_325_, v_h__3_326_);
lean_dec(v_x_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(lean_object* v_00_u03b1_328_, lean_object* v_motive_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_h__1_332_, lean_object* v_h__2_333_, lean_object* v_h__3_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(v_x_330_, v_x_331_, v_h__1_332_, v_h__2_333_, v_h__3_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_336_, lean_object* v_motive_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_, lean_object* v_h__3_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(v_00_u03b1_336_, v_motive_337_, v_x_338_, v_x_339_, v_h__1_340_, v_h__2_341_, v_h__3_342_);
lean_dec(v_x_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object* v_p_344_, lean_object* v_l_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
if (lean_obj_tag(v_a_346_) == 0)
{
lean_dec_ref(v_a_347_);
lean_dec_ref(v_p_344_);
lean_inc(v_l_345_);
return v_l_345_;
}
else
{
lean_object* v_head_348_; lean_object* v_tail_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_head_348_ = lean_ctor_get(v_a_346_, 0);
lean_inc(v_head_348_);
v_tail_349_ = lean_ctor_get(v_a_346_, 1);
lean_inc(v_tail_349_);
lean_dec_ref(v_a_346_);
lean_inc_ref(v_p_344_);
lean_inc(v_head_348_);
v___x_350_ = lean_apply_1(v_p_344_, v_head_348_);
v___x_351_ = lean_unbox(v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec(v_tail_349_);
lean_dec(v_head_348_);
lean_dec_ref(v_p_344_);
v___x_352_ = lean_array_to_list(v_a_347_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_array_push(v_a_347_, v_head_348_);
v_a_346_ = v_tail_349_;
v_a_347_ = v___x_353_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object* v_p_355_, lean_object* v_l_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_355_, v_l_356_, v_a_357_, v_a_358_);
lean_dec(v_l_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object* v_00_u03b1_360_, lean_object* v_p_361_, lean_object* v_l_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_361_, v_l_362_, v_a_363_, v_a_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object* v_00_u03b1_366_, lean_object* v_p_367_, lean_object* v_l_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(v_00_u03b1_366_, v_p_367_, v_l_368_, v_a_369_, v_a_370_);
lean_dec(v_l_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object* v_p_372_, lean_object* v_l_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_373_);
v___x_375_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_372_, v_l_373_, v_l_373_, v___x_374_);
lean_dec(v_l_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object* v_00_u03b1_376_, lean_object* v_p_377_, lean_object* v_l_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_378_);
v___x_380_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_377_, v_l_378_, v_l_378_, v___x_379_);
lean_dec(v_l_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_381_, lean_object* v_h__1_382_, lean_object* v_h__2_383_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v_h__2_383_);
v___x_384_ = lean_box(0);
v___x_385_ = lean_apply_1(v_h__1_382_, v___x_384_);
return v___x_385_;
}
else
{
lean_object* v_head_386_; lean_object* v_tail_387_; lean_object* v___x_388_; 
lean_dec(v_h__1_382_);
v_head_386_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_head_386_);
v_tail_387_ = lean_ctor_get(v_x_381_, 1);
lean_inc(v_tail_387_);
lean_dec_ref(v_x_381_);
v___x_388_ = lean_apply_2(v_h__2_383_, v_head_386_, v_tail_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_389_, lean_object* v_motive_390_, lean_object* v_x_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(v_x_391_, v_h__1_392_, v_h__2_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t v_x_395_, lean_object* v_h__1_396_, lean_object* v_h__2_397_){
_start:
{
if (v_x_395_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_h__1_396_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_apply_1(v_h__2_397_, v___x_398_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v_h__2_397_);
v___x_400_ = lean_box(0);
v___x_401_ = lean_apply_1(v_h__1_396_, v___x_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_402_, lean_object* v_h__1_403_, lean_object* v_h__2_404_){
_start:
{
uint8_t v_x_22__boxed_405_; lean_object* v_res_406_; 
v_x_22__boxed_405_ = lean_unbox(v_x_402_);
v_res_406_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_405_, v_h__1_403_, v_h__2_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object* v_motive_407_, uint8_t v_x_408_, lean_object* v_h__1_409_, lean_object* v_h__2_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_408_, v_h__1_409_, v_h__2_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_412_, lean_object* v_x_413_, lean_object* v_h__1_414_, lean_object* v_h__2_415_){
_start:
{
uint8_t v_x_33__boxed_416_; lean_object* v_res_417_; 
v_x_33__boxed_416_ = lean_unbox(v_x_413_);
v_res_417_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(v_motive_412_, v_x_33__boxed_416_, v_h__1_414_, v_h__2_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_h__1_420_, lean_object* v_h__2_421_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v___x_422_; 
lean_dec(v_h__2_421_);
v___x_422_ = lean_apply_1(v_h__1_420_, v_x_419_);
return v___x_422_;
}
else
{
lean_object* v_head_423_; lean_object* v_tail_424_; lean_object* v___x_425_; 
lean_dec(v_h__1_420_);
v_head_423_ = lean_ctor_get(v_x_418_, 0);
lean_inc(v_head_423_);
v_tail_424_ = lean_ctor_get(v_x_418_, 1);
lean_inc(v_tail_424_);
lean_dec_ref(v_x_418_);
v___x_425_ = lean_apply_3(v_h__2_421_, v_head_423_, v_tail_424_, v_x_419_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(lean_object* v_00_u03b1_426_, lean_object* v_motive_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(v_x_428_, v_x_429_, v_h__1_430_, v_h__2_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR___redArg(lean_object* v_l_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_array_mk(v_l_433_);
v___x_435_ = lean_array_pop(v___x_434_);
v___x_436_ = lean_array_to_list(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR(lean_object* v_00_u03b1_437_, lean_object* v_l_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_array_mk(v_l_438_);
v___x_440_ = lean_array_pop(v___x_439_);
v___x_441_ = lean_array_to_list(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object* v_p_442_, lean_object* v_l_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = l_List_reverse___redArg(v_l_443_);
v___x_445_ = l_List_find_x3f___redArg(v_p_442_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object* v_00_u03b1_446_, lean_object* v_p_447_, lean_object* v_l_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_List_findRev_x3fTR___redArg(v_p_447_, v_l_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_450_, lean_object* v_h__1_451_, lean_object* v_h__2_452_){
_start:
{
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_h__1_451_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_apply_1(v_h__2_452_, v___x_453_);
return v___x_454_;
}
else
{
lean_object* v_val_455_; lean_object* v___x_456_; 
lean_dec(v_h__2_452_);
v_val_455_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_val_455_);
lean_dec_ref(v_x_450_);
v___x_456_ = lean_apply_1(v_h__1_451_, v_val_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_457_, lean_object* v_motive_458_, lean_object* v_x_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(v_x_459_, v_h__1_460_, v_h__2_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object* v_f_463_, lean_object* v_l_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = l_List_reverse___redArg(v_l_464_);
v___x_466_ = l_List_findSome_x3f___redArg(v_f_463_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object* v_00_u03b1_467_, lean_object* v_00_u03b2_468_, lean_object* v_f_469_, lean_object* v_l_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_List_findSomeRev_x3fTR___redArg(v_f_469_, v_l_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object* v_x1_472_, lean_object* v_x2_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v_x1_472_);
lean_ctor_set(v___x_474_, 1, v_x2_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object* v_inst_476_, lean_object* v_l_477_, lean_object* v_b_478_, lean_object* v_c_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
if (lean_obj_tag(v_a_480_) == 0)
{
lean_dec_ref(v_a_481_);
lean_dec(v_c_479_);
lean_dec(v_b_478_);
lean_dec_ref(v_inst_476_);
lean_inc(v_l_477_);
return v_l_477_;
}
else
{
lean_object* v_head_482_; lean_object* v_tail_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_502_; 
v_head_482_ = lean_ctor_get(v_a_480_, 0);
v_tail_483_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_502_ == 0)
{
v___x_485_ = v_a_480_;
v_isShared_486_ = v_isSharedCheck_502_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_tail_483_);
lean_inc(v_head_482_);
lean_dec(v_a_480_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_502_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
lean_inc_ref(v_inst_476_);
lean_inc(v_head_482_);
lean_inc(v_b_478_);
v___x_487_ = lean_apply_2(v_inst_476_, v_b_478_, v_head_482_);
v___x_488_ = lean_unbox(v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_del_object(v___x_485_);
v___x_489_ = lean_array_push(v_a_481_, v_head_482_);
v_a_480_ = v_tail_483_;
v_a_481_ = v___x_489_;
goto _start;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_head_482_);
lean_dec(v_b_478_);
lean_dec_ref(v_inst_476_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v_c_479_);
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_c_479_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_tail_483_);
v___x_492_ = v_reuseFailAlloc_501_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_493_ = lean_array_get_size(v_a_481_);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_493_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_a_481_);
return v___x_492_;
}
else
{
lean_object* v___f_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___f_497_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_498_ = lean_usize_of_nat(v___x_493_);
v___x_499_ = ((size_t)0ULL);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_495_, v___f_497_, v_a_481_, v___x_498_, v___x_499_, v___x_492_);
return v___x_500_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object* v_inst_503_, lean_object* v_l_504_, lean_object* v_b_505_, lean_object* v_c_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_503_, v_l_504_, v_b_505_, v_c_506_, v_a_507_, v_a_508_);
lean_dec(v_l_504_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object* v_00_u03b1_510_, lean_object* v_inst_511_, lean_object* v_l_512_, lean_object* v_b_513_, lean_object* v_c_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_511_, v_l_512_, v_b_513_, v_c_514_, v_a_515_, v_a_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object* v_00_u03b1_518_, lean_object* v_inst_519_, lean_object* v_l_520_, lean_object* v_b_521_, lean_object* v_c_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(v_00_u03b1_518_, v_inst_519_, v_l_520_, v_b_521_, v_c_522_, v_a_523_, v_a_524_);
lean_dec(v_l_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object* v_inst_526_, lean_object* v_l_527_, lean_object* v_b_528_, lean_object* v_c_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_527_);
v___x_531_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_526_, v_l_527_, v_b_528_, v_c_529_, v_l_527_, v___x_530_);
lean_dec(v_l_527_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object* v_00_u03b1_532_, lean_object* v_inst_533_, lean_object* v_l_534_, lean_object* v_b_535_, lean_object* v_c_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_534_);
v___x_538_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_533_, v_l_534_, v_b_535_, v_c_536_, v_l_534_, v___x_537_);
lean_dec(v_l_534_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v___x_544_; 
lean_dec(v_h__2_543_);
v___x_544_ = lean_apply_2(v_h__1_542_, v_x_540_, v_x_541_);
return v___x_544_;
}
else
{
lean_object* v_head_545_; lean_object* v_tail_546_; lean_object* v___x_547_; 
lean_dec(v_h__1_542_);
v_head_545_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_head_545_);
v_tail_546_ = lean_ctor_get(v_x_539_, 1);
lean_inc(v_tail_546_);
lean_dec_ref(v_x_539_);
v___x_547_ = lean_apply_4(v_h__2_543_, v_head_545_, v_tail_546_, v_x_540_, v_x_541_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter(lean_object* v_00_u03b1_548_, lean_object* v_motive_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_h__1_553_, lean_object* v_h__2_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(v_x_550_, v_x_551_, v_x_552_, v_h__1_553_, v_h__2_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object* v_f_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
if (lean_obj_tag(v_a_557_) == 0)
{
lean_object* v___x_560_; 
lean_dec(v_a_558_);
lean_dec(v_f_556_);
v___x_560_ = lean_array_to_list(v_a_559_);
return v___x_560_;
}
else
{
lean_object* v_head_561_; lean_object* v_tail_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_581_; 
v_head_561_ = lean_ctor_get(v_a_557_, 0);
v_tail_562_ = lean_ctor_get(v_a_557_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_581_ == 0)
{
v___x_564_ = v_a_557_;
v_isShared_565_ = v_isSharedCheck_581_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_tail_562_);
lean_inc(v_head_561_);
lean_dec(v_a_557_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_581_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_zero_566_; uint8_t v_isZero_567_; 
v_zero_566_ = lean_unsigned_to_nat(0u);
v_isZero_567_ = lean_nat_dec_eq(v_a_558_, v_zero_566_);
if (v_isZero_567_ == 1)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_a_558_);
v___x_568_ = lean_apply_1(v_f_556_, v_head_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_568_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_tail_562_);
v___x_570_ = v_reuseFailAlloc_576_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v_a_559_);
v___x_572_ = lean_nat_dec_lt(v_zero_566_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec_ref(v_a_559_);
return v___x_570_;
}
else
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_usize_of_nat(v___x_571_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_559_, v___x_573_, v___x_574_, v___x_570_);
lean_dec_ref(v_a_559_);
return v___x_575_;
}
}
}
else
{
lean_object* v_one_577_; lean_object* v_n_578_; lean_object* v___x_579_; 
lean_del_object(v___x_564_);
v_one_577_ = lean_unsigned_to_nat(1u);
v_n_578_ = lean_nat_sub(v_a_558_, v_one_577_);
lean_dec(v_a_558_);
v___x_579_ = lean_array_push(v_a_559_, v_head_561_);
v_a_557_ = v_tail_562_;
v_a_558_ = v_n_578_;
v_a_559_ = v___x_579_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object* v_00_u03b1_582_, lean_object* v_f_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_583_, v_a_584_, v_a_585_, v_a_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object* v_l_588_, lean_object* v_i_589_, lean_object* v_f_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_592_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_590_, v_l_588_, v_i_589_, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object* v_00_u03b1_593_, lean_object* v_l_594_, lean_object* v_i_595_, lean_object* v_f_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_List_modifyTR___redArg(v_l_594_, v_i_595_, v_f_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_zero_602_; uint8_t v_isZero_603_; 
v_zero_602_ = lean_unsigned_to_nat(0u);
v_isZero_603_ = lean_nat_dec_eq(v_a_599_, v_zero_602_);
if (v_isZero_603_ == 1)
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
lean_dec(v_a_599_);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_598_);
lean_ctor_set(v___x_604_, 1, v_a_600_);
v___x_605_ = lean_array_get_size(v_a_601_);
v___x_606_ = lean_nat_dec_lt(v_zero_602_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_a_601_);
return v___x_604_;
}
else
{
size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_usize_of_nat(v___x_605_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_601_, v___x_607_, v___x_608_, v___x_604_);
lean_dec_ref(v_a_601_);
return v___x_609_;
}
}
else
{
if (lean_obj_tag(v_a_600_) == 0)
{
lean_object* v___x_610_; 
lean_dec(v_a_599_);
lean_dec(v_a_598_);
v___x_610_ = lean_array_to_list(v_a_601_);
return v___x_610_;
}
else
{
lean_object* v_head_611_; lean_object* v_tail_612_; lean_object* v_one_613_; lean_object* v_n_614_; lean_object* v___x_615_; 
v_head_611_ = lean_ctor_get(v_a_600_, 0);
lean_inc(v_head_611_);
v_tail_612_ = lean_ctor_get(v_a_600_, 1);
lean_inc(v_tail_612_);
lean_dec_ref(v_a_600_);
v_one_613_ = lean_unsigned_to_nat(1u);
v_n_614_ = lean_nat_sub(v_a_599_, v_one_613_);
lean_dec(v_a_599_);
v___x_615_ = lean_array_push(v_a_601_, v_head_611_);
v_a_599_ = v_n_614_;
v_a_600_ = v_tail_612_;
v_a_601_ = v___x_615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object* v_00_u03b1_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object* v_l_623_, lean_object* v_n_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_627_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_625_, v_n_624_, v_l_623_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object* v_00_u03b1_628_, lean_object* v_l_629_, lean_object* v_n_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_633_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_631_, v_n_630_, v_l_629_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_, lean_object* v_h__3_639_){
_start:
{
lean_object* v_zero_640_; uint8_t v_isZero_641_; 
v_zero_640_ = lean_unsigned_to_nat(0u);
v_isZero_641_ = lean_nat_dec_eq(v_x_634_, v_zero_640_);
if (v_isZero_641_ == 1)
{
lean_object* v___x_642_; 
lean_dec(v_h__3_639_);
lean_dec(v_h__2_638_);
lean_dec(v_x_634_);
v___x_642_ = lean_apply_2(v_h__1_637_, v_x_635_, v_x_636_);
return v___x_642_;
}
else
{
lean_dec(v_h__1_637_);
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_643_; 
lean_dec(v_h__3_639_);
v___x_643_ = lean_apply_3(v_h__2_638_, v_x_634_, v_x_636_, lean_box(0));
return v___x_643_;
}
else
{
lean_object* v_head_644_; lean_object* v_tail_645_; lean_object* v_one_646_; lean_object* v_n_647_; lean_object* v___x_648_; 
lean_dec(v_h__2_638_);
v_head_644_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_head_644_);
v_tail_645_ = lean_ctor_get(v_x_635_, 1);
lean_inc(v_tail_645_);
lean_dec_ref(v_x_635_);
v_one_646_ = lean_unsigned_to_nat(1u);
v_n_647_ = lean_nat_sub(v_x_634_, v_one_646_);
lean_dec(v_x_634_);
v___x_648_ = lean_apply_4(v_h__3_639_, v_n_647_, v_head_644_, v_tail_645_, v_x_636_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object* v_00_u03b1_649_, lean_object* v_motive_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_, lean_object* v_h__3_656_){
_start:
{
lean_object* v_zero_657_; uint8_t v_isZero_658_; 
v_zero_657_ = lean_unsigned_to_nat(0u);
v_isZero_658_ = lean_nat_dec_eq(v_x_651_, v_zero_657_);
if (v_isZero_658_ == 1)
{
lean_object* v___x_659_; 
lean_dec(v_h__3_656_);
lean_dec(v_h__2_655_);
lean_dec(v_x_651_);
v___x_659_ = lean_apply_2(v_h__1_654_, v_x_652_, v_x_653_);
return v___x_659_;
}
else
{
lean_dec(v_h__1_654_);
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v___x_660_; 
lean_dec(v_h__3_656_);
v___x_660_ = lean_apply_3(v_h__2_655_, v_x_651_, v_x_653_, lean_box(0));
return v___x_660_;
}
else
{
lean_object* v_head_661_; lean_object* v_tail_662_; lean_object* v_one_663_; lean_object* v_n_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_655_);
v_head_661_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_head_661_);
v_tail_662_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_tail_662_);
lean_dec_ref(v_x_652_);
v_one_663_ = lean_unsigned_to_nat(1u);
v_n_664_ = lean_nat_sub(v_x_651_, v_one_663_);
lean_dec(v_x_651_);
v___x_665_ = lean_apply_4(v_h__3_656_, v_n_664_, v_head_661_, v_tail_662_, v_x_653_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object* v_inst_666_, lean_object* v_l_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
if (lean_obj_tag(v_a_669_) == 0)
{
lean_dec_ref(v_a_670_);
lean_dec(v_a_668_);
lean_dec_ref(v_inst_666_);
lean_inc(v_l_667_);
return v_l_667_;
}
else
{
lean_object* v_head_671_; lean_object* v_tail_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_head_671_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_head_671_);
v_tail_672_ = lean_ctor_get(v_a_669_, 1);
lean_inc(v_tail_672_);
lean_dec_ref(v_a_669_);
lean_inc_ref(v_inst_666_);
lean_inc(v_a_668_);
lean_inc(v_head_671_);
v___x_673_ = lean_apply_2(v_inst_666_, v_head_671_, v_a_668_);
v___x_674_ = lean_unbox(v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_array_push(v_a_670_, v_head_671_);
v_a_669_ = v_tail_672_;
v_a_670_ = v___x_675_;
goto _start;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
lean_dec(v_head_671_);
lean_dec(v_a_668_);
lean_dec_ref(v_inst_666_);
v___x_677_ = lean_array_get_size(v_a_670_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_677_);
if (v___x_680_ == 0)
{
lean_dec_ref(v_a_670_);
return v_tail_672_;
}
else
{
lean_object* v___f_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___f_681_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_682_ = lean_usize_of_nat(v___x_677_);
v___x_683_ = ((size_t)0ULL);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_679_, v___f_681_, v_a_670_, v___x_682_, v___x_683_, v_tail_672_);
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object* v_inst_685_, lean_object* v_l_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_685_, v_l_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_l_686_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object* v_00_u03b1_691_, lean_object* v_inst_692_, lean_object* v_l_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_692_, v_l_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object* v_00_u03b1_698_, lean_object* v_inst_699_, lean_object* v_l_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(v_00_u03b1_698_, v_inst_699_, v_l_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_l_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object* v_inst_705_, lean_object* v_l_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_706_);
v___x_709_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_705_, v_l_706_, v_a_707_, v_l_706_, v___x_708_);
lean_dec(v_l_706_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object* v_00_u03b1_710_, lean_object* v_inst_711_, lean_object* v_l_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_712_);
v___x_715_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_711_, v_l_712_, v_a_713_, v_l_712_, v___x_714_);
lean_dec(v_l_712_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object* v_p_716_, lean_object* v_l_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
if (lean_obj_tag(v_a_718_) == 0)
{
lean_dec_ref(v_a_719_);
lean_dec_ref(v_p_716_);
lean_inc(v_l_717_);
return v_l_717_;
}
else
{
lean_object* v_head_720_; lean_object* v_tail_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_head_720_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_head_720_);
v_tail_721_ = lean_ctor_get(v_a_718_, 1);
lean_inc(v_tail_721_);
lean_dec_ref(v_a_718_);
lean_inc_ref(v_p_716_);
lean_inc(v_head_720_);
v___x_722_ = lean_apply_1(v_p_716_, v_head_720_);
v___x_723_ = lean_unbox(v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_array_push(v_a_719_, v_head_720_);
v_a_718_ = v_tail_721_;
v_a_719_ = v___x_724_;
goto _start;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
lean_dec(v_head_720_);
lean_dec_ref(v_p_716_);
v___x_726_ = lean_array_get_size(v_a_719_);
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_729_ = lean_nat_dec_lt(v___x_727_, v___x_726_);
if (v___x_729_ == 0)
{
lean_dec_ref(v_a_719_);
return v_tail_721_;
}
else
{
lean_object* v___f_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___f_730_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_731_ = lean_usize_of_nat(v___x_726_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_728_, v___f_730_, v_a_719_, v___x_731_, v___x_732_, v_tail_721_);
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object* v_p_734_, lean_object* v_l_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_734_, v_l_735_, v_a_736_, v_a_737_);
lean_dec(v_l_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object* v_00_u03b1_739_, lean_object* v_p_740_, lean_object* v_l_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_740_, v_l_741_, v_a_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object* v_00_u03b1_745_, lean_object* v_p_746_, lean_object* v_l_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(v_00_u03b1_745_, v_p_746_, v_l_747_, v_a_748_, v_a_749_);
lean_dec(v_l_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object* v_p_751_, lean_object* v_l_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_752_);
v___x_754_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_751_, v_l_752_, v_l_752_, v___x_753_);
lean_dec(v_l_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object* v_00_u03b1_755_, lean_object* v_p_756_, lean_object* v_l_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_757_);
v___x_759_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_756_, v_l_757_, v_l_757_, v___x_758_);
lean_dec(v_l_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object* v_l_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
if (lean_obj_tag(v_a_761_) == 0)
{
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_inc(v_l_760_);
return v_l_760_;
}
else
{
lean_object* v_head_764_; lean_object* v_tail_765_; lean_object* v_zero_766_; uint8_t v_isZero_767_; 
v_head_764_ = lean_ctor_get(v_a_761_, 0);
lean_inc(v_head_764_);
v_tail_765_ = lean_ctor_get(v_a_761_, 1);
lean_inc(v_tail_765_);
lean_dec_ref(v_a_761_);
v_zero_766_ = lean_unsigned_to_nat(0u);
v_isZero_767_ = lean_nat_dec_eq(v_a_762_, v_zero_766_);
if (v_isZero_767_ == 1)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
lean_dec(v_head_764_);
lean_dec(v_a_762_);
v___x_768_ = lean_array_get_size(v_a_763_);
v___x_769_ = lean_nat_dec_lt(v_zero_766_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec_ref(v_a_763_);
return v_tail_765_;
}
else
{
size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_usize_of_nat(v___x_768_);
v___x_771_ = ((size_t)0ULL);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_763_, v___x_770_, v___x_771_, v_tail_765_);
lean_dec_ref(v_a_763_);
return v___x_772_;
}
}
else
{
lean_object* v_one_773_; lean_object* v_n_774_; lean_object* v___x_775_; 
v_one_773_ = lean_unsigned_to_nat(1u);
v_n_774_ = lean_nat_sub(v_a_762_, v_one_773_);
lean_dec(v_a_762_);
v___x_775_ = lean_array_push(v_a_763_, v_head_764_);
v_a_761_ = v_tail_765_;
v_a_762_ = v_n_774_;
v_a_763_ = v___x_775_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object* v_l_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_l_777_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object* v_00_u03b1_782_, lean_object* v_l_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_783_, v_a_784_, v_a_785_, v_a_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object* v_00_u03b1_788_, lean_object* v_l_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(v_00_u03b1_788_, v_l_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_l_789_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object* v_l_794_, lean_object* v_n_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_794_);
v___x_797_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_794_, v_l_794_, v_n_795_, v___x_796_);
lean_dec(v_l_794_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object* v_00_u03b1_798_, lean_object* v_l_799_, lean_object* v_n_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_799_);
v___x_802_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_799_, v_l_799_, v_n_800_, v___x_801_);
lean_dec(v_l_799_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_h__1_805_, lean_object* v_h__2_806_, lean_object* v_h__3_807_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v___x_808_; 
lean_dec(v_h__3_807_);
lean_dec(v_h__2_806_);
v___x_808_ = lean_apply_1(v_h__1_805_, v_x_804_);
return v___x_808_;
}
else
{
lean_object* v_head_809_; lean_object* v_tail_810_; lean_object* v_zero_811_; uint8_t v_isZero_812_; 
lean_dec(v_h__1_805_);
v_head_809_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_head_809_);
v_tail_810_ = lean_ctor_get(v_x_803_, 1);
lean_inc(v_tail_810_);
lean_dec_ref(v_x_803_);
v_zero_811_ = lean_unsigned_to_nat(0u);
v_isZero_812_ = lean_nat_dec_eq(v_x_804_, v_zero_811_);
if (v_isZero_812_ == 1)
{
lean_object* v___x_813_; 
lean_dec(v_h__3_807_);
lean_dec(v_x_804_);
v___x_813_ = lean_apply_2(v_h__2_806_, v_head_809_, v_tail_810_);
return v___x_813_;
}
else
{
lean_object* v_one_814_; lean_object* v_n_815_; lean_object* v___x_816_; 
lean_dec(v_h__2_806_);
v_one_814_ = lean_unsigned_to_nat(1u);
v_n_815_ = lean_nat_sub(v_x_804_, v_one_814_);
lean_dec(v_x_804_);
v___x_816_ = lean_apply_3(v_h__3_807_, v_head_809_, v_tail_810_, v_n_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_817_, lean_object* v_motive_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_h__1_821_, lean_object* v_h__2_822_, lean_object* v_h__3_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(v_x_819_, v_x_820_, v_h__1_821_, v_h__2_822_, v_h__3_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object* v_f_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
if (lean_obj_tag(v_a_826_) == 1)
{
if (lean_obj_tag(v_a_827_) == 1)
{
lean_object* v_head_829_; lean_object* v_tail_830_; lean_object* v_head_831_; lean_object* v_tail_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_head_829_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_head_829_);
v_tail_830_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_tail_830_);
lean_dec_ref(v_a_826_);
v_head_831_ = lean_ctor_get(v_a_827_, 0);
lean_inc(v_head_831_);
v_tail_832_ = lean_ctor_get(v_a_827_, 1);
lean_inc(v_tail_832_);
lean_dec_ref(v_a_827_);
lean_inc(v_f_825_);
v___x_833_ = lean_apply_2(v_f_825_, v_head_829_, v_head_831_);
v___x_834_ = lean_array_push(v_a_828_, v___x_833_);
v_a_826_ = v_tail_830_;
v_a_827_ = v_tail_832_;
v_a_828_ = v___x_834_;
goto _start;
}
else
{
lean_object* v___x_836_; 
lean_dec_ref(v_a_826_);
lean_dec(v_a_827_);
lean_dec(v_f_825_);
v___x_836_ = lean_array_to_list(v_a_828_);
return v___x_836_;
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_a_827_);
lean_dec(v_a_826_);
lean_dec(v_f_825_);
v___x_837_ = lean_array_to_list(v_a_828_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object* v_00_u03b1_838_, lean_object* v_00_u03b2_839_, lean_object* v_00_u03b3_840_, lean_object* v_f_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_841_, v_a_842_, v_a_843_, v_a_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object* v_f_846_, lean_object* v_as_847_, lean_object* v_bs_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_850_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_846_, v_as_847_, v_bs_848_, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_00_u03b3_853_, lean_object* v_f_854_, lean_object* v_as_855_, lean_object* v_bs_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_858_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_854_, v_as_855_, v_bs_856_, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_){
_start:
{
if (lean_obj_tag(v_x_859_) == 1)
{
if (lean_obj_tag(v_x_860_) == 1)
{
lean_object* v_head_864_; lean_object* v_tail_865_; lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v___x_868_; 
lean_dec(v_h__2_863_);
v_head_864_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_head_864_);
v_tail_865_ = lean_ctor_get(v_x_859_, 1);
lean_inc(v_tail_865_);
lean_dec_ref(v_x_859_);
v_head_866_ = lean_ctor_get(v_x_860_, 0);
lean_inc(v_head_866_);
v_tail_867_ = lean_ctor_get(v_x_860_, 1);
lean_inc(v_tail_867_);
lean_dec_ref(v_x_860_);
v___x_868_ = lean_apply_5(v_h__1_862_, v_head_864_, v_tail_865_, v_head_866_, v_tail_867_, v_x_861_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; 
lean_dec(v_h__1_862_);
v___x_869_ = lean_apply_4(v_h__2_863_, v_x_859_, v_x_860_, v_x_861_, lean_box(0));
return v___x_869_;
}
}
else
{
lean_object* v___x_870_; 
lean_dec(v_h__1_862_);
v___x_870_ = lean_apply_4(v_h__2_863_, v_x_859_, v_x_860_, v_x_861_, lean_box(0));
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_00_u03b3_873_, lean_object* v_motive_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_h__1_878_, lean_object* v_h__2_879_){
_start:
{
if (lean_obj_tag(v_x_875_) == 1)
{
if (lean_obj_tag(v_x_876_) == 1)
{
lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v_head_882_; lean_object* v_tail_883_; lean_object* v___x_884_; 
lean_dec(v_h__2_879_);
v_head_880_ = lean_ctor_get(v_x_875_, 0);
lean_inc(v_head_880_);
v_tail_881_ = lean_ctor_get(v_x_875_, 1);
lean_inc(v_tail_881_);
lean_dec_ref(v_x_875_);
v_head_882_ = lean_ctor_get(v_x_876_, 0);
lean_inc(v_head_882_);
v_tail_883_ = lean_ctor_get(v_x_876_, 1);
lean_inc(v_tail_883_);
lean_dec_ref(v_x_876_);
v___x_884_ = lean_apply_5(v_h__1_878_, v_head_880_, v_tail_881_, v_head_882_, v_tail_883_, v_x_877_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
lean_dec(v_h__1_878_);
v___x_885_ = lean_apply_4(v_h__2_879_, v_x_875_, v_x_876_, v_x_877_, lean_box(0));
return v___x_885_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_h__1_878_);
v___x_886_ = lean_apply_4(v_h__2_879_, v_x_875_, v_x_876_, v_x_877_, lean_box(0));
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object* v_as_887_, size_t v_i_888_, size_t v_stop_889_, lean_object* v_b_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_eq(v_i_888_, v_stop_889_);
if (v___x_891_ == 0)
{
lean_object* v_fst_892_; lean_object* v_snd_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_908_; 
v_fst_892_ = lean_ctor_get(v_b_890_, 0);
v_snd_893_ = lean_ctor_get(v_b_890_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_b_890_);
if (v_isSharedCheck_908_ == 0)
{
v___x_895_ = v_b_890_;
v_isShared_896_ = v_isSharedCheck_908_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_snd_893_);
lean_inc(v_fst_892_);
lean_dec(v_b_890_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_908_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v_i_888_, v___x_897_);
v___x_899_ = lean_array_uget_borrowed(v_as_887_, v___x_898_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_sub(v_fst_892_, v___x_900_);
lean_dec(v_fst_892_);
lean_inc(v___x_901_);
lean_inc(v___x_899_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___x_901_);
lean_ctor_set(v___x_895_, 0, v___x_899_);
v___x_903_ = v___x_895_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_snd_893_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_901_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v_i_888_ = v___x_898_;
v_b_890_ = v___x_905_;
goto _start;
}
}
}
else
{
return v_b_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object* v_as_909_, lean_object* v_i_910_, lean_object* v_stop_911_, lean_object* v_b_912_){
_start:
{
size_t v_i_boxed_913_; size_t v_stop_boxed_914_; lean_object* v_res_915_; 
v_i_boxed_913_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_stop_boxed_914_ = lean_unbox_usize(v_stop_911_);
lean_dec(v_stop_911_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_909_, v_i_boxed_913_, v_stop_boxed_914_, v_b_912_);
lean_dec_ref(v_as_909_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object* v_l_916_, lean_object* v_n_917_){
_start:
{
lean_object* v_as_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_as_918_ = lean_array_mk(v_l_916_);
v___x_919_ = lean_array_get_size(v_as_918_);
v___x_920_ = lean_box(0);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_nat_dec_lt(v___x_921_, v___x_919_);
if (v___x_922_ == 0)
{
lean_dec_ref(v_as_918_);
return v___x_920_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; lean_object* v_snd_928_; 
v___x_923_ = lean_nat_add(v_n_917_, v___x_919_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_920_);
v___x_925_ = lean_usize_of_nat(v___x_919_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_918_, v___x_925_, v___x_926_, v___x_924_);
lean_dec_ref(v_as_918_);
v_snd_928_ = lean_ctor_get(v___x_927_, 1);
lean_inc(v_snd_928_);
lean_dec_ref(v___x_927_);
return v_snd_928_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object* v_l_929_, lean_object* v_n_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_List_zipIdxTR___redArg(v_l_929_, v_n_930_);
lean_dec(v_n_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object* v_00_u03b1_932_, lean_object* v_l_933_, lean_object* v_n_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_List_zipIdxTR___redArg(v_l_933_, v_n_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object* v_00_u03b1_936_, lean_object* v_l_937_, lean_object* v_n_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_List_zipIdxTR(v_00_u03b1_936_, v_l_937_, v_n_938_);
lean_dec(v_n_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object* v_00_u03b1_940_, lean_object* v_as_941_, size_t v_i_942_, size_t v_stop_943_, lean_object* v_b_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_941_, v_i_942_, v_stop_943_, v_b_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object* v_00_u03b1_946_, lean_object* v_as_947_, lean_object* v_i_948_, lean_object* v_stop_949_, lean_object* v_b_950_){
_start:
{
size_t v_i_boxed_951_; size_t v_stop_boxed_952_; lean_object* v_res_953_; 
v_i_boxed_951_ = lean_unbox_usize(v_i_948_);
lean_dec(v_i_948_);
v_stop_boxed_952_ = lean_unbox_usize(v_stop_949_);
lean_dec(v_stop_949_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(v_00_u03b1_946_, v_as_947_, v_i_boxed_951_, v_stop_boxed_952_, v_b_950_);
lean_dec_ref(v_as_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_h__1_956_, lean_object* v_h__2_957_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v___x_958_; 
lean_dec(v_h__2_957_);
v___x_958_ = lean_apply_1(v_h__1_956_, v_x_955_);
return v___x_958_;
}
else
{
lean_object* v_head_959_; lean_object* v_tail_960_; lean_object* v___x_961_; 
lean_dec(v_h__1_956_);
v_head_959_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_head_959_);
v_tail_960_ = lean_ctor_get(v_x_954_, 1);
lean_inc(v_tail_960_);
lean_dec_ref(v_x_954_);
v___x_961_ = lean_apply_3(v_h__2_957_, v_head_959_, v_tail_960_, v_x_955_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_962_, lean_object* v_motive_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_h__1_966_, lean_object* v_h__2_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(v_x_964_, v_x_965_, v_h__1_966_, v_h__2_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object* v_sep_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
if (lean_obj_tag(v_a_971_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_973_ = lean_array_get_size(v_a_972_);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_nat_dec_lt(v___x_974_, v___x_973_);
if (v___x_975_ == 0)
{
lean_dec_ref(v_a_972_);
return v_a_970_;
}
else
{
size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_usize_of_nat(v___x_973_);
v___x_977_ = ((size_t)0ULL);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_972_, v___x_976_, v___x_977_, v_a_970_);
lean_dec_ref(v_a_972_);
return v___x_978_;
}
}
else
{
lean_object* v_head_979_; lean_object* v_tail_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_head_979_ = lean_ctor_get(v_a_971_, 0);
lean_inc(v_head_979_);
v_tail_980_ = lean_ctor_get(v_a_971_, 1);
lean_inc(v_tail_980_);
lean_dec_ref(v_a_971_);
v___x_981_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_972_, v_a_970_);
v___x_982_ = l_Array_append___redArg(v___x_981_, v_sep_969_);
v_a_970_ = v_head_979_;
v_a_971_ = v_tail_980_;
v_a_972_ = v___x_982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object* v_sep_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec_ref(v_sep_984_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object* v_00_u03b1_989_, lean_object* v_sep_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object* v_00_u03b1_995_, lean_object* v_sep_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(v_00_u03b1_995_, v_sep_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec_ref(v_sep_996_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object* v_sep_1001_, lean_object* v_x_1002_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_object* v___x_1003_; 
lean_dec(v_sep_1001_);
v___x_1003_ = lean_box(0);
return v___x_1003_;
}
else
{
lean_object* v_tail_1004_; 
v_tail_1004_ = lean_ctor_get(v_x_1002_, 1);
if (lean_obj_tag(v_tail_1004_) == 0)
{
lean_object* v_head_1005_; 
lean_dec(v_sep_1001_);
v_head_1005_ = lean_ctor_get(v_x_1002_, 0);
lean_inc(v_head_1005_);
lean_dec_ref(v_x_1002_);
return v_head_1005_;
}
else
{
lean_object* v_head_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc(v_tail_1004_);
v_head_1006_ = lean_ctor_get(v_x_1002_, 0);
lean_inc(v_head_1006_);
lean_dec_ref(v_x_1002_);
v___x_1007_ = lean_array_mk(v_sep_1001_);
v___x_1008_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_1009_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v___x_1007_, v_head_1006_, v_tail_1004_, v___x_1008_);
lean_dec_ref(v___x_1007_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object* v_00_u03b1_1010_, lean_object* v_sep_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_List_intercalateTR___redArg(v_sep_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object* v_x_1014_, lean_object* v_h__1_1015_, lean_object* v_h__2_1016_, lean_object* v_h__3_1017_){
_start:
{
if (lean_obj_tag(v_x_1014_) == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_h__3_1017_);
lean_dec(v_h__2_1016_);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_apply_1(v_h__1_1015_, v___x_1018_);
return v___x_1019_;
}
else
{
lean_object* v_tail_1020_; 
lean_dec(v_h__1_1015_);
v_tail_1020_ = lean_ctor_get(v_x_1014_, 1);
if (lean_obj_tag(v_tail_1020_) == 0)
{
lean_object* v_head_1021_; lean_object* v___x_1022_; 
lean_dec(v_h__3_1017_);
v_head_1021_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_head_1021_);
lean_dec_ref(v_x_1014_);
v___x_1022_ = lean_apply_1(v_h__2_1016_, v_head_1021_);
return v___x_1022_;
}
else
{
lean_object* v_head_1023_; lean_object* v___x_1024_; 
lean_inc(v_tail_1020_);
lean_dec(v_h__2_1016_);
v_head_1023_ = lean_ctor_get(v_x_1014_, 0);
lean_inc(v_head_1023_);
lean_dec_ref(v_x_1014_);
v___x_1024_ = lean_apply_3(v_h__3_1017_, v_head_1023_, v_tail_1020_, lean_box(0));
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object* v_00_u03b1_1025_, lean_object* v_motive_1026_, lean_object* v_x_1027_, lean_object* v_h__1_1028_, lean_object* v_h__2_1029_, lean_object* v_h__3_1030_){
_start:
{
if (lean_obj_tag(v_x_1027_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__3_1030_);
lean_dec(v_h__2_1029_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_apply_1(v_h__1_1028_, v___x_1031_);
return v___x_1032_;
}
else
{
lean_object* v_tail_1033_; 
lean_dec(v_h__1_1028_);
v_tail_1033_ = lean_ctor_get(v_x_1027_, 1);
if (lean_obj_tag(v_tail_1033_) == 0)
{
lean_object* v_head_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__3_1030_);
v_head_1034_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_head_1034_);
lean_dec_ref(v_x_1027_);
v___x_1035_ = lean_apply_1(v_h__2_1029_, v_head_1034_);
return v___x_1035_;
}
else
{
lean_object* v_head_1036_; lean_object* v___x_1037_; 
lean_inc(v_tail_1033_);
lean_dec(v_h__2_1029_);
v_head_1036_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_head_1036_);
lean_dec_ref(v_x_1027_);
v___x_1037_ = lean_apply_3(v_h__3_1030_, v_head_1036_, v_tail_1033_, lean_box(0));
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_h__1_1041_, lean_object* v_h__2_1042_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v___x_1043_; 
lean_dec(v_h__2_1042_);
v___x_1043_ = lean_apply_2(v_h__1_1041_, v_x_1038_, v_x_1040_);
return v___x_1043_;
}
else
{
lean_object* v_head_1044_; lean_object* v_tail_1045_; lean_object* v___x_1046_; 
lean_dec(v_h__1_1041_);
v_head_1044_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_head_1044_);
v_tail_1045_ = lean_ctor_get(v_x_1039_, 1);
lean_inc(v_tail_1045_);
lean_dec_ref(v_x_1039_);
v___x_1046_ = lean_apply_4(v_h__2_1042_, v_x_1038_, v_head_1044_, v_tail_1045_, v_x_1040_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter(lean_object* v_00_u03b1_1047_, lean_object* v_motive_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_h__1_1052_, lean_object* v_h__2_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(v_x_1049_, v_x_1050_, v_x_1051_, v_h__1_1052_, v_h__2_1053_);
return v___x_1054_;
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
