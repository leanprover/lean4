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
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object* v_p_477_, lean_object* v_l_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = l_List_reverse___redArg(v_l_478_);
v___x_480_ = l_List_find_x3f___redArg(v_p_477_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object* v_00_u03b1_481_, lean_object* v_p_482_, lean_object* v_l_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_List_findRev_x3fTR___redArg(v_p_482_, v_l_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_485_, lean_object* v_h__1_486_, lean_object* v_h__2_487_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_h__1_486_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_apply_1(v_h__2_487_, v___x_488_);
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_487_);
v_val_490_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_val_490_);
lean_dec_ref(v_x_485_);
v___x_491_ = lean_apply_1(v_h__1_486_, v_val_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_492_, lean_object* v_motive_493_, lean_object* v_x_494_, lean_object* v_h__1_495_, lean_object* v_h__2_496_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_h__1_495_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_apply_1(v_h__2_496_, v___x_497_);
return v___x_498_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_500_; 
lean_dec(v_h__2_496_);
v_val_499_ = lean_ctor_get(v_x_494_, 0);
lean_inc(v_val_499_);
lean_dec_ref(v_x_494_);
v___x_500_ = lean_apply_1(v_h__1_495_, v_val_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object* v_f_501_, lean_object* v_l_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = l_List_reverse___redArg(v_l_502_);
v___x_504_ = l_List_findSome_x3f___redArg(v_f_501_, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_f_507_, lean_object* v_l_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_List_findSomeRev_x3fTR___redArg(v_f_507_, v_l_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object* v_x1_510_, lean_object* v_x2_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_512_, 0, v_x1_510_);
lean_ctor_set(v___x_512_, 1, v_x2_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object* v_inst_514_, lean_object* v_l_515_, lean_object* v_b_516_, lean_object* v_c_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
if (lean_obj_tag(v_a_518_) == 0)
{
lean_dec_ref(v_a_519_);
lean_dec(v_c_517_);
lean_dec(v_b_516_);
lean_dec_ref(v_inst_514_);
lean_inc(v_l_515_);
return v_l_515_;
}
else
{
lean_object* v_head_520_; lean_object* v_tail_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_540_; 
v_head_520_ = lean_ctor_get(v_a_518_, 0);
v_tail_521_ = lean_ctor_get(v_a_518_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_540_ == 0)
{
v___x_523_ = v_a_518_;
v_isShared_524_ = v_isSharedCheck_540_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_tail_521_);
lean_inc(v_head_520_);
lean_dec(v_a_518_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_540_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
lean_inc_ref(v_inst_514_);
lean_inc(v_head_520_);
lean_inc(v_b_516_);
v___x_525_ = lean_apply_2(v_inst_514_, v_b_516_, v_head_520_);
v___x_526_ = lean_unbox(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_del_object(v___x_523_);
v___x_527_ = lean_array_push(v_a_519_, v_head_520_);
v_a_518_ = v_tail_521_;
v_a_519_ = v___x_527_;
goto _start;
}
else
{
lean_object* v___x_530_; 
lean_dec(v_head_520_);
lean_dec(v_b_516_);
lean_dec_ref(v_inst_514_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v_c_517_);
v___x_530_ = v___x_523_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_c_517_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_tail_521_);
v___x_530_ = v_reuseFailAlloc_539_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_531_ = lean_array_get_size(v_a_519_);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_534_ = lean_nat_dec_lt(v___x_532_, v___x_531_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_a_519_);
return v___x_530_;
}
else
{
lean_object* v___f_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
v___f_535_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_536_ = lean_usize_of_nat(v___x_531_);
v___x_537_ = ((size_t)0ULL);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_533_, v___f_535_, v_a_519_, v___x_536_, v___x_537_, v___x_530_);
return v___x_538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object* v_inst_541_, lean_object* v_l_542_, lean_object* v_b_543_, lean_object* v_c_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_541_, v_l_542_, v_b_543_, v_c_544_, v_a_545_, v_a_546_);
lean_dec(v_l_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object* v_00_u03b1_548_, lean_object* v_inst_549_, lean_object* v_l_550_, lean_object* v_b_551_, lean_object* v_c_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_549_, v_l_550_, v_b_551_, v_c_552_, v_a_553_, v_a_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_l_558_, lean_object* v_b_559_, lean_object* v_c_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(v_00_u03b1_556_, v_inst_557_, v_l_558_, v_b_559_, v_c_560_, v_a_561_, v_a_562_);
lean_dec(v_l_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object* v_inst_564_, lean_object* v_l_565_, lean_object* v_b_566_, lean_object* v_c_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_565_);
v___x_569_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_564_, v_l_565_, v_b_566_, v_c_567_, v_l_565_, v___x_568_);
lean_dec(v_l_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object* v_00_u03b1_570_, lean_object* v_inst_571_, lean_object* v_l_572_, lean_object* v_b_573_, lean_object* v_c_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_572_);
v___x_576_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_571_, v_l_572_, v_b_573_, v_c_574_, v_l_572_, v___x_575_);
lean_dec(v_l_572_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_h__1_580_, lean_object* v_h__2_581_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_582_; 
lean_dec(v_h__2_581_);
v___x_582_ = lean_apply_2(v_h__1_580_, v_x_578_, v_x_579_);
return v___x_582_;
}
else
{
lean_object* v_head_583_; lean_object* v_tail_584_; lean_object* v___x_585_; 
lean_dec(v_h__1_580_);
v_head_583_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_583_);
v_tail_584_ = lean_ctor_get(v_x_577_, 1);
lean_inc(v_tail_584_);
lean_dec_ref(v_x_577_);
v___x_585_ = lean_apply_4(v_h__2_581_, v_head_583_, v_tail_584_, v_x_578_, v_x_579_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter(lean_object* v_00_u03b1_586_, lean_object* v_motive_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_h__1_591_, lean_object* v_h__2_592_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v___x_593_; 
lean_dec(v_h__2_592_);
v___x_593_ = lean_apply_2(v_h__1_591_, v_x_589_, v_x_590_);
return v___x_593_;
}
else
{
lean_object* v_head_594_; lean_object* v_tail_595_; lean_object* v___x_596_; 
lean_dec(v_h__1_591_);
v_head_594_ = lean_ctor_get(v_x_588_, 0);
lean_inc(v_head_594_);
v_tail_595_ = lean_ctor_get(v_x_588_, 1);
lean_inc(v_tail_595_);
lean_dec_ref(v_x_588_);
v___x_596_ = lean_apply_4(v_h__2_592_, v_head_594_, v_tail_595_, v_x_589_, v_x_590_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object* v_f_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
if (lean_obj_tag(v_a_598_) == 0)
{
lean_object* v___x_601_; 
lean_dec(v_a_599_);
lean_dec(v_f_597_);
v___x_601_ = lean_array_to_list(v_a_600_);
return v___x_601_;
}
else
{
lean_object* v_head_602_; lean_object* v_tail_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_622_; 
v_head_602_ = lean_ctor_get(v_a_598_, 0);
v_tail_603_ = lean_ctor_get(v_a_598_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_a_598_);
if (v_isSharedCheck_622_ == 0)
{
v___x_605_ = v_a_598_;
v_isShared_606_ = v_isSharedCheck_622_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_tail_603_);
lean_inc(v_head_602_);
lean_dec(v_a_598_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_622_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_zero_607_; uint8_t v_isZero_608_; 
v_zero_607_ = lean_unsigned_to_nat(0u);
v_isZero_608_ = lean_nat_dec_eq(v_a_599_, v_zero_607_);
if (v_isZero_608_ == 1)
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_a_599_);
v___x_609_ = lean_apply_1(v_f_597_, v_head_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_609_);
v___x_611_ = v___x_605_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_tail_603_);
v___x_611_ = v_reuseFailAlloc_617_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_get_size(v_a_600_);
v___x_613_ = lean_nat_dec_lt(v_zero_607_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_a_600_);
return v___x_611_;
}
else
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_usize_of_nat(v___x_612_);
v___x_615_ = ((size_t)0ULL);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_600_, v___x_614_, v___x_615_, v___x_611_);
lean_dec_ref(v_a_600_);
return v___x_616_;
}
}
}
else
{
lean_object* v_one_618_; lean_object* v_n_619_; lean_object* v___x_620_; 
lean_del_object(v___x_605_);
v_one_618_ = lean_unsigned_to_nat(1u);
v_n_619_ = lean_nat_sub(v_a_599_, v_one_618_);
lean_dec(v_a_599_);
v___x_620_ = lean_array_push(v_a_600_, v_head_602_);
v_a_598_ = v_tail_603_;
v_a_599_ = v_n_619_;
v_a_600_ = v___x_620_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object* v_00_u03b1_623_, lean_object* v_f_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_624_, v_a_625_, v_a_626_, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object* v_l_629_, lean_object* v_i_630_, lean_object* v_f_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_633_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_631_, v_l_629_, v_i_630_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object* v_00_u03b1_634_, lean_object* v_l_635_, lean_object* v_i_636_, lean_object* v_f_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_List_modifyTR___redArg(v_l_635_, v_i_636_, v_f_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_zero_643_; uint8_t v_isZero_644_; 
v_zero_643_ = lean_unsigned_to_nat(0u);
v_isZero_644_ = lean_nat_dec_eq(v_a_640_, v_zero_643_);
if (v_isZero_644_ == 1)
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
lean_dec(v_a_640_);
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v_a_639_);
lean_ctor_set(v___x_645_, 1, v_a_641_);
v___x_646_ = lean_array_get_size(v_a_642_);
v___x_647_ = lean_nat_dec_lt(v_zero_643_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec_ref(v_a_642_);
return v___x_645_;
}
else
{
size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_usize_of_nat(v___x_646_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_642_, v___x_648_, v___x_649_, v___x_645_);
lean_dec_ref(v_a_642_);
return v___x_650_;
}
}
else
{
if (lean_obj_tag(v_a_641_) == 0)
{
lean_object* v___x_651_; 
lean_dec(v_a_640_);
lean_dec(v_a_639_);
v___x_651_ = lean_array_to_list(v_a_642_);
return v___x_651_;
}
else
{
lean_object* v_head_652_; lean_object* v_tail_653_; lean_object* v_one_654_; lean_object* v_n_655_; lean_object* v___x_656_; 
v_head_652_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_head_652_);
v_tail_653_ = lean_ctor_get(v_a_641_, 1);
lean_inc(v_tail_653_);
lean_dec_ref(v_a_641_);
v_one_654_ = lean_unsigned_to_nat(1u);
v_n_655_ = lean_nat_sub(v_a_640_, v_one_654_);
lean_dec(v_a_640_);
v___x_656_ = lean_array_push(v_a_642_, v_head_652_);
v_a_640_ = v_n_655_;
v_a_641_ = v_tail_653_;
v_a_642_ = v___x_656_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object* v_00_u03b1_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_659_, v_a_660_, v_a_661_, v_a_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object* v_l_664_, lean_object* v_n_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_668_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_666_, v_n_665_, v_l_664_, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object* v_00_u03b1_669_, lean_object* v_l_670_, lean_object* v_n_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_674_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_672_, v_n_671_, v_l_670_, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_h__1_678_, lean_object* v_h__2_679_, lean_object* v_h__3_680_){
_start:
{
lean_object* v_zero_681_; uint8_t v_isZero_682_; 
v_zero_681_ = lean_unsigned_to_nat(0u);
v_isZero_682_ = lean_nat_dec_eq(v_x_675_, v_zero_681_);
if (v_isZero_682_ == 1)
{
lean_object* v___x_683_; 
lean_dec(v_h__3_680_);
lean_dec(v_h__2_679_);
lean_dec(v_x_675_);
v___x_683_ = lean_apply_2(v_h__1_678_, v_x_676_, v_x_677_);
return v___x_683_;
}
else
{
lean_dec(v_h__1_678_);
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v___x_684_; 
lean_dec(v_h__3_680_);
v___x_684_ = lean_apply_3(v_h__2_679_, v_x_675_, v_x_677_, lean_box(0));
return v___x_684_;
}
else
{
lean_object* v_head_685_; lean_object* v_tail_686_; lean_object* v_one_687_; lean_object* v_n_688_; lean_object* v___x_689_; 
lean_dec(v_h__2_679_);
v_head_685_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_head_685_);
v_tail_686_ = lean_ctor_get(v_x_676_, 1);
lean_inc(v_tail_686_);
lean_dec_ref(v_x_676_);
v_one_687_ = lean_unsigned_to_nat(1u);
v_n_688_ = lean_nat_sub(v_x_675_, v_one_687_);
lean_dec(v_x_675_);
v___x_689_ = lean_apply_4(v_h__3_680_, v_n_688_, v_head_685_, v_tail_686_, v_x_677_);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object* v_00_u03b1_690_, lean_object* v_motive_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_h__1_695_, lean_object* v_h__2_696_, lean_object* v_h__3_697_){
_start:
{
lean_object* v_zero_698_; uint8_t v_isZero_699_; 
v_zero_698_ = lean_unsigned_to_nat(0u);
v_isZero_699_ = lean_nat_dec_eq(v_x_692_, v_zero_698_);
if (v_isZero_699_ == 1)
{
lean_object* v___x_700_; 
lean_dec(v_h__3_697_);
lean_dec(v_h__2_696_);
lean_dec(v_x_692_);
v___x_700_ = lean_apply_2(v_h__1_695_, v_x_693_, v_x_694_);
return v___x_700_;
}
else
{
lean_dec(v_h__1_695_);
if (lean_obj_tag(v_x_693_) == 0)
{
lean_object* v___x_701_; 
lean_dec(v_h__3_697_);
v___x_701_ = lean_apply_3(v_h__2_696_, v_x_692_, v_x_694_, lean_box(0));
return v___x_701_;
}
else
{
lean_object* v_head_702_; lean_object* v_tail_703_; lean_object* v_one_704_; lean_object* v_n_705_; lean_object* v___x_706_; 
lean_dec(v_h__2_696_);
v_head_702_ = lean_ctor_get(v_x_693_, 0);
lean_inc(v_head_702_);
v_tail_703_ = lean_ctor_get(v_x_693_, 1);
lean_inc(v_tail_703_);
lean_dec_ref(v_x_693_);
v_one_704_ = lean_unsigned_to_nat(1u);
v_n_705_ = lean_nat_sub(v_x_692_, v_one_704_);
lean_dec(v_x_692_);
v___x_706_ = lean_apply_4(v_h__3_697_, v_n_705_, v_head_702_, v_tail_703_, v_x_694_);
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object* v_inst_707_, lean_object* v_l_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
if (lean_obj_tag(v_a_710_) == 0)
{
lean_dec_ref(v_a_711_);
lean_dec(v_a_709_);
lean_dec_ref(v_inst_707_);
lean_inc(v_l_708_);
return v_l_708_;
}
else
{
lean_object* v_head_712_; lean_object* v_tail_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_head_712_ = lean_ctor_get(v_a_710_, 0);
lean_inc_n(v_head_712_, 2);
v_tail_713_ = lean_ctor_get(v_a_710_, 1);
lean_inc(v_tail_713_);
lean_dec_ref(v_a_710_);
lean_inc_ref(v_inst_707_);
lean_inc(v_a_709_);
v___x_714_ = lean_apply_2(v_inst_707_, v_head_712_, v_a_709_);
v___x_715_ = lean_unbox(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_array_push(v_a_711_, v_head_712_);
v_a_710_ = v_tail_713_;
v_a_711_ = v___x_716_;
goto _start;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
lean_dec(v_head_712_);
lean_dec(v_a_709_);
lean_dec_ref(v_inst_707_);
v___x_718_ = lean_array_get_size(v_a_711_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_718_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_a_711_);
return v_tail_713_;
}
else
{
lean_object* v___f_722_; size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v___f_722_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_723_ = lean_usize_of_nat(v___x_718_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_720_, v___f_722_, v_a_711_, v___x_723_, v___x_724_, v_tail_713_);
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object* v_inst_726_, lean_object* v_l_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_726_, v_l_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_l_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object* v_00_u03b1_732_, lean_object* v_inst_733_, lean_object* v_l_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_733_, v_l_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object* v_00_u03b1_739_, lean_object* v_inst_740_, lean_object* v_l_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(v_00_u03b1_739_, v_inst_740_, v_l_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_l_741_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object* v_inst_746_, lean_object* v_l_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_747_);
v___x_750_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_746_, v_l_747_, v_a_748_, v_l_747_, v___x_749_);
lean_dec(v_l_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object* v_00_u03b1_751_, lean_object* v_inst_752_, lean_object* v_l_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_753_);
v___x_756_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_752_, v_l_753_, v_a_754_, v_l_753_, v___x_755_);
lean_dec(v_l_753_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object* v_p_757_, lean_object* v_l_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
if (lean_obj_tag(v_a_759_) == 0)
{
lean_dec_ref(v_a_760_);
lean_dec_ref(v_p_757_);
lean_inc(v_l_758_);
return v_l_758_;
}
else
{
lean_object* v_head_761_; lean_object* v_tail_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_head_761_ = lean_ctor_get(v_a_759_, 0);
lean_inc_n(v_head_761_, 2);
v_tail_762_ = lean_ctor_get(v_a_759_, 1);
lean_inc(v_tail_762_);
lean_dec_ref(v_a_759_);
lean_inc_ref(v_p_757_);
v___x_763_ = lean_apply_1(v_p_757_, v_head_761_);
v___x_764_ = lean_unbox(v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_array_push(v_a_760_, v_head_761_);
v_a_759_ = v_tail_762_;
v_a_760_ = v___x_765_;
goto _start;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
lean_dec(v_head_761_);
lean_dec_ref(v_p_757_);
v___x_767_ = lean_array_get_size(v_a_760_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_770_ = lean_nat_dec_lt(v___x_768_, v___x_767_);
if (v___x_770_ == 0)
{
lean_dec_ref(v_a_760_);
return v_tail_762_;
}
else
{
lean_object* v___f_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___f_771_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_772_ = lean_usize_of_nat(v___x_767_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_769_, v___f_771_, v_a_760_, v___x_772_, v___x_773_, v_tail_762_);
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object* v_p_775_, lean_object* v_l_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_775_, v_l_776_, v_a_777_, v_a_778_);
lean_dec(v_l_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object* v_00_u03b1_780_, lean_object* v_p_781_, lean_object* v_l_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_781_, v_l_782_, v_a_783_, v_a_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object* v_00_u03b1_786_, lean_object* v_p_787_, lean_object* v_l_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(v_00_u03b1_786_, v_p_787_, v_l_788_, v_a_789_, v_a_790_);
lean_dec(v_l_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object* v_p_792_, lean_object* v_l_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_793_);
v___x_795_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_792_, v_l_793_, v_l_793_, v___x_794_);
lean_dec(v_l_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object* v_00_u03b1_796_, lean_object* v_p_797_, lean_object* v_l_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_798_);
v___x_800_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_797_, v_l_798_, v_l_798_, v___x_799_);
lean_dec(v_l_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object* v_l_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
if (lean_obj_tag(v_a_802_) == 0)
{
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_inc(v_l_801_);
return v_l_801_;
}
else
{
lean_object* v_head_805_; lean_object* v_tail_806_; lean_object* v_zero_807_; uint8_t v_isZero_808_; 
v_head_805_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_head_805_);
v_tail_806_ = lean_ctor_get(v_a_802_, 1);
lean_inc(v_tail_806_);
lean_dec_ref(v_a_802_);
v_zero_807_ = lean_unsigned_to_nat(0u);
v_isZero_808_ = lean_nat_dec_eq(v_a_803_, v_zero_807_);
if (v_isZero_808_ == 1)
{
lean_object* v___x_809_; uint8_t v___x_810_; 
lean_dec(v_head_805_);
lean_dec(v_a_803_);
v___x_809_ = lean_array_get_size(v_a_804_);
v___x_810_ = lean_nat_dec_lt(v_zero_807_, v___x_809_);
if (v___x_810_ == 0)
{
lean_dec_ref(v_a_804_);
return v_tail_806_;
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_usize_of_nat(v___x_809_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_804_, v___x_811_, v___x_812_, v_tail_806_);
lean_dec_ref(v_a_804_);
return v___x_813_;
}
}
else
{
lean_object* v_one_814_; lean_object* v_n_815_; lean_object* v___x_816_; 
v_one_814_ = lean_unsigned_to_nat(1u);
v_n_815_ = lean_nat_sub(v_a_803_, v_one_814_);
lean_dec(v_a_803_);
v___x_816_ = lean_array_push(v_a_804_, v_head_805_);
v_a_802_ = v_tail_806_;
v_a_803_ = v_n_815_;
v_a_804_ = v___x_816_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object* v_l_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_l_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object* v_00_u03b1_823_, lean_object* v_l_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_824_, v_a_825_, v_a_826_, v_a_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object* v_00_u03b1_829_, lean_object* v_l_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(v_00_u03b1_829_, v_l_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_l_830_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object* v_l_835_, lean_object* v_n_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_835_);
v___x_838_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_835_, v_l_835_, v_n_836_, v___x_837_);
lean_dec(v_l_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object* v_00_u03b1_839_, lean_object* v_l_840_, lean_object* v_n_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_840_);
v___x_843_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_840_, v_l_840_, v_n_841_, v___x_842_);
lean_dec(v_l_840_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_h__1_846_, lean_object* v_h__2_847_, lean_object* v_h__3_848_){
_start:
{
if (lean_obj_tag(v_x_844_) == 0)
{
lean_object* v___x_849_; 
lean_dec(v_h__3_848_);
lean_dec(v_h__2_847_);
v___x_849_ = lean_apply_1(v_h__1_846_, v_x_845_);
return v___x_849_;
}
else
{
lean_object* v_head_850_; lean_object* v_tail_851_; lean_object* v_zero_852_; uint8_t v_isZero_853_; 
lean_dec(v_h__1_846_);
v_head_850_ = lean_ctor_get(v_x_844_, 0);
lean_inc(v_head_850_);
v_tail_851_ = lean_ctor_get(v_x_844_, 1);
lean_inc(v_tail_851_);
lean_dec_ref(v_x_844_);
v_zero_852_ = lean_unsigned_to_nat(0u);
v_isZero_853_ = lean_nat_dec_eq(v_x_845_, v_zero_852_);
if (v_isZero_853_ == 1)
{
lean_object* v___x_854_; 
lean_dec(v_h__3_848_);
lean_dec(v_x_845_);
v___x_854_ = lean_apply_2(v_h__2_847_, v_head_850_, v_tail_851_);
return v___x_854_;
}
else
{
lean_object* v_one_855_; lean_object* v_n_856_; lean_object* v___x_857_; 
lean_dec(v_h__2_847_);
v_one_855_ = lean_unsigned_to_nat(1u);
v_n_856_ = lean_nat_sub(v_x_845_, v_one_855_);
lean_dec(v_x_845_);
v___x_857_ = lean_apply_3(v_h__3_848_, v_head_850_, v_tail_851_, v_n_856_);
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_858_, lean_object* v_motive_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_, lean_object* v_h__3_864_){
_start:
{
if (lean_obj_tag(v_x_860_) == 0)
{
lean_object* v___x_865_; 
lean_dec(v_h__3_864_);
lean_dec(v_h__2_863_);
v___x_865_ = lean_apply_1(v_h__1_862_, v_x_861_);
return v___x_865_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v_zero_868_; uint8_t v_isZero_869_; 
lean_dec(v_h__1_862_);
v_head_866_ = lean_ctor_get(v_x_860_, 0);
lean_inc(v_head_866_);
v_tail_867_ = lean_ctor_get(v_x_860_, 1);
lean_inc(v_tail_867_);
lean_dec_ref(v_x_860_);
v_zero_868_ = lean_unsigned_to_nat(0u);
v_isZero_869_ = lean_nat_dec_eq(v_x_861_, v_zero_868_);
if (v_isZero_869_ == 1)
{
lean_object* v___x_870_; 
lean_dec(v_h__3_864_);
lean_dec(v_x_861_);
v___x_870_ = lean_apply_2(v_h__2_863_, v_head_866_, v_tail_867_);
return v___x_870_;
}
else
{
lean_object* v_one_871_; lean_object* v_n_872_; lean_object* v___x_873_; 
lean_dec(v_h__2_863_);
v_one_871_ = lean_unsigned_to_nat(1u);
v_n_872_ = lean_nat_sub(v_x_861_, v_one_871_);
lean_dec(v_x_861_);
v___x_873_ = lean_apply_3(v_h__3_864_, v_head_866_, v_tail_867_, v_n_872_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object* v_f_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
if (lean_obj_tag(v_a_875_) == 1)
{
if (lean_obj_tag(v_a_876_) == 1)
{
lean_object* v_head_878_; lean_object* v_tail_879_; lean_object* v_head_880_; lean_object* v_tail_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_head_878_ = lean_ctor_get(v_a_875_, 0);
lean_inc(v_head_878_);
v_tail_879_ = lean_ctor_get(v_a_875_, 1);
lean_inc(v_tail_879_);
lean_dec_ref(v_a_875_);
v_head_880_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_head_880_);
v_tail_881_ = lean_ctor_get(v_a_876_, 1);
lean_inc(v_tail_881_);
lean_dec_ref(v_a_876_);
lean_inc(v_f_874_);
v___x_882_ = lean_apply_2(v_f_874_, v_head_878_, v_head_880_);
v___x_883_ = lean_array_push(v_a_877_, v___x_882_);
v_a_875_ = v_tail_879_;
v_a_876_ = v_tail_881_;
v_a_877_ = v___x_883_;
goto _start;
}
else
{
lean_object* v___x_885_; 
lean_dec_ref(v_a_875_);
lean_dec(v_a_876_);
lean_dec(v_f_874_);
v___x_885_ = lean_array_to_list(v_a_877_);
return v___x_885_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_a_876_);
lean_dec(v_a_875_);
lean_dec(v_f_874_);
v___x_886_ = lean_array_to_list(v_a_877_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_00_u03b3_889_, lean_object* v_f_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_890_, v_a_891_, v_a_892_, v_a_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object* v_f_895_, lean_object* v_as_896_, lean_object* v_bs_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_899_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_895_, v_as_896_, v_bs_897_, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_00_u03b3_902_, lean_object* v_f_903_, lean_object* v_as_904_, lean_object* v_bs_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_907_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_903_, v_as_904_, v_bs_905_, v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_h__1_911_, lean_object* v_h__2_912_){
_start:
{
if (lean_obj_tag(v_x_908_) == 1)
{
if (lean_obj_tag(v_x_909_) == 1)
{
lean_object* v_head_913_; lean_object* v_tail_914_; lean_object* v_head_915_; lean_object* v_tail_916_; lean_object* v___x_917_; 
lean_dec(v_h__2_912_);
v_head_913_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_head_913_);
v_tail_914_ = lean_ctor_get(v_x_908_, 1);
lean_inc(v_tail_914_);
lean_dec_ref(v_x_908_);
v_head_915_ = lean_ctor_get(v_x_909_, 0);
lean_inc(v_head_915_);
v_tail_916_ = lean_ctor_get(v_x_909_, 1);
lean_inc(v_tail_916_);
lean_dec_ref(v_x_909_);
v___x_917_ = lean_apply_5(v_h__1_911_, v_head_913_, v_tail_914_, v_head_915_, v_tail_916_, v_x_910_);
return v___x_917_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_h__1_911_);
v___x_918_ = lean_apply_4(v_h__2_912_, v_x_908_, v_x_909_, v_x_910_, lean_box(0));
return v___x_918_;
}
}
else
{
lean_object* v___x_919_; 
lean_dec(v_h__1_911_);
v___x_919_ = lean_apply_4(v_h__2_912_, v_x_908_, v_x_909_, v_x_910_, lean_box(0));
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object* v_00_u03b1_920_, lean_object* v_00_u03b2_921_, lean_object* v_00_u03b3_922_, lean_object* v_motive_923_, lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_h__1_927_, lean_object* v_h__2_928_){
_start:
{
if (lean_obj_tag(v_x_924_) == 1)
{
if (lean_obj_tag(v_x_925_) == 1)
{
lean_object* v_head_929_; lean_object* v_tail_930_; lean_object* v_head_931_; lean_object* v_tail_932_; lean_object* v___x_933_; 
lean_dec(v_h__2_928_);
v_head_929_ = lean_ctor_get(v_x_924_, 0);
lean_inc(v_head_929_);
v_tail_930_ = lean_ctor_get(v_x_924_, 1);
lean_inc(v_tail_930_);
lean_dec_ref(v_x_924_);
v_head_931_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_head_931_);
v_tail_932_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_tail_932_);
lean_dec_ref(v_x_925_);
v___x_933_ = lean_apply_5(v_h__1_927_, v_head_929_, v_tail_930_, v_head_931_, v_tail_932_, v_x_926_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; 
lean_dec(v_h__1_927_);
v___x_934_ = lean_apply_4(v_h__2_928_, v_x_924_, v_x_925_, v_x_926_, lean_box(0));
return v___x_934_;
}
}
else
{
lean_object* v___x_935_; 
lean_dec(v_h__1_927_);
v___x_935_ = lean_apply_4(v_h__2_928_, v_x_924_, v_x_925_, v_x_926_, lean_box(0));
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object* v_as_936_, size_t v_i_937_, size_t v_stop_938_, lean_object* v_b_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = lean_usize_dec_eq(v_i_937_, v_stop_938_);
if (v___x_940_ == 0)
{
lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_957_; 
v_fst_941_ = lean_ctor_get(v_b_939_, 0);
v_snd_942_ = lean_ctor_get(v_b_939_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v_b_939_);
if (v_isSharedCheck_957_ == 0)
{
v___x_944_ = v_b_939_;
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_inc(v_fst_941_);
lean_dec(v_b_939_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_957_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
size_t v___x_946_; size_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_sub(v_i_937_, v___x_946_);
v___x_948_ = lean_array_uget_borrowed(v_as_936_, v___x_947_);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_sub(v_fst_941_, v___x_949_);
lean_dec(v_fst_941_);
lean_inc(v___x_950_);
lean_inc(v___x_948_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_950_);
lean_ctor_set(v___x_944_, 0, v___x_948_);
v___x_952_ = v___x_944_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v_snd_942_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_950_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v_i_937_ = v___x_947_;
v_b_939_ = v___x_954_;
goto _start;
}
}
}
else
{
return v_b_939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object* v_as_958_, lean_object* v_i_959_, lean_object* v_stop_960_, lean_object* v_b_961_){
_start:
{
size_t v_i_boxed_962_; size_t v_stop_boxed_963_; lean_object* v_res_964_; 
v_i_boxed_962_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_stop_boxed_963_ = lean_unbox_usize(v_stop_960_);
lean_dec(v_stop_960_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_958_, v_i_boxed_962_, v_stop_boxed_963_, v_b_961_);
lean_dec_ref(v_as_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object* v_l_965_, lean_object* v_n_966_){
_start:
{
lean_object* v_as_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_as_967_ = lean_array_mk(v_l_965_);
v___x_968_ = lean_array_get_size(v_as_967_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = lean_nat_dec_lt(v___x_970_, v___x_968_);
if (v___x_971_ == 0)
{
lean_dec_ref(v_as_967_);
return v___x_969_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; lean_object* v_snd_977_; 
v___x_972_ = lean_nat_add(v_n_966_, v___x_968_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_969_);
v___x_974_ = lean_usize_of_nat(v___x_968_);
v___x_975_ = ((size_t)0ULL);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_967_, v___x_974_, v___x_975_, v___x_973_);
lean_dec_ref(v_as_967_);
v_snd_977_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_snd_977_);
lean_dec_ref(v___x_976_);
return v_snd_977_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object* v_l_978_, lean_object* v_n_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_List_zipIdxTR___redArg(v_l_978_, v_n_979_);
lean_dec(v_n_979_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object* v_00_u03b1_981_, lean_object* v_l_982_, lean_object* v_n_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_List_zipIdxTR___redArg(v_l_982_, v_n_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object* v_00_u03b1_985_, lean_object* v_l_986_, lean_object* v_n_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_List_zipIdxTR(v_00_u03b1_985_, v_l_986_, v_n_987_);
lean_dec(v_n_987_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object* v_00_u03b1_989_, lean_object* v_as_990_, size_t v_i_991_, size_t v_stop_992_, lean_object* v_b_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_990_, v_i_991_, v_stop_992_, v_b_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object* v_00_u03b1_995_, lean_object* v_as_996_, lean_object* v_i_997_, lean_object* v_stop_998_, lean_object* v_b_999_){
_start:
{
size_t v_i_boxed_1000_; size_t v_stop_boxed_1001_; lean_object* v_res_1002_; 
v_i_boxed_1000_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_stop_boxed_1001_ = lean_unbox_usize(v_stop_998_);
lean_dec(v_stop_998_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(v_00_u03b1_995_, v_as_996_, v_i_boxed_1000_, v_stop_boxed_1001_, v_b_999_);
lean_dec_ref(v_as_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_h__1_1005_, lean_object* v_h__2_1006_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_object* v___x_1007_; 
lean_dec(v_h__2_1006_);
v___x_1007_ = lean_apply_1(v_h__1_1005_, v_x_1004_);
return v___x_1007_;
}
else
{
lean_object* v_head_1008_; lean_object* v_tail_1009_; lean_object* v___x_1010_; 
lean_dec(v_h__1_1005_);
v_head_1008_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_head_1008_);
v_tail_1009_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_tail_1009_);
lean_dec_ref(v_x_1003_);
v___x_1010_ = lean_apply_3(v_h__2_1006_, v_head_1008_, v_tail_1009_, v_x_1004_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_1011_, lean_object* v_motive_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_, lean_object* v_h__1_1015_, lean_object* v_h__2_1016_){
_start:
{
if (lean_obj_tag(v_x_1013_) == 0)
{
lean_object* v___x_1017_; 
lean_dec(v_h__2_1016_);
v___x_1017_ = lean_apply_1(v_h__1_1015_, v_x_1014_);
return v___x_1017_;
}
else
{
lean_object* v_head_1018_; lean_object* v_tail_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__1_1015_);
v_head_1018_ = lean_ctor_get(v_x_1013_, 0);
lean_inc(v_head_1018_);
v_tail_1019_ = lean_ctor_get(v_x_1013_, 1);
lean_inc(v_tail_1019_);
lean_dec_ref(v_x_1013_);
v___x_1020_ = lean_apply_3(v_h__2_1016_, v_head_1018_, v_tail_1019_, v_x_1014_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object* v_sep_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
if (lean_obj_tag(v_a_1023_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = lean_array_get_size(v_a_1024_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_nat_dec_lt(v___x_1026_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_dec_ref(v_a_1024_);
return v_a_1022_;
}
else
{
size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_usize_of_nat(v___x_1025_);
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1024_, v___x_1028_, v___x_1029_, v_a_1022_);
lean_dec_ref(v_a_1024_);
return v___x_1030_;
}
}
else
{
lean_object* v_head_1031_; lean_object* v_tail_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_head_1031_ = lean_ctor_get(v_a_1023_, 0);
lean_inc(v_head_1031_);
v_tail_1032_ = lean_ctor_get(v_a_1023_, 1);
lean_inc(v_tail_1032_);
lean_dec_ref(v_a_1023_);
v___x_1033_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1024_, v_a_1022_);
v___x_1034_ = l_Array_append___redArg(v___x_1033_, v_sep_1021_);
v_a_1022_ = v_head_1031_;
v_a_1023_ = v_tail_1032_;
v_a_1024_ = v___x_1034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object* v_sep_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
lean_dec_ref(v_sep_1036_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object* v_00_u03b1_1041_, lean_object* v_sep_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_sep_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(v_00_u03b1_1047_, v_sep_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec_ref(v_sep_1048_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object* v_sep_1053_, lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v___x_1055_; 
lean_dec(v_sep_1053_);
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
else
{
lean_object* v_tail_1056_; 
v_tail_1056_ = lean_ctor_get(v_x_1054_, 1);
if (lean_obj_tag(v_tail_1056_) == 0)
{
lean_object* v_head_1057_; 
lean_dec(v_sep_1053_);
v_head_1057_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_head_1057_);
lean_dec_ref(v_x_1054_);
return v_head_1057_;
}
else
{
lean_object* v_head_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_inc(v_tail_1056_);
v_head_1058_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_head_1058_);
lean_dec_ref(v_x_1054_);
v___x_1059_ = lean_array_mk(v_sep_1053_);
v___x_1060_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_1061_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v___x_1059_, v_head_1058_, v_tail_1056_, v___x_1060_);
lean_dec_ref(v___x_1059_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object* v_00_u03b1_1062_, lean_object* v_sep_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_List_intercalateTR___redArg(v_sep_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object* v_x_1066_, lean_object* v_h__1_1067_, lean_object* v_h__2_1068_, lean_object* v_h__3_1069_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v_h__3_1069_);
lean_dec(v_h__2_1068_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_apply_1(v_h__1_1067_, v___x_1070_);
return v___x_1071_;
}
else
{
lean_object* v_tail_1072_; 
lean_dec(v_h__1_1067_);
v_tail_1072_ = lean_ctor_get(v_x_1066_, 1);
if (lean_obj_tag(v_tail_1072_) == 0)
{
lean_object* v_head_1073_; lean_object* v___x_1074_; 
lean_dec(v_h__3_1069_);
v_head_1073_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_head_1073_);
lean_dec_ref(v_x_1066_);
v___x_1074_ = lean_apply_1(v_h__2_1068_, v_head_1073_);
return v___x_1074_;
}
else
{
lean_object* v_head_1075_; lean_object* v___x_1076_; 
lean_inc(v_tail_1072_);
lean_dec(v_h__2_1068_);
v_head_1075_ = lean_ctor_get(v_x_1066_, 0);
lean_inc(v_head_1075_);
lean_dec_ref(v_x_1066_);
v___x_1076_ = lean_apply_3(v_h__3_1069_, v_head_1075_, v_tail_1072_, lean_box(0));
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object* v_00_u03b1_1077_, lean_object* v_motive_1078_, lean_object* v_x_1079_, lean_object* v_h__1_1080_, lean_object* v_h__2_1081_, lean_object* v_h__3_1082_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_h__3_1082_);
lean_dec(v_h__2_1081_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_apply_1(v_h__1_1080_, v___x_1083_);
return v___x_1084_;
}
else
{
lean_object* v_tail_1085_; 
lean_dec(v_h__1_1080_);
v_tail_1085_ = lean_ctor_get(v_x_1079_, 1);
if (lean_obj_tag(v_tail_1085_) == 0)
{
lean_object* v_head_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__3_1082_);
v_head_1086_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_head_1086_);
lean_dec_ref(v_x_1079_);
v___x_1087_ = lean_apply_1(v_h__2_1081_, v_head_1086_);
return v___x_1087_;
}
else
{
lean_object* v_head_1088_; lean_object* v___x_1089_; 
lean_inc(v_tail_1085_);
lean_dec(v_h__2_1081_);
v_head_1088_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_head_1088_);
lean_dec_ref(v_x_1079_);
v___x_1089_ = lean_apply_3(v_h__3_1082_, v_head_1088_, v_tail_1085_, lean_box(0));
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_h__1_1093_, lean_object* v_h__2_1094_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_h__2_1094_);
v___x_1095_ = lean_apply_2(v_h__1_1093_, v_x_1090_, v_x_1092_);
return v___x_1095_;
}
else
{
lean_object* v_head_1096_; lean_object* v_tail_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__1_1093_);
v_head_1096_ = lean_ctor_get(v_x_1091_, 0);
lean_inc(v_head_1096_);
v_tail_1097_ = lean_ctor_get(v_x_1091_, 1);
lean_inc(v_tail_1097_);
lean_dec_ref(v_x_1091_);
v___x_1098_ = lean_apply_4(v_h__2_1094_, v_x_1090_, v_head_1096_, v_tail_1097_, v_x_1092_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter(lean_object* v_00_u03b1_1099_, lean_object* v_motive_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_h__1_1104_, lean_object* v_h__2_1105_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v___x_1106_; 
lean_dec(v_h__2_1105_);
v___x_1106_ = lean_apply_2(v_h__1_1104_, v_x_1101_, v_x_1103_);
return v___x_1106_;
}
else
{
lean_object* v_head_1107_; lean_object* v_tail_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__1_1104_);
v_head_1107_ = lean_ctor_get(v_x_1102_, 0);
lean_inc(v_head_1107_);
v_tail_1108_ = lean_ctor_get(v_x_1102_, 1);
lean_inc(v_tail_1108_);
lean_dec_ref(v_x_1102_);
v___x_1109_ = lean_apply_4(v_h__2_1105_, v_x_1101_, v_head_1107_, v_tail_1108_, v_x_1103_);
return v___x_1109_;
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
