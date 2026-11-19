// Lean compiler output
// Module: Init.Data.List.Impl
// Imports: public import Init.Ext import Init.Data.Array.Bootstrap import Init.Data.Bool public import Init.Data.List.Lemmas import all Init.Data.List.Basic import Init.Data.Option.Lemmas
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_pop(lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_sumTR___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sumTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_sumTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_prodTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_prodTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_foldrRecOnImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_foldrRecOnImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_foldrRecOnImpl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_foldrRecOnImpl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_extractTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extractTR___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extractTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_extractTR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeftTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeftTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeftTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateLeftTR___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRightTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRightTR___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRightTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_rotateRightTR___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_isPermTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPermTR___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isPermTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_isPermTR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_reverseAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_reverseAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_isPermTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_isPermTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipTR___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_List_zipTR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_zipTR___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_zipTR___redArg___closed__0 = (const lean_object*)&l_List_zipTR___redArg___closed__0_value;
static const lean_array_object l_List_zipTR___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_zipTR___redArg___closed__1 = (const lean_object*)&l_List_zipTR___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_zipTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipTR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_unzipTR_spec__0___redArg(lean_object*, lean_object*);
static const lean_ctor_object l_List_unzipTR___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_unzipTR___redArg___closed__0 = (const lean_object*)&l_List_unzipTR___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_unzipTR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_intersperseTR_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_intersperseTR_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intersperseTR_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intersperseTR_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_90_, 2);
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
lean_dec_ref_known(v_x_107_, 2);
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
lean_dec_ref_known(v_a_123_, 2);
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
lean_dec_ref_known(v___x_128_, 1);
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
lean_dec_ref_known(v_x_149_, 2);
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
lean_dec_ref_known(v_x_160_, 2);
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
lean_dec_ref_known(v_x_168_, 1);
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
lean_dec_ref_known(v_x_177_, 1);
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
lean_dec_ref_known(v_x_184_, 1);
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
lean_dec_ref_known(v_x_193_, 1);
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
LEAN_EXPORT lean_object* l_List_sumTR___redArg___lam__0(lean_object* v_inst_251_, lean_object* v_x1_252_, lean_object* v_x2_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_apply_2(v_inst_251_, v_x1_252_, v_x2_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_List_sumTR___redArg(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_l_257_){
_start:
{
lean_object* v___f_258_; lean_object* v___x_259_; 
v___f_258_ = lean_alloc_closure((void*)(l_List_sumTR___redArg___lam__0), 3, 1);
lean_closure_set(v___f_258_, 0, v_inst_255_);
v___x_259_ = l_List_foldrTR___redArg(v___f_258_, v_inst_256_, v_l_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_List_sumTR(lean_object* v_00_u03b1_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_l_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_List_sumTR___redArg(v_inst_261_, v_inst_262_, v_l_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_List_prodTR___redArg(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_l_267_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; 
v___f_268_ = lean_alloc_closure((void*)(l_List_sumTR___redArg___lam__0), 3, 1);
lean_closure_set(v___f_268_, 0, v_inst_265_);
v___x_269_ = l_List_foldrTR___redArg(v___f_268_, v_inst_266_, v_l_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_List_prodTR(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_l_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_List_prodTR___redArg(v_inst_271_, v_inst_272_, v_l_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___redArg___lam__0(lean_object* v_x_275_, lean_object* v_b_276_, lean_object* v_c_277_, lean_object* v_a_278_, lean_object* v_m_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_apply_4(v_x_275_, v_b_276_, v_c_277_, v_a_278_, lean_box(0));
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg(lean_object* v_x_281_, lean_object* v_as_282_, size_t v_i_283_, size_t v_stop_284_, lean_object* v_b_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_eq(v_i_283_, v_stop_284_);
if (v___x_286_ == 0)
{
size_t v___x_287_; size_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_sub(v_i_283_, v___x_287_);
v___x_289_ = lean_array_uget_borrowed(v_as_282_, v___x_288_);
lean_inc(v_x_281_);
lean_inc(v___x_289_);
v___x_290_ = lean_apply_2(v_x_281_, v___x_289_, v_b_285_);
v_i_283_ = v___x_288_;
v_b_285_ = v___x_290_;
goto _start;
}
else
{
lean_dec(v_x_281_);
return v_b_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_292_, lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_stop_295_, lean_object* v_b_296_){
_start:
{
size_t v_i_boxed_297_; size_t v_stop_boxed_298_; lean_object* v_res_299_; 
v_i_boxed_297_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_stop_boxed_298_ = lean_unbox_usize(v_stop_295_);
lean_dec(v_stop_295_);
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg(v_x_292_, v_as_293_, v_i_boxed_297_, v_stop_boxed_298_, v_b_296_);
lean_dec_ref(v_as_293_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_foldrRecOnImpl_spec__0___redArg(lean_object* v_x_300_, lean_object* v_init_301_, lean_object* v_l_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_303_ = lean_array_mk(v_l_302_);
v___x_304_ = lean_array_get_size(v___x_303_);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_nat_dec_lt(v___x_305_, v___x_304_);
if (v___x_306_ == 0)
{
lean_dec_ref(v___x_303_);
lean_dec(v_x_300_);
return v_init_301_;
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_usize_of_nat(v___x_304_);
v___x_308_ = ((size_t)0ULL);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg(v_x_300_, v___x_303_, v___x_307_, v___x_308_, v_init_301_);
lean_dec_ref(v___x_303_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___redArg(lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_310_) == 0)
{
lean_dec(v_x_314_);
lean_dec(v_x_312_);
lean_dec(v_x_311_);
lean_inc(v_x_313_);
return v_x_313_;
}
else
{
lean_object* v_head_315_; lean_object* v_tail_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_head_315_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_head_315_);
v_tail_316_ = lean_ctor_get(v_x_310_, 1);
lean_inc_n(v_tail_316_, 2);
lean_dec_ref_known(v_x_310_, 2);
lean_inc(v_x_314_);
v___f_317_ = lean_alloc_closure((void*)(l_List_foldrRecOnImpl___redArg___lam__0), 5, 1);
lean_closure_set(v___f_317_, 0, v_x_314_);
lean_inc(v_x_312_);
lean_inc(v_x_311_);
v___x_318_ = l_List_foldrTR___at___00List_foldrRecOnImpl_spec__0___redArg(v_x_311_, v_x_312_, v_tail_316_);
v___x_319_ = l_List_foldrRecOnImpl___redArg(v_tail_316_, v_x_311_, v_x_312_, v_x_313_, v___f_317_);
v___x_320_ = lean_apply_4(v_x_314_, v___x_318_, v___x_319_, v_head_315_, lean_box(0));
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___redArg___boxed(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_List_foldrRecOnImpl___redArg(v_x_321_, v_x_322_, v_x_323_, v_x_324_, v_x_325_);
lean_dec(v_x_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl(lean_object* v_00_u03b2_327_, lean_object* v_00_u03b1_328_, lean_object* v_motive_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_List_foldrRecOnImpl___redArg(v_x_330_, v_x_331_, v_x_332_, v_x_333_, v_x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_List_foldrRecOnImpl___boxed(lean_object* v_00_u03b2_336_, lean_object* v_00_u03b1_337_, lean_object* v_motive_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_List_foldrRecOnImpl(v_00_u03b2_336_, v_00_u03b1_337_, v_motive_338_, v_x_339_, v_x_340_, v_x_341_, v_x_342_, v_x_343_);
lean_dec(v_x_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_foldrRecOnImpl_spec__0(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_x_347_, lean_object* v_init_348_, lean_object* v_l_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_List_foldrTR___at___00List_foldrRecOnImpl_spec__0___redArg(v_x_347_, v_init_348_, v_l_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0(lean_object* v_00_u03b1_351_, lean_object* v_00_u03b2_352_, lean_object* v_x_353_, lean_object* v_as_354_, size_t v_i_355_, size_t v_stop_356_, lean_object* v_b_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___redArg(v_x_353_, v_as_354_, v_i_355_, v_stop_356_, v_b_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_359_, lean_object* v_00_u03b2_360_, lean_object* v_x_361_, lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_stop_364_, lean_object* v_b_365_){
_start:
{
size_t v_i_boxed_366_; size_t v_stop_boxed_367_; lean_object* v_res_368_; 
v_i_boxed_366_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_stop_boxed_367_ = lean_unbox_usize(v_stop_364_);
lean_dec(v_stop_364_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_foldrRecOnImpl_spec__0_spec__0(v_00_u03b1_359_, v_00_u03b2_360_, v_x_361_, v_as_362_, v_i_boxed_366_, v_stop_boxed_367_, v_b_365_);
lean_dec_ref(v_as_362_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_foldrRecOnImpl_match__1_splitter___redArg(lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_h__1_374_, lean_object* v_h__2_375_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v___x_376_; 
lean_dec(v_h__2_375_);
v___x_376_ = lean_apply_4(v_h__1_374_, v_x_370_, v_x_371_, v_x_372_, v_x_373_);
return v___x_376_;
}
else
{
lean_object* v_head_377_; lean_object* v_tail_378_; lean_object* v___x_379_; 
lean_dec(v_h__1_374_);
v_head_377_ = lean_ctor_get(v_x_369_, 0);
lean_inc(v_head_377_);
v_tail_378_ = lean_ctor_get(v_x_369_, 1);
lean_inc(v_tail_378_);
lean_dec_ref_known(v_x_369_, 2);
v___x_379_ = lean_apply_6(v_h__2_375_, v_head_377_, v_tail_378_, v_x_370_, v_x_371_, v_x_372_, v_x_373_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_foldrRecOnImpl_match__1_splitter(lean_object* v_00_u03b2_380_, lean_object* v_00_u03b1_381_, lean_object* v_motive_382_, lean_object* v_motive_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_h__1_389_, lean_object* v_h__2_390_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_391_; 
lean_dec(v_h__2_390_);
v___x_391_ = lean_apply_4(v_h__1_389_, v_x_385_, v_x_386_, v_x_387_, v_x_388_);
return v___x_391_;
}
else
{
lean_object* v_head_392_; lean_object* v_tail_393_; lean_object* v___x_394_; 
lean_dec(v_h__1_389_);
v_head_392_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_head_392_);
v_tail_393_ = lean_ctor_get(v_x_384_, 1);
lean_inc(v_tail_393_);
lean_dec_ref_known(v_x_384_, 2);
v___x_394_ = lean_apply_6(v_h__2_390_, v_head_392_, v_tail_393_, v_x_385_, v_x_386_, v_x_387_, v_x_388_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(lean_object* v_f_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
if (lean_obj_tag(v_a_396_) == 0)
{
lean_object* v___x_398_; 
lean_dec_ref(v_f_395_);
v___x_398_ = lean_array_to_list(v_a_397_);
return v___x_398_;
}
else
{
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_head_399_ = lean_ctor_get(v_a_396_, 0);
lean_inc(v_head_399_);
v_tail_400_ = lean_ctor_get(v_a_396_, 1);
lean_inc(v_tail_400_);
lean_dec_ref_known(v_a_396_, 2);
lean_inc_ref(v_f_395_);
v___x_401_ = lean_apply_1(v_f_395_, v_head_399_);
v___x_402_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_397_, v___x_401_);
v_a_396_ = v_tail_400_;
v_a_397_ = v___x_402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_f_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_406_, v_a_407_, v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR___redArg(lean_object* v_f_410_, lean_object* v_as_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_413_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_410_, v_as_411_, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_f_416_, lean_object* v_as_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_419_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v_f_416_, v_as_417_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR___redArg(lean_object* v_l_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_423_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_424_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_422_, v_l_421_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_List_flattenTR(lean_object* v_00_u03b1_425_, lean_object* v_l_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = ((lean_object*)(l_List_flattenTR___redArg___closed__0));
v___x_428_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_429_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___redArg(v___x_427_, v_l_426_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object* v_l_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_inc(v_l_430_);
return v_l_430_;
}
else
{
lean_object* v_head_434_; lean_object* v_tail_435_; lean_object* v_zero_436_; uint8_t v_isZero_437_; 
v_head_434_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_head_434_);
v_tail_435_ = lean_ctor_get(v_a_431_, 1);
lean_inc(v_tail_435_);
lean_dec_ref_known(v_a_431_, 2);
v_zero_436_ = lean_unsigned_to_nat(0u);
v_isZero_437_ = lean_nat_dec_eq(v_a_432_, v_zero_436_);
if (v_isZero_437_ == 1)
{
lean_object* v___x_438_; 
lean_dec(v_tail_435_);
lean_dec(v_head_434_);
lean_dec(v_a_432_);
v___x_438_ = lean_array_to_list(v_a_433_);
return v___x_438_;
}
else
{
lean_object* v_one_439_; lean_object* v_n_440_; lean_object* v___x_441_; 
v_one_439_ = lean_unsigned_to_nat(1u);
v_n_440_ = lean_nat_sub(v_a_432_, v_one_439_);
lean_dec(v_a_432_);
v___x_441_ = lean_array_push(v_a_433_, v_head_434_);
v_a_431_ = v_tail_435_;
v_a_432_ = v_n_440_;
v_a_433_ = v___x_441_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg___boxed(lean_object* v_l_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_l_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object* v_00_u03b1_448_, lean_object* v_l_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_449_, v_a_450_, v_a_451_, v_a_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___boxed(lean_object* v_00_u03b1_454_, lean_object* v_l_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(v_00_u03b1_454_, v_l_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_l_455_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR___redArg(lean_object* v_n_460_, lean_object* v_l_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_461_);
v___x_463_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_461_, v_l_461_, v_n_460_, v___x_462_);
lean_dec(v_l_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_List_takeTR(lean_object* v_00_u03b1_464_, lean_object* v_n_465_, lean_object* v_l_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_466_);
v___x_468_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_l_466_, v_l_466_, v_n_465_, v___x_467_);
lean_dec(v_l_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_h__1_471_, lean_object* v_h__2_472_, lean_object* v_h__3_473_){
_start:
{
lean_object* v_zero_474_; uint8_t v_isZero_475_; 
v_zero_474_ = lean_unsigned_to_nat(0u);
v_isZero_475_ = lean_nat_dec_eq(v_x_469_, v_zero_474_);
if (v_isZero_475_ == 1)
{
lean_object* v___x_476_; 
lean_dec(v_h__3_473_);
lean_dec(v_h__2_472_);
v___x_476_ = lean_apply_1(v_h__1_471_, v_x_470_);
return v___x_476_;
}
else
{
lean_object* v_one_477_; lean_object* v_n_478_; 
lean_dec(v_h__1_471_);
v_one_477_ = lean_unsigned_to_nat(1u);
v_n_478_ = lean_nat_sub(v_x_469_, v_one_477_);
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_479_; 
lean_dec(v_h__3_473_);
v___x_479_ = lean_apply_1(v_h__2_472_, v_n_478_);
return v___x_479_;
}
else
{
lean_object* v_head_480_; lean_object* v_tail_481_; lean_object* v___x_482_; 
lean_dec(v_h__2_472_);
v_head_480_ = lean_ctor_get(v_x_470_, 0);
lean_inc(v_head_480_);
v_tail_481_ = lean_ctor_get(v_x_470_, 1);
lean_inc(v_tail_481_);
lean_dec_ref_known(v_x_470_, 2);
v___x_482_ = lean_apply_3(v_h__3_473_, v_n_478_, v_head_480_, v_tail_481_);
return v___x_482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg___boxed(lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_, lean_object* v_h__3_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___redArg(v_x_483_, v_x_484_, v_h__1_485_, v_h__2_486_, v_h__3_487_);
lean_dec(v_x_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(lean_object* v_00_u03b1_489_, lean_object* v_motive_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_h__1_493_, lean_object* v_h__2_494_, lean_object* v_h__3_495_){
_start:
{
lean_object* v_zero_496_; uint8_t v_isZero_497_; 
v_zero_496_ = lean_unsigned_to_nat(0u);
v_isZero_497_ = lean_nat_dec_eq(v_x_491_, v_zero_496_);
if (v_isZero_497_ == 1)
{
lean_object* v___x_498_; 
lean_dec(v_h__3_495_);
lean_dec(v_h__2_494_);
v___x_498_ = lean_apply_1(v_h__1_493_, v_x_492_);
return v___x_498_;
}
else
{
lean_object* v_one_499_; lean_object* v_n_500_; 
lean_dec(v_h__1_493_);
v_one_499_ = lean_unsigned_to_nat(1u);
v_n_500_ = lean_nat_sub(v_x_491_, v_one_499_);
if (lean_obj_tag(v_x_492_) == 0)
{
lean_object* v___x_501_; 
lean_dec(v_h__3_495_);
v___x_501_ = lean_apply_1(v_h__2_494_, v_n_500_);
return v___x_501_;
}
else
{
lean_object* v_head_502_; lean_object* v_tail_503_; lean_object* v___x_504_; 
lean_dec(v_h__2_494_);
v_head_502_ = lean_ctor_get(v_x_492_, 0);
lean_inc(v_head_502_);
v_tail_503_ = lean_ctor_get(v_x_492_, 1);
lean_inc(v_tail_503_);
lean_dec_ref_known(v_x_492_, 2);
v___x_504_ = lean_apply_3(v_h__3_495_, v_n_500_, v_head_502_, v_tail_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_505_, lean_object* v_motive_506_, lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_, lean_object* v_h__3_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_List_Impl_0__List_take_match__1_splitter(v_00_u03b1_505_, v_motive_506_, v_x_507_, v_x_508_, v_h__1_509_, v_h__2_510_, v_h__3_511_);
lean_dec(v_x_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_extractTR___redArg(lean_object* v_l_513_, lean_object* v_start_514_, lean_object* v_stop_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = lean_nat_sub(v_stop_515_, v_start_514_);
v___x_517_ = l_List_drop___redArg(v_start_514_, v_l_513_);
v___x_518_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v___x_517_);
v___x_519_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v___x_517_, v___x_517_, v___x_516_, v___x_518_);
lean_dec(v___x_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_List_extractTR___redArg___boxed(lean_object* v_l_520_, lean_object* v_start_521_, lean_object* v_stop_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_List_extractTR___redArg(v_l_520_, v_start_521_, v_stop_522_);
lean_dec(v_stop_522_);
lean_dec(v_l_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_List_extractTR(lean_object* v_00_u03b1_524_, lean_object* v_l_525_, lean_object* v_start_526_, lean_object* v_stop_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_nat_sub(v_stop_527_, v_start_526_);
v___x_529_ = l_List_drop___redArg(v_start_526_, v_l_525_);
v___x_530_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v___x_529_);
v___x_531_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v___x_529_, v___x_529_, v___x_528_, v___x_530_);
lean_dec(v___x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_List_extractTR___boxed(lean_object* v_00_u03b1_532_, lean_object* v_l_533_, lean_object* v_start_534_, lean_object* v_stop_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_List_extractTR(v_00_u03b1_532_, v_l_533_, v_start_534_, v_stop_535_);
lean_dec(v_stop_535_);
lean_dec(v_l_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeftTR___redArg(lean_object* v_xs_537_, lean_object* v_i_538_){
_start:
{
lean_object* v_len_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_len_539_ = l_List_lengthTR___redArg(v_xs_537_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_dec_le(v_len_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v_i_542_; lean_object* v___x_543_; lean_object* v_ys_544_; lean_object* v_zs_545_; lean_object* v___x_546_; 
v_i_542_ = lean_nat_mod(v_i_538_, v_len_539_);
lean_dec(v_len_539_);
v___x_543_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_i_542_);
lean_inc(v_xs_537_);
v_ys_544_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_xs_537_, v_xs_537_, v_i_542_, v___x_543_);
v_zs_545_ = l_List_drop___redArg(v_i_542_, v_xs_537_);
lean_dec(v_xs_537_);
v___x_546_ = l_List_appendTR___redArg(v_zs_545_, v_ys_544_);
return v___x_546_;
}
else
{
lean_dec(v_len_539_);
return v_xs_537_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateLeftTR___redArg___boxed(lean_object* v_xs_547_, lean_object* v_i_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_List_rotateLeftTR___redArg(v_xs_547_, v_i_548_);
lean_dec(v_i_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeftTR(lean_object* v_00_u03b1_550_, lean_object* v_xs_551_, lean_object* v_i_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_List_rotateLeftTR___redArg(v_xs_551_, v_i_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_List_rotateLeftTR___boxed(lean_object* v_00_u03b1_554_, lean_object* v_xs_555_, lean_object* v_i_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_List_rotateLeftTR(v_00_u03b1_554_, v_xs_555_, v_i_556_);
lean_dec(v_i_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRightTR___redArg(lean_object* v_xs_558_, lean_object* v_i_559_){
_start:
{
lean_object* v_len_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_len_560_ = l_List_lengthTR___redArg(v_xs_558_);
v___x_561_ = lean_unsigned_to_nat(1u);
v___x_562_ = lean_nat_dec_le(v_len_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v_i_564_; lean_object* v___x_565_; lean_object* v_ys_566_; lean_object* v_zs_567_; lean_object* v___x_568_; 
v___x_563_ = lean_nat_mod(v_i_559_, v_len_560_);
v_i_564_ = lean_nat_sub(v_len_560_, v___x_563_);
lean_dec(v___x_563_);
lean_dec(v_len_560_);
v___x_565_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_i_564_);
lean_inc(v_xs_558_);
v_ys_566_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v_xs_558_, v_xs_558_, v_i_564_, v___x_565_);
v_zs_567_ = l_List_drop___redArg(v_i_564_, v_xs_558_);
lean_dec(v_xs_558_);
v___x_568_ = l_List_appendTR___redArg(v_zs_567_, v_ys_566_);
return v___x_568_;
}
else
{
lean_dec(v_len_560_);
return v_xs_558_;
}
}
}
LEAN_EXPORT lean_object* l_List_rotateRightTR___redArg___boxed(lean_object* v_xs_569_, lean_object* v_i_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_List_rotateRightTR___redArg(v_xs_569_, v_i_570_);
lean_dec(v_i_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRightTR(lean_object* v_00_u03b1_572_, lean_object* v_xs_573_, lean_object* v_i_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_List_rotateRightTR___redArg(v_xs_573_, v_i_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_List_rotateRightTR___boxed(lean_object* v_00_u03b1_576_, lean_object* v_xs_577_, lean_object* v_i_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_List_rotateRightTR(v_00_u03b1_576_, v_xs_577_, v_i_578_);
lean_dec(v_i_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(lean_object* v_p_580_, lean_object* v_l_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
if (lean_obj_tag(v_a_582_) == 0)
{
lean_dec_ref(v_a_583_);
lean_dec_ref(v_p_580_);
lean_inc(v_l_581_);
return v_l_581_;
}
else
{
lean_object* v_head_584_; lean_object* v_tail_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_head_584_ = lean_ctor_get(v_a_582_, 0);
lean_inc_n(v_head_584_, 2);
v_tail_585_ = lean_ctor_get(v_a_582_, 1);
lean_inc(v_tail_585_);
lean_dec_ref_known(v_a_582_, 2);
lean_inc_ref(v_p_580_);
v___x_586_ = lean_apply_1(v_p_580_, v_head_584_);
v___x_587_ = lean_unbox(v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v_tail_585_);
lean_dec(v_head_584_);
lean_dec_ref(v_p_580_);
v___x_588_ = lean_array_to_list(v_a_583_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_array_push(v_a_583_, v_head_584_);
v_a_582_ = v_tail_585_;
v_a_583_ = v___x_589_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg___boxed(lean_object* v_p_591_, lean_object* v_l_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_591_, v_l_592_, v_a_593_, v_a_594_);
lean_dec(v_l_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(lean_object* v_00_u03b1_596_, lean_object* v_p_597_, lean_object* v_l_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_597_, v_l_598_, v_a_599_, v_a_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___boxed(lean_object* v_00_u03b1_602_, lean_object* v_p_603_, lean_object* v_l_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go(v_00_u03b1_602_, v_p_603_, v_l_604_, v_a_605_, v_a_606_);
lean_dec(v_l_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR___redArg(lean_object* v_p_608_, lean_object* v_l_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_609_);
v___x_611_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_608_, v_l_609_, v_l_609_, v___x_610_);
lean_dec(v_l_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_List_takeWhileTR(lean_object* v_00_u03b1_612_, lean_object* v_p_613_, lean_object* v_l_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_614_);
v___x_616_ = l___private_Init_Data_List_Impl_0__List_takeWhileTR_go___redArg(v_p_613_, v_l_614_, v_l_614_, v___x_615_);
lean_dec(v_l_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_617_, lean_object* v_h__1_618_, lean_object* v_h__2_619_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_h__2_619_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_apply_1(v_h__1_618_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_624_; 
lean_dec(v_h__1_618_);
v_head_622_ = lean_ctor_get(v_x_617_, 0);
lean_inc(v_head_622_);
v_tail_623_ = lean_ctor_get(v_x_617_, 1);
lean_inc(v_tail_623_);
lean_dec_ref_known(v_x_617_, 2);
v___x_624_ = lean_apply_2(v_h__2_619_, v_head_622_, v_tail_623_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_625_, lean_object* v_motive_626_, lean_object* v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_h__2_629_);
v___x_630_ = lean_box(0);
v___x_631_ = lean_apply_1(v_h__1_628_, v___x_630_);
return v___x_631_;
}
else
{
lean_object* v_head_632_; lean_object* v_tail_633_; lean_object* v___x_634_; 
lean_dec(v_h__1_628_);
v_head_632_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_head_632_);
v_tail_633_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_tail_633_);
lean_dec_ref_known(v_x_627_, 2);
v___x_634_ = lean_apply_2(v_h__2_629_, v_head_632_, v_tail_633_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(uint8_t v_x_635_, lean_object* v_h__1_636_, lean_object* v_h__2_637_){
_start:
{
if (v_x_635_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_h__1_636_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_apply_1(v_h__2_637_, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_h__2_637_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_apply_1(v_h__1_636_, v___x_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
uint8_t v_x_24__boxed_645_; lean_object* v_res_646_; 
v_x_24__boxed_645_ = lean_unbox(v_x_642_);
v_res_646_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_645_, v_h__1_643_, v_h__2_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(lean_object* v_motive_647_, uint8_t v_x_648_, lean_object* v_h__1_649_, lean_object* v_h__2_650_){
_start:
{
if (v_x_648_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_h__1_649_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_apply_1(v_h__2_650_, v___x_651_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_h__2_650_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_apply_1(v_h__1_649_, v___x_653_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_655_, lean_object* v_x_656_, lean_object* v_h__1_657_, lean_object* v_h__2_658_){
_start:
{
uint8_t v_x_35__boxed_659_; lean_object* v_res_660_; 
v_x_35__boxed_659_ = lean_unbox(v_x_656_);
v_res_660_ = l___private_Init_Data_List_Impl_0__List_filter_match__1_splitter(v_motive_655_, v_x_35__boxed_659_, v_h__1_657_, v_h__2_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter___redArg(lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_h__1_663_, lean_object* v_h__2_664_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
lean_object* v___x_665_; 
lean_dec(v_h__2_664_);
v___x_665_ = lean_apply_1(v_h__1_663_, v_x_662_);
return v___x_665_;
}
else
{
lean_object* v_head_666_; lean_object* v_tail_667_; lean_object* v___x_668_; 
lean_dec(v_h__1_663_);
v_head_666_ = lean_ctor_get(v_x_661_, 0);
lean_inc(v_head_666_);
v_tail_667_ = lean_ctor_get(v_x_661_, 1);
lean_inc(v_tail_667_);
lean_dec_ref_known(v_x_661_, 2);
v___x_668_ = lean_apply_3(v_h__2_664_, v_head_666_, v_tail_667_, v_x_662_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_takeWhileTR_go_match__1_splitter(lean_object* v_00_u03b1_669_, lean_object* v_motive_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_h__1_673_, lean_object* v_h__2_674_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_675_; 
lean_dec(v_h__2_674_);
v___x_675_ = lean_apply_1(v_h__1_673_, v_x_672_);
return v___x_675_;
}
else
{
lean_object* v_head_676_; lean_object* v_tail_677_; lean_object* v___x_678_; 
lean_dec(v_h__1_673_);
v_head_676_ = lean_ctor_get(v_x_671_, 0);
lean_inc(v_head_676_);
v_tail_677_ = lean_ctor_get(v_x_671_, 1);
lean_inc(v_tail_677_);
lean_dec_ref_known(v_x_671_, 2);
v___x_678_ = lean_apply_3(v_h__2_674_, v_head_676_, v_tail_677_, v_x_672_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR___redArg(lean_object* v_l_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_array_mk(v_l_679_);
v___x_681_ = lean_array_pop(v___x_680_);
v___x_682_ = lean_array_to_list(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_List_dropLastTR(lean_object* v_00_u03b1_683_, lean_object* v_l_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_array_mk(v_l_684_);
v___x_686_ = lean_array_pop(v___x_685_);
v___x_687_ = lean_array_to_list(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(lean_object* v_p_688_, lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v___x_690_; 
lean_dec_ref(v_p_688_);
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
lean_object* v_head_691_; lean_object* v_tail_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_head_691_ = lean_ctor_get(v_x_689_, 0);
lean_inc_n(v_head_691_, 2);
v_tail_692_ = lean_ctor_get(v_x_689_, 1);
lean_inc(v_tail_692_);
lean_dec_ref_known(v_x_689_, 2);
lean_inc_ref(v_p_688_);
v___x_693_ = lean_apply_1(v_p_688_, v_head_691_);
v___x_694_ = lean_unbox(v___x_693_);
if (v___x_694_ == 0)
{
lean_dec(v_head_691_);
v_x_689_ = v_tail_692_;
goto _start;
}
else
{
lean_object* v___x_696_; 
lean_dec(v_tail_692_);
lean_dec_ref(v_p_688_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_head_691_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR___redArg(lean_object* v_p_697_, lean_object* v_l_698_){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = l_List_reverse___redArg(v_l_698_);
v___x_700_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_697_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_List_findRev_x3fTR(lean_object* v_00_u03b1_701_, lean_object* v_p_702_, lean_object* v_l_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_List_findRev_x3fTR___redArg(v_p_702_, v_l_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00List_findRev_x3fTR_spec__0(lean_object* v_00_u03b1_705_, lean_object* v_p_706_, lean_object* v_x_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_List_find_x3f___at___00List_findRev_x3fTR_spec__0___redArg(v_p_706_, v_x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter___redArg(lean_object* v_x_709_, lean_object* v_h__1_710_, lean_object* v_h__2_711_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_h__1_710_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_apply_1(v_h__2_711_, v___x_712_);
return v___x_713_;
}
else
{
lean_object* v_val_714_; lean_object* v___x_715_; 
lean_dec(v_h__2_711_);
v_val_714_ = lean_ctor_get(v_x_709_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v_x_709_, 1);
v___x_715_ = lean_apply_1(v_h__1_710_, v_val_714_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findSome_x3f_match__1_splitter(lean_object* v_00_u03b2_716_, lean_object* v_motive_717_, lean_object* v_x_718_, lean_object* v_h__1_719_, lean_object* v_h__2_720_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v_h__1_719_);
v___x_721_ = lean_box(0);
v___x_722_ = lean_apply_1(v_h__2_720_, v___x_721_);
return v___x_722_;
}
else
{
lean_object* v_val_723_; lean_object* v___x_724_; 
lean_dec(v_h__2_720_);
v_val_723_ = lean_ctor_get(v_x_718_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v_x_718_, 1);
v___x_724_ = lean_apply_1(v_h__1_719_, v_val_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(lean_object* v_f_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_f_725_);
v___x_727_ = lean_box(0);
return v___x_727_;
}
else
{
lean_object* v_head_728_; lean_object* v_tail_729_; lean_object* v___x_730_; 
v_head_728_ = lean_ctor_get(v_x_726_, 0);
lean_inc(v_head_728_);
v_tail_729_ = lean_ctor_get(v_x_726_, 1);
lean_inc(v_tail_729_);
lean_dec_ref_known(v_x_726_, 2);
lean_inc_ref(v_f_725_);
v___x_730_ = lean_apply_1(v_f_725_, v_head_728_);
if (lean_obj_tag(v___x_730_) == 0)
{
v_x_726_ = v_tail_729_;
goto _start;
}
else
{
lean_dec(v_tail_729_);
lean_dec_ref(v_f_725_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR___redArg(lean_object* v_f_732_, lean_object* v_l_733_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_List_reverse___redArg(v_l_733_);
v___x_735_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_732_, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_List_findSomeRev_x3fTR(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_f_738_, lean_object* v_l_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_List_findSomeRev_x3fTR___redArg(v_f_738_, v_l_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_f_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_List_findSome_x3f___at___00List_findSomeRev_x3fTR_spec__0___redArg(v_f_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___lam__0(lean_object* v_x1_746_, lean_object* v_x2_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v_x1_746_);
lean_ctor_set(v___x_748_, 1, v_x2_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(lean_object* v_inst_750_, lean_object* v_l_751_, lean_object* v_b_752_, lean_object* v_c_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
if (lean_obj_tag(v_a_754_) == 0)
{
lean_dec_ref(v_a_755_);
lean_dec(v_c_753_);
lean_dec(v_b_752_);
lean_dec_ref(v_inst_750_);
lean_inc(v_l_751_);
return v_l_751_;
}
else
{
lean_object* v_head_756_; lean_object* v_tail_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_776_; 
v_head_756_ = lean_ctor_get(v_a_754_, 0);
v_tail_757_ = lean_ctor_get(v_a_754_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_a_754_);
if (v_isSharedCheck_776_ == 0)
{
v___x_759_ = v_a_754_;
v_isShared_760_ = v_isSharedCheck_776_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_tail_757_);
lean_inc(v_head_756_);
lean_dec(v_a_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_776_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
lean_inc_ref(v_inst_750_);
lean_inc(v_head_756_);
lean_inc(v_b_752_);
v___x_761_ = lean_apply_2(v_inst_750_, v_b_752_, v_head_756_);
v___x_762_ = lean_unbox(v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_del_object(v___x_759_);
v___x_763_ = lean_array_push(v_a_755_, v_head_756_);
v_a_754_ = v_tail_757_;
v_a_755_ = v___x_763_;
goto _start;
}
else
{
lean_object* v___x_766_; 
lean_dec(v_head_756_);
lean_dec(v_b_752_);
lean_dec_ref(v_inst_750_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_c_753_);
v___x_766_ = v___x_759_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_c_753_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_tail_757_);
v___x_766_ = v_reuseFailAlloc_775_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_767_ = lean_array_get_size(v_a_755_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_770_ = lean_nat_dec_lt(v___x_768_, v___x_767_);
if (v___x_770_ == 0)
{
lean_dec_ref(v_a_755_);
return v___x_766_;
}
else
{
lean_object* v___f_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___f_771_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_772_ = lean_usize_of_nat(v___x_767_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_769_, v___f_771_, v_a_755_, v___x_772_, v___x_773_, v___x_766_);
return v___x_774_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___boxed(lean_object* v_inst_777_, lean_object* v_l_778_, lean_object* v_b_779_, lean_object* v_c_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_777_, v_l_778_, v_b_779_, v_c_780_, v_a_781_, v_a_782_);
lean_dec(v_l_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go(lean_object* v_00_u03b1_784_, lean_object* v_inst_785_, lean_object* v_l_786_, lean_object* v_b_787_, lean_object* v_c_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_785_, v_l_786_, v_b_787_, v_c_788_, v_a_789_, v_a_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replaceTR_go___boxed(lean_object* v_00_u03b1_792_, lean_object* v_inst_793_, lean_object* v_l_794_, lean_object* v_b_795_, lean_object* v_c_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go(v_00_u03b1_792_, v_inst_793_, v_l_794_, v_b_795_, v_c_796_, v_a_797_, v_a_798_);
lean_dec(v_l_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR___redArg(lean_object* v_inst_800_, lean_object* v_l_801_, lean_object* v_b_802_, lean_object* v_c_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_801_);
v___x_805_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_800_, v_l_801_, v_b_802_, v_c_803_, v_l_801_, v___x_804_);
lean_dec(v_l_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_List_replaceTR(lean_object* v_00_u03b1_806_, lean_object* v_inst_807_, lean_object* v_l_808_, lean_object* v_b_809_, lean_object* v_c_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_808_);
v___x_812_ = l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg(v_inst_807_, v_l_808_, v_b_809_, v_c_810_, v_l_808_, v___x_811_);
lean_dec(v_l_808_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter___redArg(lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_h__1_816_, lean_object* v_h__2_817_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v___x_818_; 
lean_dec(v_h__2_817_);
v___x_818_ = lean_apply_2(v_h__1_816_, v_x_814_, v_x_815_);
return v___x_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; lean_object* v___x_821_; 
lean_dec(v_h__1_816_);
v_head_819_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_head_819_);
v_tail_820_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_tail_820_);
lean_dec_ref_known(v_x_813_, 2);
v___x_821_ = lean_apply_4(v_h__2_817_, v_head_819_, v_tail_820_, v_x_814_, v_x_815_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_replace_match__1_splitter(lean_object* v_00_u03b1_822_, lean_object* v_motive_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_h__1_827_, lean_object* v_h__2_828_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v___x_829_; 
lean_dec(v_h__2_828_);
v___x_829_ = lean_apply_2(v_h__1_827_, v_x_825_, v_x_826_);
return v___x_829_;
}
else
{
lean_object* v_head_830_; lean_object* v_tail_831_; lean_object* v___x_832_; 
lean_dec(v_h__1_827_);
v_head_830_ = lean_ctor_get(v_x_824_, 0);
lean_inc(v_head_830_);
v_tail_831_ = lean_ctor_get(v_x_824_, 1);
lean_inc(v_tail_831_);
lean_dec_ref_known(v_x_824_, 2);
v___x_832_ = lean_apply_4(v_h__2_828_, v_head_830_, v_tail_831_, v_x_825_, v_x_826_);
return v___x_832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(lean_object* v_f_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v___x_837_; 
lean_dec(v_a_835_);
lean_dec(v_f_833_);
v___x_837_ = lean_array_to_list(v_a_836_);
return v___x_837_;
}
else
{
lean_object* v_head_838_; lean_object* v_tail_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_858_; 
v_head_838_ = lean_ctor_get(v_a_834_, 0);
v_tail_839_ = lean_ctor_get(v_a_834_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_858_ == 0)
{
v___x_841_ = v_a_834_;
v_isShared_842_ = v_isSharedCheck_858_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_tail_839_);
lean_inc(v_head_838_);
lean_dec(v_a_834_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_858_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_zero_843_; uint8_t v_isZero_844_; 
v_zero_843_ = lean_unsigned_to_nat(0u);
v_isZero_844_ = lean_nat_dec_eq(v_a_835_, v_zero_843_);
if (v_isZero_844_ == 1)
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec(v_a_835_);
v___x_845_ = lean_apply_1(v_f_833_, v_head_838_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_845_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_tail_839_);
v___x_847_ = v_reuseFailAlloc_853_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_array_get_size(v_a_836_);
v___x_849_ = lean_nat_dec_lt(v_zero_843_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v_a_836_);
return v___x_847_;
}
else
{
size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_usize_of_nat(v___x_848_);
v___x_851_ = ((size_t)0ULL);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_836_, v___x_850_, v___x_851_, v___x_847_);
lean_dec_ref(v_a_836_);
return v___x_852_;
}
}
}
else
{
lean_object* v_one_854_; lean_object* v_n_855_; lean_object* v___x_856_; 
lean_del_object(v___x_841_);
v_one_854_ = lean_unsigned_to_nat(1u);
v_n_855_ = lean_nat_sub(v_a_835_, v_one_854_);
lean_dec(v_a_835_);
v___x_856_ = lean_array_push(v_a_836_, v_head_838_);
v_a_834_ = v_tail_839_;
v_a_835_ = v_n_855_;
v_a_836_ = v___x_856_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_modifyTR_go(lean_object* v_00_u03b1_859_, lean_object* v_f_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_860_, v_a_861_, v_a_862_, v_a_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR___redArg(lean_object* v_l_865_, lean_object* v_i_866_, lean_object* v_f_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_869_ = l___private_Init_Data_List_Impl_0__List_modifyTR_go___redArg(v_f_867_, v_l_865_, v_i_866_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_List_modifyTR(lean_object* v_00_u03b1_870_, lean_object* v_l_871_, lean_object* v_i_872_, lean_object* v_f_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_List_modifyTR___redArg(v_l_871_, v_i_872_, v_f_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_zero_879_; uint8_t v_isZero_880_; 
v_zero_879_ = lean_unsigned_to_nat(0u);
v_isZero_880_ = lean_nat_dec_eq(v_a_876_, v_zero_879_);
if (v_isZero_880_ == 1)
{
lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
lean_dec(v_a_876_);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v_a_875_);
lean_ctor_set(v___x_881_, 1, v_a_877_);
v___x_882_ = lean_array_get_size(v_a_878_);
v___x_883_ = lean_nat_dec_lt(v_zero_879_, v___x_882_);
if (v___x_883_ == 0)
{
lean_dec_ref(v_a_878_);
return v___x_881_;
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_usize_of_nat(v___x_882_);
v___x_885_ = ((size_t)0ULL);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_878_, v___x_884_, v___x_885_, v___x_881_);
lean_dec_ref(v_a_878_);
return v___x_886_;
}
}
else
{
if (lean_obj_tag(v_a_877_) == 0)
{
lean_object* v___x_887_; 
lean_dec(v_a_876_);
lean_dec(v_a_875_);
v___x_887_ = lean_array_to_list(v_a_878_);
return v___x_887_;
}
else
{
lean_object* v_head_888_; lean_object* v_tail_889_; lean_object* v_one_890_; lean_object* v_n_891_; lean_object* v___x_892_; 
v_head_888_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_head_888_);
v_tail_889_ = lean_ctor_get(v_a_877_, 1);
lean_inc(v_tail_889_);
lean_dec_ref_known(v_a_877_, 2);
v_one_890_ = lean_unsigned_to_nat(1u);
v_n_891_ = lean_nat_sub(v_a_876_, v_one_890_);
lean_dec(v_a_876_);
v___x_892_ = lean_array_push(v_a_878_, v_head_888_);
v_a_876_ = v_n_891_;
v_a_877_ = v_tail_889_;
v_a_878_ = v___x_892_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go(lean_object* v_00_u03b1_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_895_, v_a_896_, v_a_897_, v_a_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR___redArg(lean_object* v_l_900_, lean_object* v_n_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_904_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_902_, v_n_901_, v_l_900_, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_List_insertIdxTR(lean_object* v_00_u03b1_905_, lean_object* v_l_906_, lean_object* v_n_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_910_ = l___private_Init_Data_List_Impl_0__List_insertIdxTR_go___redArg(v_a_908_, v_n_907_, v_l_906_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter___redArg(lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_h__1_914_, lean_object* v_h__2_915_, lean_object* v_h__3_916_){
_start:
{
lean_object* v_zero_917_; uint8_t v_isZero_918_; 
v_zero_917_ = lean_unsigned_to_nat(0u);
v_isZero_918_ = lean_nat_dec_eq(v_x_911_, v_zero_917_);
if (v_isZero_918_ == 1)
{
lean_object* v___x_919_; 
lean_dec(v_h__3_916_);
lean_dec(v_h__2_915_);
lean_dec(v_x_911_);
v___x_919_ = lean_apply_2(v_h__1_914_, v_x_912_, v_x_913_);
return v___x_919_;
}
else
{
lean_dec(v_h__1_914_);
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v___x_920_; 
lean_dec(v_h__3_916_);
v___x_920_ = lean_apply_3(v_h__2_915_, v_x_911_, v_x_913_, lean_box(0));
return v___x_920_;
}
else
{
lean_object* v_head_921_; lean_object* v_tail_922_; lean_object* v_one_923_; lean_object* v_n_924_; lean_object* v___x_925_; 
lean_dec(v_h__2_915_);
v_head_921_ = lean_ctor_get(v_x_912_, 0);
lean_inc(v_head_921_);
v_tail_922_ = lean_ctor_get(v_x_912_, 1);
lean_inc(v_tail_922_);
lean_dec_ref_known(v_x_912_, 2);
v_one_923_ = lean_unsigned_to_nat(1u);
v_n_924_ = lean_nat_sub(v_x_911_, v_one_923_);
lean_dec(v_x_911_);
v___x_925_ = lean_apply_4(v_h__3_916_, v_n_924_, v_head_921_, v_tail_922_, v_x_913_);
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_insertIdxTR_go_match__1_splitter(lean_object* v_00_u03b1_926_, lean_object* v_motive_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_h__1_931_, lean_object* v_h__2_932_, lean_object* v_h__3_933_){
_start:
{
lean_object* v_zero_934_; uint8_t v_isZero_935_; 
v_zero_934_ = lean_unsigned_to_nat(0u);
v_isZero_935_ = lean_nat_dec_eq(v_x_928_, v_zero_934_);
if (v_isZero_935_ == 1)
{
lean_object* v___x_936_; 
lean_dec(v_h__3_933_);
lean_dec(v_h__2_932_);
lean_dec(v_x_928_);
v___x_936_ = lean_apply_2(v_h__1_931_, v_x_929_, v_x_930_);
return v___x_936_;
}
else
{
lean_dec(v_h__1_931_);
if (lean_obj_tag(v_x_929_) == 0)
{
lean_object* v___x_937_; 
lean_dec(v_h__3_933_);
v___x_937_ = lean_apply_3(v_h__2_932_, v_x_928_, v_x_930_, lean_box(0));
return v___x_937_;
}
else
{
lean_object* v_head_938_; lean_object* v_tail_939_; lean_object* v_one_940_; lean_object* v_n_941_; lean_object* v___x_942_; 
lean_dec(v_h__2_932_);
v_head_938_ = lean_ctor_get(v_x_929_, 0);
lean_inc(v_head_938_);
v_tail_939_ = lean_ctor_get(v_x_929_, 1);
lean_inc(v_tail_939_);
lean_dec_ref_known(v_x_929_, 2);
v_one_940_ = lean_unsigned_to_nat(1u);
v_n_941_ = lean_nat_sub(v_x_928_, v_one_940_);
lean_dec(v_x_928_);
v___x_942_ = lean_apply_4(v_h__3_933_, v_n_941_, v_head_938_, v_tail_939_, v_x_930_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(lean_object* v_inst_943_, lean_object* v_l_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
if (lean_obj_tag(v_a_946_) == 0)
{
lean_dec_ref(v_a_947_);
lean_dec(v_a_945_);
lean_dec_ref(v_inst_943_);
lean_inc(v_l_944_);
return v_l_944_;
}
else
{
lean_object* v_head_948_; lean_object* v_tail_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_head_948_ = lean_ctor_get(v_a_946_, 0);
lean_inc_n(v_head_948_, 2);
v_tail_949_ = lean_ctor_get(v_a_946_, 1);
lean_inc(v_tail_949_);
lean_dec_ref_known(v_a_946_, 2);
lean_inc_ref(v_inst_943_);
lean_inc(v_a_945_);
v___x_950_ = lean_apply_2(v_inst_943_, v_head_948_, v_a_945_);
v___x_951_ = lean_unbox(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
v___x_952_ = lean_array_push(v_a_947_, v_head_948_);
v_a_946_ = v_tail_949_;
v_a_947_ = v___x_952_;
goto _start;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
lean_dec(v_head_948_);
lean_dec(v_a_945_);
lean_dec_ref(v_inst_943_);
v___x_954_ = lean_array_get_size(v_a_947_);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_957_ = lean_nat_dec_lt(v___x_955_, v___x_954_);
if (v___x_957_ == 0)
{
lean_dec_ref(v_a_947_);
return v_tail_949_;
}
else
{
lean_object* v___f_958_; size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v___f_958_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_959_ = lean_usize_of_nat(v___x_954_);
v___x_960_ = ((size_t)0ULL);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_956_, v___f_958_, v_a_947_, v___x_959_, v___x_960_, v_tail_949_);
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg___boxed(lean_object* v_inst_962_, lean_object* v_l_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_962_, v_l_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_l_963_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go(lean_object* v_00_u03b1_968_, lean_object* v_inst_969_, lean_object* v_l_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_969_, v_l_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___boxed(lean_object* v_00_u03b1_975_, lean_object* v_inst_976_, lean_object* v_l_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go(v_00_u03b1_975_, v_inst_976_, v_l_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_l_977_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR___redArg(lean_object* v_inst_982_, lean_object* v_l_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_983_);
v___x_986_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_982_, v_l_983_, v_a_984_, v_l_983_, v___x_985_);
lean_dec(v_l_983_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_List_eraseTR(lean_object* v_00_u03b1_987_, lean_object* v_inst_988_, lean_object* v_l_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_989_);
v___x_992_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_988_, v_l_989_, v_a_990_, v_l_989_, v___x_991_);
lean_dec(v_l_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(lean_object* v_p_993_, lean_object* v_l_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
if (lean_obj_tag(v_a_995_) == 0)
{
lean_dec_ref(v_a_996_);
lean_dec_ref(v_p_993_);
lean_inc(v_l_994_);
return v_l_994_;
}
else
{
lean_object* v_head_997_; lean_object* v_tail_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_head_997_ = lean_ctor_get(v_a_995_, 0);
lean_inc_n(v_head_997_, 2);
v_tail_998_ = lean_ctor_get(v_a_995_, 1);
lean_inc(v_tail_998_);
lean_dec_ref_known(v_a_995_, 2);
lean_inc_ref(v_p_993_);
v___x_999_ = lean_apply_1(v_p_993_, v_head_997_);
v___x_1000_ = lean_unbox(v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_array_push(v_a_996_, v_head_997_);
v_a_995_ = v_tail_998_;
v_a_996_ = v___x_1001_;
goto _start;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
lean_dec(v_head_997_);
lean_dec_ref(v_p_993_);
v___x_1003_ = lean_array_get_size(v_a_996_);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = ((lean_object*)(l_List_foldrTR___redArg___closed__9));
v___x_1006_ = lean_nat_dec_lt(v___x_1004_, v___x_1003_);
if (v___x_1006_ == 0)
{
lean_dec_ref(v_a_996_);
return v_tail_998_;
}
else
{
lean_object* v___f_1007_; size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___f_1007_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_replaceTR_go___redArg___closed__0));
v___x_1008_ = lean_usize_of_nat(v___x_1003_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1005_, v___f_1007_, v_a_996_, v___x_1008_, v___x_1009_, v_tail_998_);
return v___x_1010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg___boxed(lean_object* v_p_1011_, lean_object* v_l_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_1011_, v_l_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_l_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go(lean_object* v_00_u03b1_1016_, lean_object* v_p_1017_, lean_object* v_l_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_1017_, v_l_1018_, v_a_1019_, v_a_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_erasePTR_go___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_p_1023_, lean_object* v_l_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go(v_00_u03b1_1022_, v_p_1023_, v_l_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_l_1024_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR___redArg(lean_object* v_p_1028_, lean_object* v_l_1029_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_1029_);
v___x_1031_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_1028_, v_l_1029_, v_l_1029_, v___x_1030_);
lean_dec(v_l_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_List_erasePTR(lean_object* v_00_u03b1_1032_, lean_object* v_p_1033_, lean_object* v_l_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_1034_);
v___x_1036_ = l___private_Init_Data_List_Impl_0__List_erasePTR_go___redArg(v_p_1033_, v_l_1034_, v_l_1034_, v___x_1035_);
lean_dec(v_l_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(lean_object* v_l_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_inc(v_l_1037_);
return v_l_1037_;
}
else
{
lean_object* v_head_1041_; lean_object* v_tail_1042_; lean_object* v_zero_1043_; uint8_t v_isZero_1044_; 
v_head_1041_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_head_1041_);
v_tail_1042_ = lean_ctor_get(v_a_1038_, 1);
lean_inc(v_tail_1042_);
lean_dec_ref_known(v_a_1038_, 2);
v_zero_1043_ = lean_unsigned_to_nat(0u);
v_isZero_1044_ = lean_nat_dec_eq(v_a_1039_, v_zero_1043_);
if (v_isZero_1044_ == 1)
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
lean_dec(v_head_1041_);
lean_dec(v_a_1039_);
v___x_1045_ = lean_array_get_size(v_a_1040_);
v___x_1046_ = lean_nat_dec_lt(v_zero_1043_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec_ref(v_a_1040_);
return v_tail_1042_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_usize_of_nat(v___x_1045_);
v___x_1048_ = ((size_t)0ULL);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1040_, v___x_1047_, v___x_1048_, v_tail_1042_);
lean_dec_ref(v_a_1040_);
return v___x_1049_;
}
}
else
{
lean_object* v_one_1050_; lean_object* v_n_1051_; lean_object* v___x_1052_; 
v_one_1050_ = lean_unsigned_to_nat(1u);
v_n_1051_ = lean_nat_sub(v_a_1039_, v_one_1050_);
lean_dec(v_a_1039_);
v___x_1052_ = lean_array_push(v_a_1040_, v_head_1041_);
v_a_1038_ = v_tail_1042_;
v_a_1039_ = v_n_1051_;
v_a_1040_ = v___x_1052_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg___boxed(lean_object* v_l_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_l_1054_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(lean_object* v_00_u03b1_1059_, lean_object* v_l_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_l_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go(v_00_u03b1_1065_, v_l_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_l_1066_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR___redArg(lean_object* v_l_1071_, lean_object* v_n_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_1071_);
v___x_1074_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_1071_, v_l_1071_, v_n_1072_, v___x_1073_);
lean_dec(v_l_1071_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_List_eraseIdxTR(lean_object* v_00_u03b1_1075_, lean_object* v_l_1076_, lean_object* v_n_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_l_1076_);
v___x_1079_ = l___private_Init_Data_List_Impl_0__List_eraseIdxTR_go___redArg(v_l_1076_, v_l_1076_, v_n_1077_, v___x_1078_);
lean_dec(v_l_1076_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_h__1_1082_, lean_object* v_h__2_1083_, lean_object* v_h__3_1084_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1085_; 
lean_dec(v_h__3_1084_);
lean_dec(v_h__2_1083_);
v___x_1085_ = lean_apply_1(v_h__1_1082_, v_x_1081_);
return v___x_1085_;
}
else
{
lean_object* v_head_1086_; lean_object* v_tail_1087_; lean_object* v_zero_1088_; uint8_t v_isZero_1089_; 
lean_dec(v_h__1_1082_);
v_head_1086_ = lean_ctor_get(v_x_1080_, 0);
lean_inc(v_head_1086_);
v_tail_1087_ = lean_ctor_get(v_x_1080_, 1);
lean_inc(v_tail_1087_);
lean_dec_ref_known(v_x_1080_, 2);
v_zero_1088_ = lean_unsigned_to_nat(0u);
v_isZero_1089_ = lean_nat_dec_eq(v_x_1081_, v_zero_1088_);
if (v_isZero_1089_ == 1)
{
lean_object* v___x_1090_; 
lean_dec(v_h__3_1084_);
lean_dec(v_x_1081_);
v___x_1090_ = lean_apply_2(v_h__2_1083_, v_head_1086_, v_tail_1087_);
return v___x_1090_;
}
else
{
lean_object* v_one_1091_; lean_object* v_n_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__2_1083_);
v_one_1091_ = lean_unsigned_to_nat(1u);
v_n_1092_ = lean_nat_sub(v_x_1081_, v_one_1091_);
lean_dec(v_x_1081_);
v___x_1093_ = lean_apply_3(v_h__3_1084_, v_head_1086_, v_tail_1087_, v_n_1092_);
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_1094_, lean_object* v_motive_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_h__1_1098_, lean_object* v_h__2_1099_, lean_object* v_h__3_1100_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_h__3_1100_);
lean_dec(v_h__2_1099_);
v___x_1101_ = lean_apply_1(v_h__1_1098_, v_x_1097_);
return v___x_1101_;
}
else
{
lean_object* v_head_1102_; lean_object* v_tail_1103_; lean_object* v_zero_1104_; uint8_t v_isZero_1105_; 
lean_dec(v_h__1_1098_);
v_head_1102_ = lean_ctor_get(v_x_1096_, 0);
lean_inc(v_head_1102_);
v_tail_1103_ = lean_ctor_get(v_x_1096_, 1);
lean_inc(v_tail_1103_);
lean_dec_ref_known(v_x_1096_, 2);
v_zero_1104_ = lean_unsigned_to_nat(0u);
v_isZero_1105_ = lean_nat_dec_eq(v_x_1097_, v_zero_1104_);
if (v_isZero_1105_ == 1)
{
lean_object* v___x_1106_; 
lean_dec(v_h__3_1100_);
lean_dec(v_x_1097_);
v___x_1106_ = lean_apply_2(v_h__2_1099_, v_head_1102_, v_tail_1103_);
return v___x_1106_;
}
else
{
lean_object* v_one_1107_; lean_object* v_n_1108_; lean_object* v___x_1109_; 
lean_dec(v_h__2_1099_);
v_one_1107_ = lean_unsigned_to_nat(1u);
v_n_1108_ = lean_nat_sub(v_x_1097_, v_one_1107_);
lean_dec(v_x_1097_);
v___x_1109_ = lean_apply_3(v_h__3_1100_, v_head_1102_, v_tail_1103_, v_n_1108_);
return v___x_1109_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_isPermTR___redArg(lean_object* v_inst_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1111_) == 0)
{
uint8_t v___x_1113_; 
lean_dec_ref(v_inst_1110_);
v___x_1113_ = l_List_isEmpty___redArg(v_x_1112_);
lean_dec(v_x_1112_);
return v___x_1113_;
}
else
{
lean_object* v_head_1114_; lean_object* v_tail_1115_; uint8_t v___x_1116_; 
v_head_1114_ = lean_ctor_get(v_x_1111_, 0);
lean_inc_n(v_head_1114_, 2);
v_tail_1115_ = lean_ctor_get(v_x_1111_, 1);
lean_inc(v_tail_1115_);
lean_dec_ref_known(v_x_1111_, 2);
lean_inc(v_x_1112_);
lean_inc_ref(v_inst_1110_);
v___x_1116_ = l_List_elem___redArg(v_inst_1110_, v_head_1114_, v_x_1112_);
if (v___x_1116_ == 0)
{
lean_dec(v_tail_1115_);
lean_dec(v_head_1114_);
lean_dec(v_x_1112_);
lean_dec_ref(v_inst_1110_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
lean_inc(v_x_1112_);
lean_inc_ref(v_inst_1110_);
v___x_1118_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___redArg(v_inst_1110_, v_x_1112_, v_head_1114_, v_x_1112_, v___x_1117_);
lean_dec(v_x_1112_);
v_x_1111_ = v_tail_1115_;
v_x_1112_ = v___x_1118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isPermTR___redArg___boxed(lean_object* v_inst_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_List_isPermTR___redArg(v_inst_1120_, v_x_1121_, v_x_1122_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT uint8_t l_List_isPermTR(lean_object* v_00_u03b1_1125_, lean_object* v_inst_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = l_List_isPermTR___redArg(v_inst_1126_, v_x_1127_, v_x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_List_isPermTR___boxed(lean_object* v_00_u03b1_1130_, lean_object* v_inst_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_List_isPermTR(v_00_u03b1_1130_, v_inst_1131_, v_x_1132_, v_x_1133_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_reverseAux_match__1_splitter___redArg(lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_h__1_1138_, lean_object* v_h__2_1139_){
_start:
{
if (lean_obj_tag(v_x_1136_) == 0)
{
lean_object* v___x_1140_; 
lean_dec(v_h__2_1139_);
v___x_1140_ = lean_apply_1(v_h__1_1138_, v_x_1137_);
return v___x_1140_;
}
else
{
lean_object* v_head_1141_; lean_object* v_tail_1142_; lean_object* v___x_1143_; 
lean_dec(v_h__1_1138_);
v_head_1141_ = lean_ctor_get(v_x_1136_, 0);
lean_inc(v_head_1141_);
v_tail_1142_ = lean_ctor_get(v_x_1136_, 1);
lean_inc(v_tail_1142_);
lean_dec_ref_known(v_x_1136_, 2);
v___x_1143_ = lean_apply_3(v_h__2_1139_, v_head_1141_, v_tail_1142_, v_x_1137_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_reverseAux_match__1_splitter(lean_object* v_00_u03b1_1144_, lean_object* v_motive_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_h__1_1148_, lean_object* v_h__2_1149_){
_start:
{
if (lean_obj_tag(v_x_1146_) == 0)
{
lean_object* v___x_1150_; 
lean_dec(v_h__2_1149_);
v___x_1150_ = lean_apply_1(v_h__1_1148_, v_x_1147_);
return v___x_1150_;
}
else
{
lean_object* v_head_1151_; lean_object* v_tail_1152_; lean_object* v___x_1153_; 
lean_dec(v_h__1_1148_);
v_head_1151_ = lean_ctor_get(v_x_1146_, 0);
lean_inc(v_head_1151_);
v_tail_1152_ = lean_ctor_get(v_x_1146_, 1);
lean_inc(v_tail_1152_);
lean_dec_ref_known(v_x_1146_, 2);
v___x_1153_ = lean_apply_3(v_h__2_1149_, v_head_1151_, v_tail_1152_, v_x_1147_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_isPermTR_match__1_splitter___redArg(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_h__1_1156_, lean_object* v_h__2_1157_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
lean_object* v___x_1158_; 
lean_dec(v_h__2_1157_);
v___x_1158_ = lean_apply_1(v_h__1_1156_, v_x_1155_);
return v___x_1158_;
}
else
{
lean_object* v_head_1159_; lean_object* v_tail_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__1_1156_);
v_head_1159_ = lean_ctor_get(v_x_1154_, 0);
lean_inc(v_head_1159_);
v_tail_1160_ = lean_ctor_get(v_x_1154_, 1);
lean_inc(v_tail_1160_);
lean_dec_ref_known(v_x_1154_, 2);
v___x_1161_ = lean_apply_3(v_h__2_1157_, v_head_1159_, v_tail_1160_, v_x_1155_);
return v___x_1161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_isPermTR_match__1_splitter(lean_object* v_00_u03b1_1162_, lean_object* v_motive_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_h__1_1166_, lean_object* v_h__2_1167_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_object* v___x_1168_; 
lean_dec(v_h__2_1167_);
v___x_1168_ = lean_apply_1(v_h__1_1166_, v_x_1165_);
return v___x_1168_;
}
else
{
lean_object* v_head_1169_; lean_object* v_tail_1170_; lean_object* v___x_1171_; 
lean_dec(v_h__1_1166_);
v_head_1169_ = lean_ctor_get(v_x_1164_, 0);
lean_inc(v_head_1169_);
v_tail_1170_ = lean_ctor_get(v_x_1164_, 1);
lean_inc(v_tail_1170_);
lean_dec_ref_known(v_x_1164_, 2);
v___x_1171_ = lean_apply_3(v_h__2_1167_, v_head_1169_, v_tail_1170_, v_x_1165_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object* v_f_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
if (lean_obj_tag(v_a_1173_) == 1)
{
if (lean_obj_tag(v_a_1174_) == 1)
{
lean_object* v_head_1176_; lean_object* v_tail_1177_; lean_object* v_head_1178_; lean_object* v_tail_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_head_1176_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_head_1176_);
v_tail_1177_ = lean_ctor_get(v_a_1173_, 1);
lean_inc(v_tail_1177_);
lean_dec_ref_known(v_a_1173_, 2);
v_head_1178_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_head_1178_);
v_tail_1179_ = lean_ctor_get(v_a_1174_, 1);
lean_inc(v_tail_1179_);
lean_dec_ref_known(v_a_1174_, 2);
lean_inc(v_f_1172_);
v___x_1180_ = lean_apply_2(v_f_1172_, v_head_1176_, v_head_1178_);
v___x_1181_ = lean_array_push(v_a_1175_, v___x_1180_);
v_a_1173_ = v_tail_1177_;
v_a_1174_ = v_tail_1179_;
v_a_1175_ = v___x_1181_;
goto _start;
}
else
{
lean_object* v___x_1183_; 
lean_dec_ref_known(v_a_1173_, 2);
lean_dec(v_a_1174_);
lean_dec(v_f_1172_);
v___x_1183_ = lean_array_to_list(v_a_1175_);
return v___x_1183_;
}
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec(v_f_1172_);
v___x_1184_ = lean_array_to_list(v_a_1175_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_00_u03b3_1187_, lean_object* v_f_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR___redArg(lean_object* v_f_1193_, lean_object* v_as_1194_, lean_object* v_bs_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_1197_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_1193_, v_as_1194_, v_bs_1195_, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithTR(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_00_u03b3_1200_, lean_object* v_f_1201_, lean_object* v_as_1202_, lean_object* v_bs_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_1205_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v_f_1201_, v_as_1202_, v_bs_1203_, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter___redArg(lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v_x_1208_, lean_object* v_h__1_1209_, lean_object* v_h__2_1210_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 1)
{
if (lean_obj_tag(v_x_1207_) == 1)
{
lean_object* v_head_1211_; lean_object* v_tail_1212_; lean_object* v_head_1213_; lean_object* v_tail_1214_; lean_object* v___x_1215_; 
lean_dec(v_h__2_1210_);
v_head_1211_ = lean_ctor_get(v_x_1206_, 0);
lean_inc(v_head_1211_);
v_tail_1212_ = lean_ctor_get(v_x_1206_, 1);
lean_inc(v_tail_1212_);
lean_dec_ref_known(v_x_1206_, 2);
v_head_1213_ = lean_ctor_get(v_x_1207_, 0);
lean_inc(v_head_1213_);
v_tail_1214_ = lean_ctor_get(v_x_1207_, 1);
lean_inc(v_tail_1214_);
lean_dec_ref_known(v_x_1207_, 2);
v___x_1215_ = lean_apply_5(v_h__1_1209_, v_head_1211_, v_tail_1212_, v_head_1213_, v_tail_1214_, v_x_1208_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; 
lean_dec(v_h__1_1209_);
v___x_1216_ = lean_apply_4(v_h__2_1210_, v_x_1206_, v_x_1207_, v_x_1208_, lean_box(0));
return v___x_1216_;
}
}
else
{
lean_object* v___x_1217_; 
lean_dec(v_h__1_1209_);
v___x_1217_ = lean_apply_4(v_h__2_1210_, v_x_1206_, v_x_1207_, v_x_1208_, lean_box(0));
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go_match__1_splitter(lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_00_u03b3_1220_, lean_object* v_motive_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v_h__1_1225_, lean_object* v_h__2_1226_){
_start:
{
if (lean_obj_tag(v_x_1222_) == 1)
{
if (lean_obj_tag(v_x_1223_) == 1)
{
lean_object* v_head_1227_; lean_object* v_tail_1228_; lean_object* v_head_1229_; lean_object* v_tail_1230_; lean_object* v___x_1231_; 
lean_dec(v_h__2_1226_);
v_head_1227_ = lean_ctor_get(v_x_1222_, 0);
lean_inc(v_head_1227_);
v_tail_1228_ = lean_ctor_get(v_x_1222_, 1);
lean_inc(v_tail_1228_);
lean_dec_ref_known(v_x_1222_, 2);
v_head_1229_ = lean_ctor_get(v_x_1223_, 0);
lean_inc(v_head_1229_);
v_tail_1230_ = lean_ctor_get(v_x_1223_, 1);
lean_inc(v_tail_1230_);
lean_dec_ref_known(v_x_1223_, 2);
v___x_1231_ = lean_apply_5(v_h__1_1225_, v_head_1227_, v_tail_1228_, v_head_1229_, v_tail_1230_, v_x_1224_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; 
lean_dec(v_h__1_1225_);
v___x_1232_ = lean_apply_4(v_h__2_1226_, v_x_1222_, v_x_1223_, v_x_1224_, lean_box(0));
return v___x_1232_;
}
}
else
{
lean_object* v___x_1233_; 
lean_dec(v_h__1_1225_);
v___x_1233_ = lean_apply_4(v_h__2_1226_, v_x_1222_, v_x_1223_, v_x_1224_, lean_box(0));
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipTR___redArg___lam__0(lean_object* v_fst_1234_, lean_object* v_snd_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_fst_1234_);
lean_ctor_set(v___x_1236_, 1, v_snd_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_List_zipTR___redArg(lean_object* v_xs_1240_, lean_object* v_ys_1241_){
_start:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___f_1242_ = ((lean_object*)(l_List_zipTR___redArg___closed__0));
v___x_1243_ = ((lean_object*)(l_List_zipTR___redArg___closed__1));
v___x_1244_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v___f_1242_, v_xs_1240_, v_ys_1241_, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_List_zipTR(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_xs_1247_, lean_object* v_ys_1248_){
_start:
{
lean_object* v___f_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___f_1249_ = ((lean_object*)(l_List_zipTR___redArg___closed__0));
v___x_1250_ = ((lean_object*)(l_List_zipTR___redArg___closed__1));
v___x_1251_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(v___f_1249_, v_xs_1247_, v_ys_1248_, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg(lean_object* v_as_1252_, size_t v_i_1253_, size_t v_stop_1254_, lean_object* v_b_1255_){
_start:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_usize_dec_eq(v_i_1253_, v_stop_1254_);
if (v___x_1256_ == 0)
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1279_; 
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_sub(v_i_1253_, v___x_1257_);
v___x_1259_ = lean_array_uget(v_as_1252_, v___x_1258_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
v_snd_1261_ = lean_ctor_get(v___x_1259_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1263_ = v___x_1259_;
v_isShared_1264_ = v_isSharedCheck_1279_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v___x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1279_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1278_; 
v_fst_1265_ = lean_ctor_get(v_b_1255_, 0);
v_snd_1266_ = lean_ctor_get(v_b_1255_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_b_1255_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1268_ = v_b_1255_;
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_b_1255_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1278_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
lean_ctor_set(v___x_1263_, 1, v_fst_1265_);
v___x_1271_ = v___x_1263_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_fst_1260_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_fst_1265_);
v___x_1271_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_snd_1261_);
lean_ctor_set(v___x_1272_, 1, v_snd_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1272_);
lean_ctor_set(v___x_1268_, 0, v___x_1271_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v_i_1253_ = v___x_1258_;
v_b_1255_ = v___x_1274_;
goto _start;
}
}
}
}
}
else
{
return v_b_1255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg___boxed(lean_object* v_as_1280_, lean_object* v_i_1281_, lean_object* v_stop_1282_, lean_object* v_b_1283_){
_start:
{
size_t v_i_boxed_1284_; size_t v_stop_boxed_1285_; lean_object* v_res_1286_; 
v_i_boxed_1284_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_stop_boxed_1285_ = lean_unbox_usize(v_stop_1282_);
lean_dec(v_stop_1282_);
v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg(v_as_1280_, v_i_boxed_1284_, v_stop_boxed_1285_, v_b_1283_);
lean_dec_ref(v_as_1280_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_unzipTR_spec__0___redArg(lean_object* v_init_1287_, lean_object* v_l_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1289_ = lean_array_mk(v_l_1288_);
v___x_1290_ = lean_array_get_size(v___x_1289_);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_nat_dec_lt(v___x_1291_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_dec_ref(v___x_1289_);
return v_init_1287_;
}
else
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_usize_of_nat(v___x_1290_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg(v___x_1289_, v___x_1293_, v___x_1294_, v_init_1287_);
lean_dec_ref(v___x_1289_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_List_unzipTR___redArg(lean_object* v_l_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_List_unzipTR___redArg___closed__0));
v___x_1300_ = l_List_foldrTR___at___00List_unzipTR_spec__0___redArg(v___x_1299_, v_l_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_List_unzipTR(lean_object* v_00_u03b1_1301_, lean_object* v_00_u03b2_1302_, lean_object* v_l_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_List_unzipTR___redArg(v_l_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_unzipTR_spec__0(lean_object* v_00_u03b1_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_init_1307_, lean_object* v_l_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_List_foldrTR___at___00List_unzipTR_spec__0___redArg(v_init_1307_, v_l_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0(lean_object* v_00_u03b1_1310_, lean_object* v_00_u03b2_1311_, lean_object* v_as_1312_, size_t v_i_1313_, size_t v_stop_1314_, lean_object* v_b_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___redArg(v_as_1312_, v_i_1313_, v_stop_1314_, v_b_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_as_1319_, lean_object* v_i_1320_, lean_object* v_stop_1321_, lean_object* v_b_1322_){
_start:
{
size_t v_i_boxed_1323_; size_t v_stop_boxed_1324_; lean_object* v_res_1325_; 
v_i_boxed_1323_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_stop_boxed_1324_ = lean_unbox_usize(v_stop_1321_);
lean_dec(v_stop_1321_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_unzipTR_spec__0_spec__0(v_00_u03b1_1317_, v_00_u03b2_1318_, v_as_1319_, v_i_boxed_1323_, v_stop_boxed_1324_, v_b_1322_);
lean_dec_ref(v_as_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(lean_object* v_as_1326_, size_t v_i_1327_, size_t v_stop_1328_, lean_object* v_b_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_eq(v_i_1327_, v_stop_1328_);
if (v___x_1330_ == 0)
{
lean_object* v_fst_1331_; lean_object* v_snd_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1347_; 
v_fst_1331_ = lean_ctor_get(v_b_1329_, 0);
v_snd_1332_ = lean_ctor_get(v_b_1329_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_b_1329_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1334_ = v_b_1329_;
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snd_1332_);
lean_inc(v_fst_1331_);
lean_dec(v_b_1329_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_sub(v_i_1327_, v___x_1336_);
v___x_1338_ = lean_array_uget_borrowed(v_as_1326_, v___x_1337_);
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_sub(v_fst_1331_, v___x_1339_);
lean_dec(v_fst_1331_);
lean_inc(v___x_1340_);
lean_inc(v___x_1338_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 1, v___x_1340_);
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1342_ = v___x_1334_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_snd_1332_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v_i_1327_ = v___x_1337_;
v_b_1329_ = v___x_1344_;
goto _start;
}
}
}
else
{
return v_b_1329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg___boxed(lean_object* v_as_1348_, lean_object* v_i_1349_, lean_object* v_stop_1350_, lean_object* v_b_1351_){
_start:
{
size_t v_i_boxed_1352_; size_t v_stop_boxed_1353_; lean_object* v_res_1354_; 
v_i_boxed_1352_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_stop_boxed_1353_ = lean_unbox_usize(v_stop_1350_);
lean_dec(v_stop_1350_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_1348_, v_i_boxed_1352_, v_stop_boxed_1353_, v_b_1351_);
lean_dec_ref(v_as_1348_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg(lean_object* v_l_1355_, lean_object* v_n_1356_){
_start:
{
lean_object* v_as_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_as_1357_ = lean_array_mk(v_l_1355_);
v___x_1358_ = lean_array_get_size(v_as_1357_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_nat_dec_lt(v___x_1360_, v___x_1358_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v_as_1357_);
return v___x_1359_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; lean_object* v___x_1366_; lean_object* v_snd_1367_; 
v___x_1362_ = lean_nat_add(v_n_1356_, v___x_1358_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v___x_1359_);
v___x_1364_ = lean_usize_of_nat(v___x_1358_);
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_1357_, v___x_1364_, v___x_1365_, v___x_1363_);
lean_dec_ref(v_as_1357_);
v_snd_1367_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_snd_1367_);
lean_dec_ref(v___x_1366_);
return v_snd_1367_;
}
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___redArg___boxed(lean_object* v_l_1368_, lean_object* v_n_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_List_zipIdxTR___redArg(v_l_1368_, v_n_1369_);
lean_dec(v_n_1369_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR(lean_object* v_00_u03b1_1371_, lean_object* v_l_1372_, lean_object* v_n_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_List_zipIdxTR___redArg(v_l_1372_, v_n_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_List_zipIdxTR___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_l_1376_, lean_object* v_n_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_List_zipIdxTR(v_00_u03b1_1375_, v_l_1376_, v_n_1377_);
lean_dec(v_n_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(lean_object* v_00_u03b1_1379_, lean_object* v_as_1380_, size_t v_i_1381_, size_t v_stop_1382_, lean_object* v_b_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___redArg(v_as_1380_, v_i_1381_, v_stop_1382_, v_b_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_as_1386_, lean_object* v_i_1387_, lean_object* v_stop_1388_, lean_object* v_b_1389_){
_start:
{
size_t v_i_boxed_1390_; size_t v_stop_boxed_1391_; lean_object* v_res_1392_; 
v_i_boxed_1390_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_stop_boxed_1391_ = lean_unbox_usize(v_stop_1388_);
lean_dec(v_stop_1388_);
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_zipIdxTR_spec__0(v_00_u03b1_1385_, v_as_1386_, v_i_boxed_1390_, v_stop_boxed_1391_, v_b_1389_);
lean_dec_ref(v_as_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter___redArg(lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_h__1_1395_, lean_object* v_h__2_1396_){
_start:
{
if (lean_obj_tag(v_x_1393_) == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_h__2_1396_);
v___x_1397_ = lean_apply_1(v_h__1_1395_, v_x_1394_);
return v___x_1397_;
}
else
{
lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v___x_1400_; 
lean_dec(v_h__1_1395_);
v_head_1398_ = lean_ctor_get(v_x_1393_, 0);
lean_inc(v_head_1398_);
v_tail_1399_ = lean_ctor_get(v_x_1393_, 1);
lean_inc(v_tail_1399_);
lean_dec_ref_known(v_x_1393_, 2);
v___x_1400_ = lean_apply_3(v_h__2_1396_, v_head_1398_, v_tail_1399_, v_x_1394_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_findIdx_go_match__1_splitter(lean_object* v_00_u03b1_1401_, lean_object* v_motive_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_, lean_object* v_h__1_1405_, lean_object* v_h__2_1406_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_h__2_1406_);
v___x_1407_ = lean_apply_1(v_h__1_1405_, v_x_1404_);
return v___x_1407_;
}
else
{
lean_object* v_head_1408_; lean_object* v_tail_1409_; lean_object* v___x_1410_; 
lean_dec(v_h__1_1405_);
v_head_1408_ = lean_ctor_get(v_x_1403_, 0);
lean_inc(v_head_1408_);
v_tail_1409_ = lean_ctor_get(v_x_1403_, 1);
lean_inc(v_tail_1409_);
lean_dec_ref_known(v_x_1403_, 2);
v___x_1410_ = lean_apply_3(v_h__2_1406_, v_head_1408_, v_tail_1409_, v_x_1404_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg(lean_object* v_sep_1411_, lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_, lean_object* v_b_1415_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1416_ == 0)
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_sub(v_i_1413_, v___x_1417_);
v___x_1419_ = lean_array_uget_borrowed(v_as_1412_, v___x_1418_);
lean_inc(v___x_1419_);
v___x_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v_b_1415_);
lean_inc(v_sep_1411_);
v___x_1421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1421_, 0, v_sep_1411_);
lean_ctor_set(v___x_1421_, 1, v___x_1420_);
v_i_1413_ = v___x_1418_;
v_b_1415_ = v___x_1421_;
goto _start;
}
else
{
lean_dec(v_sep_1411_);
return v_b_1415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg___boxed(lean_object* v_sep_1423_, lean_object* v_as_1424_, lean_object* v_i_1425_, lean_object* v_stop_1426_, lean_object* v_b_1427_){
_start:
{
size_t v_i_boxed_1428_; size_t v_stop_boxed_1429_; lean_object* v_res_1430_; 
v_i_boxed_1428_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_stop_boxed_1429_ = lean_unbox_usize(v_stop_1426_);
lean_dec(v_stop_1426_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg(v_sep_1423_, v_as_1424_, v_i_boxed_1428_, v_stop_boxed_1429_, v_b_1427_);
lean_dec_ref(v_as_1424_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_intersperseTR_spec__0___redArg(lean_object* v_sep_1431_, lean_object* v_init_1432_, lean_object* v_l_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1434_ = lean_array_mk(v_l_1433_);
v___x_1435_ = lean_array_get_size(v___x_1434_);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_nat_dec_lt(v___x_1436_, v___x_1435_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v___x_1434_);
lean_dec(v_sep_1431_);
return v_init_1432_;
}
else
{
size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_usize_of_nat(v___x_1435_);
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg(v_sep_1431_, v___x_1434_, v___x_1438_, v___x_1439_, v_init_1432_);
lean_dec_ref(v___x_1434_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR___redArg(lean_object* v_sep_1441_, lean_object* v_x_1442_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_dec(v_sep_1441_);
return v_x_1442_;
}
else
{
lean_object* v_tail_1443_; 
v_tail_1443_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_tail_1443_);
if (lean_obj_tag(v_tail_1443_) == 0)
{
lean_dec(v_sep_1441_);
return v_x_1442_;
}
else
{
lean_object* v_head_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1463_; 
v_head_1444_ = lean_ctor_get(v_x_1442_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1442_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_x_1442_, 1);
lean_dec(v_unused_1464_);
v___x_1446_ = v_x_1442_;
v_isShared_1447_ = v_isSharedCheck_1463_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_head_1444_);
lean_dec(v_x_1442_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1463_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1462_; 
v_head_1448_ = lean_ctor_get(v_tail_1443_, 0);
v_tail_1449_ = lean_ctor_get(v_tail_1443_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_tail_1443_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1451_ = v_tail_1443_;
v_isShared_1452_ = v_isSharedCheck_1462_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_tail_1449_);
lean_inc(v_head_1448_);
lean_dec(v_tail_1443_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1462_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1453_ = lean_box(0);
lean_inc(v_sep_1441_);
v___x_1454_ = l_List_foldrTR___at___00List_intersperseTR_spec__0___redArg(v_sep_1441_, v___x_1453_, v_tail_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_head_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1456_);
lean_ctor_set(v___x_1446_, 0, v_sep_1441_);
v___x_1458_ = v___x_1446_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_sep_1441_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_head_1444_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
return v___x_1459_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_intersperseTR(lean_object* v_00_u03b1_1465_, lean_object* v_sep_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_List_intersperseTR___redArg(v_sep_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00List_intersperseTR_spec__0(lean_object* v_00_u03b1_1469_, lean_object* v_sep_1470_, lean_object* v_init_1471_, lean_object* v_l_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_List_foldrTR___at___00List_intersperseTR_spec__0___redArg(v_sep_1470_, v_init_1471_, v_l_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0(lean_object* v_00_u03b1_1474_, lean_object* v_sep_1475_, lean_object* v_as_1476_, size_t v_i_1477_, size_t v_stop_1478_, lean_object* v_b_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___redArg(v_sep_1475_, v_as_1476_, v_i_1477_, v_stop_1478_, v_b_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_sep_1482_, lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_stop_1485_, lean_object* v_b_1486_){
_start:
{
size_t v_i_boxed_1487_; size_t v_stop_boxed_1488_; lean_object* v_res_1489_; 
v_i_boxed_1487_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_stop_boxed_1488_ = lean_unbox_usize(v_stop_1485_);
lean_dec(v_stop_1485_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00List_intersperseTR_spec__0_spec__0(v_00_u03b1_1481_, v_sep_1482_, v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_, v_b_1486_);
lean_dec_ref(v_as_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intersperseTR_match__1_splitter___redArg(lean_object* v_x_1490_, lean_object* v_h__1_1491_, lean_object* v_h__2_1492_, lean_object* v_h__3_1493_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__3_1493_);
lean_dec(v_h__2_1492_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_apply_1(v_h__1_1491_, v___x_1494_);
return v___x_1495_;
}
else
{
lean_object* v_tail_1496_; 
lean_dec(v_h__1_1491_);
v_tail_1496_ = lean_ctor_get(v_x_1490_, 1);
if (lean_obj_tag(v_tail_1496_) == 0)
{
lean_object* v_head_1497_; lean_object* v___x_1498_; 
lean_dec(v_h__3_1493_);
v_head_1497_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_head_1497_);
lean_dec_ref_known(v_x_1490_, 2);
v___x_1498_ = lean_apply_1(v_h__2_1492_, v_head_1497_);
return v___x_1498_;
}
else
{
lean_object* v_head_1499_; lean_object* v_head_1500_; lean_object* v_tail_1501_; lean_object* v___x_1502_; 
lean_inc_ref(v_tail_1496_);
lean_dec(v_h__2_1492_);
v_head_1499_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_head_1499_);
lean_dec_ref_known(v_x_1490_, 2);
v_head_1500_ = lean_ctor_get(v_tail_1496_, 0);
lean_inc(v_head_1500_);
v_tail_1501_ = lean_ctor_get(v_tail_1496_, 1);
lean_inc(v_tail_1501_);
lean_dec_ref_known(v_tail_1496_, 2);
v___x_1502_ = lean_apply_3(v_h__3_1493_, v_head_1499_, v_head_1500_, v_tail_1501_);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intersperseTR_match__1_splitter(lean_object* v_00_u03b1_1503_, lean_object* v_motive_1504_, lean_object* v_x_1505_, lean_object* v_h__1_1506_, lean_object* v_h__2_1507_, lean_object* v_h__3_1508_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__3_1508_);
lean_dec(v_h__2_1507_);
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_apply_1(v_h__1_1506_, v___x_1509_);
return v___x_1510_;
}
else
{
lean_object* v_tail_1511_; 
lean_dec(v_h__1_1506_);
v_tail_1511_ = lean_ctor_get(v_x_1505_, 1);
if (lean_obj_tag(v_tail_1511_) == 0)
{
lean_object* v_head_1512_; lean_object* v___x_1513_; 
lean_dec(v_h__3_1508_);
v_head_1512_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_head_1512_);
lean_dec_ref_known(v_x_1505_, 2);
v___x_1513_ = lean_apply_1(v_h__2_1507_, v_head_1512_);
return v___x_1513_;
}
else
{
lean_object* v_head_1514_; lean_object* v_head_1515_; lean_object* v_tail_1516_; lean_object* v___x_1517_; 
lean_inc_ref(v_tail_1511_);
lean_dec(v_h__2_1507_);
v_head_1514_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_head_1514_);
lean_dec_ref_known(v_x_1505_, 2);
v_head_1515_ = lean_ctor_get(v_tail_1511_, 0);
lean_inc(v_head_1515_);
v_tail_1516_ = lean_ctor_get(v_tail_1511_, 1);
lean_inc(v_tail_1516_);
lean_dec_ref_known(v_tail_1511_, 2);
v___x_1517_ = lean_apply_3(v_h__3_1508_, v_head_1514_, v_head_1515_, v_tail_1516_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_1518_, lean_object* v_h__1_1519_, lean_object* v_h__2_1520_, lean_object* v_h__3_1521_){
_start:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_dec(v_h__3_1521_);
lean_dec(v_h__2_1520_);
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_apply_1(v_h__1_1519_, v___x_1522_);
return v___x_1523_;
}
else
{
lean_object* v_tail_1524_; 
lean_dec(v_h__1_1519_);
v_tail_1524_ = lean_ctor_get(v_x_1518_, 1);
if (lean_obj_tag(v_tail_1524_) == 0)
{
lean_object* v_head_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__3_1521_);
v_head_1525_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_head_1525_);
lean_dec_ref_known(v_x_1518_, 2);
v___x_1526_ = lean_apply_1(v_h__2_1520_, v_head_1525_);
return v___x_1526_;
}
else
{
lean_object* v_head_1527_; lean_object* v___x_1528_; 
lean_inc(v_tail_1524_);
lean_dec(v_h__2_1520_);
v_head_1527_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_head_1527_);
lean_dec_ref_known(v_x_1518_, 2);
v___x_1528_ = lean_apply_3(v_h__3_1521_, v_head_1527_, v_tail_1524_, lean_box(0));
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_1529_, lean_object* v_motive_1530_, lean_object* v_x_1531_, lean_object* v_h__1_1532_, lean_object* v_h__2_1533_, lean_object* v_h__3_1534_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__3_1534_);
lean_dec(v_h__2_1533_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_apply_1(v_h__1_1532_, v___x_1535_);
return v___x_1536_;
}
else
{
lean_object* v_tail_1537_; 
lean_dec(v_h__1_1532_);
v_tail_1537_ = lean_ctor_get(v_x_1531_, 1);
if (lean_obj_tag(v_tail_1537_) == 0)
{
lean_object* v_head_1538_; lean_object* v___x_1539_; 
lean_dec(v_h__3_1534_);
v_head_1538_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_head_1538_);
lean_dec_ref_known(v_x_1531_, 2);
v___x_1539_ = lean_apply_1(v_h__2_1533_, v_head_1538_);
return v___x_1539_;
}
else
{
lean_object* v_head_1540_; lean_object* v___x_1541_; 
lean_inc(v_tail_1537_);
lean_dec(v_h__2_1533_);
v_head_1540_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_head_1540_);
lean_dec_ref_known(v_x_1531_, 2);
v___x_1541_ = lean_apply_3(v_h__3_1534_, v_head_1540_, v_tail_1537_, lean_box(0));
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(lean_object* v_sep_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
if (lean_obj_tag(v_a_1544_) == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_array_get_size(v_a_1545_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_lt(v___x_1547_, v___x_1546_);
if (v___x_1548_ == 0)
{
lean_dec_ref(v_a_1545_);
return v_a_1543_;
}
else
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_usize_of_nat(v___x_1546_);
v___x_1550_ = ((size_t)0ULL);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_setTR_go_spec__0___redArg(v_a_1545_, v___x_1549_, v___x_1550_, v_a_1543_);
lean_dec_ref(v_a_1545_);
return v___x_1551_;
}
}
else
{
lean_object* v_head_1552_; lean_object* v_tail_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_head_1552_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_head_1552_);
v_tail_1553_ = lean_ctor_get(v_a_1544_, 1);
lean_inc(v_tail_1553_);
lean_dec_ref_known(v_a_1544_, 2);
v___x_1554_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1545_, v_a_1543_);
v___x_1555_ = l_Array_append___redArg(v___x_1554_, v_sep_1542_);
v_a_1543_ = v_head_1552_;
v_a_1544_ = v_tail_1553_;
v_a_1545_ = v___x_1555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg___boxed(lean_object* v_sep_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec_ref(v_sep_1557_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go(lean_object* v_00_u03b1_1562_, lean_object* v_sep_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v_sep_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go___boxed(lean_object* v_00_u03b1_1568_, lean_object* v_sep_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go(v_00_u03b1_1568_, v_sep_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec_ref(v_sep_1569_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR___redArg(lean_object* v_sep_1574_, lean_object* v_x_1575_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_sep_1574_);
v___x_1576_ = lean_box(0);
return v___x_1576_;
}
else
{
lean_object* v_tail_1577_; 
v_tail_1577_ = lean_ctor_get(v_x_1575_, 1);
if (lean_obj_tag(v_tail_1577_) == 0)
{
lean_object* v_head_1578_; 
lean_dec(v_sep_1574_);
v_head_1578_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_head_1578_);
lean_dec_ref_known(v_x_1575_, 2);
return v_head_1578_;
}
else
{
lean_object* v_head_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_inc(v_tail_1577_);
v_head_1579_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_head_1579_);
lean_dec_ref_known(v_x_1575_, 2);
v___x_1580_ = lean_array_mk(v_sep_1574_);
v___x_1581_ = ((lean_object*)(l_List_setTR___redArg___closed__0));
v___x_1582_ = l___private_Init_Data_List_Impl_0__List_intercalateTR_go___redArg(v___x_1580_, v_head_1579_, v_tail_1577_, v___x_1581_);
lean_dec_ref(v___x_1580_);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_intercalateTR(lean_object* v_00_u03b1_1583_, lean_object* v_sep_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_List_intercalateTR___redArg(v_sep_1584_, v_x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter___redArg(lean_object* v_x_1587_, lean_object* v_h__1_1588_, lean_object* v_h__2_1589_, lean_object* v_h__3_1590_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_h__3_1590_);
lean_dec(v_h__2_1589_);
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_apply_1(v_h__1_1588_, v___x_1591_);
return v___x_1592_;
}
else
{
lean_object* v_tail_1593_; 
lean_dec(v_h__1_1588_);
v_tail_1593_ = lean_ctor_get(v_x_1587_, 1);
if (lean_obj_tag(v_tail_1593_) == 0)
{
lean_object* v_head_1594_; lean_object* v___x_1595_; 
lean_dec(v_h__3_1590_);
v_head_1594_ = lean_ctor_get(v_x_1587_, 0);
lean_inc(v_head_1594_);
lean_dec_ref_known(v_x_1587_, 2);
v___x_1595_ = lean_apply_1(v_h__2_1589_, v_head_1594_);
return v___x_1595_;
}
else
{
lean_object* v_head_1596_; lean_object* v___x_1597_; 
lean_inc(v_tail_1593_);
lean_dec(v_h__2_1589_);
v_head_1596_ = lean_ctor_get(v_x_1587_, 0);
lean_inc(v_head_1596_);
lean_dec_ref_known(v_x_1587_, 2);
v___x_1597_ = lean_apply_3(v_h__3_1590_, v_head_1596_, v_tail_1593_, lean_box(0));
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_match__1_splitter(lean_object* v_00_u03b1_1598_, lean_object* v_motive_1599_, lean_object* v_x_1600_, lean_object* v_h__1_1601_, lean_object* v_h__2_1602_, lean_object* v_h__3_1603_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_h__3_1603_);
lean_dec(v_h__2_1602_);
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_apply_1(v_h__1_1601_, v___x_1604_);
return v___x_1605_;
}
else
{
lean_object* v_tail_1606_; 
lean_dec(v_h__1_1601_);
v_tail_1606_ = lean_ctor_get(v_x_1600_, 1);
if (lean_obj_tag(v_tail_1606_) == 0)
{
lean_object* v_head_1607_; lean_object* v___x_1608_; 
lean_dec(v_h__3_1603_);
v_head_1607_ = lean_ctor_get(v_x_1600_, 0);
lean_inc(v_head_1607_);
lean_dec_ref_known(v_x_1600_, 2);
v___x_1608_ = lean_apply_1(v_h__2_1602_, v_head_1607_);
return v___x_1608_;
}
else
{
lean_object* v_head_1609_; lean_object* v___x_1610_; 
lean_inc(v_tail_1606_);
lean_dec(v_h__2_1602_);
v_head_1609_ = lean_ctor_get(v_x_1600_, 0);
lean_inc(v_head_1609_);
lean_dec_ref_known(v_x_1600_, 2);
v___x_1610_ = lean_apply_3(v_h__3_1603_, v_head_1609_, v_tail_1606_, lean_box(0));
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter___redArg(lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_h__1_1614_, lean_object* v_h__2_1615_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
lean_object* v___x_1616_; 
lean_dec(v_h__2_1615_);
v___x_1616_ = lean_apply_2(v_h__1_1614_, v_x_1611_, v_x_1613_);
return v___x_1616_;
}
else
{
lean_object* v_head_1617_; lean_object* v_tail_1618_; lean_object* v___x_1619_; 
lean_dec(v_h__1_1614_);
v_head_1617_ = lean_ctor_get(v_x_1612_, 0);
lean_inc(v_head_1617_);
v_tail_1618_ = lean_ctor_get(v_x_1612_, 1);
lean_inc(v_tail_1618_);
lean_dec_ref_known(v_x_1612_, 2);
v___x_1619_ = lean_apply_4(v_h__2_1615_, v_x_1611_, v_head_1617_, v_tail_1618_, v_x_1613_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_intercalateTR_go_match__1_splitter(lean_object* v_00_u03b1_1620_, lean_object* v_motive_1621_, lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_h__1_1625_, lean_object* v_h__2_1626_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v___x_1627_; 
lean_dec(v_h__2_1626_);
v___x_1627_ = lean_apply_2(v_h__1_1625_, v_x_1622_, v_x_1624_);
return v___x_1627_;
}
else
{
lean_object* v_head_1628_; lean_object* v_tail_1629_; lean_object* v___x_1630_; 
lean_dec(v_h__1_1625_);
v_head_1628_ = lean_ctor_get(v_x_1623_, 0);
lean_inc(v_head_1628_);
v_tail_1629_ = lean_ctor_get(v_x_1623_, 1);
lean_inc(v_tail_1629_);
lean_dec_ref_known(v_x_1623_, 2);
v___x_1630_ = lean_apply_4(v_h__2_1626_, v_x_1622_, v_head_1628_, v_tail_1629_, v_x_1624_);
return v___x_1630_;
}
}
}
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
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
res = runtime_initialize_Init_Data_List_Basic(builtin);
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
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
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
res = initialize_Init_Data_List_Basic(builtin);
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
