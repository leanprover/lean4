// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Zipper
// Imports: public import Std.Data.Iterators.Lemmas.Producers.Slice public import Init.Data.Slice public import Std.Data.DTreeMap.Internal.Lemmas public import Init.Data.Iterators.Combinators.FilterMap import Init.Data.Iterators.Lemmas.Combinators.FilterMap import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.List.Pairwise import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Slice.InternalLemmas
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
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Zipper_step___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(lean_object* v_inst_1_, lean_object* v_t_2_, lean_object* v_lowerBound_3_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_size_4_; lean_object* v_k_5_; lean_object* v_v_6_; lean_object* v_l_7_; lean_object* v_r_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_23_; 
v_size_4_ = lean_ctor_get(v_t_2_, 0);
v_k_5_ = lean_ctor_get(v_t_2_, 1);
v_v_6_ = lean_ctor_get(v_t_2_, 2);
v_l_7_ = lean_ctor_get(v_t_2_, 3);
v_r_8_ = lean_ctor_get(v_t_2_, 4);
v_isSharedCheck_23_ = !lean_is_exclusive(v_t_2_);
if (v_isSharedCheck_23_ == 0)
{
v___x_10_ = v_t_2_;
v_isShared_11_ = v_isSharedCheck_23_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_r_8_);
lean_inc(v_l_7_);
lean_inc(v_v_6_);
lean_inc(v_k_5_);
lean_inc(v_size_4_);
lean_dec(v_t_2_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_23_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; uint8_t v___x_13_; 
lean_inc_ref(v_inst_1_);
lean_inc(v_k_5_);
lean_inc(v_lowerBound_3_);
v___x_12_ = lean_apply_2(v_inst_1_, v_lowerBound_3_, v_k_5_);
v___x_13_ = lean_unbox(v___x_12_);
switch(v___x_13_)
{
case 0:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(v_inst_1_, v_l_7_, v_lowerBound_3_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 3, v___x_14_);
v___x_16_ = v___x_10_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_size_4_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_17_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_17_, 3, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_17_, 4, v_r_8_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
case 1:
{
lean_object* v___x_18_; lean_object* v___x_20_; 
lean_dec(v_l_7_);
lean_dec(v_lowerBound_3_);
lean_dec_ref(v_inst_1_);
v___x_18_ = lean_box(1);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 3, v___x_18_);
v___x_20_ = v___x_10_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_size_4_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_k_5_);
lean_ctor_set(v_reuseFailAlloc_21_, 2, v_v_6_);
lean_ctor_set(v_reuseFailAlloc_21_, 3, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_21_, 4, v_r_8_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
default: 
{
lean_del_object(v___x_10_);
lean_dec(v_l_7_);
lean_dec(v_v_6_);
lean_dec(v_k_5_);
lean_dec(v_size_4_);
v_t_2_ = v_r_8_;
goto _start;
}
}
}
}
else
{
lean_dec(v_lowerBound_3_);
lean_dec_ref(v_inst_1_);
return v_t_2_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_t_27_, lean_object* v_lowerBound_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(v_inst_26_, v_t_27_, v_lowerBound_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(lean_object* v_inst_30_, lean_object* v_t_31_, lean_object* v_lowerBound_32_){
_start:
{
if (lean_obj_tag(v_t_31_) == 0)
{
lean_object* v_size_33_; lean_object* v_k_34_; lean_object* v_v_35_; lean_object* v_l_36_; lean_object* v_r_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_48_; 
v_size_33_ = lean_ctor_get(v_t_31_, 0);
v_k_34_ = lean_ctor_get(v_t_31_, 1);
v_v_35_ = lean_ctor_get(v_t_31_, 2);
v_l_36_ = lean_ctor_get(v_t_31_, 3);
v_r_37_ = lean_ctor_get(v_t_31_, 4);
v_isSharedCheck_48_ = !lean_is_exclusive(v_t_31_);
if (v_isSharedCheck_48_ == 0)
{
v___x_39_ = v_t_31_;
v_isShared_40_ = v_isSharedCheck_48_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_r_37_);
lean_inc(v_l_36_);
lean_inc(v_v_35_);
lean_inc(v_k_34_);
lean_inc(v_size_33_);
lean_dec(v_t_31_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_48_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; uint8_t v___x_42_; 
lean_inc_ref(v_inst_30_);
lean_inc(v_k_34_);
lean_inc(v_lowerBound_32_);
v___x_41_ = lean_apply_2(v_inst_30_, v_lowerBound_32_, v_k_34_);
v___x_42_ = lean_unbox(v___x_41_);
switch(v___x_42_)
{
case 0:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(v_inst_30_, v_l_36_, v_lowerBound_32_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 3, v___x_43_);
v___x_45_ = v___x_39_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_size_33_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_k_34_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v_v_35_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_46_, 4, v_r_37_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
case 1:
{
lean_del_object(v___x_39_);
lean_dec(v_l_36_);
lean_dec(v_v_35_);
lean_dec(v_k_34_);
lean_dec(v_size_33_);
lean_dec(v_lowerBound_32_);
lean_dec_ref(v_inst_30_);
return v_r_37_;
}
default: 
{
lean_del_object(v___x_39_);
lean_dec(v_l_36_);
lean_dec(v_v_35_);
lean_dec(v_k_34_);
lean_dec(v_size_33_);
v_t_31_ = v_r_37_;
goto _start;
}
}
}
}
else
{
lean_dec(v_lowerBound_32_);
lean_dec_ref(v_inst_30_);
return v_t_31_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_t_52_, lean_object* v_lowerBound_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(v_inst_51_, v_t_52_, v_lowerBound_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(lean_object* v_t_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
if (lean_obj_tag(v_t_55_) == 0)
{
lean_object* v_size_58_; lean_object* v_k_59_; lean_object* v_v_60_; lean_object* v_l_61_; lean_object* v_r_62_; lean_object* v___x_63_; 
lean_dec(v_h__1_56_);
v_size_58_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_size_58_);
v_k_59_ = lean_ctor_get(v_t_55_, 1);
lean_inc(v_k_59_);
v_v_60_ = lean_ctor_get(v_t_55_, 2);
lean_inc(v_v_60_);
v_l_61_ = lean_ctor_get(v_t_55_, 3);
lean_inc(v_l_61_);
v_r_62_ = lean_ctor_get(v_t_55_, 4);
lean_inc(v_r_62_);
lean_dec_ref(v_t_55_);
v___x_63_ = lean_apply_5(v_h__2_57_, v_size_58_, v_k_59_, v_v_60_, v_l_61_, v_r_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v_h__2_57_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_1(v_h__1_56_, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_t_69_) == 0)
{
lean_object* v_size_72_; lean_object* v_k_73_; lean_object* v_v_74_; lean_object* v_l_75_; lean_object* v_r_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_70_);
v_size_72_ = lean_ctor_get(v_t_69_, 0);
lean_inc(v_size_72_);
v_k_73_ = lean_ctor_get(v_t_69_, 1);
lean_inc(v_k_73_);
v_v_74_ = lean_ctor_get(v_t_69_, 2);
lean_inc(v_v_74_);
v_l_75_ = lean_ctor_get(v_t_69_, 3);
lean_inc(v_l_75_);
v_r_76_ = lean_ctor_get(v_t_69_, 4);
lean_inc(v_r_76_);
lean_dec_ref(v_t_69_);
v___x_77_ = lean_apply_5(v_h__2_71_, v_size_72_, v_k_73_, v_v_74_, v_l_75_, v_r_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_71_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__1_70_, v___x_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t v_x_80_, lean_object* v_h__1_81_, lean_object* v_h__2_82_, lean_object* v_h__3_83_){
_start:
{
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__2_82_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__1_81_, v___x_84_);
return v___x_85_;
}
case 1:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__3_83_);
lean_dec(v_h__1_81_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__2_82_, v___x_86_);
return v___x_87_;
}
default: 
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_82_);
lean_dec(v_h__1_81_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__3_83_, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_, lean_object* v_h__3_93_){
_start:
{
uint8_t v_x_36__boxed_94_; lean_object* v_res_95_; 
v_x_36__boxed_94_ = lean_unbox(v_x_90_);
v_res_95_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_36__boxed_94_, v_h__1_91_, v_h__2_92_, v_h__3_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object* v_motive_96_, uint8_t v_x_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_, lean_object* v_h__3_100_){
_start:
{
switch(v_x_97_)
{
case 0:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__3_100_);
lean_dec(v_h__2_99_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__1_98_, v___x_101_);
return v___x_102_;
}
case 1:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_h__3_100_);
lean_dec(v_h__1_98_);
v___x_103_ = lean_box(0);
v___x_104_ = lean_apply_1(v_h__2_99_, v___x_103_);
return v___x_104_;
}
default: 
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__2_99_);
lean_dec(v_h__1_98_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__3_100_, v___x_105_);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object* v_motive_107_, lean_object* v_x_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_, lean_object* v_h__3_111_){
_start:
{
uint8_t v_x_51__boxed_112_; lean_object* v_res_113_; 
v_x_51__boxed_112_ = lean_unbox(v_x_108_);
v_res_113_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_107_, v_x_51__boxed_112_, v_h__1_109_, v_h__2_110_, v_h__3_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (v_x_114_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_h__1_115_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__2_116_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_116_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_apply_1(v_h__1_115_, v___x_119_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_){
_start:
{
uint8_t v_x_26__boxed_124_; lean_object* v_res_125_; 
v_x_26__boxed_124_ = lean_unbox(v_x_121_);
v_res_125_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_26__boxed_124_, v_h__1_122_, v_h__2_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object* v_motive_126_, uint8_t v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (v_x_127_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__1_128_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__2_129_, v___x_130_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_129_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__1_128_, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_134_, lean_object* v_x_135_, lean_object* v_h__1_136_, lean_object* v_h__2_137_){
_start:
{
uint8_t v_x_37__boxed_138_; lean_object* v_res_139_; 
v_x_37__boxed_138_ = lean_unbox(v_x_135_);
v_res_139_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(v_motive_134_, v_x_37__boxed_138_, v_h__1_136_, v_h__2_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_unsigned_to_nat(0u);
return v___x_141_;
}
else
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(1u);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_143_);
lean_dec(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx(v_00_u03b1_149_, v_00_u03b2_150_, v_x_151_);
lean_dec(v_x_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* v_t_153_, lean_object* v_k_154_){
_start:
{
if (lean_obj_tag(v_t_153_) == 0)
{
return v_k_154_;
}
else
{
lean_object* v_k_155_; lean_object* v_v_156_; lean_object* v_tree_157_; lean_object* v_next_158_; lean_object* v___x_159_; 
v_k_155_ = lean_ctor_get(v_t_153_, 0);
lean_inc(v_k_155_);
v_v_156_ = lean_ctor_get(v_t_153_, 1);
lean_inc(v_v_156_);
v_tree_157_ = lean_ctor_get(v_t_153_, 2);
lean_inc(v_tree_157_);
v_next_158_ = lean_ctor_get(v_t_153_, 3);
lean_inc(v_next_158_);
lean_dec_ref(v_t_153_);
v___x_159_ = lean_apply_4(v_k_154_, v_k_155_, v_v_156_, v_tree_157_, v_next_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_motive_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_164_, v_k_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_motive_170_, lean_object* v_ctorIdx_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(v_00_u03b1_168_, v_00_u03b2_169_, v_motive_170_, v_ctorIdx_171_, v_t_172_, v_h_173_, v_k_174_);
lean_dec(v_ctorIdx_171_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* v_t_176_, lean_object* v_done_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_176_, v_done_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_motive_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_done_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_182_, v_done_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* v_t_186_, lean_object* v_cons_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_186_, v_cons_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_cons_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_192_, v_cons_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* v_init_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v_k_198_; lean_object* v_v_199_; lean_object* v_l_200_; lean_object* v_r_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_k_198_ = lean_ctor_get(v_x_197_, 1);
v_v_199_ = lean_ctor_get(v_x_197_, 2);
v_l_200_ = lean_ctor_get(v_x_197_, 3);
v_r_201_ = lean_ctor_get(v_x_197_, 4);
v___x_202_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_196_, v_r_201_);
lean_inc(v_v_199_);
lean_inc(v_k_198_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_k_198_);
lean_ctor_set(v___x_203_, 1, v_v_199_);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
v_init_196_ = v___x_204_;
v_x_197_ = v_l_200_;
goto _start;
}
else
{
return v_init_196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* v_init_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_206_, v_x_207_);
lean_dec(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v_k_211_; lean_object* v_v_212_; lean_object* v_tree_213_; lean_object* v_next_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_k_211_ = lean_ctor_get(v_x_209_, 0);
v_v_212_ = lean_ctor_get(v_x_209_, 1);
v_tree_213_ = lean_ctor_get(v_x_209_, 2);
v_next_214_ = lean_ctor_get(v_x_209_, 3);
lean_inc(v_v_212_);
lean_inc(v_k_211_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v_k_211_);
lean_ctor_set(v___x_215_, 1, v_v_212_);
v___x_216_ = lean_box(0);
v___x_217_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_216_, v_tree_213_);
v___x_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_215_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_214_);
v___x_220_ = l_List_appendTR___redArg(v___x_218_, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* v_x_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_221_);
lean_dec(v_x_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_x_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_227_, v_00_u03b2_228_, v_x_229_);
lean_dec(v_x_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_init_233_, lean_object* v_x_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_233_, v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_init_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(v_00_u03b1_236_, v_00_u03b2_237_, v_init_238_, v_x_239_);
lean_dec(v_x_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(0u);
return v___x_242_;
}
else
{
lean_object* v_tree_243_; lean_object* v_next_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_tree_243_ = lean_ctor_get(v_x_241_, 2);
v_next_244_ = lean_ctor_get(v_x_241_, 3);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_243_);
v___x_247_ = lean_nat_add(v___x_245_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_244_);
v___x_249_ = lean_nat_add(v___x_247_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v___x_247_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_250_);
lean_dec(v_x_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(v_00_u03b1_256_, v_00_u03b2_257_, v_x_258_);
lean_dec(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_k_262_; lean_object* v_v_263_; lean_object* v_l_264_; lean_object* v_r_265_; lean_object* v___x_266_; 
v_k_262_ = lean_ctor_get(v_x_260_, 1);
v_v_263_ = lean_ctor_get(v_x_260_, 2);
v_l_264_ = lean_ctor_get(v_x_260_, 3);
v_r_265_ = lean_ctor_get(v_x_260_, 4);
lean_inc(v_r_265_);
lean_inc(v_v_263_);
lean_inc(v_k_262_);
v___x_266_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_266_, 0, v_k_262_);
lean_ctor_set(v___x_266_, 1, v_v_263_);
lean_ctor_set(v___x_266_, 2, v_r_265_);
lean_ctor_set(v___x_266_, 3, v_x_261_);
v_x_260_ = v_l_264_;
v_x_261_ = v___x_266_;
goto _start;
}
else
{
return v_x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_268_, v_x_269_);
lean_dec(v_x_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* v_00_u03b1_271_, lean_object* v_00_u03b2_272_, lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_273_, v_x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_DTreeMap_Internal_Zipper_prependMap(v_00_u03b1_276_, v_00_u03b2_277_, v_x_278_, v_x_279_);
lean_dec(v_x_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* v_inst_281_, lean_object* v_t_282_, lean_object* v_lowerBound_283_, lean_object* v_it_284_){
_start:
{
if (lean_obj_tag(v_t_282_) == 0)
{
lean_object* v_k_285_; lean_object* v_v_286_; lean_object* v_l_287_; lean_object* v_r_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_k_285_ = lean_ctor_get(v_t_282_, 1);
lean_inc(v_k_285_);
v_v_286_ = lean_ctor_get(v_t_282_, 2);
lean_inc(v_v_286_);
v_l_287_ = lean_ctor_get(v_t_282_, 3);
lean_inc(v_l_287_);
v_r_288_ = lean_ctor_get(v_t_282_, 4);
lean_inc(v_r_288_);
lean_dec_ref(v_t_282_);
lean_inc_ref(v_inst_281_);
lean_inc(v_k_285_);
lean_inc(v_lowerBound_283_);
v___x_289_ = lean_apply_2(v_inst_281_, v_lowerBound_283_, v_k_285_);
v___x_290_ = lean_unbox(v___x_289_);
switch(v___x_290_)
{
case 0:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_291_, 0, v_k_285_);
lean_ctor_set(v___x_291_, 1, v_v_286_);
lean_ctor_set(v___x_291_, 2, v_r_288_);
lean_ctor_set(v___x_291_, 3, v_it_284_);
v_t_282_ = v_l_287_;
v_it_284_ = v___x_291_;
goto _start;
}
case 1:
{
lean_object* v___x_293_; 
lean_dec(v_l_287_);
lean_dec(v_lowerBound_283_);
lean_dec_ref(v_inst_281_);
v___x_293_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_293_, 0, v_k_285_);
lean_ctor_set(v___x_293_, 1, v_v_286_);
lean_ctor_set(v___x_293_, 2, v_r_288_);
lean_ctor_set(v___x_293_, 3, v_it_284_);
return v___x_293_;
}
default: 
{
lean_dec(v_l_287_);
lean_dec(v_v_286_);
lean_dec(v_k_285_);
v_t_282_ = v_r_288_;
goto _start;
}
}
}
else
{
lean_dec(v_lowerBound_283_);
lean_dec_ref(v_inst_281_);
return v_it_284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_t_298_, lean_object* v_lowerBound_299_, lean_object* v_it_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_297_, v_t_298_, v_lowerBound_299_, v_it_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* v_inst_302_, lean_object* v_t_303_, lean_object* v_lowerBound_304_, lean_object* v_it_305_){
_start:
{
if (lean_obj_tag(v_t_303_) == 0)
{
lean_object* v_k_306_; lean_object* v_v_307_; lean_object* v_l_308_; lean_object* v_r_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_k_306_ = lean_ctor_get(v_t_303_, 1);
lean_inc(v_k_306_);
v_v_307_ = lean_ctor_get(v_t_303_, 2);
lean_inc(v_v_307_);
v_l_308_ = lean_ctor_get(v_t_303_, 3);
lean_inc(v_l_308_);
v_r_309_ = lean_ctor_get(v_t_303_, 4);
lean_inc(v_r_309_);
lean_dec_ref(v_t_303_);
lean_inc_ref(v_inst_302_);
lean_inc(v_k_306_);
lean_inc(v_lowerBound_304_);
v___x_310_ = lean_apply_2(v_inst_302_, v_lowerBound_304_, v_k_306_);
v___x_311_ = lean_unbox(v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_312_, 0, v_k_306_);
lean_ctor_set(v___x_312_, 1, v_v_307_);
lean_ctor_set(v___x_312_, 2, v_r_309_);
lean_ctor_set(v___x_312_, 3, v_it_305_);
v_t_303_ = v_l_308_;
v_it_305_ = v___x_312_;
goto _start;
}
else
{
lean_dec(v_l_308_);
lean_dec(v_v_307_);
lean_dec(v_k_306_);
v_t_303_ = v_r_309_;
goto _start;
}
}
else
{
lean_dec(v_lowerBound_304_);
lean_dec_ref(v_inst_302_);
return v_it_305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* v_00_u03b1_315_, lean_object* v_00_u03b2_316_, lean_object* v_inst_317_, lean_object* v_t_318_, lean_object* v_lowerBound_319_, lean_object* v_it_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_317_, v_t_318_, v_lowerBound_319_, v_it_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_size_326_; lean_object* v_k_327_; lean_object* v_v_328_; lean_object* v_l_329_; lean_object* v_r_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_324_);
v_size_326_ = lean_ctor_get(v_x_322_, 0);
lean_inc(v_size_326_);
v_k_327_ = lean_ctor_get(v_x_322_, 1);
lean_inc(v_k_327_);
v_v_328_ = lean_ctor_get(v_x_322_, 2);
lean_inc(v_v_328_);
v_l_329_ = lean_ctor_get(v_x_322_, 3);
lean_inc(v_l_329_);
v_r_330_ = lean_ctor_get(v_x_322_, 4);
lean_inc(v_r_330_);
lean_dec_ref(v_x_322_);
v___x_331_ = lean_apply_6(v_h__2_325_, v_size_326_, v_k_327_, v_v_328_, v_l_329_, v_r_330_, v_x_323_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; 
lean_dec(v_h__2_325_);
v___x_332_ = lean_apply_1(v_h__1_324_, v_x_323_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_motive_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v_size_340_; lean_object* v_k_341_; lean_object* v_v_342_; lean_object* v_l_343_; lean_object* v_r_344_; lean_object* v___x_345_; 
lean_dec(v_h__1_338_);
v_size_340_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_size_340_);
v_k_341_ = lean_ctor_get(v_x_336_, 1);
lean_inc(v_k_341_);
v_v_342_ = lean_ctor_get(v_x_336_, 2);
lean_inc(v_v_342_);
v_l_343_ = lean_ctor_get(v_x_336_, 3);
lean_inc(v_l_343_);
v_r_344_ = lean_ctor_get(v_x_336_, 4);
lean_inc(v_r_344_);
lean_dec_ref(v_x_336_);
v___x_345_ = lean_apply_6(v_h__2_339_, v_size_340_, v_k_341_, v_v_342_, v_l_343_, v_r_344_, v_x_337_);
return v___x_345_;
}
else
{
lean_object* v___x_346_; 
lean_dec(v_h__2_339_);
v___x_346_ = lean_apply_1(v_h__1_338_, v_x_337_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object* v_x_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_h__2_349_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_apply_1(v_h__1_348_, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v_k_352_; lean_object* v_v_353_; lean_object* v_tree_354_; lean_object* v_next_355_; lean_object* v___x_356_; 
lean_dec(v_h__1_348_);
v_k_352_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_k_352_);
v_v_353_ = lean_ctor_get(v_x_347_, 1);
lean_inc(v_v_353_);
v_tree_354_ = lean_ctor_get(v_x_347_, 2);
lean_inc(v_tree_354_);
v_next_355_ = lean_ctor_get(v_x_347_, 3);
lean_inc(v_next_355_);
lean_dec_ref(v_x_347_);
v___x_356_ = lean_apply_4(v_h__2_349_, v_k_352_, v_v_353_, v_tree_354_, v_next_355_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object* v_00_u03b1_357_, lean_object* v_00_u03b2_358_, lean_object* v_motive_359_, lean_object* v_x_360_, lean_object* v_h__1_361_, lean_object* v_h__2_362_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_h__2_362_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_h__1_361_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_k_365_; lean_object* v_v_366_; lean_object* v_tree_367_; lean_object* v_next_368_; lean_object* v___x_369_; 
lean_dec(v_h__1_361_);
v_k_365_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_k_365_);
v_v_366_ = lean_ctor_get(v_x_360_, 1);
lean_inc(v_v_366_);
v_tree_367_ = lean_ctor_get(v_x_360_, 2);
lean_inc(v_tree_367_);
v_next_368_ = lean_ctor_get(v_x_360_, 3);
lean_inc(v_next_368_);
lean_dec_ref(v_x_360_);
v___x_369_ = lean_apply_4(v_h__2_362_, v_k_365_, v_v_366_, v_tree_367_, v_next_368_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object* v_x_370_, lean_object* v_h__1_371_, lean_object* v_h__2_372_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
lean_object* v_size_373_; lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_l_376_; lean_object* v_r_377_; lean_object* v___x_378_; 
lean_dec(v_h__1_371_);
v_size_373_ = lean_ctor_get(v_x_370_, 0);
lean_inc(v_size_373_);
v_k_374_ = lean_ctor_get(v_x_370_, 1);
lean_inc(v_k_374_);
v_v_375_ = lean_ctor_get(v_x_370_, 2);
lean_inc(v_v_375_);
v_l_376_ = lean_ctor_get(v_x_370_, 3);
lean_inc(v_l_376_);
v_r_377_ = lean_ctor_get(v_x_370_, 4);
lean_inc(v_r_377_);
lean_dec_ref(v_x_370_);
v___x_378_ = lean_apply_5(v_h__2_372_, v_size_373_, v_k_374_, v_v_375_, v_l_376_, v_r_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_dec(v_h__2_372_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_apply_1(v_h__1_371_, v___x_379_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_motive_383_, lean_object* v_x_384_, lean_object* v_h__1_385_, lean_object* v_h__2_386_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v_size_387_; lean_object* v_k_388_; lean_object* v_v_389_; lean_object* v_l_390_; lean_object* v_r_391_; lean_object* v___x_392_; 
lean_dec(v_h__1_385_);
v_size_387_ = lean_ctor_get(v_x_384_, 0);
lean_inc(v_size_387_);
v_k_388_ = lean_ctor_get(v_x_384_, 1);
lean_inc(v_k_388_);
v_v_389_ = lean_ctor_get(v_x_384_, 2);
lean_inc(v_v_389_);
v_l_390_ = lean_ctor_get(v_x_384_, 3);
lean_inc(v_l_390_);
v_r_391_ = lean_ctor_get(v_x_384_, 4);
lean_inc(v_r_391_);
lean_dec_ref(v_x_384_);
v___x_392_ = lean_apply_5(v_h__2_386_, v_size_387_, v_k_388_, v_v_389_, v_l_390_, v_r_391_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_h__2_386_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_apply_1(v_h__1_385_, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_box(2);
return v___x_396_;
}
else
{
lean_object* v_k_397_; lean_object* v_v_398_; lean_object* v_tree_399_; lean_object* v_next_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_k_397_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_k_397_);
v_v_398_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_v_398_);
v_tree_399_ = lean_ctor_get(v_x_395_, 2);
lean_inc(v_tree_399_);
v_next_400_ = lean_ctor_get(v_x_395_, 3);
lean_inc(v_next_400_);
lean_dec_ref(v_x_395_);
v___x_401_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_399_, v_next_400_);
lean_dec(v_tree_399_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_k_397_);
lean_ctor_set(v___x_402_, 1, v_v_398_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_x_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_){
_start:
{
lean_object* v___f_411_; 
v___f_411_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0));
return v___f_411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_415_){
_start:
{
lean_inc(v_t_415_);
return v_t_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_416_);
lean_dec(v_t_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_t_420_){
_start:
{
lean_inc(v_t_420_);
return v_t_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_t_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_421_, v_00_u03b2_422_, v_t_423_);
lean_dec(v_t_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_box(0);
v___x_427_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_428_);
lean_dec(v_t_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_t_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_434_, lean_object* v_00_u03b2_435_, lean_object* v_t_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_434_, v_00_u03b2_435_, v_t_436_);
lean_dec(v_t_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(lean_object* v_x_438_){
_start:
{
lean_inc(v_x_438_);
return v_x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(v_x_439_);
lean_dec(v_x_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_442_, lean_object* v_00_u03b2_443_){
_start:
{
lean_object* v___f_444_; 
v___f_444_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0));
return v___f_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_, lean_object* v_h__3_448_){
_start:
{
switch(lean_obj_tag(v_x_445_))
{
case 0:
{
lean_object* v_it_449_; lean_object* v_out_450_; lean_object* v___x_451_; 
lean_dec(v_h__3_448_);
lean_dec(v_h__2_447_);
v_it_449_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_it_449_);
v_out_450_ = lean_ctor_get(v_x_445_, 1);
lean_inc(v_out_450_);
lean_dec_ref(v_x_445_);
v___x_451_ = lean_apply_2(v_h__1_446_, v_it_449_, v_out_450_);
return v___x_451_;
}
case 1:
{
lean_object* v_it_452_; lean_object* v___x_453_; 
lean_dec(v_h__3_448_);
lean_dec(v_h__1_446_);
v_it_452_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_it_452_);
lean_dec_ref(v_x_445_);
v___x_453_ = lean_apply_1(v_h__2_447_, v_it_452_);
return v___x_453_;
}
default: 
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_h__2_447_);
lean_dec(v_h__1_446_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_apply_1(v_h__3_448_, v___x_454_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_m_458_, lean_object* v_motive_459_, lean_object* v_x_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_, lean_object* v_h__3_463_){
_start:
{
switch(lean_obj_tag(v_x_460_))
{
case 0:
{
lean_object* v_it_464_; lean_object* v_out_465_; lean_object* v___x_466_; 
lean_dec(v_h__3_463_);
lean_dec(v_h__2_462_);
v_it_464_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_it_464_);
v_out_465_ = lean_ctor_get(v_x_460_, 1);
lean_inc(v_out_465_);
lean_dec_ref(v_x_460_);
v___x_466_ = lean_apply_2(v_h__1_461_, v_it_464_, v_out_465_);
return v___x_466_;
}
case 1:
{
lean_object* v_it_467_; lean_object* v___x_468_; 
lean_dec(v_h__3_463_);
lean_dec(v_h__1_461_);
v_it_467_ = lean_ctor_get(v_x_460_, 0);
lean_inc(v_it_467_);
lean_dec_ref(v_x_460_);
v___x_468_ = lean_apply_1(v_h__2_462_, v_it_467_);
return v___x_468_;
}
default: 
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_h__2_462_);
lean_dec(v_h__1_461_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_apply_1(v_h__3_463_, v___x_469_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_471_, lean_object* v_x_472_){
_start:
{
lean_object* v_iter_473_; 
v_iter_473_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_iter_473_);
if (lean_obj_tag(v_iter_473_) == 0)
{
lean_object* v___x_474_; 
lean_dec_ref(v_x_472_);
lean_dec_ref(v_inst_471_);
v___x_474_ = lean_box(2);
return v___x_474_;
}
else
{
lean_object* v_upper_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_492_; 
v_upper_475_ = lean_ctor_get(v_x_472_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_472_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_x_472_, 0);
lean_dec(v_unused_493_);
v___x_477_ = v_x_472_;
v_isShared_478_ = v_isSharedCheck_492_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_upper_475_);
lean_dec(v_x_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_492_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v_tree_481_; lean_object* v_next_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_k_479_ = lean_ctor_get(v_iter_473_, 0);
lean_inc(v_k_479_);
v_v_480_ = lean_ctor_get(v_iter_473_, 1);
lean_inc(v_v_480_);
v_tree_481_ = lean_ctor_get(v_iter_473_, 2);
lean_inc(v_tree_481_);
v_next_482_ = lean_ctor_get(v_iter_473_, 3);
lean_inc(v_next_482_);
lean_dec_ref(v_iter_473_);
lean_inc(v_upper_475_);
lean_inc(v_k_479_);
v___x_483_ = lean_apply_2(v_inst_471_, v_k_479_, v_upper_475_);
v___x_484_ = lean_unbox(v___x_483_);
if (v___x_484_ == 2)
{
lean_object* v___x_485_; 
lean_dec(v_next_482_);
lean_dec(v_tree_481_);
lean_dec(v_v_480_);
lean_dec(v_k_479_);
lean_del_object(v___x_477_);
lean_dec(v_upper_475_);
v___x_485_ = lean_box(2);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_481_, v_next_482_);
lean_dec(v_tree_481_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_486_);
v___x_488_ = v___x_477_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_upper_475_);
v___x_488_ = v_reuseFailAlloc_491_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_k_479_);
lean_ctor_set(v___x_489_, 1, v_v_480_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_inst_496_, lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_496_, v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_499_, lean_object* v_it_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_499_, v_it_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_502_){
_start:
{
lean_object* v___f_503_; 
v___f_503_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_503_, 0, v_inst_502_);
return v___f_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v___f_507_; 
v___f_507_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_507_, 0, v_inst_506_);
return v___f_507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
lean_object* v_iter_511_; 
v_iter_511_ = lean_ctor_get(v_x_508_, 0);
if (lean_obj_tag(v_iter_511_) == 0)
{
lean_object* v_upper_512_; lean_object* v___x_513_; 
lean_dec(v_h__2_510_);
v_upper_512_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_upper_512_);
lean_dec_ref(v_x_508_);
v___x_513_ = lean_apply_1(v_h__1_509_, v_upper_512_);
return v___x_513_;
}
else
{
lean_object* v_upper_514_; lean_object* v_k_515_; lean_object* v_v_516_; lean_object* v_tree_517_; lean_object* v_next_518_; lean_object* v___x_519_; 
lean_inc_ref(v_iter_511_);
lean_dec(v_h__1_509_);
v_upper_514_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_upper_514_);
lean_dec_ref(v_x_508_);
v_k_515_ = lean_ctor_get(v_iter_511_, 0);
lean_inc(v_k_515_);
v_v_516_ = lean_ctor_get(v_iter_511_, 1);
lean_inc(v_v_516_);
v_tree_517_ = lean_ctor_get(v_iter_511_, 2);
lean_inc(v_tree_517_);
v_next_518_ = lean_ctor_get(v_iter_511_, 3);
lean_inc(v_next_518_);
lean_dec_ref(v_iter_511_);
v___x_519_ = lean_apply_5(v_h__2_510_, v_k_515_, v_v_516_, v_tree_517_, v_next_518_, v_upper_514_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_motive_523_, lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_){
_start:
{
lean_object* v_iter_527_; 
v_iter_527_ = lean_ctor_get(v_x_524_, 0);
if (lean_obj_tag(v_iter_527_) == 0)
{
lean_object* v_upper_528_; lean_object* v___x_529_; 
lean_dec(v_h__2_526_);
v_upper_528_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_upper_528_);
lean_dec_ref(v_x_524_);
v___x_529_ = lean_apply_1(v_h__1_525_, v_upper_528_);
return v___x_529_;
}
else
{
lean_object* v_upper_530_; lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v_tree_533_; lean_object* v_next_534_; lean_object* v___x_535_; 
lean_inc_ref(v_iter_527_);
lean_dec(v_h__1_525_);
v_upper_530_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_upper_530_);
lean_dec_ref(v_x_524_);
v_k_531_ = lean_ctor_get(v_iter_527_, 0);
lean_inc(v_k_531_);
v_v_532_ = lean_ctor_get(v_iter_527_, 1);
lean_inc(v_v_532_);
v_tree_533_ = lean_ctor_get(v_iter_527_, 2);
lean_inc(v_tree_533_);
v_next_534_ = lean_ctor_get(v_iter_527_, 3);
lean_inc(v_next_534_);
lean_dec_ref(v_iter_527_);
v___x_535_ = lean_apply_5(v_h__2_526_, v_k_531_, v_v_532_, v_tree_533_, v_next_534_, v_upper_530_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_motive_539_, lean_object* v_x_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_536_, v_00_u03b2_537_, v_inst_538_, v_motive_539_, v_x_540_, v_h__1_541_, v_h__2_542_);
lean_dec_ref(v_inst_538_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_inst_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_box(0);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_548_, v_00_u03b2_549_, v_inst_550_);
lean_dec_ref(v_inst_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_iter_554_; 
v_iter_554_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_iter_554_);
if (lean_obj_tag(v_iter_554_) == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v_x_553_);
lean_dec_ref(v_inst_552_);
v___x_555_ = lean_box(2);
return v___x_555_;
}
else
{
lean_object* v_upper_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_573_; 
v_upper_556_ = lean_ctor_get(v_x_553_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_x_553_, 0);
lean_dec(v_unused_574_);
v___x_558_ = v_x_553_;
v_isShared_559_ = v_isSharedCheck_573_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_upper_556_);
lean_dec(v_x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_573_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v_tree_562_; lean_object* v_next_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_k_560_ = lean_ctor_get(v_iter_554_, 0);
lean_inc(v_k_560_);
v_v_561_ = lean_ctor_get(v_iter_554_, 1);
lean_inc(v_v_561_);
v_tree_562_ = lean_ctor_get(v_iter_554_, 2);
lean_inc(v_tree_562_);
v_next_563_ = lean_ctor_get(v_iter_554_, 3);
lean_inc(v_next_563_);
lean_dec_ref(v_iter_554_);
lean_inc(v_upper_556_);
lean_inc(v_k_560_);
v___x_564_ = lean_apply_2(v_inst_552_, v_k_560_, v_upper_556_);
v___x_565_ = lean_unbox(v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_562_, v_next_563_);
lean_dec(v_tree_562_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_566_);
v___x_568_ = v___x_558_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_upper_556_);
v___x_568_ = v_reuseFailAlloc_571_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_k_560_);
lean_ctor_set(v___x_569_, 1, v_v_561_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_572_; 
lean_dec(v_next_563_);
lean_dec(v_tree_562_);
lean_dec(v_v_561_);
lean_dec(v_k_560_);
lean_del_object(v___x_558_);
lean_dec(v_upper_556_);
v___x_572_ = lean_box(2);
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_inst_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_580_, lean_object* v_it_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_580_, v_it_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_583_){
_start:
{
lean_object* v___f_584_; 
v___f_584_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_584_, 0, v_inst_583_);
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v___f_588_; 
v___f_588_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_588_, 0, v_inst_587_);
return v___f_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_){
_start:
{
lean_object* v_iter_592_; 
v_iter_592_ = lean_ctor_get(v_x_589_, 0);
if (lean_obj_tag(v_iter_592_) == 0)
{
lean_object* v_upper_593_; lean_object* v___x_594_; 
lean_dec(v_h__2_591_);
v_upper_593_ = lean_ctor_get(v_x_589_, 1);
lean_inc(v_upper_593_);
lean_dec_ref(v_x_589_);
v___x_594_ = lean_apply_1(v_h__1_590_, v_upper_593_);
return v___x_594_;
}
else
{
lean_object* v_upper_595_; lean_object* v_k_596_; lean_object* v_v_597_; lean_object* v_tree_598_; lean_object* v_next_599_; lean_object* v___x_600_; 
lean_inc_ref(v_iter_592_);
lean_dec(v_h__1_590_);
v_upper_595_ = lean_ctor_get(v_x_589_, 1);
lean_inc(v_upper_595_);
lean_dec_ref(v_x_589_);
v_k_596_ = lean_ctor_get(v_iter_592_, 0);
lean_inc(v_k_596_);
v_v_597_ = lean_ctor_get(v_iter_592_, 1);
lean_inc(v_v_597_);
v_tree_598_ = lean_ctor_get(v_iter_592_, 2);
lean_inc(v_tree_598_);
v_next_599_ = lean_ctor_get(v_iter_592_, 3);
lean_inc(v_next_599_);
lean_dec_ref(v_iter_592_);
v___x_600_ = lean_apply_5(v_h__2_591_, v_k_596_, v_v_597_, v_tree_598_, v_next_599_, v_upper_595_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_motive_604_, lean_object* v_x_605_, lean_object* v_h__1_606_, lean_object* v_h__2_607_){
_start:
{
lean_object* v_iter_608_; 
v_iter_608_ = lean_ctor_get(v_x_605_, 0);
if (lean_obj_tag(v_iter_608_) == 0)
{
lean_object* v_upper_609_; lean_object* v___x_610_; 
lean_dec(v_h__2_607_);
v_upper_609_ = lean_ctor_get(v_x_605_, 1);
lean_inc(v_upper_609_);
lean_dec_ref(v_x_605_);
v___x_610_ = lean_apply_1(v_h__1_606_, v_upper_609_);
return v___x_610_;
}
else
{
lean_object* v_upper_611_; lean_object* v_k_612_; lean_object* v_v_613_; lean_object* v_tree_614_; lean_object* v_next_615_; lean_object* v___x_616_; 
lean_inc_ref(v_iter_608_);
lean_dec(v_h__1_606_);
v_upper_611_ = lean_ctor_get(v_x_605_, 1);
lean_inc(v_upper_611_);
lean_dec_ref(v_x_605_);
v_k_612_ = lean_ctor_get(v_iter_608_, 0);
lean_inc(v_k_612_);
v_v_613_ = lean_ctor_get(v_iter_608_, 1);
lean_inc(v_v_613_);
v_tree_614_ = lean_ctor_get(v_iter_608_, 2);
lean_inc(v_tree_614_);
v_next_615_ = lean_ctor_get(v_iter_608_, 3);
lean_inc(v_next_615_);
lean_dec_ref(v_iter_608_);
v___x_616_ = lean_apply_5(v_h__2_607_, v_k_612_, v_v_613_, v_tree_614_, v_next_615_, v_upper_611_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_inst_619_, lean_object* v_motive_620_, lean_object* v_x_621_, lean_object* v_h__1_622_, lean_object* v_h__2_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_617_, v_00_u03b2_618_, v_inst_619_, v_motive_620_, v_x_621_, v_h__1_622_, v_h__2_623_);
lean_dec_ref(v_inst_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = lean_box(0);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_629_, v_00_u03b2_630_, v_inst_631_);
lean_dec_ref(v_inst_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(lean_object* v_carrier_633_, lean_object* v_range_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_carrier_633_);
lean_ctor_set(v___x_635_, 1, v_range_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_inst_639_){
_start:
{
lean_object* v___f_640_; 
v___f_640_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0));
return v___f_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_inst_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_641_, v_00_u03b2_642_, v_inst_643_);
lean_dec_ref(v_inst_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(lean_object* v_x_645_){
_start:
{
lean_object* v_treeMap_646_; lean_object* v_range_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_656_; 
v_treeMap_646_ = lean_ctor_get(v_x_645_, 0);
v_range_647_ = lean_ctor_get(v_x_645_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_656_ == 0)
{
v___x_649_ = v_x_645_;
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_range_647_);
lean_inc(v_treeMap_646_);
lean_dec(v_x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_651_ = lean_box(0);
v___x_652_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_646_, v___x_651_);
lean_dec(v_treeMap_646_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_range_647_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_inst_660_){
_start:
{
lean_object* v___f_661_; 
v___f_661_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0));
return v___f_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_662_, lean_object* v_00_u03b2_663_, lean_object* v_inst_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_662_, v_00_u03b2_663_, v_inst_664_);
lean_dec_ref(v_inst_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(lean_object* v_carrier_666_, lean_object* v_range_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_carrier_666_);
lean_ctor_set(v___x_668_, 1, v_range_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_670_, lean_object* v_inst_671_){
_start:
{
lean_object* v___f_672_; 
v___f_672_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0));
return v___f_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_673_, lean_object* v_inst_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_673_, v_inst_674_);
lean_dec_ref(v_inst_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(lean_object* v_x_676_){
_start:
{
lean_object* v_treeMap_677_; lean_object* v_range_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
v_treeMap_677_ = lean_ctor_get(v_x_676_, 0);
v_range_678_ = lean_ctor_get(v_x_676_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_687_ == 0)
{
v___x_680_ = v_x_676_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_range_678_);
lean_inc(v_treeMap_677_);
lean_dec(v_x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_682_ = lean_box(0);
v___x_683_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_677_, v___x_682_);
lean_dec(v_treeMap_677_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_683_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_range_678_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v___f_691_; 
v___f_691_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0));
return v___f_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_692_, lean_object* v_inst_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_692_, v_inst_693_);
lean_dec_ref(v_inst_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(lean_object* v_carrier_695_, lean_object* v_range_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_carrier_695_);
lean_ctor_set(v___x_697_, 1, v_range_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v___f_702_; 
v___f_702_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0));
return v___f_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_inst_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_703_, v_00_u03b2_704_, v_inst_705_);
lean_dec_ref(v_inst_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(lean_object* v_x_707_){
_start:
{
lean_object* v_treeMap_708_; lean_object* v_range_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
v_treeMap_708_ = lean_ctor_get(v_x_707_, 0);
v_range_709_ = lean_ctor_get(v_x_707_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v_x_707_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_range_709_);
lean_inc(v_treeMap_708_);
lean_dec(v_x_707_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_708_, v___x_713_);
lean_dec(v_treeMap_708_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_range_709_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_inst_722_){
_start:
{
lean_object* v___f_723_; 
v___f_723_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0));
return v___f_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_724_, v_00_u03b2_725_, v_inst_726_);
lean_dec_ref(v_inst_726_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(lean_object* v_carrier_728_, lean_object* v_range_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v_carrier_728_);
lean_ctor_set(v___x_730_, 1, v_range_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_inst_734_){
_start:
{
lean_object* v___f_735_; 
v___f_735_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0));
return v___f_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_inst_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_736_, v_00_u03b2_737_, v_inst_738_);
lean_dec_ref(v_inst_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(lean_object* v_x_740_){
_start:
{
lean_object* v_treeMap_741_; lean_object* v_range_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_751_; 
v_treeMap_741_ = lean_ctor_get(v_x_740_, 0);
v_range_742_ = lean_ctor_get(v_x_740_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_740_);
if (v_isSharedCheck_751_ == 0)
{
v___x_744_ = v_x_740_;
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_range_742_);
lean_inc(v_treeMap_741_);
lean_dec(v_x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_box(0);
v___x_747_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_741_, v___x_746_);
lean_dec(v_treeMap_741_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_range_742_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_753_, lean_object* v_00_u03b2_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v___f_756_; 
v___f_756_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0));
return v___f_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_inst_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_757_, v_00_u03b2_758_, v_inst_759_);
lean_dec_ref(v_inst_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(lean_object* v_carrier_761_, lean_object* v_range_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_carrier_761_);
lean_ctor_set(v___x_763_, 1, v_range_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_765_, lean_object* v_inst_766_){
_start:
{
lean_object* v___f_767_; 
v___f_767_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0));
return v___f_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_768_, lean_object* v_inst_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_768_, v_inst_769_);
lean_dec_ref(v_inst_769_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(lean_object* v_x_771_){
_start:
{
lean_object* v_treeMap_772_; lean_object* v_range_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v_treeMap_772_ = lean_ctor_get(v_x_771_, 0);
v_range_773_ = lean_ctor_get(v_x_771_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_782_ == 0)
{
v___x_775_ = v_x_771_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_range_773_);
lean_inc(v_treeMap_772_);
lean_dec(v_x_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_777_ = lean_box(0);
v___x_778_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_772_, v___x_777_);
lean_dec(v_treeMap_772_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_778_);
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_range_773_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_784_, lean_object* v_inst_785_){
_start:
{
lean_object* v___f_786_; 
v___f_786_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0));
return v___f_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_787_, lean_object* v_inst_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_787_, v_inst_788_);
lean_dec_ref(v_inst_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(lean_object* v_carrier_790_, lean_object* v_range_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_carrier_790_);
lean_ctor_set(v___x_792_, 1, v_range_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_794_, lean_object* v_00_u03b2_795_, lean_object* v_inst_796_){
_start:
{
lean_object* v___f_797_; 
v___f_797_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0));
return v___f_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_798_, lean_object* v_00_u03b2_799_, lean_object* v_inst_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_798_, v_00_u03b2_799_, v_inst_800_);
lean_dec_ref(v_inst_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(lean_object* v_x_802_){
_start:
{
lean_object* v_treeMap_803_; lean_object* v_range_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v_treeMap_803_ = lean_ctor_get(v_x_802_, 0);
v_range_804_ = lean_ctor_get(v_x_802_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_813_ == 0)
{
v___x_806_ = v_x_802_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_range_804_);
lean_inc(v_treeMap_803_);
lean_dec(v_x_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_803_, v___x_808_);
lean_dec(v_treeMap_803_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_range_804_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v___f_818_; 
v___f_818_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0));
return v___f_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_819_, lean_object* v_00_u03b2_820_, lean_object* v_inst_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_819_, v_00_u03b2_820_, v_inst_821_);
lean_dec_ref(v_inst_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_823_, lean_object* v_t_824_, lean_object* v_lowerBound_825_, lean_object* v_upperBound_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_box(0);
v___x_828_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_823_, v_t_824_, v_lowerBound_825_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_upperBound_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_inst_832_, lean_object* v_t_833_, lean_object* v_lowerBound_834_, lean_object* v_upperBound_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_box(0);
v___x_837_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_832_, v_t_833_, v_lowerBound_834_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_upperBound_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(lean_object* v_carrier_839_, lean_object* v_range_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v_carrier_839_);
lean_ctor_set(v___x_841_, 1, v_range_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_inst_845_){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0));
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_inst_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_847_, v_00_u03b2_848_, v_inst_849_);
lean_dec_ref(v_inst_849_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_range_853_; lean_object* v_treeMap_854_; lean_object* v_lower_855_; lean_object* v_upper_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_865_; 
v_range_853_ = lean_ctor_get(v_x_852_, 1);
lean_inc_ref(v_range_853_);
v_treeMap_854_ = lean_ctor_get(v_x_852_, 0);
lean_inc(v_treeMap_854_);
lean_dec_ref(v_x_852_);
v_lower_855_ = lean_ctor_get(v_range_853_, 0);
v_upper_856_ = lean_ctor_get(v_range_853_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_range_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_858_ = v_range_853_;
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_upper_856_);
lean_inc(v_lower_855_);
lean_dec(v_range_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = lean_box(0);
v___x_861_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_851_, v_treeMap_854_, v_lower_855_, v___x_860_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_upper_856_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_866_){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_867_, 0, v_inst_866_);
return v___f_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_868_, lean_object* v_00_u03b2_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(lean_object* v_carrier_872_, lean_object* v_range_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_carrier_872_);
lean_ctor_set(v___x_874_, 1, v_range_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_876_, lean_object* v_inst_877_){
_start:
{
lean_object* v___f_878_; 
v___f_878_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0));
return v___f_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_879_, lean_object* v_inst_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_879_, v_inst_880_);
lean_dec_ref(v_inst_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_range_884_; lean_object* v_treeMap_885_; lean_object* v_lower_886_; lean_object* v_upper_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_896_; 
v_range_884_ = lean_ctor_get(v_x_883_, 1);
lean_inc_ref(v_range_884_);
v_treeMap_885_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_treeMap_885_);
lean_dec_ref(v_x_883_);
v_lower_886_ = lean_ctor_get(v_range_884_, 0);
v_upper_887_ = lean_ctor_get(v_range_884_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_range_884_);
if (v_isSharedCheck_896_ == 0)
{
v___x_889_ = v_range_884_;
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_upper_887_);
lean_inc(v_lower_886_);
lean_dec(v_range_884_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_896_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
v___x_892_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_882_, v_treeMap_885_, v_lower_886_, v___x_891_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_upper_887_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_897_){
_start:
{
lean_object* v___f_898_; 
v___f_898_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_898_, 0, v_inst_897_);
return v___f_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_899_, lean_object* v_inst_900_){
_start:
{
lean_object* v___f_901_; 
v___f_901_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_901_, 0, v_inst_900_);
return v___f_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(lean_object* v_carrier_902_, lean_object* v_range_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_carrier_902_);
lean_ctor_set(v___x_904_, 1, v_range_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_inst_908_){
_start:
{
lean_object* v___f_909_; 
v___f_909_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0));
return v___f_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_inst_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_910_, v_00_u03b2_911_, v_inst_912_);
lean_dec_ref(v_inst_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_914_, lean_object* v_x_915_){
_start:
{
lean_object* v_range_916_; lean_object* v_treeMap_917_; lean_object* v_lower_918_; lean_object* v_upper_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_928_; 
v_range_916_ = lean_ctor_get(v_x_915_, 1);
lean_inc_ref(v_range_916_);
v_treeMap_917_ = lean_ctor_get(v_x_915_, 0);
lean_inc(v_treeMap_917_);
lean_dec_ref(v_x_915_);
v_lower_918_ = lean_ctor_get(v_range_916_, 0);
v_upper_919_ = lean_ctor_get(v_range_916_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_range_916_);
if (v_isSharedCheck_928_ == 0)
{
v___x_921_ = v_range_916_;
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_upper_919_);
lean_inc(v_lower_918_);
lean_dec(v_range_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v___x_924_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_914_, v_treeMap_917_, v_lower_918_, v___x_923_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_upper_919_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_929_){
_start:
{
lean_object* v___f_930_; 
v___f_930_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_930_, 0, v_inst_929_);
return v___f_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_inst_933_){
_start:
{
lean_object* v___f_934_; 
v___f_934_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_934_, 0, v_inst_933_);
return v___f_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_935_, lean_object* v_t_936_, lean_object* v_lowerBound_937_, lean_object* v_upperBound_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_box(0);
v___x_940_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_935_, v_t_936_, v_lowerBound_937_, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v_upperBound_938_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_inst_944_, lean_object* v_t_945_, lean_object* v_lowerBound_946_, lean_object* v_upperBound_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_box(0);
v___x_949_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_944_, v_t_945_, v_lowerBound_946_, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v_upperBound_947_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(lean_object* v_carrier_951_, lean_object* v_range_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_carrier_951_);
lean_ctor_set(v___x_953_, 1, v_range_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_955_, lean_object* v_00_u03b2_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v___f_958_; 
v___f_958_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0));
return v___f_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_959_, v_00_u03b2_960_, v_inst_961_);
lean_dec_ref(v_inst_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_963_, lean_object* v_x_964_){
_start:
{
lean_object* v_range_965_; lean_object* v_treeMap_966_; lean_object* v_lower_967_; lean_object* v_upper_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_range_965_ = lean_ctor_get(v_x_964_, 1);
lean_inc_ref(v_range_965_);
v_treeMap_966_ = lean_ctor_get(v_x_964_, 0);
lean_inc(v_treeMap_966_);
lean_dec_ref(v_x_964_);
v_lower_967_ = lean_ctor_get(v_range_965_, 0);
v_upper_968_ = lean_ctor_get(v_range_965_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_range_965_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v_range_965_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_upper_968_);
lean_inc(v_lower_967_);
lean_dec(v_range_965_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_box(0);
v___x_973_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_963_, v_treeMap_966_, v_lower_967_, v___x_972_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_973_);
v___x_975_ = v___x_970_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_upper_968_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_978_){
_start:
{
lean_object* v___f_979_; 
v___f_979_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_979_, 0, v_inst_978_);
return v___f_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_980_, lean_object* v_00_u03b2_981_, lean_object* v_inst_982_){
_start:
{
lean_object* v___f_983_; 
v___f_983_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_983_, 0, v_inst_982_);
return v___f_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(lean_object* v_carrier_984_, lean_object* v_range_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v_carrier_984_);
lean_ctor_set(v___x_986_, 1, v_range_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v___f_990_; 
v___f_990_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0));
return v___f_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_991_, lean_object* v_inst_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_991_, v_inst_992_);
lean_dec_ref(v_inst_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_994_, lean_object* v_x_995_){
_start:
{
lean_object* v_range_996_; lean_object* v_treeMap_997_; lean_object* v_lower_998_; lean_object* v_upper_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
v_range_996_ = lean_ctor_get(v_x_995_, 1);
lean_inc_ref(v_range_996_);
v_treeMap_997_ = lean_ctor_get(v_x_995_, 0);
lean_inc(v_treeMap_997_);
lean_dec_ref(v_x_995_);
v_lower_998_ = lean_ctor_get(v_range_996_, 0);
v_upper_999_ = lean_ctor_get(v_range_996_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_range_996_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1001_ = v_range_996_;
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_upper_999_);
lean_inc(v_lower_998_);
lean_dec(v_range_996_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_994_, v_treeMap_997_, v_lower_998_, v___x_1003_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_upper_999_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1009_){
_start:
{
lean_object* v___f_1010_; 
v___f_1010_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1010_, 0, v_inst_1009_);
return v___f_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1011_, lean_object* v_inst_1012_){
_start:
{
lean_object* v___f_1013_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1013_, 0, v_inst_1012_);
return v___f_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(lean_object* v_carrier_1014_, lean_object* v_range_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v_carrier_1014_);
lean_ctor_set(v___x_1016_, 1, v_range_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_inst_1020_){
_start:
{
lean_object* v___f_1021_; 
v___f_1021_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0));
return v___f_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_inst_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1022_, v_00_u03b2_1023_, v_inst_1024_);
lean_dec_ref(v_inst_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1026_, lean_object* v_x_1027_){
_start:
{
lean_object* v_range_1028_; lean_object* v_treeMap_1029_; lean_object* v_lower_1030_; lean_object* v_upper_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1040_; 
v_range_1028_ = lean_ctor_get(v_x_1027_, 1);
lean_inc_ref(v_range_1028_);
v_treeMap_1029_ = lean_ctor_get(v_x_1027_, 0);
lean_inc(v_treeMap_1029_);
lean_dec_ref(v_x_1027_);
v_lower_1030_ = lean_ctor_get(v_range_1028_, 0);
v_upper_1031_ = lean_ctor_get(v_range_1028_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_range_1028_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1033_ = v_range_1028_;
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_upper_1031_);
lean_inc(v_lower_1030_);
lean_dec(v_range_1028_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1035_ = lean_box(0);
v___x_1036_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1026_, v_treeMap_1029_, v_lower_1030_, v___x_1035_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_upper_1031_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1041_){
_start:
{
lean_object* v___f_1042_; 
v___f_1042_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1042_, 0, v_inst_1041_);
return v___f_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v___f_1046_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1046_, 0, v_inst_1045_);
return v___f_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1047_, lean_object* v_t_1048_, lean_object* v_lowerBound_1049_, lean_object* v_upperBound_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1047_, v_t_1048_, v_lowerBound_1049_, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_upperBound_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_inst_1056_, lean_object* v_t_1057_, lean_object* v_lowerBound_1058_, lean_object* v_upperBound_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1056_, v_t_1057_, v_lowerBound_1058_, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v_upperBound_1059_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(lean_object* v_carrier_1063_, lean_object* v_range_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_carrier_1063_);
lean_ctor_set(v___x_1065_, 1, v_range_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_inst_1069_){
_start:
{
lean_object* v___f_1070_; 
v___f_1070_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0));
return v___f_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1071_, v_00_u03b2_1072_, v_inst_1073_);
lean_dec_ref(v_inst_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v_range_1077_; lean_object* v_treeMap_1078_; lean_object* v_lower_1079_; lean_object* v_upper_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
v_range_1077_ = lean_ctor_get(v_x_1076_, 1);
lean_inc_ref(v_range_1077_);
v_treeMap_1078_ = lean_ctor_get(v_x_1076_, 0);
lean_inc(v_treeMap_1078_);
lean_dec_ref(v_x_1076_);
v_lower_1079_ = lean_ctor_get(v_range_1077_, 0);
v_upper_1080_ = lean_ctor_get(v_range_1077_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_range_1077_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v_range_1077_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_upper_1080_);
lean_inc(v_lower_1079_);
lean_dec(v_range_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1075_, v_treeMap_1078_, v_lower_1079_, v___x_1084_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_upper_1080_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1090_){
_start:
{
lean_object* v___f_1091_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1091_, 0, v_inst_1090_);
return v___f_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_inst_1094_){
_start:
{
lean_object* v___f_1095_; 
v___f_1095_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1095_, 0, v_inst_1094_);
return v___f_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(lean_object* v_carrier_1096_, lean_object* v_range_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v_carrier_1096_);
lean_ctor_set(v___x_1098_, 1, v_range_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v___f_1102_; 
v___f_1102_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0));
return v___f_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1103_, lean_object* v_inst_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1103_, v_inst_1104_);
lean_dec_ref(v_inst_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v_range_1108_; lean_object* v_treeMap_1109_; lean_object* v_lower_1110_; lean_object* v_upper_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v_range_1108_ = lean_ctor_get(v_x_1107_, 1);
lean_inc_ref(v_range_1108_);
v_treeMap_1109_ = lean_ctor_get(v_x_1107_, 0);
lean_inc(v_treeMap_1109_);
lean_dec_ref(v_x_1107_);
v_lower_1110_ = lean_ctor_get(v_range_1108_, 0);
v_upper_1111_ = lean_ctor_get(v_range_1108_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_range_1108_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v_range_1108_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_upper_1111_);
lean_inc(v_lower_1110_);
lean_dec(v_range_1108_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1106_, v_treeMap_1109_, v_lower_1110_, v___x_1115_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1116_);
v___x_1118_ = v___x_1113_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_upper_1111_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1121_){
_start:
{
lean_object* v___f_1122_; 
v___f_1122_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1122_, 0, v_inst_1121_);
return v___f_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v___f_1125_; 
v___f_1125_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1125_, 0, v_inst_1124_);
return v___f_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(lean_object* v_carrier_1126_, lean_object* v_range_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_carrier_1126_);
lean_ctor_set(v___x_1128_, 1, v_range_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_inst_1132_){
_start:
{
lean_object* v___f_1133_; 
v___f_1133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0));
return v___f_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_inst_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1134_, v_00_u03b2_1135_, v_inst_1136_);
lean_dec_ref(v_inst_1136_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_range_1140_; lean_object* v_treeMap_1141_; lean_object* v_lower_1142_; lean_object* v_upper_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1152_; 
v_range_1140_ = lean_ctor_get(v_x_1139_, 1);
lean_inc_ref(v_range_1140_);
v_treeMap_1141_ = lean_ctor_get(v_x_1139_, 0);
lean_inc(v_treeMap_1141_);
lean_dec_ref(v_x_1139_);
v_lower_1142_ = lean_ctor_get(v_range_1140_, 0);
v_upper_1143_ = lean_ctor_get(v_range_1140_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_range_1140_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1145_ = v_range_1140_;
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_upper_1143_);
lean_inc(v_lower_1142_);
lean_dec(v_range_1140_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1152_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1138_, v_treeMap_1141_, v_lower_1142_, v___x_1147_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1148_);
v___x_1150_ = v___x_1145_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_upper_1143_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1153_){
_start:
{
lean_object* v___f_1154_; 
v___f_1154_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1154_, 0, v_inst_1153_);
return v___f_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v___f_1158_; 
v___f_1158_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1158_, 0, v_inst_1157_);
return v___f_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1159_, lean_object* v_t_1160_, lean_object* v_lowerBound_1161_, lean_object* v_upperBound_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1159_, v_t_1160_, v_lowerBound_1161_, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v_upperBound_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_inst_1168_, lean_object* v_t_1169_, lean_object* v_lowerBound_1170_, lean_object* v_upperBound_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1168_, v_t_1169_, v_lowerBound_1170_, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_upperBound_1171_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(lean_object* v_carrier_1175_, lean_object* v_range_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_carrier_1175_);
lean_ctor_set(v___x_1177_, 1, v_range_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v___f_1182_; 
v___f_1182_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0));
return v___f_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1183_, v_00_u03b2_1184_, v_inst_1185_);
lean_dec_ref(v_inst_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v_range_1189_; lean_object* v_treeMap_1190_; lean_object* v_lower_1191_; lean_object* v_upper_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1201_; 
v_range_1189_ = lean_ctor_get(v_x_1188_, 1);
lean_inc_ref(v_range_1189_);
v_treeMap_1190_ = lean_ctor_get(v_x_1188_, 0);
lean_inc(v_treeMap_1190_);
lean_dec_ref(v_x_1188_);
v_lower_1191_ = lean_ctor_get(v_range_1189_, 0);
v_upper_1192_ = lean_ctor_get(v_range_1189_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_range_1189_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1194_ = v_range_1189_;
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_upper_1192_);
lean_inc(v_lower_1191_);
lean_dec(v_range_1189_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1187_, v_treeMap_1190_, v_lower_1191_, v___x_1196_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_upper_1192_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1202_){
_start:
{
lean_object* v___f_1203_; 
v___f_1203_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1203_, 0, v_inst_1202_);
return v___f_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_inst_1206_){
_start:
{
lean_object* v___f_1207_; 
v___f_1207_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1207_, 0, v_inst_1206_);
return v___f_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(lean_object* v_carrier_1208_, lean_object* v_range_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_carrier_1208_);
lean_ctor_set(v___x_1210_, 1, v_range_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1212_, lean_object* v_inst_1213_){
_start:
{
lean_object* v___f_1214_; 
v___f_1214_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0));
return v___f_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1215_, v_inst_1216_);
lean_dec_ref(v_inst_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1218_, lean_object* v_x_1219_){
_start:
{
lean_object* v_range_1220_; lean_object* v_treeMap_1221_; lean_object* v_lower_1222_; lean_object* v_upper_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1232_; 
v_range_1220_ = lean_ctor_get(v_x_1219_, 1);
lean_inc_ref(v_range_1220_);
v_treeMap_1221_ = lean_ctor_get(v_x_1219_, 0);
lean_inc(v_treeMap_1221_);
lean_dec_ref(v_x_1219_);
v_lower_1222_ = lean_ctor_get(v_range_1220_, 0);
v_upper_1223_ = lean_ctor_get(v_range_1220_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_range_1220_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1225_ = v_range_1220_;
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_upper_1223_);
lean_inc(v_lower_1222_);
lean_dec(v_range_1220_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1227_ = lean_box(0);
v___x_1228_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1218_, v_treeMap_1221_, v_lower_1222_, v___x_1227_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1228_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_upper_1223_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1233_){
_start:
{
lean_object* v___f_1234_; 
v___f_1234_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1234_, 0, v_inst_1233_);
return v___f_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1235_, lean_object* v_inst_1236_){
_start:
{
lean_object* v___f_1237_; 
v___f_1237_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1237_, 0, v_inst_1236_);
return v___f_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(lean_object* v_carrier_1238_, lean_object* v_range_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_carrier_1238_);
lean_ctor_set(v___x_1240_, 1, v_range_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_inst_1244_){
_start:
{
lean_object* v___f_1245_; 
v___f_1245_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0));
return v___f_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_inst_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1246_, v_00_u03b2_1247_, v_inst_1248_);
lean_dec_ref(v_inst_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1250_, lean_object* v_x_1251_){
_start:
{
lean_object* v_range_1252_; lean_object* v_treeMap_1253_; lean_object* v_lower_1254_; lean_object* v_upper_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_range_1252_ = lean_ctor_get(v_x_1251_, 1);
lean_inc_ref(v_range_1252_);
v_treeMap_1253_ = lean_ctor_get(v_x_1251_, 0);
lean_inc(v_treeMap_1253_);
lean_dec_ref(v_x_1251_);
v_lower_1254_ = lean_ctor_get(v_range_1252_, 0);
v_upper_1255_ = lean_ctor_get(v_range_1252_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_range_1252_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v_range_1252_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_upper_1255_);
lean_inc(v_lower_1254_);
lean_dec(v_range_1252_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1250_, v_treeMap_1253_, v_lower_1254_, v___x_1259_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_upper_1255_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1265_){
_start:
{
lean_object* v___f_1266_; 
v___f_1266_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1266_, 0, v_inst_1265_);
return v___f_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03b2_1268_, lean_object* v_inst_1269_){
_start:
{
lean_object* v___f_1270_; 
v___f_1270_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1270_, 0, v_inst_1269_);
return v___f_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1271_, lean_object* v_t_1272_, lean_object* v_lowerBound_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1271_, v_t_1272_, v_lowerBound_1273_, v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_inst_1278_, lean_object* v_t_1279_, lean_object* v_lowerBound_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1278_, v_t_1279_, v_lowerBound_1280_, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(lean_object* v_carrier_1283_, lean_object* v_range_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_carrier_1283_);
lean_ctor_set(v___x_1285_, 1, v_range_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_inst_1289_){
_start:
{
lean_object* v___f_1290_; 
v___f_1290_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0));
return v___f_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_00_u03b2_1292_, lean_object* v_inst_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1291_, v_00_u03b2_1292_, v_inst_1293_);
lean_dec_ref(v_inst_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_treeMap_1297_; lean_object* v_range_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_treeMap_1297_ = lean_ctor_get(v_x_1296_, 0);
lean_inc(v_treeMap_1297_);
v_range_1298_ = lean_ctor_get(v_x_1296_, 1);
lean_inc(v_range_1298_);
lean_dec_ref(v_x_1296_);
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1295_, v_treeMap_1297_, v_range_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1301_){
_start:
{
lean_object* v___f_1302_; 
v___f_1302_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1302_, 0, v_inst_1301_);
return v___f_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_inst_1305_){
_start:
{
lean_object* v___f_1306_; 
v___f_1306_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1306_, 0, v_inst_1305_);
return v___f_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(lean_object* v_carrier_1307_, lean_object* v_range_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_carrier_1307_);
lean_ctor_set(v___x_1309_, 1, v_range_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1311_, lean_object* v_inst_1312_){
_start:
{
lean_object* v___f_1313_; 
v___f_1313_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0));
return v___f_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_inst_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1314_, v_inst_1315_);
lean_dec_ref(v_inst_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v_treeMap_1319_; lean_object* v_range_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_treeMap_1319_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_treeMap_1319_);
v_range_1320_ = lean_ctor_get(v_x_1318_, 1);
lean_inc(v_range_1320_);
lean_dec_ref(v_x_1318_);
v___x_1321_ = lean_box(0);
v___x_1322_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1317_, v_treeMap_1319_, v_range_1320_, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1323_){
_start:
{
lean_object* v___f_1324_; 
v___f_1324_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1324_, 0, v_inst_1323_);
return v___f_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1325_, lean_object* v_inst_1326_){
_start:
{
lean_object* v___f_1327_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1327_, 0, v_inst_1326_);
return v___f_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(lean_object* v_carrier_1328_, lean_object* v_range_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_carrier_1328_);
lean_ctor_set(v___x_1330_, 1, v_range_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_inst_1334_){
_start:
{
lean_object* v___f_1335_; 
v___f_1335_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0));
return v___f_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_00_u03b2_1337_, lean_object* v_inst_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1336_, v_00_u03b2_1337_, v_inst_1338_);
lean_dec_ref(v_inst_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v_treeMap_1342_; lean_object* v_range_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_treeMap_1342_ = lean_ctor_get(v_x_1341_, 0);
lean_inc(v_treeMap_1342_);
v_range_1343_ = lean_ctor_get(v_x_1341_, 1);
lean_inc(v_range_1343_);
lean_dec_ref(v_x_1341_);
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1340_, v_treeMap_1342_, v_range_1343_, v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1346_){
_start:
{
lean_object* v___f_1347_; 
v___f_1347_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1347_, 0, v_inst_1346_);
return v___f_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_inst_1350_){
_start:
{
lean_object* v___f_1351_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1351_, 0, v_inst_1350_);
return v___f_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1352_, lean_object* v_t_1353_, lean_object* v_lowerBound_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1352_, v_t_1353_, v_lowerBound_1354_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_inst_1359_, lean_object* v_t_1360_, lean_object* v_lowerBound_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1359_, v_t_1360_, v_lowerBound_1361_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(lean_object* v_carrier_1364_, lean_object* v_range_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_carrier_1364_);
lean_ctor_set(v___x_1366_, 1, v_range_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_inst_1370_){
_start:
{
lean_object* v___f_1371_; 
v___f_1371_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0));
return v___f_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_inst_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1372_, v_00_u03b2_1373_, v_inst_1374_);
lean_dec_ref(v_inst_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v_treeMap_1378_; lean_object* v_range_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_treeMap_1378_ = lean_ctor_get(v_x_1377_, 0);
lean_inc(v_treeMap_1378_);
v_range_1379_ = lean_ctor_get(v_x_1377_, 1);
lean_inc(v_range_1379_);
lean_dec_ref(v_x_1377_);
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1376_, v_treeMap_1378_, v_range_1379_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1382_){
_start:
{
lean_object* v___f_1383_; 
v___f_1383_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1383_, 0, v_inst_1382_);
return v___f_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_inst_1386_){
_start:
{
lean_object* v___f_1387_; 
v___f_1387_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1387_, 0, v_inst_1386_);
return v___f_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(lean_object* v_carrier_1388_, lean_object* v_range_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_carrier_1388_);
lean_ctor_set(v___x_1390_, 1, v_range_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1392_, lean_object* v_inst_1393_){
_start:
{
lean_object* v___f_1394_; 
v___f_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0));
return v___f_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1395_, lean_object* v_inst_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1395_, v_inst_1396_);
lean_dec_ref(v_inst_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_treeMap_1400_; lean_object* v_range_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_treeMap_1400_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_treeMap_1400_);
v_range_1401_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_range_1401_);
lean_dec_ref(v_x_1399_);
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1398_, v_treeMap_1400_, v_range_1401_, v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1404_){
_start:
{
lean_object* v___f_1405_; 
v___f_1405_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1405_, 0, v_inst_1404_);
return v___f_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1406_, lean_object* v_inst_1407_){
_start:
{
lean_object* v___f_1408_; 
v___f_1408_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1408_, 0, v_inst_1407_);
return v___f_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(lean_object* v_carrier_1409_, lean_object* v_range_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_carrier_1409_);
lean_ctor_set(v___x_1411_, 1, v_range_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1413_, lean_object* v_00_u03b2_1414_, lean_object* v_inst_1415_){
_start:
{
lean_object* v___f_1416_; 
v___f_1416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0));
return v___f_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_inst_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1417_, v_00_u03b2_1418_, v_inst_1419_);
lean_dec_ref(v_inst_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v_treeMap_1423_; lean_object* v_range_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_treeMap_1423_ = lean_ctor_get(v_x_1422_, 0);
lean_inc(v_treeMap_1423_);
v_range_1424_ = lean_ctor_get(v_x_1422_, 1);
lean_inc(v_range_1424_);
lean_dec_ref(v_x_1422_);
v___x_1425_ = lean_box(0);
v___x_1426_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1421_, v_treeMap_1423_, v_range_1424_, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1427_){
_start:
{
lean_object* v___f_1428_; 
v___f_1428_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1428_, 0, v_inst_1427_);
return v___f_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_inst_1431_){
_start:
{
lean_object* v___f_1432_; 
v___f_1432_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1432_, 0, v_inst_1431_);
return v___f_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1433_, v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1436_);
lean_dec(v_t_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_t_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_00_u03b2_1443_, lean_object* v_t_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1442_, v_00_u03b2_1443_, v_t_1444_);
lean_dec(v_t_1444_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(lean_object* v_carrier_1446_, lean_object* v_range_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_carrier_1446_);
lean_ctor_set(v___x_1448_, 1, v_range_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_){
_start:
{
lean_object* v___f_1452_; 
v___f_1452_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0));
return v___f_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(lean_object* v_x_1453_){
_start:
{
lean_object* v_treeMap_1454_; lean_object* v___x_1455_; 
v_treeMap_1454_ = lean_ctor_get(v_x_1453_, 0);
v___x_1455_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(v_x_1456_);
lean_dec_ref(v_x_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_){
_start:
{
lean_object* v___f_1461_; 
v___f_1461_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0));
return v___f_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(lean_object* v_carrier_1462_, lean_object* v_range_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_carrier_1462_);
lean_ctor_set(v___x_1464_, 1, v_range_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1466_){
_start:
{
lean_object* v___f_1467_; 
v___f_1467_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0));
return v___f_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(lean_object* v_x_1468_){
_start:
{
lean_object* v_treeMap_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_treeMap_1469_ = lean_ctor_get(v_x_1468_, 0);
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1469_, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(v_x_1472_);
lean_dec_ref(v_x_1472_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1475_){
_start:
{
lean_object* v___f_1476_; 
v___f_1476_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0));
return v___f_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(lean_object* v_carrier_1477_, lean_object* v_range_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_carrier_1477_);
lean_ctor_set(v___x_1479_, 1, v_range_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_){
_start:
{
lean_object* v___f_1483_; 
v___f_1483_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0));
return v___f_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(lean_object* v_x_1484_){
_start:
{
lean_object* v_treeMap_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_treeMap_1485_ = lean_ctor_get(v_x_1484_, 0);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1485_, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(v_x_1488_);
lean_dec_ref(v_x_1488_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1491_, lean_object* v_00_u03b2_1492_){
_start:
{
lean_object* v___f_1493_; 
v___f_1493_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0));
return v___f_1493_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_InternalLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_InternalLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Slice(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_InternalLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_InternalLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Zipper(builtin);
}
#ifdef __cplusplus
}
#endif
