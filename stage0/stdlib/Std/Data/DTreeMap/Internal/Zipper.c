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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Zipper_step___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_t_55_, 5);
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
lean_dec_ref_known(v_t_69_, 5);
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
uint8_t v_x_33__boxed_94_; lean_object* v_res_95_; 
v_x_33__boxed_94_ = lean_unbox(v_x_90_);
v_res_95_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_33__boxed_94_, v_h__1_91_, v_h__2_92_, v_h__3_93_);
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
uint8_t v_x_48__boxed_112_; lean_object* v_res_113_; 
v_x_48__boxed_112_ = lean_unbox(v_x_108_);
v_res_113_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_107_, v_x_48__boxed_112_, v_h__1_109_, v_h__2_110_, v_h__3_111_);
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
uint8_t v_x_24__boxed_124_; lean_object* v_res_125_; 
v_x_24__boxed_124_ = lean_unbox(v_x_121_);
v_res_125_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_124_, v_h__1_122_, v_h__2_123_);
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
uint8_t v_x_35__boxed_138_; lean_object* v_res_139_; 
v_x_35__boxed_138_ = lean_unbox(v_x_135_);
v_res_139_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(v_motive_134_, v_x_35__boxed_138_, v_h__1_136_, v_h__2_137_);
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
lean_dec_ref_known(v_t_153_, 4);
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
lean_inc_n(v_k_285_, 2);
v_v_286_ = lean_ctor_get(v_t_282_, 2);
lean_inc(v_v_286_);
v_l_287_ = lean_ctor_get(v_t_282_, 3);
lean_inc(v_l_287_);
v_r_288_ = lean_ctor_get(v_t_282_, 4);
lean_inc(v_r_288_);
lean_dec_ref_known(v_t_282_, 5);
lean_inc_ref(v_inst_281_);
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
lean_inc_n(v_k_306_, 2);
v_v_307_ = lean_ctor_get(v_t_303_, 2);
lean_inc(v_v_307_);
v_l_308_ = lean_ctor_get(v_t_303_, 3);
lean_inc(v_l_308_);
v_r_309_ = lean_ctor_get(v_t_303_, 4);
lean_inc(v_r_309_);
lean_dec_ref_known(v_t_303_, 5);
lean_inc_ref(v_inst_302_);
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
lean_dec_ref_known(v_x_322_, 5);
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
lean_dec_ref_known(v_x_336_, 5);
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
lean_dec_ref_known(v_x_347_, 4);
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
lean_dec_ref_known(v_x_360_, 4);
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
lean_dec_ref_known(v_x_370_, 5);
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
lean_dec_ref_known(v_x_384_, 5);
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
lean_dec_ref_known(v_x_395_, 4);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg(){
_start:
{
lean_object* v___f_410_; 
v___f_410_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object* v___dummy_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_413_, lean_object* v_00_u03b2_414_){
_start:
{
lean_object* v___f_415_; 
v___f_415_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg___boxed(lean_object* v___dummy_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_423_, lean_object* v_recur_424_, lean_object* v_it_425_, lean_object* v_____do__lift_426_){
_start:
{
if (lean_obj_tag(v_____do__lift_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
lean_dec(v_it_425_);
lean_dec(v_recur_424_);
v_a_427_ = lean_ctor_get(v_____do__lift_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v_____do__lift_426_, 1);
v___x_428_ = lean_apply_2(v_toPure_423_, lean_box(0), v_a_427_);
return v___x_428_;
}
else
{
lean_object* v_a_429_; lean_object* v___x_430_; 
lean_dec(v_toPure_423_);
v_a_429_ = lean_ctor_get(v_____do__lift_426_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v_____do__lift_426_, 1);
v___x_430_ = lean_apply_4(v_recur_424_, v_it_425_, v_a_429_, lean_box(0), lean_box(0));
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_431_, lean_object* v_recur_432_, lean_object* v___y_433_, lean_object* v_acc_434_, lean_object* v_toBind_435_, lean_object* v_s_436_){
_start:
{
switch(lean_obj_tag(v_s_436_))
{
case 0:
{
lean_object* v_it_437_; lean_object* v_out_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_it_437_ = lean_ctor_get(v_s_436_, 0);
lean_inc(v_it_437_);
v_out_438_ = lean_ctor_get(v_s_436_, 1);
lean_inc(v_out_438_);
lean_dec_ref_known(v_s_436_, 2);
v___f_439_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_439_, 0, v_toPure_431_);
lean_closure_set(v___f_439_, 1, v_recur_432_);
lean_closure_set(v___f_439_, 2, v_it_437_);
v___x_440_ = lean_apply_3(v___y_433_, v_out_438_, lean_box(0), v_acc_434_);
v___x_441_ = lean_apply_4(v_toBind_435_, lean_box(0), lean_box(0), v___x_440_, v___f_439_);
return v___x_441_;
}
case 1:
{
lean_object* v_it_442_; lean_object* v___x_443_; 
lean_dec(v_toBind_435_);
lean_dec(v___y_433_);
lean_dec(v_toPure_431_);
v_it_442_ = lean_ctor_get(v_s_436_, 0);
lean_inc(v_it_442_);
lean_dec_ref_known(v_s_436_, 1);
v___x_443_ = lean_apply_4(v_recur_432_, v_it_442_, v_acc_434_, lean_box(0), lean_box(0));
return v___x_443_;
}
default: 
{
lean_object* v___x_444_; 
lean_dec(v_toBind_435_);
lean_dec(v___y_433_);
lean_dec(v_recur_432_);
v___x_444_ = lean_apply_2(v_toPure_431_, lean_box(0), v_acc_434_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_445_, lean_object* v___y_446_, lean_object* v_toBind_447_, lean_object* v_lift_448_, lean_object* v_it_449_, lean_object* v_acc_450_, lean_object* v_hP_451_, lean_object* v_recur_452_){
_start:
{
lean_object* v___f_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___f_453_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_453_, 0, v_toPure_445_);
lean_closure_set(v___f_453_, 1, v_recur_452_);
lean_closure_set(v___f_453_, 2, v___y_446_);
lean_closure_set(v___f_453_, 3, v_acc_450_);
lean_closure_set(v___f_453_, 4, v_toBind_447_);
v___x_454_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_it_449_);
v___x_455_ = lean_apply_4(v_lift_448_, lean_box(0), lean_box(0), v___f_453_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_456_, lean_object* v_lift_457_, lean_object* v_00_u03b3_458_, lean_object* v_Pl_459_, lean_object* v_it_460_, lean_object* v_init_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_toApplicative_463_; lean_object* v_toBind_464_; lean_object* v_toPure_465_; lean_object* v___f_466_; lean_object* v___x_467_; 
v_toApplicative_463_ = lean_ctor_get(v_inst_456_, 0);
lean_inc_ref(v_toApplicative_463_);
v_toBind_464_ = lean_ctor_get(v_inst_456_, 1);
lean_inc(v_toBind_464_);
lean_dec_ref(v_inst_456_);
v_toPure_465_ = lean_ctor_get(v_toApplicative_463_, 1);
lean_inc(v_toPure_465_);
lean_dec_ref(v_toApplicative_463_);
v___f_466_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_466_, 0, v_toPure_465_);
lean_closure_set(v___f_466_, 1, v___y_462_);
lean_closure_set(v___f_466_, 2, v_toBind_464_);
lean_closure_set(v___f_466_, 3, v_lift_457_);
v___x_467_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_466_, v_it_460_, v_init_461_, lean_box(0));
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object* v_inst_468_){
_start:
{
lean_object* v___f_469_; 
v___f_469_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_469_, 0, v_inst_468_);
return v___f_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_m_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v___f_474_; 
v___f_474_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_474_, 0, v_inst_473_);
return v___f_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_475_){
_start:
{
lean_inc(v_t_475_);
return v_t_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_476_);
lean_dec(v_t_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_t_480_){
_start:
{
lean_inc(v_t_480_);
return v_t_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_t_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_481_, v_00_u03b2_482_, v_t_483_);
lean_dec(v_t_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_485_, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_488_);
lean_dec(v_t_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_t_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_t_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_494_, v_00_u03b2_495_, v_t_496_);
lean_dec(v_t_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(lean_object* v_x_498_){
_start:
{
lean_inc(v_x_498_);
return v_x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed(lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(v_x_499_);
lean_dec(v_x_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg(){
_start:
{
lean_object* v___f_503_; 
v___f_503_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___boxed(lean_object* v___dummy_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_){
_start:
{
lean_object* v___f_508_; 
v___f_508_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_509_, lean_object* v_h__1_510_, lean_object* v_h__2_511_, lean_object* v_h__3_512_){
_start:
{
switch(lean_obj_tag(v_x_509_))
{
case 0:
{
lean_object* v_it_513_; lean_object* v_out_514_; lean_object* v___x_515_; 
lean_dec(v_h__3_512_);
lean_dec(v_h__2_511_);
v_it_513_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_it_513_);
v_out_514_ = lean_ctor_get(v_x_509_, 1);
lean_inc(v_out_514_);
lean_dec_ref_known(v_x_509_, 2);
v___x_515_ = lean_apply_2(v_h__1_510_, v_it_513_, v_out_514_);
return v___x_515_;
}
case 1:
{
lean_object* v_it_516_; lean_object* v___x_517_; 
lean_dec(v_h__3_512_);
lean_dec(v_h__1_510_);
v_it_516_ = lean_ctor_get(v_x_509_, 0);
lean_inc(v_it_516_);
lean_dec_ref_known(v_x_509_, 1);
v___x_517_ = lean_apply_1(v_h__2_511_, v_it_516_);
return v___x_517_;
}
default: 
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_h__2_511_);
lean_dec(v_h__1_510_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v_h__3_512_, v___x_518_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_motive_523_, lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_){
_start:
{
switch(lean_obj_tag(v_x_524_))
{
case 0:
{
lean_object* v_it_528_; lean_object* v_out_529_; lean_object* v___x_530_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__2_526_);
v_it_528_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_it_528_);
v_out_529_ = lean_ctor_get(v_x_524_, 1);
lean_inc(v_out_529_);
lean_dec_ref_known(v_x_524_, 2);
v___x_530_ = lean_apply_2(v_h__1_525_, v_it_528_, v_out_529_);
return v___x_530_;
}
case 1:
{
lean_object* v_it_531_; lean_object* v___x_532_; 
lean_dec(v_h__3_527_);
lean_dec(v_h__1_525_);
v_it_531_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_it_531_);
lean_dec_ref_known(v_x_524_, 1);
v___x_532_ = lean_apply_1(v_h__2_526_, v_it_531_);
return v___x_532_;
}
default: 
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_h__2_526_);
lean_dec(v_h__1_525_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_apply_1(v_h__3_527_, v___x_533_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_iter_537_; 
v_iter_537_ = lean_ctor_get(v_x_536_, 0);
lean_inc(v_iter_537_);
if (lean_obj_tag(v_iter_537_) == 0)
{
lean_object* v___x_538_; 
lean_dec_ref(v_x_536_);
lean_dec_ref(v_inst_535_);
v___x_538_ = lean_box(2);
return v___x_538_;
}
else
{
lean_object* v_upper_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_556_; 
v_upper_539_ = lean_ctor_get(v_x_536_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_x_536_, 0);
lean_dec(v_unused_557_);
v___x_541_ = v_x_536_;
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_upper_539_);
lean_dec(v_x_536_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_k_543_; lean_object* v_v_544_; lean_object* v_tree_545_; lean_object* v_next_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_k_543_ = lean_ctor_get(v_iter_537_, 0);
lean_inc_n(v_k_543_, 2);
v_v_544_ = lean_ctor_get(v_iter_537_, 1);
lean_inc(v_v_544_);
v_tree_545_ = lean_ctor_get(v_iter_537_, 2);
lean_inc(v_tree_545_);
v_next_546_ = lean_ctor_get(v_iter_537_, 3);
lean_inc(v_next_546_);
lean_dec_ref_known(v_iter_537_, 4);
lean_inc(v_upper_539_);
v___x_547_ = lean_apply_2(v_inst_535_, v_k_543_, v_upper_539_);
v___x_548_ = lean_unbox(v___x_547_);
if (v___x_548_ == 2)
{
lean_object* v___x_549_; 
lean_dec(v_next_546_);
lean_dec(v_tree_545_);
lean_dec(v_v_544_);
lean_dec(v_k_543_);
lean_del_object(v___x_541_);
lean_dec(v_upper_539_);
v___x_549_ = lean_box(2);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_545_, v_next_546_);
lean_dec(v_tree_545_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_550_);
v___x_552_ = v___x_541_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_upper_539_);
v___x_552_ = v_reuseFailAlloc_555_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_k_543_);
lean_ctor_set(v___x_553_, 1, v_v_544_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_inst_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_560_, v_x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_563_, lean_object* v_it_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_563_, v_it_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_566_){
_start:
{
lean_object* v___f_567_; 
v___f_567_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_567_, 0, v_inst_566_);
return v___f_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_568_, lean_object* v_00_u03b2_569_, lean_object* v_inst_570_){
_start:
{
lean_object* v___f_571_; 
v___f_571_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_571_, 0, v_inst_570_);
return v___f_571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_){
_start:
{
lean_object* v_iter_575_; 
v_iter_575_ = lean_ctor_get(v_x_572_, 0);
if (lean_obj_tag(v_iter_575_) == 0)
{
lean_object* v_upper_576_; lean_object* v___x_577_; 
lean_dec(v_h__2_574_);
v_upper_576_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_upper_576_);
lean_dec_ref(v_x_572_);
v___x_577_ = lean_apply_1(v_h__1_573_, v_upper_576_);
return v___x_577_;
}
else
{
lean_object* v_upper_578_; lean_object* v_k_579_; lean_object* v_v_580_; lean_object* v_tree_581_; lean_object* v_next_582_; lean_object* v___x_583_; 
lean_inc_ref(v_iter_575_);
lean_dec(v_h__1_573_);
v_upper_578_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_upper_578_);
lean_dec_ref(v_x_572_);
v_k_579_ = lean_ctor_get(v_iter_575_, 0);
lean_inc(v_k_579_);
v_v_580_ = lean_ctor_get(v_iter_575_, 1);
lean_inc(v_v_580_);
v_tree_581_ = lean_ctor_get(v_iter_575_, 2);
lean_inc(v_tree_581_);
v_next_582_ = lean_ctor_get(v_iter_575_, 3);
lean_inc(v_next_582_);
lean_dec_ref_known(v_iter_575_, 4);
v___x_583_ = lean_apply_5(v_h__2_574_, v_k_579_, v_v_580_, v_tree_581_, v_next_582_, v_upper_578_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_inst_586_, lean_object* v_motive_587_, lean_object* v_x_588_, lean_object* v_h__1_589_, lean_object* v_h__2_590_){
_start:
{
lean_object* v_iter_591_; 
v_iter_591_ = lean_ctor_get(v_x_588_, 0);
if (lean_obj_tag(v_iter_591_) == 0)
{
lean_object* v_upper_592_; lean_object* v___x_593_; 
lean_dec(v_h__2_590_);
v_upper_592_ = lean_ctor_get(v_x_588_, 1);
lean_inc(v_upper_592_);
lean_dec_ref(v_x_588_);
v___x_593_ = lean_apply_1(v_h__1_589_, v_upper_592_);
return v___x_593_;
}
else
{
lean_object* v_upper_594_; lean_object* v_k_595_; lean_object* v_v_596_; lean_object* v_tree_597_; lean_object* v_next_598_; lean_object* v___x_599_; 
lean_inc_ref(v_iter_591_);
lean_dec(v_h__1_589_);
v_upper_594_ = lean_ctor_get(v_x_588_, 1);
lean_inc(v_upper_594_);
lean_dec_ref(v_x_588_);
v_k_595_ = lean_ctor_get(v_iter_591_, 0);
lean_inc(v_k_595_);
v_v_596_ = lean_ctor_get(v_iter_591_, 1);
lean_inc(v_v_596_);
v_tree_597_ = lean_ctor_get(v_iter_591_, 2);
lean_inc(v_tree_597_);
v_next_598_ = lean_ctor_get(v_iter_591_, 3);
lean_inc(v_next_598_);
lean_dec_ref_known(v_iter_591_, 4);
v___x_599_ = lean_apply_5(v_h__2_590_, v_k_595_, v_v_596_, v_tree_597_, v_next_598_, v_upper_594_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_inst_602_, lean_object* v_motive_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_600_, v_00_u03b2_601_, v_inst_602_, v_motive_603_, v_x_604_, v_h__1_605_, v_h__2_606_);
lean_dec_ref(v_inst_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg___boxed(lean_object* v___dummy_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_inst_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_box(0);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b2_617_, lean_object* v_inst_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_616_, v_00_u03b2_617_, v_inst_618_);
lean_dec_ref(v_inst_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_620_, lean_object* v_recur_621_, lean_object* v_it_622_, lean_object* v_____do__lift_623_){
_start:
{
if (lean_obj_tag(v_____do__lift_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; 
lean_dec_ref(v_it_622_);
lean_dec(v_recur_621_);
v_a_624_ = lean_ctor_get(v_____do__lift_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v_____do__lift_623_, 1);
v___x_625_ = lean_apply_2(v_toPure_620_, lean_box(0), v_a_624_);
return v___x_625_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_627_; 
lean_dec(v_toPure_620_);
v_a_626_ = lean_ctor_get(v_____do__lift_623_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v_____do__lift_623_, 1);
v___x_627_ = lean_apply_4(v_recur_621_, v_it_622_, v_a_626_, lean_box(0), lean_box(0));
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_628_, lean_object* v_recur_629_, lean_object* v___y_630_, lean_object* v_acc_631_, lean_object* v_toBind_632_, lean_object* v_s_633_){
_start:
{
switch(lean_obj_tag(v_s_633_))
{
case 0:
{
lean_object* v_it_634_; lean_object* v_out_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_it_634_ = lean_ctor_get(v_s_633_, 0);
lean_inc(v_it_634_);
v_out_635_ = lean_ctor_get(v_s_633_, 1);
lean_inc(v_out_635_);
lean_dec_ref_known(v_s_633_, 2);
v___f_636_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_636_, 0, v_toPure_628_);
lean_closure_set(v___f_636_, 1, v_recur_629_);
lean_closure_set(v___f_636_, 2, v_it_634_);
v___x_637_ = lean_apply_3(v___y_630_, v_out_635_, lean_box(0), v_acc_631_);
v___x_638_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_637_, v___f_636_);
return v___x_638_;
}
case 1:
{
lean_object* v_it_639_; lean_object* v___x_640_; 
lean_dec(v_toBind_632_);
lean_dec(v___y_630_);
lean_dec(v_toPure_628_);
v_it_639_ = lean_ctor_get(v_s_633_, 0);
lean_inc(v_it_639_);
lean_dec_ref_known(v_s_633_, 1);
v___x_640_ = lean_apply_4(v_recur_629_, v_it_639_, v_acc_631_, lean_box(0), lean_box(0));
return v___x_640_;
}
default: 
{
lean_object* v___x_641_; 
lean_dec(v_toBind_632_);
lean_dec(v___y_630_);
lean_dec(v_recur_629_);
v___x_641_ = lean_apply_2(v_toPure_628_, lean_box(0), v_acc_631_);
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_642_, lean_object* v___y_643_, lean_object* v_toBind_644_, lean_object* v_inst_645_, lean_object* v_lift_646_, lean_object* v_it_647_, lean_object* v_acc_648_, lean_object* v_hP_649_, lean_object* v_recur_650_){
_start:
{
lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___f_651_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_651_, 0, v_toPure_642_);
lean_closure_set(v___f_651_, 1, v_recur_650_);
lean_closure_set(v___f_651_, 2, v___y_643_);
lean_closure_set(v___f_651_, 3, v_acc_648_);
lean_closure_set(v___f_651_, 4, v_toBind_644_);
v___x_652_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_645_, v_it_647_);
v___x_653_ = lean_apply_4(v_lift_646_, lean_box(0), lean_box(0), v___f_651_, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_lift_656_, lean_object* v_00_u03b3_657_, lean_object* v_Pl_658_, lean_object* v_it_659_, lean_object* v_init_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_toApplicative_662_; lean_object* v_toBind_663_; lean_object* v_toPure_664_; lean_object* v___f_665_; lean_object* v___x_666_; 
v_toApplicative_662_ = lean_ctor_get(v_inst_654_, 0);
lean_inc_ref(v_toApplicative_662_);
v_toBind_663_ = lean_ctor_get(v_inst_654_, 1);
lean_inc(v_toBind_663_);
lean_dec_ref(v_inst_654_);
v_toPure_664_ = lean_ctor_get(v_toApplicative_662_, 1);
lean_inc(v_toPure_664_);
lean_dec_ref(v_toApplicative_662_);
v___f_665_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_665_, 0, v_toPure_664_);
lean_closure_set(v___f_665_, 1, v___y_661_);
lean_closure_set(v___f_665_, 2, v_toBind_663_);
lean_closure_set(v___f_665_, 3, v_inst_655_);
lean_closure_set(v___f_665_, 4, v_lift_656_);
v___x_666_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_665_, v_it_659_, v_init_660_, lean_box(0));
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_){
_start:
{
lean_object* v___f_669_; 
v___f_669_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_669_, 0, v_inst_668_);
lean_closure_set(v___f_669_, 1, v_inst_667_);
return v___f_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_inst_672_, lean_object* v_m_673_, lean_object* v_inst_674_){
_start:
{
lean_object* v___f_675_; 
v___f_675_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_675_, 0, v_inst_674_);
lean_closure_set(v___f_675_, 1, v_inst_672_);
return v___f_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_iter_678_; 
v_iter_678_ = lean_ctor_get(v_x_677_, 0);
lean_inc(v_iter_678_);
if (lean_obj_tag(v_iter_678_) == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v_x_677_);
lean_dec_ref(v_inst_676_);
v___x_679_ = lean_box(2);
return v___x_679_;
}
else
{
lean_object* v_upper_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_697_; 
v_upper_680_ = lean_ctor_get(v_x_677_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_x_677_, 0);
lean_dec(v_unused_698_);
v___x_682_ = v_x_677_;
v_isShared_683_ = v_isSharedCheck_697_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_upper_680_);
lean_dec(v_x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_697_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_tree_686_; lean_object* v_next_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_k_684_ = lean_ctor_get(v_iter_678_, 0);
lean_inc_n(v_k_684_, 2);
v_v_685_ = lean_ctor_get(v_iter_678_, 1);
lean_inc(v_v_685_);
v_tree_686_ = lean_ctor_get(v_iter_678_, 2);
lean_inc(v_tree_686_);
v_next_687_ = lean_ctor_get(v_iter_678_, 3);
lean_inc(v_next_687_);
lean_dec_ref_known(v_iter_678_, 4);
lean_inc(v_upper_680_);
v___x_688_ = lean_apply_2(v_inst_676_, v_k_684_, v_upper_680_);
v___x_689_ = lean_unbox(v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_686_, v_next_687_);
lean_dec(v_tree_686_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_690_);
v___x_692_ = v___x_682_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_upper_680_);
v___x_692_ = v_reuseFailAlloc_695_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_k_684_);
lean_ctor_set(v___x_693_, 1, v_v_685_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
return v___x_694_;
}
}
else
{
lean_object* v___x_696_; 
lean_dec(v_next_687_);
lean_dec(v_tree_686_);
lean_dec(v_v_685_);
lean_dec(v_k_684_);
lean_del_object(v___x_682_);
lean_dec(v_upper_680_);
v___x_696_ = lean_box(2);
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_, lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_701_, v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_704_, lean_object* v_it_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_704_, v_it_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_707_){
_start:
{
lean_object* v___f_708_; 
v___f_708_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_708_, 0, v_inst_707_);
return v___f_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_inst_711_){
_start:
{
lean_object* v___f_712_; 
v___f_712_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_712_, 0, v_inst_711_);
return v___f_712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_713_, lean_object* v_h__1_714_, lean_object* v_h__2_715_){
_start:
{
lean_object* v_iter_716_; 
v_iter_716_ = lean_ctor_get(v_x_713_, 0);
if (lean_obj_tag(v_iter_716_) == 0)
{
lean_object* v_upper_717_; lean_object* v___x_718_; 
lean_dec(v_h__2_715_);
v_upper_717_ = lean_ctor_get(v_x_713_, 1);
lean_inc(v_upper_717_);
lean_dec_ref(v_x_713_);
v___x_718_ = lean_apply_1(v_h__1_714_, v_upper_717_);
return v___x_718_;
}
else
{
lean_object* v_upper_719_; lean_object* v_k_720_; lean_object* v_v_721_; lean_object* v_tree_722_; lean_object* v_next_723_; lean_object* v___x_724_; 
lean_inc_ref(v_iter_716_);
lean_dec(v_h__1_714_);
v_upper_719_ = lean_ctor_get(v_x_713_, 1);
lean_inc(v_upper_719_);
lean_dec_ref(v_x_713_);
v_k_720_ = lean_ctor_get(v_iter_716_, 0);
lean_inc(v_k_720_);
v_v_721_ = lean_ctor_get(v_iter_716_, 1);
lean_inc(v_v_721_);
v_tree_722_ = lean_ctor_get(v_iter_716_, 2);
lean_inc(v_tree_722_);
v_next_723_ = lean_ctor_get(v_iter_716_, 3);
lean_inc(v_next_723_);
lean_dec_ref_known(v_iter_716_, 4);
v___x_724_ = lean_apply_5(v_h__2_715_, v_k_720_, v_v_721_, v_tree_722_, v_next_723_, v_upper_719_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_inst_727_, lean_object* v_motive_728_, lean_object* v_x_729_, lean_object* v_h__1_730_, lean_object* v_h__2_731_){
_start:
{
lean_object* v_iter_732_; 
v_iter_732_ = lean_ctor_get(v_x_729_, 0);
if (lean_obj_tag(v_iter_732_) == 0)
{
lean_object* v_upper_733_; lean_object* v___x_734_; 
lean_dec(v_h__2_731_);
v_upper_733_ = lean_ctor_get(v_x_729_, 1);
lean_inc(v_upper_733_);
lean_dec_ref(v_x_729_);
v___x_734_ = lean_apply_1(v_h__1_730_, v_upper_733_);
return v___x_734_;
}
else
{
lean_object* v_upper_735_; lean_object* v_k_736_; lean_object* v_v_737_; lean_object* v_tree_738_; lean_object* v_next_739_; lean_object* v___x_740_; 
lean_inc_ref(v_iter_732_);
lean_dec(v_h__1_730_);
v_upper_735_ = lean_ctor_get(v_x_729_, 1);
lean_inc(v_upper_735_);
lean_dec_ref(v_x_729_);
v_k_736_ = lean_ctor_get(v_iter_732_, 0);
lean_inc(v_k_736_);
v_v_737_ = lean_ctor_get(v_iter_732_, 1);
lean_inc(v_v_737_);
v_tree_738_ = lean_ctor_get(v_iter_732_, 2);
lean_inc(v_tree_738_);
v_next_739_ = lean_ctor_get(v_iter_732_, 3);
lean_inc(v_next_739_);
lean_dec_ref_known(v_iter_732_, 4);
v___x_740_ = lean_apply_5(v_h__2_731_, v_k_736_, v_v_737_, v_tree_738_, v_next_739_, v_upper_735_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_inst_743_, lean_object* v_motive_744_, lean_object* v_x_745_, lean_object* v_h__1_746_, lean_object* v_h__2_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_741_, v_00_u03b2_742_, v_inst_743_, v_motive_744_, v_x_745_, v_h__1_746_, v_h__2_747_);
lean_dec_ref(v_inst_743_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_box(0);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_753_, lean_object* v_00_u03b2_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_box(0);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_757_, lean_object* v_00_u03b2_758_, lean_object* v_inst_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_757_, v_00_u03b2_758_, v_inst_759_);
lean_dec_ref(v_inst_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_761_, lean_object* v_recur_762_, lean_object* v_it_763_, lean_object* v_____do__lift_764_){
_start:
{
if (lean_obj_tag(v_____do__lift_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
lean_dec_ref(v_it_763_);
lean_dec(v_recur_762_);
v_a_765_ = lean_ctor_get(v_____do__lift_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v_____do__lift_764_, 1);
v___x_766_ = lean_apply_2(v_toPure_761_, lean_box(0), v_a_765_);
return v___x_766_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_768_; 
lean_dec(v_toPure_761_);
v_a_767_ = lean_ctor_get(v_____do__lift_764_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v_____do__lift_764_, 1);
v___x_768_ = lean_apply_4(v_recur_762_, v_it_763_, v_a_767_, lean_box(0), lean_box(0));
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_769_, lean_object* v_recur_770_, lean_object* v___y_771_, lean_object* v_acc_772_, lean_object* v_toBind_773_, lean_object* v_s_774_){
_start:
{
switch(lean_obj_tag(v_s_774_))
{
case 0:
{
lean_object* v_it_775_; lean_object* v_out_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_it_775_ = lean_ctor_get(v_s_774_, 0);
lean_inc(v_it_775_);
v_out_776_ = lean_ctor_get(v_s_774_, 1);
lean_inc(v_out_776_);
lean_dec_ref_known(v_s_774_, 2);
v___f_777_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_777_, 0, v_toPure_769_);
lean_closure_set(v___f_777_, 1, v_recur_770_);
lean_closure_set(v___f_777_, 2, v_it_775_);
v___x_778_ = lean_apply_3(v___y_771_, v_out_776_, lean_box(0), v_acc_772_);
v___x_779_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_778_, v___f_777_);
return v___x_779_;
}
case 1:
{
lean_object* v_it_780_; lean_object* v___x_781_; 
lean_dec(v_toBind_773_);
lean_dec(v___y_771_);
lean_dec(v_toPure_769_);
v_it_780_ = lean_ctor_get(v_s_774_, 0);
lean_inc(v_it_780_);
lean_dec_ref_known(v_s_774_, 1);
v___x_781_ = lean_apply_4(v_recur_770_, v_it_780_, v_acc_772_, lean_box(0), lean_box(0));
return v___x_781_;
}
default: 
{
lean_object* v___x_782_; 
lean_dec(v_toBind_773_);
lean_dec(v___y_771_);
lean_dec(v_recur_770_);
v___x_782_ = lean_apply_2(v_toPure_769_, lean_box(0), v_acc_772_);
return v___x_782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_783_, lean_object* v___y_784_, lean_object* v_toBind_785_, lean_object* v_inst_786_, lean_object* v_lift_787_, lean_object* v_it_788_, lean_object* v_acc_789_, lean_object* v_hP_790_, lean_object* v_recur_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___f_792_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_792_, 0, v_toPure_783_);
lean_closure_set(v___f_792_, 1, v_recur_791_);
lean_closure_set(v___f_792_, 2, v___y_784_);
lean_closure_set(v___f_792_, 3, v_acc_789_);
lean_closure_set(v___f_792_, 4, v_toBind_785_);
v___x_793_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_786_, v_it_788_);
v___x_794_ = lean_apply_4(v_lift_787_, lean_box(0), lean_box(0), v___f_792_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_lift_797_, lean_object* v_00_u03b3_798_, lean_object* v_Pl_799_, lean_object* v_it_800_, lean_object* v_init_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_toApplicative_803_; lean_object* v_toBind_804_; lean_object* v_toPure_805_; lean_object* v___f_806_; lean_object* v___x_807_; 
v_toApplicative_803_ = lean_ctor_get(v_inst_795_, 0);
lean_inc_ref(v_toApplicative_803_);
v_toBind_804_ = lean_ctor_get(v_inst_795_, 1);
lean_inc(v_toBind_804_);
lean_dec_ref(v_inst_795_);
v_toPure_805_ = lean_ctor_get(v_toApplicative_803_, 1);
lean_inc(v_toPure_805_);
lean_dec_ref(v_toApplicative_803_);
v___f_806_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_806_, 0, v_toPure_805_);
lean_closure_set(v___f_806_, 1, v___y_802_);
lean_closure_set(v___f_806_, 2, v_toBind_804_);
lean_closure_set(v___f_806_, 3, v_inst_796_);
lean_closure_set(v___f_806_, 4, v_lift_797_);
v___x_807_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_806_, v_it_800_, v_init_801_, lean_box(0));
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object* v_inst_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v___f_810_; 
v___f_810_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_810_, 0, v_inst_809_);
lean_closure_set(v___f_810_, 1, v_inst_808_);
return v___f_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_inst_813_, lean_object* v_m_814_, lean_object* v_inst_815_){
_start:
{
lean_object* v___f_816_; 
v___f_816_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_816_, 0, v_inst_815_);
lean_closure_set(v___f_816_, 1, v_inst_813_);
return v___f_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_817_, lean_object* v_range_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_carrier_817_);
lean_ctor_set(v___x_819_, 1, v_range_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_822_; 
v___f_822_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v___f_828_; 
v___f_828_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_inst_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_829_, v_00_u03b2_830_, v_inst_831_);
lean_dec_ref(v_inst_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_833_){
_start:
{
lean_object* v_treeMap_834_; lean_object* v_range_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_844_; 
v_treeMap_834_ = lean_ctor_get(v_x_833_, 0);
v_range_835_ = lean_ctor_get(v_x_833_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_833_);
if (v_isSharedCheck_844_ == 0)
{
v___x_837_ = v_x_833_;
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_range_835_);
lean_inc(v_treeMap_834_);
lean_dec(v_x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_839_ = lean_box(0);
v___x_840_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_834_, v___x_839_);
lean_dec(v_treeMap_834_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_840_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_range_835_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_847_; 
v___f_847_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___f_853_; 
v___f_853_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_inst_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_854_, v_00_u03b2_855_, v_inst_856_);
lean_dec_ref(v_inst_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0(lean_object* v_carrier_858_, lean_object* v_range_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_carrier_858_);
lean_ctor_set(v___x_860_, 1, v_range_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg(){
_start:
{
lean_object* v___f_863_; 
v___f_863_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___boxed(lean_object* v___dummy_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_866_, lean_object* v_inst_867_){
_start:
{
lean_object* v___f_868_; 
v___f_868_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_869_, v_inst_870_);
lean_dec_ref(v_inst_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_872_){
_start:
{
lean_object* v_treeMap_873_; lean_object* v_range_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_883_; 
v_treeMap_873_ = lean_ctor_get(v_x_872_, 0);
v_range_874_ = lean_ctor_get(v_x_872_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_883_ == 0)
{
v___x_876_ = v_x_872_;
v_isShared_877_ = v_isSharedCheck_883_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_range_874_);
lean_inc(v_treeMap_873_);
lean_dec(v_x_872_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_883_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_878_ = lean_box(0);
v___x_879_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_873_, v___x_878_);
lean_dec(v_treeMap_873_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_879_);
v___x_881_ = v___x_876_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_range_874_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_886_; 
v___f_886_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_889_, lean_object* v_inst_890_){
_start:
{
lean_object* v___f_891_; 
v___f_891_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_892_, lean_object* v_inst_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_892_, v_inst_893_);
lean_dec_ref(v_inst_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_895_, lean_object* v_range_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_carrier_895_);
lean_ctor_set(v___x_897_, 1, v_range_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_900_; 
v___f_900_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_inst_905_){
_start:
{
lean_object* v___f_906_; 
v___f_906_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_inst_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_907_, v_00_u03b2_908_, v_inst_909_);
lean_dec_ref(v_inst_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_911_){
_start:
{
lean_object* v_treeMap_912_; lean_object* v_range_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_922_; 
v_treeMap_912_ = lean_ctor_get(v_x_911_, 0);
v_range_913_ = lean_ctor_get(v_x_911_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_915_ = v_x_911_;
v_isShared_916_ = v_isSharedCheck_922_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_range_913_);
lean_inc(v_treeMap_912_);
lean_dec(v_x_911_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_922_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_917_ = lean_box(0);
v___x_918_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_912_, v___x_917_);
lean_dec(v_treeMap_912_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_920_ = v___x_915_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_range_913_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_925_; 
v___f_925_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_inst_930_){
_start:
{
lean_object* v___f_931_; 
v___f_931_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b2_933_, lean_object* v_inst_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_932_, v_00_u03b2_933_, v_inst_934_);
lean_dec_ref(v_inst_934_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_936_, lean_object* v_range_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_carrier_936_);
lean_ctor_set(v___x_938_, 1, v_range_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_941_; 
v___f_941_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_inst_946_){
_start:
{
lean_object* v___f_947_; 
v___f_947_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_948_, v_00_u03b2_949_, v_inst_950_);
lean_dec_ref(v_inst_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_952_){
_start:
{
lean_object* v_treeMap_953_; lean_object* v_range_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_963_; 
v_treeMap_953_ = lean_ctor_get(v_x_952_, 0);
v_range_954_ = lean_ctor_get(v_x_952_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_952_);
if (v_isSharedCheck_963_ == 0)
{
v___x_956_ = v_x_952_;
v_isShared_957_ = v_isSharedCheck_963_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_range_954_);
lean_inc(v_treeMap_953_);
lean_dec(v_x_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_963_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_958_ = lean_box(0);
v___x_959_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_953_, v___x_958_);
lean_dec(v_treeMap_953_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_range_954_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_966_; 
v___f_966_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_inst_971_){
_start:
{
lean_object* v___f_972_; 
v___f_972_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_973_, lean_object* v_00_u03b2_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_973_, v_00_u03b2_974_, v_inst_975_);
lean_dec_ref(v_inst_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0(lean_object* v_carrier_977_, lean_object* v_range_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_carrier_977_);
lean_ctor_set(v___x_979_, 1, v_range_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg(){
_start:
{
lean_object* v___f_982_; 
v___f_982_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___boxed(lean_object* v___dummy_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_985_, lean_object* v_inst_986_){
_start:
{
lean_object* v___f_987_; 
v___f_987_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_988_, v_inst_989_);
lean_dec_ref(v_inst_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_991_){
_start:
{
lean_object* v_treeMap_992_; lean_object* v_range_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
v_treeMap_992_ = lean_ctor_get(v_x_991_, 0);
v_range_993_ = lean_ctor_get(v_x_991_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_991_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v_x_991_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_range_993_);
lean_inc(v_treeMap_992_);
lean_dec(v_x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = lean_box(0);
v___x_998_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_992_, v___x_997_);
lean_dec(v_treeMap_992_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_range_993_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1005_; 
v___f_1005_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_1008_, lean_object* v_inst_1009_){
_start:
{
lean_object* v___f_1010_; 
v___f_1010_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_inst_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_1011_, v_inst_1012_);
lean_dec_ref(v_inst_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_1014_, lean_object* v_range_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v_carrier_1014_);
lean_ctor_set(v___x_1016_, 1, v_range_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_1019_; 
v___f_1019_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_inst_1024_){
_start:
{
lean_object* v___f_1025_; 
v___f_1025_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03b2_1027_, lean_object* v_inst_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_1026_, v_00_u03b2_1027_, v_inst_1028_);
lean_dec_ref(v_inst_1028_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_1030_){
_start:
{
lean_object* v_treeMap_1031_; lean_object* v_range_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1041_; 
v_treeMap_1031_ = lean_ctor_get(v_x_1030_, 0);
v_range_1032_ = lean_ctor_get(v_x_1030_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1034_ = v_x_1030_;
v_isShared_1035_ = v_isSharedCheck_1041_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_range_1032_);
lean_inc(v_treeMap_1031_);
lean_dec(v_x_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1041_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1031_, v___x_1036_);
lean_dec(v_treeMap_1031_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1039_ = v___x_1034_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_range_1032_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1044_; 
v___f_1044_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_inst_1049_){
_start:
{
lean_object* v___f_1050_; 
v___f_1050_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_1051_, v_00_u03b2_1052_, v_inst_1053_);
lean_dec_ref(v_inst_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_1055_, lean_object* v_t_1056_, lean_object* v_lowerBound_1057_, lean_object* v_upperBound_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1055_, v_t_1056_, v_lowerBound_1057_, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_upperBound_1058_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_inst_1064_, lean_object* v_t_1065_, lean_object* v_lowerBound_1066_, lean_object* v_upperBound_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1064_, v_t_1065_, v_lowerBound_1066_, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_upperBound_1067_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1071_, lean_object* v_range_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_carrier_1071_);
lean_ctor_set(v___x_1073_, 1, v_range_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1076_; 
v___f_1076_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_inst_1081_){
_start:
{
lean_object* v___f_1082_; 
v___f_1082_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_inst_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_1083_, v_00_u03b2_1084_, v_inst_1085_);
lean_dec_ref(v_inst_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v_range_1089_; lean_object* v_treeMap_1090_; lean_object* v_lower_1091_; lean_object* v_upper_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1101_; 
v_range_1089_ = lean_ctor_get(v_x_1088_, 1);
lean_inc_ref(v_range_1089_);
v_treeMap_1090_ = lean_ctor_get(v_x_1088_, 0);
lean_inc(v_treeMap_1090_);
lean_dec_ref(v_x_1088_);
v_lower_1091_ = lean_ctor_get(v_range_1089_, 0);
v_upper_1092_ = lean_ctor_get(v_range_1089_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_range_1089_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1094_ = v_range_1089_;
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_upper_1092_);
lean_inc(v_lower_1091_);
lean_dec(v_range_1089_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1087_, v_treeMap_1090_, v_lower_1091_, v___x_1096_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_upper_1092_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_1102_){
_start:
{
lean_object* v___f_1103_; 
v___f_1103_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1103_, 0, v_inst_1102_);
return v___f_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_){
_start:
{
lean_object* v___f_1107_; 
v___f_1107_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1107_, 0, v_inst_1106_);
return v___f_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0(lean_object* v_carrier_1108_, lean_object* v_range_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_carrier_1108_);
lean_ctor_set(v___x_1110_, 1, v_range_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg(){
_start:
{
lean_object* v___f_1113_; 
v___f_1113_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___boxed(lean_object* v___dummy_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_1116_, lean_object* v_inst_1117_){
_start:
{
lean_object* v___f_1118_; 
v___f_1118_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_inst_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_1119_, v_inst_1120_);
lean_dec_ref(v_inst_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v_range_1124_; lean_object* v_treeMap_1125_; lean_object* v_lower_1126_; lean_object* v_upper_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v_range_1124_ = lean_ctor_get(v_x_1123_, 1);
lean_inc_ref(v_range_1124_);
v_treeMap_1125_ = lean_ctor_get(v_x_1123_, 0);
lean_inc(v_treeMap_1125_);
lean_dec_ref(v_x_1123_);
v_lower_1126_ = lean_ctor_get(v_range_1124_, 0);
v_upper_1127_ = lean_ctor_get(v_range_1124_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_range_1124_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v_range_1124_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_upper_1127_);
lean_inc(v_lower_1126_);
lean_dec(v_range_1124_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1122_, v_treeMap_1125_, v_lower_1126_, v___x_1131_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_upper_1127_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_1137_){
_start:
{
lean_object* v___f_1138_; 
v___f_1138_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1138_, 0, v_inst_1137_);
return v___f_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_1139_, lean_object* v_inst_1140_){
_start:
{
lean_object* v___f_1141_; 
v___f_1141_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1141_, 0, v_inst_1140_);
return v___f_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1142_, lean_object* v_range_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_carrier_1142_);
lean_ctor_set(v___x_1144_, 1, v_range_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1147_; 
v___f_1147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_inst_1152_){
_start:
{
lean_object* v___f_1153_; 
v___f_1153_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_inst_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_1154_, v_00_u03b2_1155_, v_inst_1156_);
lean_dec_ref(v_inst_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v_range_1160_; lean_object* v_treeMap_1161_; lean_object* v_lower_1162_; lean_object* v_upper_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1172_; 
v_range_1160_ = lean_ctor_get(v_x_1159_, 1);
lean_inc_ref(v_range_1160_);
v_treeMap_1161_ = lean_ctor_get(v_x_1159_, 0);
lean_inc(v_treeMap_1161_);
lean_dec_ref(v_x_1159_);
v_lower_1162_ = lean_ctor_get(v_range_1160_, 0);
v_upper_1163_ = lean_ctor_get(v_range_1160_, 1);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_range_1160_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1165_ = v_range_1160_;
v_isShared_1166_ = v_isSharedCheck_1172_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_upper_1163_);
lean_inc(v_lower_1162_);
lean_dec(v_range_1160_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1172_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1158_, v_treeMap_1161_, v_lower_1162_, v___x_1167_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1168_);
v___x_1170_ = v___x_1165_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_upper_1163_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_1173_){
_start:
{
lean_object* v___f_1174_; 
v___f_1174_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1174_, 0, v_inst_1173_);
return v___f_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_inst_1177_){
_start:
{
lean_object* v___f_1178_; 
v___f_1178_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1178_, 0, v_inst_1177_);
return v___f_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_1179_, lean_object* v_t_1180_, lean_object* v_lowerBound_1181_, lean_object* v_upperBound_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1179_, v_t_1180_, v_lowerBound_1181_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v_upperBound_1182_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_inst_1188_, lean_object* v_t_1189_, lean_object* v_lowerBound_1190_, lean_object* v_upperBound_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1188_, v_t_1189_, v_lowerBound_1190_, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_upperBound_1191_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1195_, lean_object* v_range_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_carrier_1195_);
lean_ctor_set(v___x_1197_, 1, v_range_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1200_; 
v___f_1200_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v___f_1206_; 
v___f_1206_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_inst_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_1207_, v_00_u03b2_1208_, v_inst_1209_);
lean_dec_ref(v_inst_1209_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1211_, lean_object* v_x_1212_){
_start:
{
lean_object* v_range_1213_; lean_object* v_treeMap_1214_; lean_object* v_lower_1215_; lean_object* v_upper_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1225_; 
v_range_1213_ = lean_ctor_get(v_x_1212_, 1);
lean_inc_ref(v_range_1213_);
v_treeMap_1214_ = lean_ctor_get(v_x_1212_, 0);
lean_inc(v_treeMap_1214_);
lean_dec_ref(v_x_1212_);
v_lower_1215_ = lean_ctor_get(v_range_1213_, 0);
v_upper_1216_ = lean_ctor_get(v_range_1213_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_range_1213_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1218_ = v_range_1213_;
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_upper_1216_);
lean_inc(v_lower_1215_);
lean_dec(v_range_1213_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1211_, v_treeMap_1214_, v_lower_1215_, v___x_1220_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1221_);
v___x_1223_ = v___x_1218_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_upper_1216_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_1226_){
_start:
{
lean_object* v___f_1227_; 
v___f_1227_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1227_, 0, v_inst_1226_);
return v___f_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_inst_1230_){
_start:
{
lean_object* v___f_1231_; 
v___f_1231_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1231_, 0, v_inst_1230_);
return v___f_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0(lean_object* v_carrier_1232_, lean_object* v_range_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_carrier_1232_);
lean_ctor_set(v___x_1234_, 1, v_range_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg(){
_start:
{
lean_object* v___f_1237_; 
v___f_1237_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___boxed(lean_object* v___dummy_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_1240_, lean_object* v_inst_1241_){
_start:
{
lean_object* v___f_1242_; 
v___f_1242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_1243_, lean_object* v_inst_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_1243_, v_inst_1244_);
lean_dec_ref(v_inst_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v_range_1248_; lean_object* v_treeMap_1249_; lean_object* v_lower_1250_; lean_object* v_upper_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1260_; 
v_range_1248_ = lean_ctor_get(v_x_1247_, 1);
lean_inc_ref(v_range_1248_);
v_treeMap_1249_ = lean_ctor_get(v_x_1247_, 0);
lean_inc(v_treeMap_1249_);
lean_dec_ref(v_x_1247_);
v_lower_1250_ = lean_ctor_get(v_range_1248_, 0);
v_upper_1251_ = lean_ctor_get(v_range_1248_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_range_1248_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1253_ = v_range_1248_;
v_isShared_1254_ = v_isSharedCheck_1260_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_upper_1251_);
lean_inc(v_lower_1250_);
lean_dec(v_range_1248_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1260_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1246_, v_treeMap_1249_, v_lower_1250_, v___x_1255_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1256_);
v___x_1258_ = v___x_1253_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_upper_1251_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1261_){
_start:
{
lean_object* v___f_1262_; 
v___f_1262_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1262_, 0, v_inst_1261_);
return v___f_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1263_, lean_object* v_inst_1264_){
_start:
{
lean_object* v___f_1265_; 
v___f_1265_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1265_, 0, v_inst_1264_);
return v___f_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1266_, lean_object* v_range_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_carrier_1266_);
lean_ctor_set(v___x_1268_, 1, v_range_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1271_; 
v___f_1271_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_inst_1276_){
_start:
{
lean_object* v___f_1277_; 
v___f_1277_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_inst_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1278_, v_00_u03b2_1279_, v_inst_1280_);
lean_dec_ref(v_inst_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v_range_1284_; lean_object* v_treeMap_1285_; lean_object* v_lower_1286_; lean_object* v_upper_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1296_; 
v_range_1284_ = lean_ctor_get(v_x_1283_, 1);
lean_inc_ref(v_range_1284_);
v_treeMap_1285_ = lean_ctor_get(v_x_1283_, 0);
lean_inc(v_treeMap_1285_);
lean_dec_ref(v_x_1283_);
v_lower_1286_ = lean_ctor_get(v_range_1284_, 0);
v_upper_1287_ = lean_ctor_get(v_range_1284_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_range_1284_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1289_ = v_range_1284_;
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_upper_1287_);
lean_inc(v_lower_1286_);
lean_dec(v_range_1284_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1282_, v_treeMap_1285_, v_lower_1286_, v___x_1291_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1292_);
v___x_1294_ = v___x_1289_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_upper_1287_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1297_){
_start:
{
lean_object* v___f_1298_; 
v___f_1298_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1298_, 0, v_inst_1297_);
return v___f_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_inst_1301_){
_start:
{
lean_object* v___f_1302_; 
v___f_1302_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1302_, 0, v_inst_1301_);
return v___f_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1303_, lean_object* v_t_1304_, lean_object* v_lowerBound_1305_, lean_object* v_upperBound_1306_){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_box(0);
v___x_1308_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1303_, v_t_1304_, v_lowerBound_1305_, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
lean_ctor_set(v___x_1309_, 1, v_upperBound_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1310_, lean_object* v_00_u03b2_1311_, lean_object* v_inst_1312_, lean_object* v_t_1313_, lean_object* v_lowerBound_1314_, lean_object* v_upperBound_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_box(0);
v___x_1317_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1312_, v_t_1313_, v_lowerBound_1314_, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v_upperBound_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1319_, lean_object* v_range_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_carrier_1319_);
lean_ctor_set(v___x_1321_, 1, v_range_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1324_; 
v___f_1324_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_inst_1329_){
_start:
{
lean_object* v___f_1330_; 
v___f_1330_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_inst_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1331_, v_00_u03b2_1332_, v_inst_1333_);
lean_dec_ref(v_inst_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v_range_1337_; lean_object* v_treeMap_1338_; lean_object* v_lower_1339_; lean_object* v_upper_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1349_; 
v_range_1337_ = lean_ctor_get(v_x_1336_, 1);
lean_inc_ref(v_range_1337_);
v_treeMap_1338_ = lean_ctor_get(v_x_1336_, 0);
lean_inc(v_treeMap_1338_);
lean_dec_ref(v_x_1336_);
v_lower_1339_ = lean_ctor_get(v_range_1337_, 0);
v_upper_1340_ = lean_ctor_get(v_range_1337_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_range_1337_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1342_ = v_range_1337_;
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_upper_1340_);
lean_inc(v_lower_1339_);
lean_dec(v_range_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1335_, v_treeMap_1338_, v_lower_1339_, v___x_1344_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_upper_1340_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1350_){
_start:
{
lean_object* v___f_1351_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1351_, 0, v_inst_1350_);
return v___f_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_inst_1354_){
_start:
{
lean_object* v___f_1355_; 
v___f_1355_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1355_, 0, v_inst_1354_);
return v___f_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0(lean_object* v_carrier_1356_, lean_object* v_range_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_carrier_1356_);
lean_ctor_set(v___x_1358_, 1, v_range_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg(){
_start:
{
lean_object* v___f_1361_; 
v___f_1361_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___boxed(lean_object* v___dummy_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1364_, lean_object* v_inst_1365_){
_start:
{
lean_object* v___f_1366_; 
v___f_1366_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_inst_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1367_, v_inst_1368_);
lean_dec_ref(v_inst_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_range_1372_; lean_object* v_treeMap_1373_; lean_object* v_lower_1374_; lean_object* v_upper_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1384_; 
v_range_1372_ = lean_ctor_get(v_x_1371_, 1);
lean_inc_ref(v_range_1372_);
v_treeMap_1373_ = lean_ctor_get(v_x_1371_, 0);
lean_inc(v_treeMap_1373_);
lean_dec_ref(v_x_1371_);
v_lower_1374_ = lean_ctor_get(v_range_1372_, 0);
v_upper_1375_ = lean_ctor_get(v_range_1372_, 1);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_range_1372_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1377_ = v_range_1372_;
v_isShared_1378_ = v_isSharedCheck_1384_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_upper_1375_);
lean_inc(v_lower_1374_);
lean_dec(v_range_1372_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1384_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1370_, v_treeMap_1373_, v_lower_1374_, v___x_1379_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_upper_1375_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1385_){
_start:
{
lean_object* v___f_1386_; 
v___f_1386_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1386_, 0, v_inst_1385_);
return v___f_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1387_, lean_object* v_inst_1388_){
_start:
{
lean_object* v___f_1389_; 
v___f_1389_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1389_, 0, v_inst_1388_);
return v___f_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1390_, lean_object* v_range_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_carrier_1390_);
lean_ctor_set(v___x_1392_, 1, v_range_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1395_; 
v___f_1395_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_inst_1400_){
_start:
{
lean_object* v___f_1401_; 
v___f_1401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_inst_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1402_, v_00_u03b2_1403_, v_inst_1404_);
lean_dec_ref(v_inst_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v_range_1408_; lean_object* v_treeMap_1409_; lean_object* v_lower_1410_; lean_object* v_upper_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
v_range_1408_ = lean_ctor_get(v_x_1407_, 1);
lean_inc_ref(v_range_1408_);
v_treeMap_1409_ = lean_ctor_get(v_x_1407_, 0);
lean_inc(v_treeMap_1409_);
lean_dec_ref(v_x_1407_);
v_lower_1410_ = lean_ctor_get(v_range_1408_, 0);
v_upper_1411_ = lean_ctor_get(v_range_1408_, 1);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_range_1408_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1413_ = v_range_1408_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_upper_1411_);
lean_inc(v_lower_1410_);
lean_dec(v_range_1408_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1406_, v_treeMap_1409_, v_lower_1410_, v___x_1415_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_upper_1411_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1421_){
_start:
{
lean_object* v___f_1422_; 
v___f_1422_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1422_, 0, v_inst_1421_);
return v___f_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1423_, lean_object* v_00_u03b2_1424_, lean_object* v_inst_1425_){
_start:
{
lean_object* v___f_1426_; 
v___f_1426_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1426_, 0, v_inst_1425_);
return v___f_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1427_, lean_object* v_t_1428_, lean_object* v_lowerBound_1429_, lean_object* v_upperBound_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1427_, v_t_1428_, v_lowerBound_1429_, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v_upperBound_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_inst_1436_, lean_object* v_t_1437_, lean_object* v_lowerBound_1438_, lean_object* v_upperBound_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1436_, v_t_1437_, v_lowerBound_1438_, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_upperBound_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1443_, lean_object* v_range_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_carrier_1443_);
lean_ctor_set(v___x_1445_, 1, v_range_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1448_; 
v___f_1448_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_inst_1453_){
_start:
{
lean_object* v___f_1454_; 
v___f_1454_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_inst_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1455_, v_00_u03b2_1456_, v_inst_1457_);
lean_dec_ref(v_inst_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v_range_1461_; lean_object* v_treeMap_1462_; lean_object* v_lower_1463_; lean_object* v_upper_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1473_; 
v_range_1461_ = lean_ctor_get(v_x_1460_, 1);
lean_inc_ref(v_range_1461_);
v_treeMap_1462_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_treeMap_1462_);
lean_dec_ref(v_x_1460_);
v_lower_1463_ = lean_ctor_get(v_range_1461_, 0);
v_upper_1464_ = lean_ctor_get(v_range_1461_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_range_1461_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1466_ = v_range_1461_;
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_upper_1464_);
lean_inc(v_lower_1463_);
lean_dec(v_range_1461_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1468_ = lean_box(0);
v___x_1469_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1459_, v_treeMap_1462_, v_lower_1463_, v___x_1468_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1469_);
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_upper_1464_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1474_){
_start:
{
lean_object* v___f_1475_; 
v___f_1475_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1475_, 0, v_inst_1474_);
return v___f_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_inst_1478_){
_start:
{
lean_object* v___f_1479_; 
v___f_1479_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1479_, 0, v_inst_1478_);
return v___f_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0(lean_object* v_carrier_1480_, lean_object* v_range_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_carrier_1480_);
lean_ctor_set(v___x_1482_, 1, v_range_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg(){
_start:
{
lean_object* v___f_1485_; 
v___f_1485_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___boxed(lean_object* v___dummy_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1488_, lean_object* v_inst_1489_){
_start:
{
lean_object* v___f_1490_; 
v___f_1490_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1491_, lean_object* v_inst_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1491_, v_inst_1492_);
lean_dec_ref(v_inst_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v_range_1496_; lean_object* v_treeMap_1497_; lean_object* v_lower_1498_; lean_object* v_upper_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1508_; 
v_range_1496_ = lean_ctor_get(v_x_1495_, 1);
lean_inc_ref(v_range_1496_);
v_treeMap_1497_ = lean_ctor_get(v_x_1495_, 0);
lean_inc(v_treeMap_1497_);
lean_dec_ref(v_x_1495_);
v_lower_1498_ = lean_ctor_get(v_range_1496_, 0);
v_upper_1499_ = lean_ctor_get(v_range_1496_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_range_1496_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1501_ = v_range_1496_;
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_upper_1499_);
lean_inc(v_lower_1498_);
lean_dec(v_range_1496_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1494_, v_treeMap_1497_, v_lower_1498_, v___x_1503_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_upper_1499_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1509_){
_start:
{
lean_object* v___f_1510_; 
v___f_1510_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1510_, 0, v_inst_1509_);
return v___f_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1511_, lean_object* v_inst_1512_){
_start:
{
lean_object* v___f_1513_; 
v___f_1513_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1513_, 0, v_inst_1512_);
return v___f_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1514_, lean_object* v_range_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_carrier_1514_);
lean_ctor_set(v___x_1516_, 1, v_range_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1519_; 
v___f_1519_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1522_, lean_object* v_00_u03b2_1523_, lean_object* v_inst_1524_){
_start:
{
lean_object* v___f_1525_; 
v___f_1525_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_inst_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1526_, v_00_u03b2_1527_, v_inst_1528_);
lean_dec_ref(v_inst_1528_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v_range_1532_; lean_object* v_treeMap_1533_; lean_object* v_lower_1534_; lean_object* v_upper_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
v_range_1532_ = lean_ctor_get(v_x_1531_, 1);
lean_inc_ref(v_range_1532_);
v_treeMap_1533_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_treeMap_1533_);
lean_dec_ref(v_x_1531_);
v_lower_1534_ = lean_ctor_get(v_range_1532_, 0);
v_upper_1535_ = lean_ctor_get(v_range_1532_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_range_1532_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1537_ = v_range_1532_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_upper_1535_);
lean_inc(v_lower_1534_);
lean_dec(v_range_1532_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = lean_box(0);
v___x_1540_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1530_, v_treeMap_1533_, v_lower_1534_, v___x_1539_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_upper_1535_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1545_){
_start:
{
lean_object* v___f_1546_; 
v___f_1546_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1546_, 0, v_inst_1545_);
return v___f_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_inst_1549_){
_start:
{
lean_object* v___f_1550_; 
v___f_1550_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1550_, 0, v_inst_1549_);
return v___f_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1551_, lean_object* v_t_1552_, lean_object* v_lowerBound_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_box(0);
v___x_1555_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1551_, v_t_1552_, v_lowerBound_1553_, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_inst_1558_, lean_object* v_t_1559_, lean_object* v_lowerBound_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_box(0);
v___x_1562_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1558_, v_t_1559_, v_lowerBound_1560_, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1563_, lean_object* v_range_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_carrier_1563_);
lean_ctor_set(v___x_1565_, 1, v_range_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1568_; 
v___f_1568_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1571_, lean_object* v_00_u03b2_1572_, lean_object* v_inst_1573_){
_start:
{
lean_object* v___f_1574_; 
v___f_1574_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_inst_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1575_, v_00_u03b2_1576_, v_inst_1577_);
lean_dec_ref(v_inst_1577_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v_treeMap_1581_; lean_object* v_range_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_treeMap_1581_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_treeMap_1581_);
v_range_1582_ = lean_ctor_get(v_x_1580_, 1);
lean_inc(v_range_1582_);
lean_dec_ref(v_x_1580_);
v___x_1583_ = lean_box(0);
v___x_1584_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1579_, v_treeMap_1581_, v_range_1582_, v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1585_){
_start:
{
lean_object* v___f_1586_; 
v___f_1586_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1586_, 0, v_inst_1585_);
return v___f_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1587_, lean_object* v_00_u03b2_1588_, lean_object* v_inst_1589_){
_start:
{
lean_object* v___f_1590_; 
v___f_1590_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1590_, 0, v_inst_1589_);
return v___f_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0(lean_object* v_carrier_1591_, lean_object* v_range_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v_carrier_1591_);
lean_ctor_set(v___x_1593_, 1, v_range_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg(){
_start:
{
lean_object* v___f_1596_; 
v___f_1596_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___boxed(lean_object* v___dummy_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1599_, lean_object* v_inst_1600_){
_start:
{
lean_object* v___f_1601_; 
v___f_1601_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1602_, lean_object* v_inst_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1602_, v_inst_1603_);
lean_dec_ref(v_inst_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v_treeMap_1607_; lean_object* v_range_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_treeMap_1607_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_treeMap_1607_);
v_range_1608_ = lean_ctor_get(v_x_1606_, 1);
lean_inc(v_range_1608_);
lean_dec_ref(v_x_1606_);
v___x_1609_ = lean_box(0);
v___x_1610_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1605_, v_treeMap_1607_, v_range_1608_, v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1611_){
_start:
{
lean_object* v___f_1612_; 
v___f_1612_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1612_, 0, v_inst_1611_);
return v___f_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1613_, lean_object* v_inst_1614_){
_start:
{
lean_object* v___f_1615_; 
v___f_1615_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1615_, 0, v_inst_1614_);
return v___f_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1616_, lean_object* v_range_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_carrier_1616_);
lean_ctor_set(v___x_1618_, 1, v_range_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1621_; 
v___f_1621_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1624_, lean_object* v_00_u03b2_1625_, lean_object* v_inst_1626_){
_start:
{
lean_object* v___f_1627_; 
v___f_1627_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1628_, lean_object* v_00_u03b2_1629_, lean_object* v_inst_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1628_, v_00_u03b2_1629_, v_inst_1630_);
lean_dec_ref(v_inst_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_treeMap_1634_; lean_object* v_range_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_treeMap_1634_ = lean_ctor_get(v_x_1633_, 0);
lean_inc(v_treeMap_1634_);
v_range_1635_ = lean_ctor_get(v_x_1633_, 1);
lean_inc(v_range_1635_);
lean_dec_ref(v_x_1633_);
v___x_1636_ = lean_box(0);
v___x_1637_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1632_, v_treeMap_1634_, v_range_1635_, v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1638_){
_start:
{
lean_object* v___f_1639_; 
v___f_1639_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1639_, 0, v_inst_1638_);
return v___f_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_inst_1642_){
_start:
{
lean_object* v___f_1643_; 
v___f_1643_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1643_, 0, v_inst_1642_);
return v___f_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1644_, lean_object* v_t_1645_, lean_object* v_lowerBound_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1644_, v_t_1645_, v_lowerBound_1646_, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_inst_1651_, lean_object* v_t_1652_, lean_object* v_lowerBound_1653_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1651_, v_t_1652_, v_lowerBound_1653_, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1656_, lean_object* v_range_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_carrier_1656_);
lean_ctor_set(v___x_1658_, 1, v_range_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1661_; 
v___f_1661_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1664_, lean_object* v_00_u03b2_1665_, lean_object* v_inst_1666_){
_start:
{
lean_object* v___f_1667_; 
v___f_1667_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_inst_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1668_, v_00_u03b2_1669_, v_inst_1670_);
lean_dec_ref(v_inst_1670_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1672_, lean_object* v_x_1673_){
_start:
{
lean_object* v_treeMap_1674_; lean_object* v_range_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_treeMap_1674_ = lean_ctor_get(v_x_1673_, 0);
lean_inc(v_treeMap_1674_);
v_range_1675_ = lean_ctor_get(v_x_1673_, 1);
lean_inc(v_range_1675_);
lean_dec_ref(v_x_1673_);
v___x_1676_ = lean_box(0);
v___x_1677_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1672_, v_treeMap_1674_, v_range_1675_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1678_){
_start:
{
lean_object* v___f_1679_; 
v___f_1679_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1679_, 0, v_inst_1678_);
return v___f_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_inst_1682_){
_start:
{
lean_object* v___f_1683_; 
v___f_1683_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1683_, 0, v_inst_1682_);
return v___f_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0(lean_object* v_carrier_1684_, lean_object* v_range_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_carrier_1684_);
lean_ctor_set(v___x_1686_, 1, v_range_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg(){
_start:
{
lean_object* v___f_1689_; 
v___f_1689_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___boxed(lean_object* v___dummy_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1692_, lean_object* v_inst_1693_){
_start:
{
lean_object* v___f_1694_; 
v___f_1694_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_inst_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1695_, v_inst_1696_);
lean_dec_ref(v_inst_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_treeMap_1700_; lean_object* v_range_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_treeMap_1700_ = lean_ctor_get(v_x_1699_, 0);
lean_inc(v_treeMap_1700_);
v_range_1701_ = lean_ctor_get(v_x_1699_, 1);
lean_inc(v_range_1701_);
lean_dec_ref(v_x_1699_);
v___x_1702_ = lean_box(0);
v___x_1703_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1698_, v_treeMap_1700_, v_range_1701_, v___x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1704_){
_start:
{
lean_object* v___f_1705_; 
v___f_1705_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1705_, 0, v_inst_1704_);
return v___f_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1706_, lean_object* v_inst_1707_){
_start:
{
lean_object* v___f_1708_; 
v___f_1708_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1708_, 0, v_inst_1707_);
return v___f_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1709_, lean_object* v_range_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_carrier_1709_);
lean_ctor_set(v___x_1711_, 1, v_range_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1714_; 
v___f_1714_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1717_, lean_object* v_00_u03b2_1718_, lean_object* v_inst_1719_){
_start:
{
lean_object* v___f_1720_; 
v___f_1720_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_inst_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1721_, v_00_u03b2_1722_, v_inst_1723_);
lean_dec_ref(v_inst_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v_treeMap_1727_; lean_object* v_range_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_treeMap_1727_ = lean_ctor_get(v_x_1726_, 0);
lean_inc(v_treeMap_1727_);
v_range_1728_ = lean_ctor_get(v_x_1726_, 1);
lean_inc(v_range_1728_);
lean_dec_ref(v_x_1726_);
v___x_1729_ = lean_box(0);
v___x_1730_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1725_, v_treeMap_1727_, v_range_1728_, v___x_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1731_){
_start:
{
lean_object* v___f_1732_; 
v___f_1732_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1732_, 0, v_inst_1731_);
return v___f_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_inst_1735_){
_start:
{
lean_object* v___f_1736_; 
v___f_1736_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1736_, 0, v_inst_1735_);
return v___f_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1737_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1737_, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1740_);
lean_dec(v_t_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_t_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_t_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1746_, v_00_u03b2_1747_, v_t_1748_);
lean_dec(v_t_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1750_, lean_object* v_range_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_carrier_1750_);
lean_ctor_set(v___x_1752_, 1, v_range_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1755_; 
v___f_1755_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_){
_start:
{
lean_object* v___f_1760_; 
v___f_1760_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1761_){
_start:
{
lean_object* v_treeMap_1762_; lean_object* v___x_1763_; 
v_treeMap_1762_ = lean_ctor_get(v_x_1761_, 0);
v___x_1763_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(v_x_1764_);
lean_dec_ref(v_x_1764_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1768_; 
v___f_1768_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1771_, lean_object* v_00_u03b2_1772_){
_start:
{
lean_object* v___f_1773_; 
v___f_1773_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0(lean_object* v_carrier_1774_, lean_object* v_range_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_carrier_1774_);
lean_ctor_set(v___x_1776_, 1, v_range_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg(){
_start:
{
lean_object* v___f_1779_; 
v___f_1779_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___boxed(lean_object* v___dummy_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1782_){
_start:
{
lean_object* v___f_1783_; 
v___f_1783_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1784_){
_start:
{
lean_object* v_treeMap_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_treeMap_1785_ = lean_ctor_get(v_x_1784_, 0);
v___x_1786_ = lean_box(0);
v___x_1787_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1785_, v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(v_x_1788_);
lean_dec_ref(v_x_1788_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1792_; 
v___f_1792_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1795_){
_start:
{
lean_object* v___f_1796_; 
v___f_1796_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1797_, lean_object* v_range_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_carrier_1797_);
lean_ctor_set(v___x_1799_, 1, v_range_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1802_; 
v___f_1802_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1805_, lean_object* v_00_u03b2_1806_){
_start:
{
lean_object* v___f_1807_; 
v___f_1807_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1808_){
_start:
{
lean_object* v_treeMap_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_treeMap_1809_ = lean_ctor_get(v_x_1808_, 0);
v___x_1810_ = lean_box(0);
v___x_1811_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1809_, v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(v_x_1812_);
lean_dec_ref(v_x_1812_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1816_; 
v___f_1816_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_){
_start:
{
lean_object* v___f_1821_; 
v___f_1821_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1821_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Zipper(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
