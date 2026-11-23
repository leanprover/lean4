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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_tag_nat(v_x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(v_x_142_);
lean_dec(v_x_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_tag_nat(v_x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(v_00_u03b1_148_, v_00_u03b2_149_, v_x_150_);
lean_dec(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* v_t_152_, lean_object* v_k_153_){
_start:
{
if (lean_obj_tag(v_t_152_) == 0)
{
return v_k_153_;
}
else
{
lean_object* v_k_154_; lean_object* v_v_155_; lean_object* v_tree_156_; lean_object* v_next_157_; lean_object* v___x_158_; 
v_k_154_ = lean_ctor_get(v_t_152_, 0);
lean_inc(v_k_154_);
v_v_155_ = lean_ctor_get(v_t_152_, 1);
lean_inc(v_v_155_);
v_tree_156_ = lean_ctor_get(v_t_152_, 2);
lean_inc(v_tree_156_);
v_next_157_ = lean_ctor_get(v_t_152_, 3);
lean_inc(v_next_157_);
lean_dec_ref_known(v_t_152_, 4);
v___x_158_ = lean_apply_4(v_k_153_, v_k_154_, v_v_155_, v_tree_156_, v_next_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_motive_161_, lean_object* v_ctorIdx_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_k_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_163_, v_k_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_motive_169_, lean_object* v_ctorIdx_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_k_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(v_00_u03b1_167_, v_00_u03b2_168_, v_motive_169_, v_ctorIdx_170_, v_t_171_, v_h_172_, v_k_173_);
lean_dec(v_ctorIdx_170_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* v_t_175_, lean_object* v_done_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_175_, v_done_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_done_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_181_, v_done_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* v_t_185_, lean_object* v_cons_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_185_, v_cons_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* v_00_u03b1_188_, lean_object* v_00_u03b2_189_, lean_object* v_motive_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_cons_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_191_, v_cons_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* v_init_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v_k_197_; lean_object* v_v_198_; lean_object* v_l_199_; lean_object* v_r_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_k_197_ = lean_ctor_get(v_x_196_, 1);
v_v_198_ = lean_ctor_get(v_x_196_, 2);
v_l_199_ = lean_ctor_get(v_x_196_, 3);
v_r_200_ = lean_ctor_get(v_x_196_, 4);
v___x_201_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_195_, v_r_200_);
lean_inc(v_v_198_);
lean_inc(v_k_197_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_k_197_);
lean_ctor_set(v___x_202_, 1, v_v_198_);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
v_init_195_ = v___x_203_;
v_x_196_ = v_l_199_;
goto _start;
}
else
{
return v_init_195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* v_init_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_205_, v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v_k_210_; lean_object* v_v_211_; lean_object* v_tree_212_; lean_object* v_next_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_k_210_ = lean_ctor_get(v_x_208_, 0);
v_v_211_ = lean_ctor_get(v_x_208_, 1);
v_tree_212_ = lean_ctor_get(v_x_208_, 2);
v_next_213_ = lean_ctor_get(v_x_208_, 3);
lean_inc(v_v_211_);
lean_inc(v_k_210_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_k_210_);
lean_ctor_set(v___x_214_, 1, v_v_211_);
v___x_215_ = lean_box(0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_215_, v_tree_212_);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_213_);
v___x_219_ = l_List_appendTR___redArg(v___x_217_, v___x_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_220_);
lean_dec(v_x_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_226_, v_00_u03b2_227_, v_x_228_);
lean_dec(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_init_232_, lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_232_, v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_init_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(v_00_u03b1_235_, v_00_u03b2_236_, v_init_237_, v_x_238_);
lean_dec(v_x_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
else
{
lean_object* v_tree_242_; lean_object* v_next_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_tree_242_ = lean_ctor_get(v_x_240_, 2);
v_next_243_ = lean_ctor_get(v_x_240_, 3);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_242_);
v___x_246_ = lean_nat_add(v___x_244_, v___x_245_);
lean_dec(v___x_245_);
v___x_247_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_243_);
v___x_248_ = lean_nat_add(v___x_246_, v___x_247_);
lean_dec(v___x_247_);
lean_dec(v___x_246_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_249_);
lean_dec(v_x_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* v_00_u03b1_255_, lean_object* v_00_u03b2_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(v_00_u03b1_255_, v_00_u03b2_256_, v_x_257_);
lean_dec(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_k_261_; lean_object* v_v_262_; lean_object* v_l_263_; lean_object* v_r_264_; lean_object* v___x_265_; 
v_k_261_ = lean_ctor_get(v_x_259_, 1);
v_v_262_ = lean_ctor_get(v_x_259_, 2);
v_l_263_ = lean_ctor_get(v_x_259_, 3);
v_r_264_ = lean_ctor_get(v_x_259_, 4);
lean_inc(v_r_264_);
lean_inc(v_v_262_);
lean_inc(v_k_261_);
v___x_265_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_265_, 0, v_k_261_);
lean_ctor_set(v___x_265_, 1, v_v_262_);
lean_ctor_set(v___x_265_, 2, v_r_264_);
lean_ctor_set(v___x_265_, 3, v_x_260_);
v_x_259_ = v_l_263_;
v_x_260_ = v___x_265_;
goto _start;
}
else
{
return v_x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_267_, v_x_268_);
lean_dec(v_x_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_DTreeMap_Internal_Zipper_prependMap(v_00_u03b1_275_, v_00_u03b2_276_, v_x_277_, v_x_278_);
lean_dec(v_x_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* v_inst_280_, lean_object* v_t_281_, lean_object* v_lowerBound_282_, lean_object* v_it_283_){
_start:
{
if (lean_obj_tag(v_t_281_) == 0)
{
lean_object* v_k_284_; lean_object* v_v_285_; lean_object* v_l_286_; lean_object* v_r_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_k_284_ = lean_ctor_get(v_t_281_, 1);
lean_inc_n(v_k_284_, 2);
v_v_285_ = lean_ctor_get(v_t_281_, 2);
lean_inc(v_v_285_);
v_l_286_ = lean_ctor_get(v_t_281_, 3);
lean_inc(v_l_286_);
v_r_287_ = lean_ctor_get(v_t_281_, 4);
lean_inc(v_r_287_);
lean_dec_ref_known(v_t_281_, 5);
lean_inc_ref(v_inst_280_);
lean_inc(v_lowerBound_282_);
v___x_288_ = lean_apply_2(v_inst_280_, v_lowerBound_282_, v_k_284_);
v___x_289_ = lean_unbox(v___x_288_);
switch(v___x_289_)
{
case 0:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_290_, 0, v_k_284_);
lean_ctor_set(v___x_290_, 1, v_v_285_);
lean_ctor_set(v___x_290_, 2, v_r_287_);
lean_ctor_set(v___x_290_, 3, v_it_283_);
v_t_281_ = v_l_286_;
v_it_283_ = v___x_290_;
goto _start;
}
case 1:
{
lean_object* v___x_292_; 
lean_dec(v_l_286_);
lean_dec(v_lowerBound_282_);
lean_dec_ref(v_inst_280_);
v___x_292_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_292_, 0, v_k_284_);
lean_ctor_set(v___x_292_, 1, v_v_285_);
lean_ctor_set(v___x_292_, 2, v_r_287_);
lean_ctor_set(v___x_292_, 3, v_it_283_);
return v___x_292_;
}
default: 
{
lean_dec(v_l_286_);
lean_dec(v_v_285_);
lean_dec(v_k_284_);
v_t_281_ = v_r_287_;
goto _start;
}
}
}
else
{
lean_dec(v_lowerBound_282_);
lean_dec_ref(v_inst_280_);
return v_it_283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* v_00_u03b1_294_, lean_object* v_00_u03b2_295_, lean_object* v_inst_296_, lean_object* v_t_297_, lean_object* v_lowerBound_298_, lean_object* v_it_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_296_, v_t_297_, v_lowerBound_298_, v_it_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* v_inst_301_, lean_object* v_t_302_, lean_object* v_lowerBound_303_, lean_object* v_it_304_){
_start:
{
if (lean_obj_tag(v_t_302_) == 0)
{
lean_object* v_k_305_; lean_object* v_v_306_; lean_object* v_l_307_; lean_object* v_r_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_k_305_ = lean_ctor_get(v_t_302_, 1);
lean_inc_n(v_k_305_, 2);
v_v_306_ = lean_ctor_get(v_t_302_, 2);
lean_inc(v_v_306_);
v_l_307_ = lean_ctor_get(v_t_302_, 3);
lean_inc(v_l_307_);
v_r_308_ = lean_ctor_get(v_t_302_, 4);
lean_inc(v_r_308_);
lean_dec_ref_known(v_t_302_, 5);
lean_inc_ref(v_inst_301_);
lean_inc(v_lowerBound_303_);
v___x_309_ = lean_apply_2(v_inst_301_, v_lowerBound_303_, v_k_305_);
v___x_310_ = lean_unbox(v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_311_, 0, v_k_305_);
lean_ctor_set(v___x_311_, 1, v_v_306_);
lean_ctor_set(v___x_311_, 2, v_r_308_);
lean_ctor_set(v___x_311_, 3, v_it_304_);
v_t_302_ = v_l_307_;
v_it_304_ = v___x_311_;
goto _start;
}
else
{
lean_dec(v_l_307_);
lean_dec(v_v_306_);
lean_dec(v_k_305_);
v_t_302_ = v_r_308_;
goto _start;
}
}
else
{
lean_dec(v_lowerBound_303_);
lean_dec_ref(v_inst_301_);
return v_it_304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_inst_316_, lean_object* v_t_317_, lean_object* v_lowerBound_318_, lean_object* v_it_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_316_, v_t_317_, v_lowerBound_318_, v_it_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v_size_325_; lean_object* v_k_326_; lean_object* v_v_327_; lean_object* v_l_328_; lean_object* v_r_329_; lean_object* v___x_330_; 
lean_dec(v_h__1_323_);
v_size_325_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_size_325_);
v_k_326_ = lean_ctor_get(v_x_321_, 1);
lean_inc(v_k_326_);
v_v_327_ = lean_ctor_get(v_x_321_, 2);
lean_inc(v_v_327_);
v_l_328_ = lean_ctor_get(v_x_321_, 3);
lean_inc(v_l_328_);
v_r_329_ = lean_ctor_get(v_x_321_, 4);
lean_inc(v_r_329_);
lean_dec_ref_known(v_x_321_, 5);
v___x_330_ = lean_apply_6(v_h__2_324_, v_size_325_, v_k_326_, v_v_327_, v_l_328_, v_r_329_, v_x_322_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; 
lean_dec(v_h__2_324_);
v___x_331_ = lean_apply_1(v_h__1_323_, v_x_322_);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* v_00_u03b1_332_, lean_object* v_00_u03b2_333_, lean_object* v_motive_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_h__1_337_, lean_object* v_h__2_338_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v_size_339_; lean_object* v_k_340_; lean_object* v_v_341_; lean_object* v_l_342_; lean_object* v_r_343_; lean_object* v___x_344_; 
lean_dec(v_h__1_337_);
v_size_339_ = lean_ctor_get(v_x_335_, 0);
lean_inc(v_size_339_);
v_k_340_ = lean_ctor_get(v_x_335_, 1);
lean_inc(v_k_340_);
v_v_341_ = lean_ctor_get(v_x_335_, 2);
lean_inc(v_v_341_);
v_l_342_ = lean_ctor_get(v_x_335_, 3);
lean_inc(v_l_342_);
v_r_343_ = lean_ctor_get(v_x_335_, 4);
lean_inc(v_r_343_);
lean_dec_ref_known(v_x_335_, 5);
v___x_344_ = lean_apply_6(v_h__2_338_, v_size_339_, v_k_340_, v_v_341_, v_l_342_, v_r_343_, v_x_336_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; 
lean_dec(v_h__2_338_);
v___x_345_ = lean_apply_1(v_h__1_337_, v_x_336_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object* v_x_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_h__2_348_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_apply_1(v_h__1_347_, v___x_349_);
return v___x_350_;
}
else
{
lean_object* v_k_351_; lean_object* v_v_352_; lean_object* v_tree_353_; lean_object* v_next_354_; lean_object* v___x_355_; 
lean_dec(v_h__1_347_);
v_k_351_ = lean_ctor_get(v_x_346_, 0);
lean_inc(v_k_351_);
v_v_352_ = lean_ctor_get(v_x_346_, 1);
lean_inc(v_v_352_);
v_tree_353_ = lean_ctor_get(v_x_346_, 2);
lean_inc(v_tree_353_);
v_next_354_ = lean_ctor_get(v_x_346_, 3);
lean_inc(v_next_354_);
lean_dec_ref_known(v_x_346_, 4);
v___x_355_ = lean_apply_4(v_h__2_348_, v_k_351_, v_v_352_, v_tree_353_, v_next_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_motive_358_, lean_object* v_x_359_, lean_object* v_h__1_360_, lean_object* v_h__2_361_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v_h__2_361_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_apply_1(v_h__1_360_, v___x_362_);
return v___x_363_;
}
else
{
lean_object* v_k_364_; lean_object* v_v_365_; lean_object* v_tree_366_; lean_object* v_next_367_; lean_object* v___x_368_; 
lean_dec(v_h__1_360_);
v_k_364_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_k_364_);
v_v_365_ = lean_ctor_get(v_x_359_, 1);
lean_inc(v_v_365_);
v_tree_366_ = lean_ctor_get(v_x_359_, 2);
lean_inc(v_tree_366_);
v_next_367_ = lean_ctor_get(v_x_359_, 3);
lean_inc(v_next_367_);
lean_dec_ref_known(v_x_359_, 4);
v___x_368_ = lean_apply_4(v_h__2_361_, v_k_364_, v_v_365_, v_tree_366_, v_next_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object* v_x_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_){
_start:
{
if (lean_obj_tag(v_x_369_) == 0)
{
lean_object* v_size_372_; lean_object* v_k_373_; lean_object* v_v_374_; lean_object* v_l_375_; lean_object* v_r_376_; lean_object* v___x_377_; 
lean_dec(v_h__1_370_);
v_size_372_ = lean_ctor_get(v_x_369_, 0);
lean_inc(v_size_372_);
v_k_373_ = lean_ctor_get(v_x_369_, 1);
lean_inc(v_k_373_);
v_v_374_ = lean_ctor_get(v_x_369_, 2);
lean_inc(v_v_374_);
v_l_375_ = lean_ctor_get(v_x_369_, 3);
lean_inc(v_l_375_);
v_r_376_ = lean_ctor_get(v_x_369_, 4);
lean_inc(v_r_376_);
lean_dec_ref_known(v_x_369_, 5);
v___x_377_ = lean_apply_5(v_h__2_371_, v_size_372_, v_k_373_, v_v_374_, v_l_375_, v_r_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_h__2_371_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_apply_1(v_h__1_370_, v___x_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_motive_382_, lean_object* v_x_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_){
_start:
{
if (lean_obj_tag(v_x_383_) == 0)
{
lean_object* v_size_386_; lean_object* v_k_387_; lean_object* v_v_388_; lean_object* v_l_389_; lean_object* v_r_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_384_);
v_size_386_ = lean_ctor_get(v_x_383_, 0);
lean_inc(v_size_386_);
v_k_387_ = lean_ctor_get(v_x_383_, 1);
lean_inc(v_k_387_);
v_v_388_ = lean_ctor_get(v_x_383_, 2);
lean_inc(v_v_388_);
v_l_389_ = lean_ctor_get(v_x_383_, 3);
lean_inc(v_l_389_);
v_r_390_ = lean_ctor_get(v_x_383_, 4);
lean_inc(v_r_390_);
lean_dec_ref_known(v_x_383_, 5);
v___x_391_ = lean_apply_5(v_h__2_385_, v_size_386_, v_k_387_, v_v_388_, v_l_389_, v_r_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_h__2_385_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_apply_1(v_h__1_384_, v___x_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* v_x_394_){
_start:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_box(2);
return v___x_395_;
}
else
{
lean_object* v_k_396_; lean_object* v_v_397_; lean_object* v_tree_398_; lean_object* v_next_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_k_396_ = lean_ctor_get(v_x_394_, 0);
lean_inc(v_k_396_);
v_v_397_ = lean_ctor_get(v_x_394_, 1);
lean_inc(v_v_397_);
v_tree_398_ = lean_ctor_get(v_x_394_, 2);
lean_inc(v_tree_398_);
v_next_399_ = lean_ctor_get(v_x_394_, 3);
lean_inc(v_next_399_);
lean_dec_ref_known(v_x_394_, 4);
v___x_400_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_398_, v_next_399_);
lean_dec(v_tree_398_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_k_396_);
lean_ctor_set(v___x_401_, 1, v_v_397_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg(){
_start:
{
lean_object* v___f_409_; 
v___f_409_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object* v___dummy_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_){
_start:
{
lean_object* v___f_414_; 
v___f_414_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg___boxed(lean_object* v___dummy_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_422_, lean_object* v_recur_423_, lean_object* v_it_424_, lean_object* v_____do__lift_425_){
_start:
{
if (lean_obj_tag(v_____do__lift_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; 
lean_dec(v_it_424_);
lean_dec(v_recur_423_);
v_a_426_ = lean_ctor_get(v_____do__lift_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v_____do__lift_425_, 1);
v___x_427_ = lean_apply_2(v_toPure_422_, lean_box(0), v_a_426_);
return v___x_427_;
}
else
{
lean_object* v_a_428_; lean_object* v___x_429_; 
lean_dec(v_toPure_422_);
v_a_428_ = lean_ctor_get(v_____do__lift_425_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v_____do__lift_425_, 1);
v___x_429_ = lean_apply_4(v_recur_423_, v_it_424_, v_a_428_, lean_box(0), lean_box(0));
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_430_, lean_object* v_recur_431_, lean_object* v___y_432_, lean_object* v_acc_433_, lean_object* v_toBind_434_, lean_object* v_s_435_){
_start:
{
switch(lean_obj_tag(v_s_435_))
{
case 0:
{
lean_object* v_it_436_; lean_object* v_out_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_it_436_ = lean_ctor_get(v_s_435_, 0);
lean_inc(v_it_436_);
v_out_437_ = lean_ctor_get(v_s_435_, 1);
lean_inc(v_out_437_);
lean_dec_ref_known(v_s_435_, 2);
v___f_438_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_438_, 0, v_toPure_430_);
lean_closure_set(v___f_438_, 1, v_recur_431_);
lean_closure_set(v___f_438_, 2, v_it_436_);
v___x_439_ = lean_apply_3(v___y_432_, v_out_437_, lean_box(0), v_acc_433_);
v___x_440_ = lean_apply_4(v_toBind_434_, lean_box(0), lean_box(0), v___x_439_, v___f_438_);
return v___x_440_;
}
case 1:
{
lean_object* v_it_441_; lean_object* v___x_442_; 
lean_dec(v_toBind_434_);
lean_dec(v___y_432_);
lean_dec(v_toPure_430_);
v_it_441_ = lean_ctor_get(v_s_435_, 0);
lean_inc(v_it_441_);
lean_dec_ref_known(v_s_435_, 1);
v___x_442_ = lean_apply_4(v_recur_431_, v_it_441_, v_acc_433_, lean_box(0), lean_box(0));
return v___x_442_;
}
default: 
{
lean_object* v___x_443_; 
lean_dec(v_toBind_434_);
lean_dec(v___y_432_);
lean_dec(v_recur_431_);
v___x_443_ = lean_apply_2(v_toPure_430_, lean_box(0), v_acc_433_);
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_444_, lean_object* v___y_445_, lean_object* v_toBind_446_, lean_object* v_lift_447_, lean_object* v_it_448_, lean_object* v_acc_449_, lean_object* v_hP_450_, lean_object* v_recur_451_){
_start:
{
lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___f_452_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_452_, 0, v_toPure_444_);
lean_closure_set(v___f_452_, 1, v_recur_451_);
lean_closure_set(v___f_452_, 2, v___y_445_);
lean_closure_set(v___f_452_, 3, v_acc_449_);
lean_closure_set(v___f_452_, 4, v_toBind_446_);
v___x_453_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_it_448_);
v___x_454_ = lean_apply_4(v_lift_447_, lean_box(0), lean_box(0), v___f_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_455_, lean_object* v_lift_456_, lean_object* v_00_u03b3_457_, lean_object* v_Pl_458_, lean_object* v_it_459_, lean_object* v_init_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_toApplicative_462_; lean_object* v_toBind_463_; lean_object* v_toPure_464_; lean_object* v___f_465_; lean_object* v___x_466_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_455_, 0);
lean_inc_ref(v_toApplicative_462_);
v_toBind_463_ = lean_ctor_get(v_inst_455_, 1);
lean_inc(v_toBind_463_);
lean_dec_ref(v_inst_455_);
v_toPure_464_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc(v_toPure_464_);
lean_dec_ref(v_toApplicative_462_);
v___f_465_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_465_, 0, v_toPure_464_);
lean_closure_set(v___f_465_, 1, v___y_461_);
lean_closure_set(v___f_465_, 2, v_toBind_463_);
lean_closure_set(v___f_465_, 3, v_lift_456_);
v___x_466_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_465_, v_it_459_, v_init_460_, lean_box(0));
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object* v_inst_467_){
_start:
{
lean_object* v___f_468_; 
v___f_468_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_468_, 0, v_inst_467_);
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_m_471_, lean_object* v_inst_472_){
_start:
{
lean_object* v___f_473_; 
v___f_473_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_473_, 0, v_inst_472_);
return v___f_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_474_){
_start:
{
lean_inc(v_t_474_);
return v_t_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_475_);
lean_dec(v_t_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_t_479_){
_start:
{
lean_inc(v_t_479_);
return v_t_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_t_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_480_, v_00_u03b2_481_, v_t_482_);
lean_dec(v_t_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_box(0);
v___x_486_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_484_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_487_);
lean_dec(v_t_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_489_, lean_object* v_00_u03b2_490_, lean_object* v_t_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_t_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_493_, v_00_u03b2_494_, v_t_495_);
lean_dec(v_t_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(lean_object* v_x_497_){
_start:
{
lean_inc(v_x_497_);
return v_x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed(lean_object* v_x_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(v_x_498_);
lean_dec(v_x_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg(){
_start:
{
lean_object* v___f_502_; 
v___f_502_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___boxed(lean_object* v___dummy_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_){
_start:
{
lean_object* v___f_507_; 
v___f_507_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_, lean_object* v_h__3_511_){
_start:
{
switch(lean_obj_tag(v_x_508_))
{
case 0:
{
lean_object* v_it_512_; lean_object* v_out_513_; lean_object* v___x_514_; 
lean_dec(v_h__3_511_);
lean_dec(v_h__2_510_);
v_it_512_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_it_512_);
v_out_513_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_out_513_);
lean_dec_ref_known(v_x_508_, 2);
v___x_514_ = lean_apply_2(v_h__1_509_, v_it_512_, v_out_513_);
return v___x_514_;
}
case 1:
{
lean_object* v_it_515_; lean_object* v___x_516_; 
lean_dec(v_h__3_511_);
lean_dec(v_h__1_509_);
v_it_515_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_it_515_);
lean_dec_ref_known(v_x_508_, 1);
v___x_516_ = lean_apply_1(v_h__2_510_, v_it_515_);
return v___x_516_;
}
default: 
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_h__2_510_);
lean_dec(v_h__1_509_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_1(v_h__3_511_, v___x_517_);
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_m_521_, lean_object* v_motive_522_, lean_object* v_x_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_, lean_object* v_h__3_526_){
_start:
{
switch(lean_obj_tag(v_x_523_))
{
case 0:
{
lean_object* v_it_527_; lean_object* v_out_528_; lean_object* v___x_529_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__2_525_);
v_it_527_ = lean_ctor_get(v_x_523_, 0);
lean_inc(v_it_527_);
v_out_528_ = lean_ctor_get(v_x_523_, 1);
lean_inc(v_out_528_);
lean_dec_ref_known(v_x_523_, 2);
v___x_529_ = lean_apply_2(v_h__1_524_, v_it_527_, v_out_528_);
return v___x_529_;
}
case 1:
{
lean_object* v_it_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__1_524_);
v_it_530_ = lean_ctor_get(v_x_523_, 0);
lean_inc(v_it_530_);
lean_dec_ref_known(v_x_523_, 1);
v___x_531_ = lean_apply_1(v_h__2_525_, v_it_530_);
return v___x_531_;
}
default: 
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_h__2_525_);
lean_dec(v_h__1_524_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_apply_1(v_h__3_526_, v___x_532_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_iter_536_; 
v_iter_536_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_iter_536_);
if (lean_obj_tag(v_iter_536_) == 0)
{
lean_object* v___x_537_; 
lean_dec_ref(v_x_535_);
lean_dec_ref(v_inst_534_);
v___x_537_ = lean_box(2);
return v___x_537_;
}
else
{
lean_object* v_upper_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_555_; 
v_upper_538_ = lean_ctor_get(v_x_535_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_x_535_, 0);
lean_dec(v_unused_556_);
v___x_540_ = v_x_535_;
v_isShared_541_ = v_isSharedCheck_555_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_upper_538_);
lean_dec(v_x_535_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_555_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_k_542_; lean_object* v_v_543_; lean_object* v_tree_544_; lean_object* v_next_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_k_542_ = lean_ctor_get(v_iter_536_, 0);
lean_inc_n(v_k_542_, 2);
v_v_543_ = lean_ctor_get(v_iter_536_, 1);
lean_inc(v_v_543_);
v_tree_544_ = lean_ctor_get(v_iter_536_, 2);
lean_inc(v_tree_544_);
v_next_545_ = lean_ctor_get(v_iter_536_, 3);
lean_inc(v_next_545_);
lean_dec_ref_known(v_iter_536_, 4);
lean_inc(v_upper_538_);
v___x_546_ = lean_apply_2(v_inst_534_, v_k_542_, v_upper_538_);
v___x_547_ = lean_unbox(v___x_546_);
if (v___x_547_ == 2)
{
lean_object* v___x_548_; 
lean_dec(v_next_545_);
lean_dec(v_tree_544_);
lean_dec(v_v_543_);
lean_dec(v_k_542_);
lean_del_object(v___x_540_);
lean_dec(v_upper_538_);
v___x_548_ = lean_box(2);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_544_, v_next_545_);
lean_dec(v_tree_544_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_549_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_upper_538_);
v___x_551_ = v_reuseFailAlloc_554_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_k_542_);
lean_ctor_set(v___x_552_, 1, v_v_543_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_557_, lean_object* v_00_u03b2_558_, lean_object* v_inst_559_, lean_object* v_x_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_559_, v_x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_562_, lean_object* v_it_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_562_, v_it_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_565_){
_start:
{
lean_object* v___f_566_; 
v___f_566_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_566_, 0, v_inst_565_);
return v___f_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_inst_569_){
_start:
{
lean_object* v___f_570_; 
v___f_570_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_570_, 0, v_inst_569_);
return v___f_570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
lean_object* v_iter_574_; 
v_iter_574_ = lean_ctor_get(v_x_571_, 0);
if (lean_obj_tag(v_iter_574_) == 0)
{
lean_object* v_upper_575_; lean_object* v___x_576_; 
lean_dec(v_h__2_573_);
v_upper_575_ = lean_ctor_get(v_x_571_, 1);
lean_inc(v_upper_575_);
lean_dec_ref(v_x_571_);
v___x_576_ = lean_apply_1(v_h__1_572_, v_upper_575_);
return v___x_576_;
}
else
{
lean_object* v_upper_577_; lean_object* v_k_578_; lean_object* v_v_579_; lean_object* v_tree_580_; lean_object* v_next_581_; lean_object* v___x_582_; 
lean_inc_ref(v_iter_574_);
lean_dec(v_h__1_572_);
v_upper_577_ = lean_ctor_get(v_x_571_, 1);
lean_inc(v_upper_577_);
lean_dec_ref(v_x_571_);
v_k_578_ = lean_ctor_get(v_iter_574_, 0);
lean_inc(v_k_578_);
v_v_579_ = lean_ctor_get(v_iter_574_, 1);
lean_inc(v_v_579_);
v_tree_580_ = lean_ctor_get(v_iter_574_, 2);
lean_inc(v_tree_580_);
v_next_581_ = lean_ctor_get(v_iter_574_, 3);
lean_inc(v_next_581_);
lean_dec_ref_known(v_iter_574_, 4);
v___x_582_ = lean_apply_5(v_h__2_573_, v_k_578_, v_v_579_, v_tree_580_, v_next_581_, v_upper_577_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_583_, lean_object* v_00_u03b2_584_, lean_object* v_inst_585_, lean_object* v_motive_586_, lean_object* v_x_587_, lean_object* v_h__1_588_, lean_object* v_h__2_589_){
_start:
{
lean_object* v_iter_590_; 
v_iter_590_ = lean_ctor_get(v_x_587_, 0);
if (lean_obj_tag(v_iter_590_) == 0)
{
lean_object* v_upper_591_; lean_object* v___x_592_; 
lean_dec(v_h__2_589_);
v_upper_591_ = lean_ctor_get(v_x_587_, 1);
lean_inc(v_upper_591_);
lean_dec_ref(v_x_587_);
v___x_592_ = lean_apply_1(v_h__1_588_, v_upper_591_);
return v___x_592_;
}
else
{
lean_object* v_upper_593_; lean_object* v_k_594_; lean_object* v_v_595_; lean_object* v_tree_596_; lean_object* v_next_597_; lean_object* v___x_598_; 
lean_inc_ref(v_iter_590_);
lean_dec(v_h__1_588_);
v_upper_593_ = lean_ctor_get(v_x_587_, 1);
lean_inc(v_upper_593_);
lean_dec_ref(v_x_587_);
v_k_594_ = lean_ctor_get(v_iter_590_, 0);
lean_inc(v_k_594_);
v_v_595_ = lean_ctor_get(v_iter_590_, 1);
lean_inc(v_v_595_);
v_tree_596_ = lean_ctor_get(v_iter_590_, 2);
lean_inc(v_tree_596_);
v_next_597_ = lean_ctor_get(v_iter_590_, 3);
lean_inc(v_next_597_);
lean_dec_ref_known(v_iter_590_, 4);
v___x_598_ = lean_apply_5(v_h__2_589_, v_k_594_, v_v_595_, v_tree_596_, v_next_597_, v_upper_593_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_599_, lean_object* v_00_u03b2_600_, lean_object* v_inst_601_, lean_object* v_motive_602_, lean_object* v_x_603_, lean_object* v_h__1_604_, lean_object* v_h__2_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_599_, v_00_u03b2_600_, v_inst_601_, v_motive_602_, v_x_603_, v_h__1_604_, v_h__2_605_);
lean_dec_ref(v_inst_601_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg___boxed(lean_object* v___dummy_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_inst_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = lean_box(0);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_615_, v_00_u03b2_616_, v_inst_617_);
lean_dec_ref(v_inst_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_619_, lean_object* v_recur_620_, lean_object* v_it_621_, lean_object* v_____do__lift_622_){
_start:
{
if (lean_obj_tag(v_____do__lift_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
lean_dec_ref(v_it_621_);
lean_dec(v_recur_620_);
v_a_623_ = lean_ctor_get(v_____do__lift_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v_____do__lift_622_, 1);
v___x_624_ = lean_apply_2(v_toPure_619_, lean_box(0), v_a_623_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_626_; 
lean_dec(v_toPure_619_);
v_a_625_ = lean_ctor_get(v_____do__lift_622_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v_____do__lift_622_, 1);
v___x_626_ = lean_apply_4(v_recur_620_, v_it_621_, v_a_625_, lean_box(0), lean_box(0));
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_627_, lean_object* v_recur_628_, lean_object* v___y_629_, lean_object* v_acc_630_, lean_object* v_toBind_631_, lean_object* v_s_632_){
_start:
{
switch(lean_obj_tag(v_s_632_))
{
case 0:
{
lean_object* v_it_633_; lean_object* v_out_634_; lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_it_633_ = lean_ctor_get(v_s_632_, 0);
lean_inc(v_it_633_);
v_out_634_ = lean_ctor_get(v_s_632_, 1);
lean_inc(v_out_634_);
lean_dec_ref_known(v_s_632_, 2);
v___f_635_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_635_, 0, v_toPure_627_);
lean_closure_set(v___f_635_, 1, v_recur_628_);
lean_closure_set(v___f_635_, 2, v_it_633_);
v___x_636_ = lean_apply_3(v___y_629_, v_out_634_, lean_box(0), v_acc_630_);
v___x_637_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v___x_636_, v___f_635_);
return v___x_637_;
}
case 1:
{
lean_object* v_it_638_; lean_object* v___x_639_; 
lean_dec(v_toBind_631_);
lean_dec(v___y_629_);
lean_dec(v_toPure_627_);
v_it_638_ = lean_ctor_get(v_s_632_, 0);
lean_inc(v_it_638_);
lean_dec_ref_known(v_s_632_, 1);
v___x_639_ = lean_apply_4(v_recur_628_, v_it_638_, v_acc_630_, lean_box(0), lean_box(0));
return v___x_639_;
}
default: 
{
lean_object* v___x_640_; 
lean_dec(v_toBind_631_);
lean_dec(v___y_629_);
lean_dec(v_recur_628_);
v___x_640_ = lean_apply_2(v_toPure_627_, lean_box(0), v_acc_630_);
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_641_, lean_object* v___y_642_, lean_object* v_toBind_643_, lean_object* v_inst_644_, lean_object* v_lift_645_, lean_object* v_it_646_, lean_object* v_acc_647_, lean_object* v_hP_648_, lean_object* v_recur_649_){
_start:
{
lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___f_650_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_650_, 0, v_toPure_641_);
lean_closure_set(v___f_650_, 1, v_recur_649_);
lean_closure_set(v___f_650_, 2, v___y_642_);
lean_closure_set(v___f_650_, 3, v_acc_647_);
lean_closure_set(v___f_650_, 4, v_toBind_643_);
v___x_651_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_644_, v_it_646_);
v___x_652_ = lean_apply_4(v_lift_645_, lean_box(0), lean_box(0), v___f_650_, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_lift_655_, lean_object* v_00_u03b3_656_, lean_object* v_Pl_657_, lean_object* v_it_658_, lean_object* v_init_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_toApplicative_661_; lean_object* v_toBind_662_; lean_object* v_toPure_663_; lean_object* v___f_664_; lean_object* v___x_665_; 
v_toApplicative_661_ = lean_ctor_get(v_inst_653_, 0);
lean_inc_ref(v_toApplicative_661_);
v_toBind_662_ = lean_ctor_get(v_inst_653_, 1);
lean_inc(v_toBind_662_);
lean_dec_ref(v_inst_653_);
v_toPure_663_ = lean_ctor_get(v_toApplicative_661_, 1);
lean_inc(v_toPure_663_);
lean_dec_ref(v_toApplicative_661_);
v___f_664_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_664_, 0, v_toPure_663_);
lean_closure_set(v___f_664_, 1, v___y_660_);
lean_closure_set(v___f_664_, 2, v_toBind_662_);
lean_closure_set(v___f_664_, 3, v_inst_654_);
lean_closure_set(v___f_664_, 4, v_lift_655_);
v___x_665_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_664_, v_it_658_, v_init_659_, lean_box(0));
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object* v_inst_666_, lean_object* v_inst_667_){
_start:
{
lean_object* v___f_668_; 
v___f_668_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_668_, 0, v_inst_667_);
lean_closure_set(v___f_668_, 1, v_inst_666_);
return v___f_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_inst_671_, lean_object* v_m_672_, lean_object* v_inst_673_){
_start:
{
lean_object* v___f_674_; 
v___f_674_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_674_, 0, v_inst_673_);
lean_closure_set(v___f_674_, 1, v_inst_671_);
return v___f_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_675_, lean_object* v_x_676_){
_start:
{
lean_object* v_iter_677_; 
v_iter_677_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_iter_677_);
if (lean_obj_tag(v_iter_677_) == 0)
{
lean_object* v___x_678_; 
lean_dec_ref(v_x_676_);
lean_dec_ref(v_inst_675_);
v___x_678_ = lean_box(2);
return v___x_678_;
}
else
{
lean_object* v_upper_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_696_; 
v_upper_679_ = lean_ctor_get(v_x_676_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_x_676_, 0);
lean_dec(v_unused_697_);
v___x_681_ = v_x_676_;
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_upper_679_);
lean_dec(v_x_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v_tree_685_; lean_object* v_next_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_k_683_ = lean_ctor_get(v_iter_677_, 0);
lean_inc_n(v_k_683_, 2);
v_v_684_ = lean_ctor_get(v_iter_677_, 1);
lean_inc(v_v_684_);
v_tree_685_ = lean_ctor_get(v_iter_677_, 2);
lean_inc(v_tree_685_);
v_next_686_ = lean_ctor_get(v_iter_677_, 3);
lean_inc(v_next_686_);
lean_dec_ref_known(v_iter_677_, 4);
lean_inc(v_upper_679_);
v___x_687_ = lean_apply_2(v_inst_675_, v_k_683_, v_upper_679_);
v___x_688_ = lean_unbox(v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_685_, v_next_686_);
lean_dec(v_tree_685_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_689_);
v___x_691_ = v___x_681_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_upper_679_);
v___x_691_ = v_reuseFailAlloc_694_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_k_683_);
lean_ctor_set(v___x_692_, 1, v_v_684_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; 
lean_dec(v_next_686_);
lean_dec(v_tree_685_);
lean_dec(v_v_684_);
lean_dec(v_k_683_);
lean_del_object(v___x_681_);
lean_dec(v_upper_679_);
v___x_695_ = lean_box(2);
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_700_, v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_703_, lean_object* v_it_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_703_, v_it_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_706_){
_start:
{
lean_object* v___f_707_; 
v___f_707_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_707_, 0, v_inst_706_);
return v___f_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___f_711_; 
v___f_711_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_711_, 0, v_inst_710_);
return v___f_711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_712_, lean_object* v_h__1_713_, lean_object* v_h__2_714_){
_start:
{
lean_object* v_iter_715_; 
v_iter_715_ = lean_ctor_get(v_x_712_, 0);
if (lean_obj_tag(v_iter_715_) == 0)
{
lean_object* v_upper_716_; lean_object* v___x_717_; 
lean_dec(v_h__2_714_);
v_upper_716_ = lean_ctor_get(v_x_712_, 1);
lean_inc(v_upper_716_);
lean_dec_ref(v_x_712_);
v___x_717_ = lean_apply_1(v_h__1_713_, v_upper_716_);
return v___x_717_;
}
else
{
lean_object* v_upper_718_; lean_object* v_k_719_; lean_object* v_v_720_; lean_object* v_tree_721_; lean_object* v_next_722_; lean_object* v___x_723_; 
lean_inc_ref(v_iter_715_);
lean_dec(v_h__1_713_);
v_upper_718_ = lean_ctor_get(v_x_712_, 1);
lean_inc(v_upper_718_);
lean_dec_ref(v_x_712_);
v_k_719_ = lean_ctor_get(v_iter_715_, 0);
lean_inc(v_k_719_);
v_v_720_ = lean_ctor_get(v_iter_715_, 1);
lean_inc(v_v_720_);
v_tree_721_ = lean_ctor_get(v_iter_715_, 2);
lean_inc(v_tree_721_);
v_next_722_ = lean_ctor_get(v_iter_715_, 3);
lean_inc(v_next_722_);
lean_dec_ref_known(v_iter_715_, 4);
v___x_723_ = lean_apply_5(v_h__2_714_, v_k_719_, v_v_720_, v_tree_721_, v_next_722_, v_upper_718_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_, lean_object* v_motive_727_, lean_object* v_x_728_, lean_object* v_h__1_729_, lean_object* v_h__2_730_){
_start:
{
lean_object* v_iter_731_; 
v_iter_731_ = lean_ctor_get(v_x_728_, 0);
if (lean_obj_tag(v_iter_731_) == 0)
{
lean_object* v_upper_732_; lean_object* v___x_733_; 
lean_dec(v_h__2_730_);
v_upper_732_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_upper_732_);
lean_dec_ref(v_x_728_);
v___x_733_ = lean_apply_1(v_h__1_729_, v_upper_732_);
return v___x_733_;
}
else
{
lean_object* v_upper_734_; lean_object* v_k_735_; lean_object* v_v_736_; lean_object* v_tree_737_; lean_object* v_next_738_; lean_object* v___x_739_; 
lean_inc_ref(v_iter_731_);
lean_dec(v_h__1_729_);
v_upper_734_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_upper_734_);
lean_dec_ref(v_x_728_);
v_k_735_ = lean_ctor_get(v_iter_731_, 0);
lean_inc(v_k_735_);
v_v_736_ = lean_ctor_get(v_iter_731_, 1);
lean_inc(v_v_736_);
v_tree_737_ = lean_ctor_get(v_iter_731_, 2);
lean_inc(v_tree_737_);
v_next_738_ = lean_ctor_get(v_iter_731_, 3);
lean_inc(v_next_738_);
lean_dec_ref_known(v_iter_731_, 4);
v___x_739_ = lean_apply_5(v_h__2_730_, v_k_735_, v_v_736_, v_tree_737_, v_next_738_, v_upper_734_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_inst_742_, lean_object* v_motive_743_, lean_object* v_x_744_, lean_object* v_h__1_745_, lean_object* v_h__2_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_740_, v_00_u03b2_741_, v_inst_742_, v_motive_743_, v_x_744_, v_h__1_745_, v_h__2_746_);
lean_dec_ref(v_inst_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_box(0);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_756_, v_00_u03b2_757_, v_inst_758_);
lean_dec_ref(v_inst_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_760_, lean_object* v_recur_761_, lean_object* v_it_762_, lean_object* v_____do__lift_763_){
_start:
{
if (lean_obj_tag(v_____do__lift_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
lean_dec_ref(v_it_762_);
lean_dec(v_recur_761_);
v_a_764_ = lean_ctor_get(v_____do__lift_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v_____do__lift_763_, 1);
v___x_765_ = lean_apply_2(v_toPure_760_, lean_box(0), v_a_764_);
return v___x_765_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_767_; 
lean_dec(v_toPure_760_);
v_a_766_ = lean_ctor_get(v_____do__lift_763_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v_____do__lift_763_, 1);
v___x_767_ = lean_apply_4(v_recur_761_, v_it_762_, v_a_766_, lean_box(0), lean_box(0));
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_768_, lean_object* v_recur_769_, lean_object* v___y_770_, lean_object* v_acc_771_, lean_object* v_toBind_772_, lean_object* v_s_773_){
_start:
{
switch(lean_obj_tag(v_s_773_))
{
case 0:
{
lean_object* v_it_774_; lean_object* v_out_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_it_774_ = lean_ctor_get(v_s_773_, 0);
lean_inc(v_it_774_);
v_out_775_ = lean_ctor_get(v_s_773_, 1);
lean_inc(v_out_775_);
lean_dec_ref_known(v_s_773_, 2);
v___f_776_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_776_, 0, v_toPure_768_);
lean_closure_set(v___f_776_, 1, v_recur_769_);
lean_closure_set(v___f_776_, 2, v_it_774_);
v___x_777_ = lean_apply_3(v___y_770_, v_out_775_, lean_box(0), v_acc_771_);
v___x_778_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_777_, v___f_776_);
return v___x_778_;
}
case 1:
{
lean_object* v_it_779_; lean_object* v___x_780_; 
lean_dec(v_toBind_772_);
lean_dec(v___y_770_);
lean_dec(v_toPure_768_);
v_it_779_ = lean_ctor_get(v_s_773_, 0);
lean_inc(v_it_779_);
lean_dec_ref_known(v_s_773_, 1);
v___x_780_ = lean_apply_4(v_recur_769_, v_it_779_, v_acc_771_, lean_box(0), lean_box(0));
return v___x_780_;
}
default: 
{
lean_object* v___x_781_; 
lean_dec(v_toBind_772_);
lean_dec(v___y_770_);
lean_dec(v_recur_769_);
v___x_781_ = lean_apply_2(v_toPure_768_, lean_box(0), v_acc_771_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_782_, lean_object* v___y_783_, lean_object* v_toBind_784_, lean_object* v_inst_785_, lean_object* v_lift_786_, lean_object* v_it_787_, lean_object* v_acc_788_, lean_object* v_hP_789_, lean_object* v_recur_790_){
_start:
{
lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___f_791_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_791_, 0, v_toPure_782_);
lean_closure_set(v___f_791_, 1, v_recur_790_);
lean_closure_set(v___f_791_, 2, v___y_783_);
lean_closure_set(v___f_791_, 3, v_acc_788_);
lean_closure_set(v___f_791_, 4, v_toBind_784_);
v___x_792_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_785_, v_it_787_);
v___x_793_ = lean_apply_4(v_lift_786_, lean_box(0), lean_box(0), v___f_791_, v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_lift_796_, lean_object* v_00_u03b3_797_, lean_object* v_Pl_798_, lean_object* v_it_799_, lean_object* v_init_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_toApplicative_802_; lean_object* v_toBind_803_; lean_object* v_toPure_804_; lean_object* v___f_805_; lean_object* v___x_806_; 
v_toApplicative_802_ = lean_ctor_get(v_inst_794_, 0);
lean_inc_ref(v_toApplicative_802_);
v_toBind_803_ = lean_ctor_get(v_inst_794_, 1);
lean_inc(v_toBind_803_);
lean_dec_ref(v_inst_794_);
v_toPure_804_ = lean_ctor_get(v_toApplicative_802_, 1);
lean_inc(v_toPure_804_);
lean_dec_ref(v_toApplicative_802_);
v___f_805_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_805_, 0, v_toPure_804_);
lean_closure_set(v___f_805_, 1, v___y_801_);
lean_closure_set(v___f_805_, 2, v_toBind_803_);
lean_closure_set(v___f_805_, 3, v_inst_795_);
lean_closure_set(v___f_805_, 4, v_lift_796_);
v___x_806_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_805_, v_it_799_, v_init_800_, lean_box(0));
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object* v_inst_807_, lean_object* v_inst_808_){
_start:
{
lean_object* v___f_809_; 
v___f_809_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_809_, 0, v_inst_808_);
lean_closure_set(v___f_809_, 1, v_inst_807_);
return v___f_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_inst_812_, lean_object* v_m_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v___f_815_; 
v___f_815_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_815_, 0, v_inst_814_);
lean_closure_set(v___f_815_, 1, v_inst_812_);
return v___f_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_816_, lean_object* v_range_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_carrier_816_);
lean_ctor_set(v___x_818_, 1, v_range_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_821_; 
v___f_821_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_inst_826_){
_start:
{
lean_object* v___f_827_; 
v___f_827_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_inst_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_828_, v_00_u03b2_829_, v_inst_830_);
lean_dec_ref(v_inst_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_832_){
_start:
{
lean_object* v_treeMap_833_; lean_object* v_range_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_843_; 
v_treeMap_833_ = lean_ctor_get(v_x_832_, 0);
v_range_834_ = lean_ctor_get(v_x_832_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_832_);
if (v_isSharedCheck_843_ == 0)
{
v___x_836_ = v_x_832_;
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_range_834_);
lean_inc(v_treeMap_833_);
lean_dec(v_x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = lean_box(0);
v___x_839_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_833_, v___x_838_);
lean_dec(v_treeMap_833_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_range_834_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_inst_851_){
_start:
{
lean_object* v___f_852_; 
v___f_852_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_853_, lean_object* v_00_u03b2_854_, lean_object* v_inst_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_853_, v_00_u03b2_854_, v_inst_855_);
lean_dec_ref(v_inst_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0(lean_object* v_carrier_857_, lean_object* v_range_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_carrier_857_);
lean_ctor_set(v___x_859_, 1, v_range_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg(){
_start:
{
lean_object* v___f_862_; 
v___f_862_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___boxed(lean_object* v___dummy_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_865_, lean_object* v_inst_866_){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_868_, lean_object* v_inst_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_868_, v_inst_869_);
lean_dec_ref(v_inst_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_871_){
_start:
{
lean_object* v_treeMap_872_; lean_object* v_range_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_882_; 
v_treeMap_872_ = lean_ctor_get(v_x_871_, 0);
v_range_873_ = lean_ctor_get(v_x_871_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_882_ == 0)
{
v___x_875_ = v_x_871_;
v_isShared_876_ = v_isSharedCheck_882_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_range_873_);
lean_inc(v_treeMap_872_);
lean_dec(v_x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_882_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = lean_box(0);
v___x_878_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_872_, v___x_877_);
lean_dec(v_treeMap_872_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_range_873_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_885_; 
v___f_885_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_888_, lean_object* v_inst_889_){
_start:
{
lean_object* v___f_890_; 
v___f_890_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_891_, lean_object* v_inst_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_891_, v_inst_892_);
lean_dec_ref(v_inst_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_894_, lean_object* v_range_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_carrier_894_);
lean_ctor_set(v___x_896_, 1, v_range_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_899_; 
v___f_899_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_inst_904_){
_start:
{
lean_object* v___f_905_; 
v___f_905_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_inst_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_906_, v_00_u03b2_907_, v_inst_908_);
lean_dec_ref(v_inst_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_910_){
_start:
{
lean_object* v_treeMap_911_; lean_object* v_range_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
v_treeMap_911_ = lean_ctor_get(v_x_910_, 0);
v_range_912_ = lean_ctor_get(v_x_910_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_910_);
if (v_isSharedCheck_921_ == 0)
{
v___x_914_ = v_x_910_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_range_912_);
lean_inc(v_treeMap_911_);
lean_dec(v_x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = lean_box(0);
v___x_917_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_911_, v___x_916_);
lean_dec(v_treeMap_911_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_range_912_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_924_; 
v___f_924_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_inst_929_){
_start:
{
lean_object* v___f_930_; 
v___f_930_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_inst_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_931_, v_00_u03b2_932_, v_inst_933_);
lean_dec_ref(v_inst_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_935_, lean_object* v_range_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_carrier_935_);
lean_ctor_set(v___x_937_, 1, v_range_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_940_; 
v___f_940_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_inst_945_){
_start:
{
lean_object* v___f_946_; 
v___f_946_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_947_, lean_object* v_00_u03b2_948_, lean_object* v_inst_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_947_, v_00_u03b2_948_, v_inst_949_);
lean_dec_ref(v_inst_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_951_){
_start:
{
lean_object* v_treeMap_952_; lean_object* v_range_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_962_; 
v_treeMap_952_ = lean_ctor_get(v_x_951_, 0);
v_range_953_ = lean_ctor_get(v_x_951_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_951_);
if (v_isSharedCheck_962_ == 0)
{
v___x_955_ = v_x_951_;
v_isShared_956_ = v_isSharedCheck_962_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_range_953_);
lean_inc(v_treeMap_952_);
lean_dec(v_x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_962_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_957_ = lean_box(0);
v___x_958_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_952_, v___x_957_);
lean_dec(v_treeMap_952_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_range_953_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_965_; 
v___f_965_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_inst_970_){
_start:
{
lean_object* v___f_971_; 
v___f_971_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_972_, lean_object* v_00_u03b2_973_, lean_object* v_inst_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_972_, v_00_u03b2_973_, v_inst_974_);
lean_dec_ref(v_inst_974_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0(lean_object* v_carrier_976_, lean_object* v_range_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v_carrier_976_);
lean_ctor_set(v___x_978_, 1, v_range_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg(){
_start:
{
lean_object* v___f_981_; 
v___f_981_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___boxed(lean_object* v___dummy_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v___f_986_; 
v___f_986_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_987_, lean_object* v_inst_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_987_, v_inst_988_);
lean_dec_ref(v_inst_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_990_){
_start:
{
lean_object* v_treeMap_991_; lean_object* v_range_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1001_; 
v_treeMap_991_ = lean_ctor_get(v_x_990_, 0);
v_range_992_ = lean_ctor_get(v_x_990_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_x_990_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_994_ = v_x_990_;
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_range_992_);
lean_inc(v_treeMap_991_);
lean_dec(v_x_990_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1001_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = lean_box(0);
v___x_997_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_991_, v___x_996_);
lean_dec(v_treeMap_991_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_range_992_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1004_; 
v___f_1004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_1007_, lean_object* v_inst_1008_){
_start:
{
lean_object* v___f_1009_; 
v___f_1009_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_inst_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_1010_, v_inst_1011_);
lean_dec_ref(v_inst_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_1013_, lean_object* v_range_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_carrier_1013_);
lean_ctor_set(v___x_1015_, 1, v_range_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_1018_; 
v___f_1018_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_inst_1023_){
_start:
{
lean_object* v___f_1024_; 
v___f_1024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_inst_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_1025_, v_00_u03b2_1026_, v_inst_1027_);
lean_dec_ref(v_inst_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_1029_){
_start:
{
lean_object* v_treeMap_1030_; lean_object* v_range_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1040_; 
v_treeMap_1030_ = lean_ctor_get(v_x_1029_, 0);
v_range_1031_ = lean_ctor_get(v_x_1029_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_x_1029_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1033_ = v_x_1029_;
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_range_1031_);
lean_inc(v_treeMap_1030_);
lean_dec(v_x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1035_ = lean_box(0);
v___x_1036_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1030_, v___x_1035_);
lean_dec(v_treeMap_1030_);
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
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_range_1031_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1043_; 
v___f_1043_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_inst_1048_){
_start:
{
lean_object* v___f_1049_; 
v___f_1049_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_1050_, v_00_u03b2_1051_, v_inst_1052_);
lean_dec_ref(v_inst_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_1054_, lean_object* v_t_1055_, lean_object* v_lowerBound_1056_, lean_object* v_upperBound_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1054_, v_t_1055_, v_lowerBound_1056_, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_upperBound_1057_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_inst_1063_, lean_object* v_t_1064_, lean_object* v_lowerBound_1065_, lean_object* v_upperBound_1066_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1063_, v_t_1064_, v_lowerBound_1065_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_upperBound_1066_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1070_, lean_object* v_range_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_carrier_1070_);
lean_ctor_set(v___x_1072_, 1, v_range_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1075_; 
v___f_1075_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_){
_start:
{
lean_object* v___f_1081_; 
v___f_1081_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1082_, lean_object* v_00_u03b2_1083_, lean_object* v_inst_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_1082_, v_00_u03b2_1083_, v_inst_1084_);
lean_dec_ref(v_inst_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v_range_1088_; lean_object* v_treeMap_1089_; lean_object* v_lower_1090_; lean_object* v_upper_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1100_; 
v_range_1088_ = lean_ctor_get(v_x_1087_, 1);
lean_inc_ref(v_range_1088_);
v_treeMap_1089_ = lean_ctor_get(v_x_1087_, 0);
lean_inc(v_treeMap_1089_);
lean_dec_ref(v_x_1087_);
v_lower_1090_ = lean_ctor_get(v_range_1088_, 0);
v_upper_1091_ = lean_ctor_get(v_range_1088_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_range_1088_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1093_ = v_range_1088_;
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_upper_1091_);
lean_inc(v_lower_1090_);
lean_dec(v_range_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1086_, v_treeMap_1089_, v_lower_1090_, v___x_1095_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_upper_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_1101_){
_start:
{
lean_object* v___f_1102_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1102_, 0, v_inst_1101_);
return v___f_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_1103_, lean_object* v_00_u03b2_1104_, lean_object* v_inst_1105_){
_start:
{
lean_object* v___f_1106_; 
v___f_1106_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1106_, 0, v_inst_1105_);
return v___f_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0(lean_object* v_carrier_1107_, lean_object* v_range_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v_carrier_1107_);
lean_ctor_set(v___x_1109_, 1, v_range_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg(){
_start:
{
lean_object* v___f_1112_; 
v___f_1112_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___boxed(lean_object* v___dummy_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_1115_, lean_object* v_inst_1116_){
_start:
{
lean_object* v___f_1117_; 
v___f_1117_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_1118_, v_inst_1119_);
lean_dec_ref(v_inst_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v_range_1123_; lean_object* v_treeMap_1124_; lean_object* v_lower_1125_; lean_object* v_upper_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1135_; 
v_range_1123_ = lean_ctor_get(v_x_1122_, 1);
lean_inc_ref(v_range_1123_);
v_treeMap_1124_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_treeMap_1124_);
lean_dec_ref(v_x_1122_);
v_lower_1125_ = lean_ctor_get(v_range_1123_, 0);
v_upper_1126_ = lean_ctor_get(v_range_1123_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_range_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1128_ = v_range_1123_;
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_upper_1126_);
lean_inc(v_lower_1125_);
lean_dec(v_range_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1121_, v_treeMap_1124_, v_lower_1125_, v___x_1130_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_upper_1126_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_1136_){
_start:
{
lean_object* v___f_1137_; 
v___f_1137_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1137_, 0, v_inst_1136_);
return v___f_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v___f_1140_; 
v___f_1140_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1140_, 0, v_inst_1139_);
return v___f_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1141_, lean_object* v_range_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_carrier_1141_);
lean_ctor_set(v___x_1143_, 1, v_range_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1146_; 
v___f_1146_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_inst_1151_){
_start:
{
lean_object* v___f_1152_; 
v___f_1152_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_inst_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_1153_, v_00_u03b2_1154_, v_inst_1155_);
lean_dec_ref(v_inst_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v_range_1159_; lean_object* v_treeMap_1160_; lean_object* v_lower_1161_; lean_object* v_upper_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1171_; 
v_range_1159_ = lean_ctor_get(v_x_1158_, 1);
lean_inc_ref(v_range_1159_);
v_treeMap_1160_ = lean_ctor_get(v_x_1158_, 0);
lean_inc(v_treeMap_1160_);
lean_dec_ref(v_x_1158_);
v_lower_1161_ = lean_ctor_get(v_range_1159_, 0);
v_upper_1162_ = lean_ctor_get(v_range_1159_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_range_1159_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1164_ = v_range_1159_;
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_upper_1162_);
lean_inc(v_lower_1161_);
lean_dec(v_range_1159_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1171_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1157_, v_treeMap_1160_, v_lower_1161_, v___x_1166_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1167_);
v___x_1169_ = v___x_1164_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_upper_1162_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_1172_){
_start:
{
lean_object* v___f_1173_; 
v___f_1173_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1173_, 0, v_inst_1172_);
return v___f_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_inst_1176_){
_start:
{
lean_object* v___f_1177_; 
v___f_1177_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1177_, 0, v_inst_1176_);
return v___f_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_1178_, lean_object* v_t_1179_, lean_object* v_lowerBound_1180_, lean_object* v_upperBound_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1178_, v_t_1179_, v_lowerBound_1180_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_upperBound_1181_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_inst_1187_, lean_object* v_t_1188_, lean_object* v_lowerBound_1189_, lean_object* v_upperBound_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1187_, v_t_1188_, v_lowerBound_1189_, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v_upperBound_1190_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1194_, lean_object* v_range_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_carrier_1194_);
lean_ctor_set(v___x_1196_, 1, v_range_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1199_; 
v___f_1199_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___f_1205_; 
v___f_1205_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1206_, lean_object* v_00_u03b2_1207_, lean_object* v_inst_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_1206_, v_00_u03b2_1207_, v_inst_1208_);
lean_dec_ref(v_inst_1208_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_range_1212_; lean_object* v_treeMap_1213_; lean_object* v_lower_1214_; lean_object* v_upper_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1224_; 
v_range_1212_ = lean_ctor_get(v_x_1211_, 1);
lean_inc_ref(v_range_1212_);
v_treeMap_1213_ = lean_ctor_get(v_x_1211_, 0);
lean_inc(v_treeMap_1213_);
lean_dec_ref(v_x_1211_);
v_lower_1214_ = lean_ctor_get(v_range_1212_, 0);
v_upper_1215_ = lean_ctor_get(v_range_1212_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_range_1212_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1217_ = v_range_1212_;
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_upper_1215_);
lean_inc(v_lower_1214_);
lean_dec(v_range_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1219_ = lean_box(0);
v___x_1220_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1210_, v_treeMap_1213_, v_lower_1214_, v___x_1219_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1222_ = v___x_1217_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_upper_1215_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_1225_){
_start:
{
lean_object* v___f_1226_; 
v___f_1226_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1226_, 0, v_inst_1225_);
return v___f_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v___f_1230_; 
v___f_1230_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1230_, 0, v_inst_1229_);
return v___f_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0(lean_object* v_carrier_1231_, lean_object* v_range_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_carrier_1231_);
lean_ctor_set(v___x_1233_, 1, v_range_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg(){
_start:
{
lean_object* v___f_1236_; 
v___f_1236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___boxed(lean_object* v___dummy_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_1239_, lean_object* v_inst_1240_){
_start:
{
lean_object* v___f_1241_; 
v___f_1241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_1242_, v_inst_1243_);
lean_dec_ref(v_inst_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v_range_1247_; lean_object* v_treeMap_1248_; lean_object* v_lower_1249_; lean_object* v_upper_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1259_; 
v_range_1247_ = lean_ctor_get(v_x_1246_, 1);
lean_inc_ref(v_range_1247_);
v_treeMap_1248_ = lean_ctor_get(v_x_1246_, 0);
lean_inc(v_treeMap_1248_);
lean_dec_ref(v_x_1246_);
v_lower_1249_ = lean_ctor_get(v_range_1247_, 0);
v_upper_1250_ = lean_ctor_get(v_range_1247_, 1);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_range_1247_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1252_ = v_range_1247_;
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_upper_1250_);
lean_inc(v_lower_1249_);
lean_dec(v_range_1247_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1259_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1245_, v_treeMap_1248_, v_lower_1249_, v___x_1254_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1255_);
v___x_1257_ = v___x_1252_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_upper_1250_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1260_){
_start:
{
lean_object* v___f_1261_; 
v___f_1261_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1261_, 0, v_inst_1260_);
return v___f_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1262_, lean_object* v_inst_1263_){
_start:
{
lean_object* v___f_1264_; 
v___f_1264_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1264_, 0, v_inst_1263_);
return v___f_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1265_, lean_object* v_range_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_carrier_1265_);
lean_ctor_set(v___x_1267_, 1, v_range_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1270_; 
v___f_1270_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_inst_1275_){
_start:
{
lean_object* v___f_1276_; 
v___f_1276_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_inst_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1277_, v_00_u03b2_1278_, v_inst_1279_);
lean_dec_ref(v_inst_1279_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1281_, lean_object* v_x_1282_){
_start:
{
lean_object* v_range_1283_; lean_object* v_treeMap_1284_; lean_object* v_lower_1285_; lean_object* v_upper_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1295_; 
v_range_1283_ = lean_ctor_get(v_x_1282_, 1);
lean_inc_ref(v_range_1283_);
v_treeMap_1284_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_treeMap_1284_);
lean_dec_ref(v_x_1282_);
v_lower_1285_ = lean_ctor_get(v_range_1283_, 0);
v_upper_1286_ = lean_ctor_get(v_range_1283_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_range_1283_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1288_ = v_range_1283_;
v_isShared_1289_ = v_isSharedCheck_1295_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_upper_1286_);
lean_inc(v_lower_1285_);
lean_dec(v_range_1283_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1295_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1281_, v_treeMap_1284_, v_lower_1285_, v___x_1290_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_upper_1286_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1296_){
_start:
{
lean_object* v___f_1297_; 
v___f_1297_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1297_, 0, v_inst_1296_);
return v___f_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_inst_1300_){
_start:
{
lean_object* v___f_1301_; 
v___f_1301_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1301_, 0, v_inst_1300_);
return v___f_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1302_, lean_object* v_t_1303_, lean_object* v_lowerBound_1304_, lean_object* v_upperBound_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1302_, v_t_1303_, v_lowerBound_1304_, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v_upperBound_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_inst_1311_, lean_object* v_t_1312_, lean_object* v_lowerBound_1313_, lean_object* v_upperBound_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_box(0);
v___x_1316_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1311_, v_t_1312_, v_lowerBound_1313_, v___x_1315_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v_upperBound_1314_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1318_, lean_object* v_range_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_carrier_1318_);
lean_ctor_set(v___x_1320_, 1, v_range_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1323_; 
v___f_1323_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1326_, lean_object* v_00_u03b2_1327_, lean_object* v_inst_1328_){
_start:
{
lean_object* v___f_1329_; 
v___f_1329_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_inst_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1330_, v_00_u03b2_1331_, v_inst_1332_);
lean_dec_ref(v_inst_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v_range_1336_; lean_object* v_treeMap_1337_; lean_object* v_lower_1338_; lean_object* v_upper_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
v_range_1336_ = lean_ctor_get(v_x_1335_, 1);
lean_inc_ref(v_range_1336_);
v_treeMap_1337_ = lean_ctor_get(v_x_1335_, 0);
lean_inc(v_treeMap_1337_);
lean_dec_ref(v_x_1335_);
v_lower_1338_ = lean_ctor_get(v_range_1336_, 0);
v_upper_1339_ = lean_ctor_get(v_range_1336_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_range_1336_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1341_ = v_range_1336_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_upper_1339_);
lean_inc(v_lower_1338_);
lean_dec(v_range_1336_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1334_, v_treeMap_1337_, v_lower_1338_, v___x_1343_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1344_);
v___x_1346_ = v___x_1341_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_upper_1339_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1349_){
_start:
{
lean_object* v___f_1350_; 
v___f_1350_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1350_, 0, v_inst_1349_);
return v___f_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_inst_1353_){
_start:
{
lean_object* v___f_1354_; 
v___f_1354_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1354_, 0, v_inst_1353_);
return v___f_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0(lean_object* v_carrier_1355_, lean_object* v_range_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_carrier_1355_);
lean_ctor_set(v___x_1357_, 1, v_range_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg(){
_start:
{
lean_object* v___f_1360_; 
v___f_1360_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___boxed(lean_object* v___dummy_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1363_, lean_object* v_inst_1364_){
_start:
{
lean_object* v___f_1365_; 
v___f_1365_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1366_, v_inst_1367_);
lean_dec_ref(v_inst_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v_range_1371_; lean_object* v_treeMap_1372_; lean_object* v_lower_1373_; lean_object* v_upper_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1383_; 
v_range_1371_ = lean_ctor_get(v_x_1370_, 1);
lean_inc_ref(v_range_1371_);
v_treeMap_1372_ = lean_ctor_get(v_x_1370_, 0);
lean_inc(v_treeMap_1372_);
lean_dec_ref(v_x_1370_);
v_lower_1373_ = lean_ctor_get(v_range_1371_, 0);
v_upper_1374_ = lean_ctor_get(v_range_1371_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_range_1371_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1376_ = v_range_1371_;
v_isShared_1377_ = v_isSharedCheck_1383_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_upper_1374_);
lean_inc(v_lower_1373_);
lean_dec(v_range_1371_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1383_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1369_, v_treeMap_1372_, v_lower_1373_, v___x_1378_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1379_);
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_upper_1374_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1384_){
_start:
{
lean_object* v___f_1385_; 
v___f_1385_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1385_, 0, v_inst_1384_);
return v___f_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1386_, lean_object* v_inst_1387_){
_start:
{
lean_object* v___f_1388_; 
v___f_1388_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1388_, 0, v_inst_1387_);
return v___f_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1389_, lean_object* v_range_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_carrier_1389_);
lean_ctor_set(v___x_1391_, 1, v_range_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1394_; 
v___f_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1397_, lean_object* v_00_u03b2_1398_, lean_object* v_inst_1399_){
_start:
{
lean_object* v___f_1400_; 
v___f_1400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_inst_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1401_, v_00_u03b2_1402_, v_inst_1403_);
lean_dec_ref(v_inst_1403_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v_range_1407_; lean_object* v_treeMap_1408_; lean_object* v_lower_1409_; lean_object* v_upper_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1419_; 
v_range_1407_ = lean_ctor_get(v_x_1406_, 1);
lean_inc_ref(v_range_1407_);
v_treeMap_1408_ = lean_ctor_get(v_x_1406_, 0);
lean_inc(v_treeMap_1408_);
lean_dec_ref(v_x_1406_);
v_lower_1409_ = lean_ctor_get(v_range_1407_, 0);
v_upper_1410_ = lean_ctor_get(v_range_1407_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_range_1407_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1412_ = v_range_1407_;
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_upper_1410_);
lean_inc(v_lower_1409_);
lean_dec(v_range_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1405_, v_treeMap_1408_, v_lower_1409_, v___x_1414_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_upper_1410_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1420_){
_start:
{
lean_object* v___f_1421_; 
v___f_1421_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1421_, 0, v_inst_1420_);
return v___f_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_inst_1424_){
_start:
{
lean_object* v___f_1425_; 
v___f_1425_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1425_, 0, v_inst_1424_);
return v___f_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1426_, lean_object* v_t_1427_, lean_object* v_lowerBound_1428_, lean_object* v_upperBound_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1426_, v_t_1427_, v_lowerBound_1428_, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_upperBound_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1433_, lean_object* v_00_u03b2_1434_, lean_object* v_inst_1435_, lean_object* v_t_1436_, lean_object* v_lowerBound_1437_, lean_object* v_upperBound_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_box(0);
v___x_1440_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1435_, v_t_1436_, v_lowerBound_1437_, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v_upperBound_1438_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1442_, lean_object* v_range_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_carrier_1442_);
lean_ctor_set(v___x_1444_, 1, v_range_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1447_; 
v___f_1447_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_inst_1452_){
_start:
{
lean_object* v___f_1453_; 
v___f_1453_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_00_u03b2_1455_, lean_object* v_inst_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1454_, v_00_u03b2_1455_, v_inst_1456_);
lean_dec_ref(v_inst_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1458_, lean_object* v_x_1459_){
_start:
{
lean_object* v_range_1460_; lean_object* v_treeMap_1461_; lean_object* v_lower_1462_; lean_object* v_upper_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1472_; 
v_range_1460_ = lean_ctor_get(v_x_1459_, 1);
lean_inc_ref(v_range_1460_);
v_treeMap_1461_ = lean_ctor_get(v_x_1459_, 0);
lean_inc(v_treeMap_1461_);
lean_dec_ref(v_x_1459_);
v_lower_1462_ = lean_ctor_get(v_range_1460_, 0);
v_upper_1463_ = lean_ctor_get(v_range_1460_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_range_1460_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1465_ = v_range_1460_;
v_isShared_1466_ = v_isSharedCheck_1472_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_upper_1463_);
lean_inc(v_lower_1462_);
lean_dec(v_range_1460_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1472_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1458_, v_treeMap_1461_, v_lower_1462_, v___x_1467_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_upper_1463_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1473_){
_start:
{
lean_object* v___f_1474_; 
v___f_1474_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1474_, 0, v_inst_1473_);
return v___f_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1475_, lean_object* v_00_u03b2_1476_, lean_object* v_inst_1477_){
_start:
{
lean_object* v___f_1478_; 
v___f_1478_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1478_, 0, v_inst_1477_);
return v___f_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0(lean_object* v_carrier_1479_, lean_object* v_range_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_carrier_1479_);
lean_ctor_set(v___x_1481_, 1, v_range_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg(){
_start:
{
lean_object* v___f_1484_; 
v___f_1484_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___boxed(lean_object* v___dummy_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1487_, lean_object* v_inst_1488_){
_start:
{
lean_object* v___f_1489_; 
v___f_1489_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1490_, lean_object* v_inst_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1490_, v_inst_1491_);
lean_dec_ref(v_inst_1491_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_range_1495_; lean_object* v_treeMap_1496_; lean_object* v_lower_1497_; lean_object* v_upper_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1507_; 
v_range_1495_ = lean_ctor_get(v_x_1494_, 1);
lean_inc_ref(v_range_1495_);
v_treeMap_1496_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_treeMap_1496_);
lean_dec_ref(v_x_1494_);
v_lower_1497_ = lean_ctor_get(v_range_1495_, 0);
v_upper_1498_ = lean_ctor_get(v_range_1495_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_range_1495_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1500_ = v_range_1495_;
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_upper_1498_);
lean_inc(v_lower_1497_);
lean_dec(v_range_1495_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1507_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1502_ = lean_box(0);
v___x_1503_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1493_, v_treeMap_1496_, v_lower_1497_, v___x_1502_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1503_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_upper_1498_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1508_){
_start:
{
lean_object* v___f_1509_; 
v___f_1509_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1509_, 0, v_inst_1508_);
return v___f_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1510_, lean_object* v_inst_1511_){
_start:
{
lean_object* v___f_1512_; 
v___f_1512_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1512_, 0, v_inst_1511_);
return v___f_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1513_, lean_object* v_range_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_carrier_1513_);
lean_ctor_set(v___x_1515_, 1, v_range_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1518_; 
v___f_1518_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_inst_1523_){
_start:
{
lean_object* v___f_1524_; 
v___f_1524_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_inst_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1525_, v_00_u03b2_1526_, v_inst_1527_);
lean_dec_ref(v_inst_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1529_, lean_object* v_x_1530_){
_start:
{
lean_object* v_range_1531_; lean_object* v_treeMap_1532_; lean_object* v_lower_1533_; lean_object* v_upper_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1543_; 
v_range_1531_ = lean_ctor_get(v_x_1530_, 1);
lean_inc_ref(v_range_1531_);
v_treeMap_1532_ = lean_ctor_get(v_x_1530_, 0);
lean_inc(v_treeMap_1532_);
lean_dec_ref(v_x_1530_);
v_lower_1533_ = lean_ctor_get(v_range_1531_, 0);
v_upper_1534_ = lean_ctor_get(v_range_1531_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_range_1531_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1536_ = v_range_1531_;
v_isShared_1537_ = v_isSharedCheck_1543_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_upper_1534_);
lean_inc(v_lower_1533_);
lean_dec(v_range_1531_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1543_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1538_ = lean_box(0);
v___x_1539_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1529_, v_treeMap_1532_, v_lower_1533_, v___x_1538_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1539_);
v___x_1541_ = v___x_1536_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_upper_1534_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1544_){
_start:
{
lean_object* v___f_1545_; 
v___f_1545_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1545_, 0, v_inst_1544_);
return v___f_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_inst_1548_){
_start:
{
lean_object* v___f_1549_; 
v___f_1549_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1549_, 0, v_inst_1548_);
return v___f_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1550_, lean_object* v_t_1551_, lean_object* v_lowerBound_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1550_, v_t_1551_, v_lowerBound_1552_, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_inst_1557_, lean_object* v_t_1558_, lean_object* v_lowerBound_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1557_, v_t_1558_, v_lowerBound_1559_, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1562_, lean_object* v_range_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_carrier_1562_);
lean_ctor_set(v___x_1564_, 1, v_range_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1567_; 
v___f_1567_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1570_, lean_object* v_00_u03b2_1571_, lean_object* v_inst_1572_){
_start:
{
lean_object* v___f_1573_; 
v___f_1573_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_inst_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1574_, v_00_u03b2_1575_, v_inst_1576_);
lean_dec_ref(v_inst_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1578_, lean_object* v_x_1579_){
_start:
{
lean_object* v_treeMap_1580_; lean_object* v_range_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_treeMap_1580_ = lean_ctor_get(v_x_1579_, 0);
lean_inc(v_treeMap_1580_);
v_range_1581_ = lean_ctor_get(v_x_1579_, 1);
lean_inc(v_range_1581_);
lean_dec_ref(v_x_1579_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1578_, v_treeMap_1580_, v_range_1581_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1584_){
_start:
{
lean_object* v___f_1585_; 
v___f_1585_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1585_, 0, v_inst_1584_);
return v___f_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_inst_1588_){
_start:
{
lean_object* v___f_1589_; 
v___f_1589_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1589_, 0, v_inst_1588_);
return v___f_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0(lean_object* v_carrier_1590_, lean_object* v_range_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_carrier_1590_);
lean_ctor_set(v___x_1592_, 1, v_range_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg(){
_start:
{
lean_object* v___f_1595_; 
v___f_1595_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___boxed(lean_object* v___dummy_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1598_, lean_object* v_inst_1599_){
_start:
{
lean_object* v___f_1600_; 
v___f_1600_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_inst_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1601_, v_inst_1602_);
lean_dec_ref(v_inst_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v_treeMap_1606_; lean_object* v_range_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_treeMap_1606_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_treeMap_1606_);
v_range_1607_ = lean_ctor_get(v_x_1605_, 1);
lean_inc(v_range_1607_);
lean_dec_ref(v_x_1605_);
v___x_1608_ = lean_box(0);
v___x_1609_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1604_, v_treeMap_1606_, v_range_1607_, v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1610_){
_start:
{
lean_object* v___f_1611_; 
v___f_1611_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1611_, 0, v_inst_1610_);
return v___f_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1612_, lean_object* v_inst_1613_){
_start:
{
lean_object* v___f_1614_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1614_, 0, v_inst_1613_);
return v___f_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1615_, lean_object* v_range_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_carrier_1615_);
lean_ctor_set(v___x_1617_, 1, v_range_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1620_; 
v___f_1620_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_inst_1625_){
_start:
{
lean_object* v___f_1626_; 
v___f_1626_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_inst_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1627_, v_00_u03b2_1628_, v_inst_1629_);
lean_dec_ref(v_inst_1629_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v_treeMap_1633_; lean_object* v_range_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_treeMap_1633_ = lean_ctor_get(v_x_1632_, 0);
lean_inc(v_treeMap_1633_);
v_range_1634_ = lean_ctor_get(v_x_1632_, 1);
lean_inc(v_range_1634_);
lean_dec_ref(v_x_1632_);
v___x_1635_ = lean_box(0);
v___x_1636_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1631_, v_treeMap_1633_, v_range_1634_, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1637_){
_start:
{
lean_object* v___f_1638_; 
v___f_1638_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1638_, 0, v_inst_1637_);
return v___f_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_inst_1641_){
_start:
{
lean_object* v___f_1642_; 
v___f_1642_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1642_, 0, v_inst_1641_);
return v___f_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1643_, lean_object* v_t_1644_, lean_object* v_lowerBound_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1643_, v_t_1644_, v_lowerBound_1645_, v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_inst_1650_, lean_object* v_t_1651_, lean_object* v_lowerBound_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1650_, v_t_1651_, v_lowerBound_1652_, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1655_, lean_object* v_range_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_carrier_1655_);
lean_ctor_set(v___x_1657_, 1, v_range_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1660_; 
v___f_1660_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1663_, lean_object* v_00_u03b2_1664_, lean_object* v_inst_1665_){
_start:
{
lean_object* v___f_1666_; 
v___f_1666_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_00_u03b2_1668_, lean_object* v_inst_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1667_, v_00_u03b2_1668_, v_inst_1669_);
lean_dec_ref(v_inst_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v_treeMap_1673_; lean_object* v_range_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_treeMap_1673_ = lean_ctor_get(v_x_1672_, 0);
lean_inc(v_treeMap_1673_);
v_range_1674_ = lean_ctor_get(v_x_1672_, 1);
lean_inc(v_range_1674_);
lean_dec_ref(v_x_1672_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1671_, v_treeMap_1673_, v_range_1674_, v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1677_){
_start:
{
lean_object* v___f_1678_; 
v___f_1678_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1678_, 0, v_inst_1677_);
return v___f_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_inst_1681_){
_start:
{
lean_object* v___f_1682_; 
v___f_1682_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1682_, 0, v_inst_1681_);
return v___f_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0(lean_object* v_carrier_1683_, lean_object* v_range_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_carrier_1683_);
lean_ctor_set(v___x_1685_, 1, v_range_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg(){
_start:
{
lean_object* v___f_1688_; 
v___f_1688_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___boxed(lean_object* v___dummy_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1691_, lean_object* v_inst_1692_){
_start:
{
lean_object* v___f_1693_; 
v___f_1693_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1694_, lean_object* v_inst_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1694_, v_inst_1695_);
lean_dec_ref(v_inst_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v_treeMap_1699_; lean_object* v_range_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_treeMap_1699_ = lean_ctor_get(v_x_1698_, 0);
lean_inc(v_treeMap_1699_);
v_range_1700_ = lean_ctor_get(v_x_1698_, 1);
lean_inc(v_range_1700_);
lean_dec_ref(v_x_1698_);
v___x_1701_ = lean_box(0);
v___x_1702_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1697_, v_treeMap_1699_, v_range_1700_, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1703_){
_start:
{
lean_object* v___f_1704_; 
v___f_1704_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1704_, 0, v_inst_1703_);
return v___f_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1705_, lean_object* v_inst_1706_){
_start:
{
lean_object* v___f_1707_; 
v___f_1707_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1707_, 0, v_inst_1706_);
return v___f_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1708_, lean_object* v_range_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_carrier_1708_);
lean_ctor_set(v___x_1710_, 1, v_range_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1713_; 
v___f_1713_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_inst_1718_){
_start:
{
lean_object* v___f_1719_; 
v___f_1719_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_inst_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1720_, v_00_u03b2_1721_, v_inst_1722_);
lean_dec_ref(v_inst_1722_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v_treeMap_1726_; lean_object* v_range_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_treeMap_1726_ = lean_ctor_get(v_x_1725_, 0);
lean_inc(v_treeMap_1726_);
v_range_1727_ = lean_ctor_get(v_x_1725_, 1);
lean_inc(v_range_1727_);
lean_dec_ref(v_x_1725_);
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1724_, v_treeMap_1726_, v_range_1727_, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1730_){
_start:
{
lean_object* v___f_1731_; 
v___f_1731_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1731_, 0, v_inst_1730_);
return v___f_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_inst_1734_){
_start:
{
lean_object* v___f_1735_; 
v___f_1735_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1735_, 0, v_inst_1734_);
return v___f_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1736_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_box(0);
v___x_1738_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1736_, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1739_);
lean_dec(v_t_1739_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_t_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_t_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1745_, v_00_u03b2_1746_, v_t_1747_);
lean_dec(v_t_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1749_, lean_object* v_range_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_carrier_1749_);
lean_ctor_set(v___x_1751_, 1, v_range_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1754_; 
v___f_1754_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03b2_1758_){
_start:
{
lean_object* v___f_1759_; 
v___f_1759_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1760_){
_start:
{
lean_object* v_treeMap_1761_; lean_object* v___x_1762_; 
v_treeMap_1761_ = lean_ctor_get(v_x_1760_, 0);
v___x_1762_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(v_x_1763_);
lean_dec_ref(v_x_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1767_; 
v___f_1767_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_){
_start:
{
lean_object* v___f_1772_; 
v___f_1772_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0(lean_object* v_carrier_1773_, lean_object* v_range_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_carrier_1773_);
lean_ctor_set(v___x_1775_, 1, v_range_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg(){
_start:
{
lean_object* v___f_1778_; 
v___f_1778_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___boxed(lean_object* v___dummy_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1781_){
_start:
{
lean_object* v___f_1782_; 
v___f_1782_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1783_){
_start:
{
lean_object* v_treeMap_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_treeMap_1784_ = lean_ctor_get(v_x_1783_, 0);
v___x_1785_ = lean_box(0);
v___x_1786_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1784_, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(v_x_1787_);
lean_dec_ref(v_x_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1791_; 
v___f_1791_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1794_){
_start:
{
lean_object* v___f_1795_; 
v___f_1795_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1796_, lean_object* v_range_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_carrier_1796_);
lean_ctor_set(v___x_1798_, 1, v_range_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1801_; 
v___f_1801_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1804_, lean_object* v_00_u03b2_1805_){
_start:
{
lean_object* v___f_1806_; 
v___f_1806_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1807_){
_start:
{
lean_object* v_treeMap_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_treeMap_1808_ = lean_ctor_get(v_x_1807_, 0);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1808_, v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(v_x_1811_);
lean_dec_ref(v_x_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1815_; 
v___f_1815_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_){
_start:
{
lean_object* v___f_1820_; 
v___f_1820_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1820_;
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
