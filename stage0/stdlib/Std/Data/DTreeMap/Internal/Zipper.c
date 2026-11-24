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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_h__2_116_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_1(v_h__1_115_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_121_; 
lean_dec(v_h__1_115_);
v_head_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc(v_head_119_);
v_tail_120_ = lean_ctor_get(v_x_114_, 1);
lean_inc(v_tail_120_);
lean_dec_ref_known(v_x_114_, 2);
v___x_121_ = lean_apply_2(v_h__2_116_, v_head_119_, v_tail_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_122_, lean_object* v_motive_123_, lean_object* v_x_124_, lean_object* v_h__1_125_, lean_object* v_h__2_126_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_h__2_126_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_apply_1(v_h__1_125_, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___x_131_; 
lean_dec(v_h__1_125_);
v_head_129_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_head_129_);
v_tail_130_ = lean_ctor_get(v_x_124_, 1);
lean_inc(v_tail_130_);
lean_dec_ref_known(v_x_124_, 2);
v___x_131_ = lean_apply_2(v_h__2_126_, v_head_129_, v_tail_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_){
_start:
{
if (v_x_132_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_133_);
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_1(v_h__2_134_, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec(v_h__2_134_);
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_h__1_133_, v___x_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
uint8_t v_x_24__boxed_142_; lean_object* v_res_143_; 
v_x_24__boxed_142_ = lean_unbox(v_x_139_);
v_res_143_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_142_, v_h__1_140_, v_h__2_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object* v_motive_144_, uint8_t v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (v_x_145_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__1_146_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__2_147_, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_h__2_147_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_apply_1(v_h__1_146_, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_152_, lean_object* v_x_153_, lean_object* v_h__1_154_, lean_object* v_h__2_155_){
_start:
{
uint8_t v_x_35__boxed_156_; lean_object* v_res_157_; 
v_x_35__boxed_156_ = lean_unbox(v_x_153_);
v_res_157_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(v_motive_152_, v_x_35__boxed_156_, v_h__1_154_, v_h__2_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_tag_nat(v_x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(v_x_160_);
lean_dec(v_x_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(lean_object* v_00_u03b1_162_, lean_object* v_00_u03b2_163_, lean_object* v_x_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_tag_nat(v_x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(v_00_u03b1_166_, v_00_u03b2_167_, v_x_168_);
lean_dec(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* v_t_170_, lean_object* v_k_171_){
_start:
{
if (lean_obj_tag(v_t_170_) == 0)
{
return v_k_171_;
}
else
{
lean_object* v_k_172_; lean_object* v_v_173_; lean_object* v_tree_174_; lean_object* v_next_175_; lean_object* v___x_176_; 
v_k_172_ = lean_ctor_get(v_t_170_, 0);
lean_inc(v_k_172_);
v_v_173_ = lean_ctor_get(v_t_170_, 1);
lean_inc(v_v_173_);
v_tree_174_ = lean_ctor_get(v_t_170_, 2);
lean_inc(v_tree_174_);
v_next_175_ = lean_ctor_get(v_t_170_, 3);
lean_inc(v_next_175_);
lean_dec_ref_known(v_t_170_, 4);
v___x_176_ = lean_apply_4(v_k_171_, v_k_172_, v_v_173_, v_tree_174_, v_next_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_motive_179_, lean_object* v_ctorIdx_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_k_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_181_, v_k_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(v_00_u03b1_185_, v_00_u03b2_186_, v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* v_t_193_, lean_object* v_done_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_193_, v_done_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_done_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_199_, v_done_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* v_t_203_, lean_object* v_cons_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_203_, v_cons_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_, lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_cons_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_209_, v_cons_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* v_init_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_k_215_; lean_object* v_v_216_; lean_object* v_l_217_; lean_object* v_r_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_k_215_ = lean_ctor_get(v_x_214_, 1);
v_v_216_ = lean_ctor_get(v_x_214_, 2);
v_l_217_ = lean_ctor_get(v_x_214_, 3);
v_r_218_ = lean_ctor_get(v_x_214_, 4);
v___x_219_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_213_, v_r_218_);
lean_inc(v_v_216_);
lean_inc(v_k_215_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_k_215_);
lean_ctor_set(v___x_220_, 1, v_v_216_);
v___x_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
v_init_213_ = v___x_221_;
v_x_214_ = v_l_217_;
goto _start;
}
else
{
return v_init_213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* v_init_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_223_, v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v_k_228_; lean_object* v_v_229_; lean_object* v_tree_230_; lean_object* v_next_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_k_228_ = lean_ctor_get(v_x_226_, 0);
v_v_229_ = lean_ctor_get(v_x_226_, 1);
v_tree_230_ = lean_ctor_get(v_x_226_, 2);
v_next_231_ = lean_ctor_get(v_x_226_, 3);
lean_inc(v_v_229_);
lean_inc(v_k_228_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_k_228_);
lean_ctor_set(v___x_232_, 1, v_v_229_);
v___x_233_ = lean_box(0);
v___x_234_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_233_, v_tree_230_);
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_231_);
v___x_237_ = l_List_appendTR___redArg(v___x_235_, v___x_236_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_238_);
lean_dec(v_x_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* v_00_u03b1_240_, lean_object* v_00_u03b2_241_, lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_x_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_244_, v_00_u03b2_245_, v_x_246_);
lean_dec(v_x_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* v_00_u03b1_248_, lean_object* v_00_u03b2_249_, lean_object* v_init_250_, lean_object* v_x_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_250_, v_x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_init_255_, lean_object* v_x_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(v_00_u03b1_253_, v_00_u03b2_254_, v_init_255_, v_x_256_);
lean_dec(v_x_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v___x_259_; 
v___x_259_ = lean_unsigned_to_nat(0u);
return v___x_259_;
}
else
{
lean_object* v_tree_260_; lean_object* v_next_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_tree_260_ = lean_ctor_get(v_x_258_, 2);
v_next_261_ = lean_ctor_get(v_x_258_, 3);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_260_);
v___x_264_ = lean_nat_add(v___x_262_, v___x_263_);
lean_dec(v___x_263_);
v___x_265_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_261_);
v___x_266_ = lean_nat_add(v___x_264_, v___x_265_);
lean_dec(v___x_265_);
lean_dec(v___x_264_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* v_x_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_267_);
lean_dec(v_x_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(v_00_u03b1_273_, v_00_u03b2_274_, v_x_275_);
lean_dec(v_x_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v_k_279_; lean_object* v_v_280_; lean_object* v_l_281_; lean_object* v_r_282_; lean_object* v___x_283_; 
v_k_279_ = lean_ctor_get(v_x_277_, 1);
v_v_280_ = lean_ctor_get(v_x_277_, 2);
v_l_281_ = lean_ctor_get(v_x_277_, 3);
v_r_282_ = lean_ctor_get(v_x_277_, 4);
lean_inc(v_r_282_);
lean_inc(v_v_280_);
lean_inc(v_k_279_);
v___x_283_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_283_, 0, v_k_279_);
lean_ctor_set(v___x_283_, 1, v_v_280_);
lean_ctor_set(v___x_283_, 2, v_r_282_);
lean_ctor_set(v___x_283_, 3, v_x_278_);
v_x_277_ = v_l_281_;
v_x_278_ = v___x_283_;
goto _start;
}
else
{
return v_x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_285_, v_x_286_);
lean_dec(v_x_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_290_, v_x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DTreeMap_Internal_Zipper_prependMap(v_00_u03b1_293_, v_00_u03b2_294_, v_x_295_, v_x_296_);
lean_dec(v_x_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* v_inst_298_, lean_object* v_t_299_, lean_object* v_lowerBound_300_, lean_object* v_it_301_){
_start:
{
if (lean_obj_tag(v_t_299_) == 0)
{
lean_object* v_k_302_; lean_object* v_v_303_; lean_object* v_l_304_; lean_object* v_r_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_k_302_ = lean_ctor_get(v_t_299_, 1);
lean_inc_n(v_k_302_, 2);
v_v_303_ = lean_ctor_get(v_t_299_, 2);
lean_inc(v_v_303_);
v_l_304_ = lean_ctor_get(v_t_299_, 3);
lean_inc(v_l_304_);
v_r_305_ = lean_ctor_get(v_t_299_, 4);
lean_inc(v_r_305_);
lean_dec_ref_known(v_t_299_, 5);
lean_inc_ref(v_inst_298_);
lean_inc(v_lowerBound_300_);
v___x_306_ = lean_apply_2(v_inst_298_, v_lowerBound_300_, v_k_302_);
v___x_307_ = lean_unbox(v___x_306_);
switch(v___x_307_)
{
case 0:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_308_, 0, v_k_302_);
lean_ctor_set(v___x_308_, 1, v_v_303_);
lean_ctor_set(v___x_308_, 2, v_r_305_);
lean_ctor_set(v___x_308_, 3, v_it_301_);
v_t_299_ = v_l_304_;
v_it_301_ = v___x_308_;
goto _start;
}
case 1:
{
lean_object* v___x_310_; 
lean_dec(v_l_304_);
lean_dec(v_lowerBound_300_);
lean_dec_ref(v_inst_298_);
v___x_310_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_310_, 0, v_k_302_);
lean_ctor_set(v___x_310_, 1, v_v_303_);
lean_ctor_set(v___x_310_, 2, v_r_305_);
lean_ctor_set(v___x_310_, 3, v_it_301_);
return v___x_310_;
}
default: 
{
lean_dec(v_l_304_);
lean_dec(v_v_303_);
lean_dec(v_k_302_);
v_t_299_ = v_r_305_;
goto _start;
}
}
}
else
{
lean_dec(v_lowerBound_300_);
lean_dec_ref(v_inst_298_);
return v_it_301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* v_00_u03b1_312_, lean_object* v_00_u03b2_313_, lean_object* v_inst_314_, lean_object* v_t_315_, lean_object* v_lowerBound_316_, lean_object* v_it_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_314_, v_t_315_, v_lowerBound_316_, v_it_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* v_inst_319_, lean_object* v_t_320_, lean_object* v_lowerBound_321_, lean_object* v_it_322_){
_start:
{
if (lean_obj_tag(v_t_320_) == 0)
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_l_325_; lean_object* v_r_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_k_323_ = lean_ctor_get(v_t_320_, 1);
lean_inc_n(v_k_323_, 2);
v_v_324_ = lean_ctor_get(v_t_320_, 2);
lean_inc(v_v_324_);
v_l_325_ = lean_ctor_get(v_t_320_, 3);
lean_inc(v_l_325_);
v_r_326_ = lean_ctor_get(v_t_320_, 4);
lean_inc(v_r_326_);
lean_dec_ref_known(v_t_320_, 5);
lean_inc_ref(v_inst_319_);
lean_inc(v_lowerBound_321_);
v___x_327_ = lean_apply_2(v_inst_319_, v_lowerBound_321_, v_k_323_);
v___x_328_ = lean_unbox(v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_329_, 0, v_k_323_);
lean_ctor_set(v___x_329_, 1, v_v_324_);
lean_ctor_set(v___x_329_, 2, v_r_326_);
lean_ctor_set(v___x_329_, 3, v_it_322_);
v_t_320_ = v_l_325_;
v_it_322_ = v___x_329_;
goto _start;
}
else
{
lean_dec(v_l_325_);
lean_dec(v_v_324_);
lean_dec(v_k_323_);
v_t_320_ = v_r_326_;
goto _start;
}
}
else
{
lean_dec(v_lowerBound_321_);
lean_dec_ref(v_inst_319_);
return v_it_322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* v_00_u03b1_332_, lean_object* v_00_u03b2_333_, lean_object* v_inst_334_, lean_object* v_t_335_, lean_object* v_lowerBound_336_, lean_object* v_it_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_334_, v_t_335_, v_lowerBound_336_, v_it_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
lean_object* v_size_343_; lean_object* v_k_344_; lean_object* v_v_345_; lean_object* v_l_346_; lean_object* v_r_347_; lean_object* v___x_348_; 
lean_dec(v_h__1_341_);
v_size_343_ = lean_ctor_get(v_x_339_, 0);
lean_inc(v_size_343_);
v_k_344_ = lean_ctor_get(v_x_339_, 1);
lean_inc(v_k_344_);
v_v_345_ = lean_ctor_get(v_x_339_, 2);
lean_inc(v_v_345_);
v_l_346_ = lean_ctor_get(v_x_339_, 3);
lean_inc(v_l_346_);
v_r_347_ = lean_ctor_get(v_x_339_, 4);
lean_inc(v_r_347_);
lean_dec_ref_known(v_x_339_, 5);
v___x_348_ = lean_apply_6(v_h__2_342_, v_size_343_, v_k_344_, v_v_345_, v_l_346_, v_r_347_, v_x_340_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_h__2_342_);
v___x_349_ = lean_apply_1(v_h__1_341_, v_x_340_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_motive_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_){
_start:
{
if (lean_obj_tag(v_x_353_) == 0)
{
lean_object* v_size_357_; lean_object* v_k_358_; lean_object* v_v_359_; lean_object* v_l_360_; lean_object* v_r_361_; lean_object* v___x_362_; 
lean_dec(v_h__1_355_);
v_size_357_ = lean_ctor_get(v_x_353_, 0);
lean_inc(v_size_357_);
v_k_358_ = lean_ctor_get(v_x_353_, 1);
lean_inc(v_k_358_);
v_v_359_ = lean_ctor_get(v_x_353_, 2);
lean_inc(v_v_359_);
v_l_360_ = lean_ctor_get(v_x_353_, 3);
lean_inc(v_l_360_);
v_r_361_ = lean_ctor_get(v_x_353_, 4);
lean_inc(v_r_361_);
lean_dec_ref_known(v_x_353_, 5);
v___x_362_ = lean_apply_6(v_h__2_356_, v_size_357_, v_k_358_, v_v_359_, v_l_360_, v_r_361_, v_x_354_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; 
lean_dec(v_h__2_356_);
v___x_363_ = lean_apply_1(v_h__1_355_, v_x_354_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object* v_x_364_, lean_object* v_h__1_365_, lean_object* v_h__2_366_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v_h__2_366_);
v___x_367_ = lean_box(0);
v___x_368_ = lean_apply_1(v_h__1_365_, v___x_367_);
return v___x_368_;
}
else
{
lean_object* v_k_369_; lean_object* v_v_370_; lean_object* v_tree_371_; lean_object* v_next_372_; lean_object* v___x_373_; 
lean_dec(v_h__1_365_);
v_k_369_ = lean_ctor_get(v_x_364_, 0);
lean_inc(v_k_369_);
v_v_370_ = lean_ctor_get(v_x_364_, 1);
lean_inc(v_v_370_);
v_tree_371_ = lean_ctor_get(v_x_364_, 2);
lean_inc(v_tree_371_);
v_next_372_ = lean_ctor_get(v_x_364_, 3);
lean_inc(v_next_372_);
lean_dec_ref_known(v_x_364_, 4);
v___x_373_ = lean_apply_4(v_h__2_366_, v_k_369_, v_v_370_, v_tree_371_, v_next_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_motive_376_, lean_object* v_x_377_, lean_object* v_h__1_378_, lean_object* v_h__2_379_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_h__2_379_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_apply_1(v_h__1_378_, v___x_380_);
return v___x_381_;
}
else
{
lean_object* v_k_382_; lean_object* v_v_383_; lean_object* v_tree_384_; lean_object* v_next_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_378_);
v_k_382_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_k_382_);
v_v_383_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_v_383_);
v_tree_384_ = lean_ctor_get(v_x_377_, 2);
lean_inc(v_tree_384_);
v_next_385_ = lean_ctor_get(v_x_377_, 3);
lean_inc(v_next_385_);
lean_dec_ref_known(v_x_377_, 4);
v___x_386_ = lean_apply_4(v_h__2_379_, v_k_382_, v_v_383_, v_tree_384_, v_next_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object* v_x_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v_size_390_; lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v_l_393_; lean_object* v_r_394_; lean_object* v___x_395_; 
lean_dec(v_h__1_388_);
v_size_390_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_size_390_);
v_k_391_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_k_391_);
v_v_392_ = lean_ctor_get(v_x_387_, 2);
lean_inc(v_v_392_);
v_l_393_ = lean_ctor_get(v_x_387_, 3);
lean_inc(v_l_393_);
v_r_394_ = lean_ctor_get(v_x_387_, 4);
lean_inc(v_r_394_);
lean_dec_ref_known(v_x_387_, 5);
v___x_395_ = lean_apply_5(v_h__2_389_, v_size_390_, v_k_391_, v_v_392_, v_l_393_, v_r_394_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v_h__2_389_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_apply_1(v_h__1_388_, v___x_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v_motive_400_, lean_object* v_x_401_, lean_object* v_h__1_402_, lean_object* v_h__2_403_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v_size_404_; lean_object* v_k_405_; lean_object* v_v_406_; lean_object* v_l_407_; lean_object* v_r_408_; lean_object* v___x_409_; 
lean_dec(v_h__1_402_);
v_size_404_ = lean_ctor_get(v_x_401_, 0);
lean_inc(v_size_404_);
v_k_405_ = lean_ctor_get(v_x_401_, 1);
lean_inc(v_k_405_);
v_v_406_ = lean_ctor_get(v_x_401_, 2);
lean_inc(v_v_406_);
v_l_407_ = lean_ctor_get(v_x_401_, 3);
lean_inc(v_l_407_);
v_r_408_ = lean_ctor_get(v_x_401_, 4);
lean_inc(v_r_408_);
lean_dec_ref_known(v_x_401_, 5);
v___x_409_ = lean_apply_5(v_h__2_403_, v_size_404_, v_k_405_, v_v_406_, v_l_407_, v_r_408_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_h__2_403_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_apply_1(v_h__1_402_, v___x_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* v_x_412_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v___x_413_; 
v___x_413_ = lean_box(2);
return v___x_413_;
}
else
{
lean_object* v_k_414_; lean_object* v_v_415_; lean_object* v_tree_416_; lean_object* v_next_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_k_414_ = lean_ctor_get(v_x_412_, 0);
lean_inc(v_k_414_);
v_v_415_ = lean_ctor_get(v_x_412_, 1);
lean_inc(v_v_415_);
v_tree_416_ = lean_ctor_get(v_x_412_, 2);
lean_inc(v_tree_416_);
v_next_417_ = lean_ctor_get(v_x_412_, 3);
lean_inc(v_next_417_);
lean_dec_ref_known(v_x_412_, 4);
v___x_418_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_416_, v_next_417_);
lean_dec(v_tree_416_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_k_414_);
lean_ctor_set(v___x_419_, 1, v_v_415_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_x_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg(){
_start:
{
lean_object* v___f_427_; 
v___f_427_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object* v___dummy_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_){
_start:
{
lean_object* v___f_432_; 
v___f_432_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lean_box(0);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg___boxed(lean_object* v___dummy_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_box(0);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_440_, lean_object* v_recur_441_, lean_object* v_it_442_, lean_object* v_____do__lift_443_){
_start:
{
if (lean_obj_tag(v_____do__lift_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_445_; 
lean_dec(v_it_442_);
lean_dec(v_recur_441_);
v_a_444_ = lean_ctor_get(v_____do__lift_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v_____do__lift_443_, 1);
v___x_445_ = lean_apply_2(v_toPure_440_, lean_box(0), v_a_444_);
return v___x_445_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_447_; 
lean_dec(v_toPure_440_);
v_a_446_ = lean_ctor_get(v_____do__lift_443_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v_____do__lift_443_, 1);
v___x_447_ = lean_apply_4(v_recur_441_, v_it_442_, v_a_446_, lean_box(0), lean_box(0));
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_448_, lean_object* v_recur_449_, lean_object* v___y_450_, lean_object* v_acc_451_, lean_object* v_toBind_452_, lean_object* v_s_453_){
_start:
{
switch(lean_obj_tag(v_s_453_))
{
case 0:
{
lean_object* v_it_454_; lean_object* v_out_455_; lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_it_454_ = lean_ctor_get(v_s_453_, 0);
lean_inc(v_it_454_);
v_out_455_ = lean_ctor_get(v_s_453_, 1);
lean_inc(v_out_455_);
lean_dec_ref_known(v_s_453_, 2);
v___f_456_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_456_, 0, v_toPure_448_);
lean_closure_set(v___f_456_, 1, v_recur_449_);
lean_closure_set(v___f_456_, 2, v_it_454_);
v___x_457_ = lean_apply_3(v___y_450_, v_out_455_, lean_box(0), v_acc_451_);
v___x_458_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v___x_457_, v___f_456_);
return v___x_458_;
}
case 1:
{
lean_object* v_it_459_; lean_object* v___x_460_; 
lean_dec(v_toBind_452_);
lean_dec(v___y_450_);
lean_dec(v_toPure_448_);
v_it_459_ = lean_ctor_get(v_s_453_, 0);
lean_inc(v_it_459_);
lean_dec_ref_known(v_s_453_, 1);
v___x_460_ = lean_apply_4(v_recur_449_, v_it_459_, v_acc_451_, lean_box(0), lean_box(0));
return v___x_460_;
}
default: 
{
lean_object* v___x_461_; 
lean_dec(v_toBind_452_);
lean_dec(v___y_450_);
lean_dec(v_recur_449_);
v___x_461_ = lean_apply_2(v_toPure_448_, lean_box(0), v_acc_451_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_462_, lean_object* v___y_463_, lean_object* v_toBind_464_, lean_object* v_lift_465_, lean_object* v_it_466_, lean_object* v_acc_467_, lean_object* v_hP_468_, lean_object* v_recur_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___f_470_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_470_, 0, v_toPure_462_);
lean_closure_set(v___f_470_, 1, v_recur_469_);
lean_closure_set(v___f_470_, 2, v___y_463_);
lean_closure_set(v___f_470_, 3, v_acc_467_);
lean_closure_set(v___f_470_, 4, v_toBind_464_);
v___x_471_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_it_466_);
v___x_472_ = lean_apply_4(v_lift_465_, lean_box(0), lean_box(0), v___f_470_, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_473_, lean_object* v_lift_474_, lean_object* v_00_u03b3_475_, lean_object* v_Pl_476_, lean_object* v_it_477_, lean_object* v_init_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_toApplicative_480_; lean_object* v_toBind_481_; lean_object* v_toPure_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v_toApplicative_480_ = lean_ctor_get(v_inst_473_, 0);
lean_inc_ref(v_toApplicative_480_);
v_toBind_481_ = lean_ctor_get(v_inst_473_, 1);
lean_inc(v_toBind_481_);
lean_dec_ref(v_inst_473_);
v_toPure_482_ = lean_ctor_get(v_toApplicative_480_, 1);
lean_inc(v_toPure_482_);
lean_dec_ref(v_toApplicative_480_);
v___f_483_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_483_, 0, v_toPure_482_);
lean_closure_set(v___f_483_, 1, v___y_479_);
lean_closure_set(v___f_483_, 2, v_toBind_481_);
lean_closure_set(v___f_483_, 3, v_lift_474_);
v___x_484_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_483_, v_it_477_, v_init_478_, lean_box(0));
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object* v_inst_485_){
_start:
{
lean_object* v___f_486_; 
v___f_486_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_486_, 0, v_inst_485_);
return v___f_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object* v_00_u03b1_487_, lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_inst_490_){
_start:
{
lean_object* v___f_491_; 
v___f_491_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_491_, 0, v_inst_490_);
return v___f_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_492_){
_start:
{
lean_inc(v_t_492_);
return v_t_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_493_);
lean_dec(v_t_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_t_497_){
_start:
{
lean_inc(v_t_497_);
return v_t_497_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_t_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_498_, v_00_u03b2_499_, v_t_500_);
lean_dec(v_t_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(0);
v___x_504_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_502_, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_505_);
lean_dec(v_t_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_t_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_t_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_511_, v_00_u03b2_512_, v_t_513_);
lean_dec(v_t_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(lean_object* v_x_515_){
_start:
{
lean_inc(v_x_515_);
return v_x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed(lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(v_x_516_);
lean_dec(v_x_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg(){
_start:
{
lean_object* v___f_520_; 
v___f_520_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___boxed(lean_object* v___dummy_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_523_, lean_object* v_00_u03b2_524_){
_start:
{
lean_object* v___f_525_; 
v___f_525_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_, lean_object* v_h__3_529_){
_start:
{
switch(lean_obj_tag(v_x_526_))
{
case 0:
{
lean_object* v_it_530_; lean_object* v_out_531_; lean_object* v___x_532_; 
lean_dec(v_h__3_529_);
lean_dec(v_h__2_528_);
v_it_530_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_it_530_);
v_out_531_ = lean_ctor_get(v_x_526_, 1);
lean_inc(v_out_531_);
lean_dec_ref_known(v_x_526_, 2);
v___x_532_ = lean_apply_2(v_h__1_527_, v_it_530_, v_out_531_);
return v___x_532_;
}
case 1:
{
lean_object* v_it_533_; lean_object* v___x_534_; 
lean_dec(v_h__3_529_);
lean_dec(v_h__1_527_);
v_it_533_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_it_533_);
lean_dec_ref_known(v_x_526_, 1);
v___x_534_ = lean_apply_1(v_h__2_528_, v_it_533_);
return v___x_534_;
}
default: 
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_h__2_528_);
lean_dec(v_h__1_527_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_apply_1(v_h__3_529_, v___x_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_m_539_, lean_object* v_motive_540_, lean_object* v_x_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_, lean_object* v_h__3_544_){
_start:
{
switch(lean_obj_tag(v_x_541_))
{
case 0:
{
lean_object* v_it_545_; lean_object* v_out_546_; lean_object* v___x_547_; 
lean_dec(v_h__3_544_);
lean_dec(v_h__2_543_);
v_it_545_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_it_545_);
v_out_546_ = lean_ctor_get(v_x_541_, 1);
lean_inc(v_out_546_);
lean_dec_ref_known(v_x_541_, 2);
v___x_547_ = lean_apply_2(v_h__1_542_, v_it_545_, v_out_546_);
return v___x_547_;
}
case 1:
{
lean_object* v_it_548_; lean_object* v___x_549_; 
lean_dec(v_h__3_544_);
lean_dec(v_h__1_542_);
v_it_548_ = lean_ctor_get(v_x_541_, 0);
lean_inc(v_it_548_);
lean_dec_ref_known(v_x_541_, 1);
v___x_549_ = lean_apply_1(v_h__2_543_, v_it_548_);
return v___x_549_;
}
default: 
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_543_);
lean_dec(v_h__1_542_);
v___x_550_ = lean_box(0);
v___x_551_ = lean_apply_1(v_h__3_544_, v___x_550_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_552_, lean_object* v_x_553_){
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
lean_inc_n(v_k_560_, 2);
v_v_561_ = lean_ctor_get(v_iter_554_, 1);
lean_inc(v_v_561_);
v_tree_562_ = lean_ctor_get(v_iter_554_, 2);
lean_inc(v_tree_562_);
v_next_563_ = lean_ctor_get(v_iter_554_, 3);
lean_inc(v_next_563_);
lean_dec_ref_known(v_iter_554_, 4);
lean_inc(v_upper_556_);
v___x_564_ = lean_apply_2(v_inst_552_, v_k_560_, v_upper_556_);
v___x_565_ = lean_unbox(v___x_564_);
if (v___x_565_ == 2)
{
lean_object* v___x_566_; 
lean_dec(v_next_563_);
lean_dec(v_tree_562_);
lean_dec(v_v_561_);
lean_dec(v_k_560_);
lean_del_object(v___x_558_);
lean_dec(v_upper_556_);
v___x_566_ = lean_box(2);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_562_, v_next_563_);
lean_dec(v_tree_562_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_567_);
v___x_569_ = v___x_558_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_upper_556_);
v___x_569_ = v_reuseFailAlloc_572_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_k_560_);
lean_ctor_set(v___x_570_, 1, v_v_561_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b2_576_, lean_object* v_inst_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_580_, lean_object* v_it_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_580_, v_it_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_583_){
_start:
{
lean_object* v___f_584_; 
v___f_584_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_584_, 0, v_inst_583_);
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v___f_588_; 
v___f_588_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_588_, 0, v_inst_587_);
return v___f_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_){
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
lean_dec_ref_known(v_iter_592_, 4);
v___x_600_ = lean_apply_5(v_h__2_591_, v_k_596_, v_v_597_, v_tree_598_, v_next_599_, v_upper_595_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_motive_604_, lean_object* v_x_605_, lean_object* v_h__1_606_, lean_object* v_h__2_607_){
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
lean_dec_ref_known(v_iter_608_, 4);
v___x_616_ = lean_apply_5(v_h__2_607_, v_k_612_, v_v_613_, v_tree_614_, v_next_615_, v_upper_611_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_inst_619_, lean_object* v_motive_620_, lean_object* v_x_621_, lean_object* v_h__1_622_, lean_object* v_h__2_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_617_, v_00_u03b2_618_, v_inst_619_, v_motive_620_, v_x_621_, v_h__1_622_, v_h__2_623_);
lean_dec_ref(v_inst_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_box(0);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg___boxed(lean_object* v___dummy_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_box(0);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_inst_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_633_, v_00_u03b2_634_, v_inst_635_);
lean_dec_ref(v_inst_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_637_, lean_object* v_recur_638_, lean_object* v_it_639_, lean_object* v_____do__lift_640_){
_start:
{
if (lean_obj_tag(v_____do__lift_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; 
lean_dec_ref(v_it_639_);
lean_dec(v_recur_638_);
v_a_641_ = lean_ctor_get(v_____do__lift_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v_____do__lift_640_, 1);
v___x_642_ = lean_apply_2(v_toPure_637_, lean_box(0), v_a_641_);
return v___x_642_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_644_; 
lean_dec(v_toPure_637_);
v_a_643_ = lean_ctor_get(v_____do__lift_640_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v_____do__lift_640_, 1);
v___x_644_ = lean_apply_4(v_recur_638_, v_it_639_, v_a_643_, lean_box(0), lean_box(0));
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_645_, lean_object* v_recur_646_, lean_object* v___y_647_, lean_object* v_acc_648_, lean_object* v_toBind_649_, lean_object* v_s_650_){
_start:
{
switch(lean_obj_tag(v_s_650_))
{
case 0:
{
lean_object* v_it_651_; lean_object* v_out_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_it_651_ = lean_ctor_get(v_s_650_, 0);
lean_inc(v_it_651_);
v_out_652_ = lean_ctor_get(v_s_650_, 1);
lean_inc(v_out_652_);
lean_dec_ref_known(v_s_650_, 2);
v___f_653_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_653_, 0, v_toPure_645_);
lean_closure_set(v___f_653_, 1, v_recur_646_);
lean_closure_set(v___f_653_, 2, v_it_651_);
v___x_654_ = lean_apply_3(v___y_647_, v_out_652_, lean_box(0), v_acc_648_);
v___x_655_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_654_, v___f_653_);
return v___x_655_;
}
case 1:
{
lean_object* v_it_656_; lean_object* v___x_657_; 
lean_dec(v_toBind_649_);
lean_dec(v___y_647_);
lean_dec(v_toPure_645_);
v_it_656_ = lean_ctor_get(v_s_650_, 0);
lean_inc(v_it_656_);
lean_dec_ref_known(v_s_650_, 1);
v___x_657_ = lean_apply_4(v_recur_646_, v_it_656_, v_acc_648_, lean_box(0), lean_box(0));
return v___x_657_;
}
default: 
{
lean_object* v___x_658_; 
lean_dec(v_toBind_649_);
lean_dec(v___y_647_);
lean_dec(v_recur_646_);
v___x_658_ = lean_apply_2(v_toPure_645_, lean_box(0), v_acc_648_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_659_, lean_object* v___y_660_, lean_object* v_toBind_661_, lean_object* v_inst_662_, lean_object* v_lift_663_, lean_object* v_it_664_, lean_object* v_acc_665_, lean_object* v_hP_666_, lean_object* v_recur_667_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___f_668_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_668_, 0, v_toPure_659_);
lean_closure_set(v___f_668_, 1, v_recur_667_);
lean_closure_set(v___f_668_, 2, v___y_660_);
lean_closure_set(v___f_668_, 3, v_acc_665_);
lean_closure_set(v___f_668_, 4, v_toBind_661_);
v___x_669_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_662_, v_it_664_);
v___x_670_ = lean_apply_4(v_lift_663_, lean_box(0), lean_box(0), v___f_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_lift_673_, lean_object* v_00_u03b3_674_, lean_object* v_Pl_675_, lean_object* v_it_676_, lean_object* v_init_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_toApplicative_679_; lean_object* v_toBind_680_; lean_object* v_toPure_681_; lean_object* v___f_682_; lean_object* v___x_683_; 
v_toApplicative_679_ = lean_ctor_get(v_inst_671_, 0);
lean_inc_ref(v_toApplicative_679_);
v_toBind_680_ = lean_ctor_get(v_inst_671_, 1);
lean_inc(v_toBind_680_);
lean_dec_ref(v_inst_671_);
v_toPure_681_ = lean_ctor_get(v_toApplicative_679_, 1);
lean_inc(v_toPure_681_);
lean_dec_ref(v_toApplicative_679_);
v___f_682_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_682_, 0, v_toPure_681_);
lean_closure_set(v___f_682_, 1, v___y_678_);
lean_closure_set(v___f_682_, 2, v_toBind_680_);
lean_closure_set(v___f_682_, 3, v_inst_672_);
lean_closure_set(v___f_682_, 4, v_lift_673_);
v___x_683_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_682_, v_it_676_, v_init_677_, lean_box(0));
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object* v_inst_684_, lean_object* v_inst_685_){
_start:
{
lean_object* v___f_686_; 
v___f_686_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_686_, 0, v_inst_685_);
lean_closure_set(v___f_686_, 1, v_inst_684_);
return v___f_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_inst_689_, lean_object* v_m_690_, lean_object* v_inst_691_){
_start:
{
lean_object* v___f_692_; 
v___f_692_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_692_, 0, v_inst_691_);
lean_closure_set(v___f_692_, 1, v_inst_689_);
return v___f_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_693_, lean_object* v_x_694_){
_start:
{
lean_object* v_iter_695_; 
v_iter_695_ = lean_ctor_get(v_x_694_, 0);
lean_inc(v_iter_695_);
if (lean_obj_tag(v_iter_695_) == 0)
{
lean_object* v___x_696_; 
lean_dec_ref(v_x_694_);
lean_dec_ref(v_inst_693_);
v___x_696_ = lean_box(2);
return v___x_696_;
}
else
{
lean_object* v_upper_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_714_; 
v_upper_697_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v_x_694_, 0);
lean_dec(v_unused_715_);
v___x_699_ = v_x_694_;
v_isShared_700_ = v_isSharedCheck_714_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_upper_697_);
lean_dec(v_x_694_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_714_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v_tree_703_; lean_object* v_next_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_k_701_ = lean_ctor_get(v_iter_695_, 0);
lean_inc_n(v_k_701_, 2);
v_v_702_ = lean_ctor_get(v_iter_695_, 1);
lean_inc(v_v_702_);
v_tree_703_ = lean_ctor_get(v_iter_695_, 2);
lean_inc(v_tree_703_);
v_next_704_ = lean_ctor_get(v_iter_695_, 3);
lean_inc(v_next_704_);
lean_dec_ref_known(v_iter_695_, 4);
lean_inc(v_upper_697_);
v___x_705_ = lean_apply_2(v_inst_693_, v_k_701_, v_upper_697_);
v___x_706_ = lean_unbox(v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_703_, v_next_704_);
lean_dec(v_tree_703_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_707_);
v___x_709_ = v___x_699_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_upper_697_);
v___x_709_ = v_reuseFailAlloc_712_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_k_701_);
lean_ctor_set(v___x_710_, 1, v_v_702_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
return v___x_711_;
}
}
else
{
lean_object* v___x_713_; 
lean_dec(v_next_704_);
lean_dec(v_tree_703_);
lean_dec(v_v_702_);
lean_dec(v_k_701_);
lean_del_object(v___x_699_);
lean_dec(v_upper_697_);
v___x_713_ = lean_box(2);
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_inst_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_721_, lean_object* v_it_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_721_, v_it_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_724_){
_start:
{
lean_object* v___f_725_; 
v___f_725_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_725_, 0, v_inst_724_);
return v___f_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___f_729_; 
v___f_729_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_729_, 0, v_inst_728_);
return v___f_729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_730_, lean_object* v_h__1_731_, lean_object* v_h__2_732_){
_start:
{
lean_object* v_iter_733_; 
v_iter_733_ = lean_ctor_get(v_x_730_, 0);
if (lean_obj_tag(v_iter_733_) == 0)
{
lean_object* v_upper_734_; lean_object* v___x_735_; 
lean_dec(v_h__2_732_);
v_upper_734_ = lean_ctor_get(v_x_730_, 1);
lean_inc(v_upper_734_);
lean_dec_ref(v_x_730_);
v___x_735_ = lean_apply_1(v_h__1_731_, v_upper_734_);
return v___x_735_;
}
else
{
lean_object* v_upper_736_; lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v_tree_739_; lean_object* v_next_740_; lean_object* v___x_741_; 
lean_inc_ref(v_iter_733_);
lean_dec(v_h__1_731_);
v_upper_736_ = lean_ctor_get(v_x_730_, 1);
lean_inc(v_upper_736_);
lean_dec_ref(v_x_730_);
v_k_737_ = lean_ctor_get(v_iter_733_, 0);
lean_inc(v_k_737_);
v_v_738_ = lean_ctor_get(v_iter_733_, 1);
lean_inc(v_v_738_);
v_tree_739_ = lean_ctor_get(v_iter_733_, 2);
lean_inc(v_tree_739_);
v_next_740_ = lean_ctor_get(v_iter_733_, 3);
lean_inc(v_next_740_);
lean_dec_ref_known(v_iter_733_, 4);
v___x_741_ = lean_apply_5(v_h__2_732_, v_k_737_, v_v_738_, v_tree_739_, v_next_740_, v_upper_736_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_inst_744_, lean_object* v_motive_745_, lean_object* v_x_746_, lean_object* v_h__1_747_, lean_object* v_h__2_748_){
_start:
{
lean_object* v_iter_749_; 
v_iter_749_ = lean_ctor_get(v_x_746_, 0);
if (lean_obj_tag(v_iter_749_) == 0)
{
lean_object* v_upper_750_; lean_object* v___x_751_; 
lean_dec(v_h__2_748_);
v_upper_750_ = lean_ctor_get(v_x_746_, 1);
lean_inc(v_upper_750_);
lean_dec_ref(v_x_746_);
v___x_751_ = lean_apply_1(v_h__1_747_, v_upper_750_);
return v___x_751_;
}
else
{
lean_object* v_upper_752_; lean_object* v_k_753_; lean_object* v_v_754_; lean_object* v_tree_755_; lean_object* v_next_756_; lean_object* v___x_757_; 
lean_inc_ref(v_iter_749_);
lean_dec(v_h__1_747_);
v_upper_752_ = lean_ctor_get(v_x_746_, 1);
lean_inc(v_upper_752_);
lean_dec_ref(v_x_746_);
v_k_753_ = lean_ctor_get(v_iter_749_, 0);
lean_inc(v_k_753_);
v_v_754_ = lean_ctor_get(v_iter_749_, 1);
lean_inc(v_v_754_);
v_tree_755_ = lean_ctor_get(v_iter_749_, 2);
lean_inc(v_tree_755_);
v_next_756_ = lean_ctor_get(v_iter_749_, 3);
lean_inc(v_next_756_);
lean_dec_ref_known(v_iter_749_, 4);
v___x_757_ = lean_apply_5(v_h__2_748_, v_k_753_, v_v_754_, v_tree_755_, v_next_756_, v_upper_752_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_758_, lean_object* v_00_u03b2_759_, lean_object* v_inst_760_, lean_object* v_motive_761_, lean_object* v_x_762_, lean_object* v_h__1_763_, lean_object* v_h__2_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_758_, v_00_u03b2_759_, v_inst_760_, v_motive_761_, v_x_762_, v_h__1_763_, v_h__2_764_);
lean_dec_ref(v_inst_760_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_box(0);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_inst_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_box(0);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_inst_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_774_, v_00_u03b2_775_, v_inst_776_);
lean_dec_ref(v_inst_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_778_, lean_object* v_recur_779_, lean_object* v_it_780_, lean_object* v_____do__lift_781_){
_start:
{
if (lean_obj_tag(v_____do__lift_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
lean_dec_ref(v_it_780_);
lean_dec(v_recur_779_);
v_a_782_ = lean_ctor_get(v_____do__lift_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v_____do__lift_781_, 1);
v___x_783_ = lean_apply_2(v_toPure_778_, lean_box(0), v_a_782_);
return v___x_783_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; 
lean_dec(v_toPure_778_);
v_a_784_ = lean_ctor_get(v_____do__lift_781_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v_____do__lift_781_, 1);
v___x_785_ = lean_apply_4(v_recur_779_, v_it_780_, v_a_784_, lean_box(0), lean_box(0));
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_786_, lean_object* v_recur_787_, lean_object* v___y_788_, lean_object* v_acc_789_, lean_object* v_toBind_790_, lean_object* v_s_791_){
_start:
{
switch(lean_obj_tag(v_s_791_))
{
case 0:
{
lean_object* v_it_792_; lean_object* v_out_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_it_792_ = lean_ctor_get(v_s_791_, 0);
lean_inc(v_it_792_);
v_out_793_ = lean_ctor_get(v_s_791_, 1);
lean_inc(v_out_793_);
lean_dec_ref_known(v_s_791_, 2);
v___f_794_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_794_, 0, v_toPure_786_);
lean_closure_set(v___f_794_, 1, v_recur_787_);
lean_closure_set(v___f_794_, 2, v_it_792_);
v___x_795_ = lean_apply_3(v___y_788_, v_out_793_, lean_box(0), v_acc_789_);
v___x_796_ = lean_apply_4(v_toBind_790_, lean_box(0), lean_box(0), v___x_795_, v___f_794_);
return v___x_796_;
}
case 1:
{
lean_object* v_it_797_; lean_object* v___x_798_; 
lean_dec(v_toBind_790_);
lean_dec(v___y_788_);
lean_dec(v_toPure_786_);
v_it_797_ = lean_ctor_get(v_s_791_, 0);
lean_inc(v_it_797_);
lean_dec_ref_known(v_s_791_, 1);
v___x_798_ = lean_apply_4(v_recur_787_, v_it_797_, v_acc_789_, lean_box(0), lean_box(0));
return v___x_798_;
}
default: 
{
lean_object* v___x_799_; 
lean_dec(v_toBind_790_);
lean_dec(v___y_788_);
lean_dec(v_recur_787_);
v___x_799_ = lean_apply_2(v_toPure_786_, lean_box(0), v_acc_789_);
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_800_, lean_object* v___y_801_, lean_object* v_toBind_802_, lean_object* v_inst_803_, lean_object* v_lift_804_, lean_object* v_it_805_, lean_object* v_acc_806_, lean_object* v_hP_807_, lean_object* v_recur_808_){
_start:
{
lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___f_809_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_809_, 0, v_toPure_800_);
lean_closure_set(v___f_809_, 1, v_recur_808_);
lean_closure_set(v___f_809_, 2, v___y_801_);
lean_closure_set(v___f_809_, 3, v_acc_806_);
lean_closure_set(v___f_809_, 4, v_toBind_802_);
v___x_810_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_803_, v_it_805_);
v___x_811_ = lean_apply_4(v_lift_804_, lean_box(0), lean_box(0), v___f_809_, v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_lift_814_, lean_object* v_00_u03b3_815_, lean_object* v_Pl_816_, lean_object* v_it_817_, lean_object* v_init_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_toApplicative_820_; lean_object* v_toBind_821_; lean_object* v_toPure_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
v_toApplicative_820_ = lean_ctor_get(v_inst_812_, 0);
lean_inc_ref(v_toApplicative_820_);
v_toBind_821_ = lean_ctor_get(v_inst_812_, 1);
lean_inc(v_toBind_821_);
lean_dec_ref(v_inst_812_);
v_toPure_822_ = lean_ctor_get(v_toApplicative_820_, 1);
lean_inc(v_toPure_822_);
lean_dec_ref(v_toApplicative_820_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_823_, 0, v_toPure_822_);
lean_closure_set(v___f_823_, 1, v___y_819_);
lean_closure_set(v___f_823_, 2, v_toBind_821_);
lean_closure_set(v___f_823_, 3, v_inst_813_);
lean_closure_set(v___f_823_, 4, v_lift_814_);
v___x_824_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_823_, v_it_817_, v_init_818_, lean_box(0));
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object* v_inst_825_, lean_object* v_inst_826_){
_start:
{
lean_object* v___f_827_; 
v___f_827_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_827_, 0, v_inst_826_);
lean_closure_set(v___f_827_, 1, v_inst_825_);
return v___f_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_inst_830_, lean_object* v_m_831_, lean_object* v_inst_832_){
_start:
{
lean_object* v___f_833_; 
v___f_833_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_833_, 0, v_inst_832_);
lean_closure_set(v___f_833_, 1, v_inst_830_);
return v___f_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_834_, lean_object* v_range_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v_carrier_834_);
lean_ctor_set(v___x_836_, 1, v_range_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_839_; 
v___f_839_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_inst_844_){
_start:
{
lean_object* v___f_845_; 
v___f_845_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_inst_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_846_, v_00_u03b2_847_, v_inst_848_);
lean_dec_ref(v_inst_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_850_){
_start:
{
lean_object* v_treeMap_851_; lean_object* v_range_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
v_treeMap_851_ = lean_ctor_get(v_x_850_, 0);
v_range_852_ = lean_ctor_get(v_x_850_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_861_ == 0)
{
v___x_854_ = v_x_850_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_range_852_);
lean_inc(v_treeMap_851_);
lean_dec(v_x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v___x_857_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_851_, v___x_856_);
lean_dec(v_treeMap_851_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_range_852_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_864_; 
v___f_864_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_867_, lean_object* v_00_u03b2_868_, lean_object* v_inst_869_){
_start:
{
lean_object* v___f_870_; 
v___f_870_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_inst_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_871_, v_00_u03b2_872_, v_inst_873_);
lean_dec_ref(v_inst_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0(lean_object* v_carrier_875_, lean_object* v_range_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_carrier_875_);
lean_ctor_set(v___x_877_, 1, v_range_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg(){
_start:
{
lean_object* v___f_880_; 
v___f_880_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___boxed(lean_object* v___dummy_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_883_, lean_object* v_inst_884_){
_start:
{
lean_object* v___f_885_; 
v___f_885_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_886_, lean_object* v_inst_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_886_, v_inst_887_);
lean_dec_ref(v_inst_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_889_){
_start:
{
lean_object* v_treeMap_890_; lean_object* v_range_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_900_; 
v_treeMap_890_ = lean_ctor_get(v_x_889_, 0);
v_range_891_ = lean_ctor_get(v_x_889_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_x_889_);
if (v_isSharedCheck_900_ == 0)
{
v___x_893_ = v_x_889_;
v_isShared_894_ = v_isSharedCheck_900_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_range_891_);
lean_inc(v_treeMap_890_);
lean_dec(v_x_889_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_900_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_895_ = lean_box(0);
v___x_896_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_890_, v___x_895_);
lean_dec(v_treeMap_890_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_896_);
v___x_898_ = v___x_893_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_range_891_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_903_; 
v___f_903_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_906_, lean_object* v_inst_907_){
_start:
{
lean_object* v___f_908_; 
v___f_908_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_909_, lean_object* v_inst_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_909_, v_inst_910_);
lean_dec_ref(v_inst_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_912_, lean_object* v_range_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_carrier_912_);
lean_ctor_set(v___x_914_, 1, v_range_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_917_; 
v___f_917_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_920_, lean_object* v_00_u03b2_921_, lean_object* v_inst_922_){
_start:
{
lean_object* v___f_923_; 
v___f_923_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_924_, v_00_u03b2_925_, v_inst_926_);
lean_dec_ref(v_inst_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_928_){
_start:
{
lean_object* v_treeMap_929_; lean_object* v_range_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_939_; 
v_treeMap_929_ = lean_ctor_get(v_x_928_, 0);
v_range_930_ = lean_ctor_get(v_x_928_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_928_);
if (v_isSharedCheck_939_ == 0)
{
v___x_932_ = v_x_928_;
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_range_930_);
lean_inc(v_treeMap_929_);
lean_dec(v_x_928_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_939_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = lean_box(0);
v___x_935_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_929_, v___x_934_);
lean_dec(v_treeMap_929_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_range_930_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_942_; 
v___f_942_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_inst_947_){
_start:
{
lean_object* v___f_948_; 
v___f_948_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_949_, lean_object* v_00_u03b2_950_, lean_object* v_inst_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_949_, v_00_u03b2_950_, v_inst_951_);
lean_dec_ref(v_inst_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_953_, lean_object* v_range_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_carrier_953_);
lean_ctor_set(v___x_955_, 1, v_range_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_958_; 
v___f_958_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_961_, lean_object* v_00_u03b2_962_, lean_object* v_inst_963_){
_start:
{
lean_object* v___f_964_; 
v___f_964_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_inst_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_965_, v_00_u03b2_966_, v_inst_967_);
lean_dec_ref(v_inst_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_969_){
_start:
{
lean_object* v_treeMap_970_; lean_object* v_range_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_980_; 
v_treeMap_970_ = lean_ctor_get(v_x_969_, 0);
v_range_971_ = lean_ctor_get(v_x_969_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_x_969_);
if (v_isSharedCheck_980_ == 0)
{
v___x_973_ = v_x_969_;
v_isShared_974_ = v_isSharedCheck_980_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_range_971_);
lean_inc(v_treeMap_970_);
lean_dec(v_x_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_980_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_975_ = lean_box(0);
v___x_976_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_970_, v___x_975_);
lean_dec(v_treeMap_970_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_976_);
v___x_978_ = v___x_973_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_range_971_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_983_; 
v___f_983_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_inst_988_){
_start:
{
lean_object* v___f_989_; 
v___f_989_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_inst_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_990_, v_00_u03b2_991_, v_inst_992_);
lean_dec_ref(v_inst_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0(lean_object* v_carrier_994_, lean_object* v_range_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v_carrier_994_);
lean_ctor_set(v___x_996_, 1, v_range_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg(){
_start:
{
lean_object* v___f_999_; 
v___f_999_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___boxed(lean_object* v___dummy_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_1002_, lean_object* v_inst_1003_){
_start:
{
lean_object* v___f_1004_; 
v___f_1004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_1005_, v_inst_1006_);
lean_dec_ref(v_inst_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_1008_){
_start:
{
lean_object* v_treeMap_1009_; lean_object* v_range_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1019_; 
v_treeMap_1009_ = lean_ctor_get(v_x_1008_, 0);
v_range_1010_ = lean_ctor_get(v_x_1008_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_1008_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1012_ = v_x_1008_;
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_range_1010_);
lean_inc(v_treeMap_1009_);
lean_dec(v_x_1008_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1019_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_box(0);
v___x_1015_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1009_, v___x_1014_);
lean_dec(v_treeMap_1009_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_range_1010_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1022_; 
v___f_1022_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_1025_, lean_object* v_inst_1026_){
_start:
{
lean_object* v___f_1027_; 
v___f_1027_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_inst_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_1028_, v_inst_1029_);
lean_dec_ref(v_inst_1029_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_1031_, lean_object* v_range_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_carrier_1031_);
lean_ctor_set(v___x_1033_, 1, v_range_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_1036_; 
v___f_1036_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_inst_1041_){
_start:
{
lean_object* v___f_1042_; 
v___f_1042_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_1043_, v_00_u03b2_1044_, v_inst_1045_);
lean_dec_ref(v_inst_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_1047_){
_start:
{
lean_object* v_treeMap_1048_; lean_object* v_range_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
v_treeMap_1048_ = lean_ctor_get(v_x_1047_, 0);
v_range_1049_ = lean_ctor_get(v_x_1047_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1051_ = v_x_1047_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_range_1049_);
lean_inc(v_treeMap_1048_);
lean_dec(v_x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1048_, v___x_1053_);
lean_dec(v_treeMap_1048_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1054_);
v___x_1056_ = v___x_1051_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_range_1049_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1061_; 
v___f_1061_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v___f_1067_; 
v___f_1067_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_inst_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_1068_, v_00_u03b2_1069_, v_inst_1070_);
lean_dec_ref(v_inst_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_1072_, lean_object* v_t_1073_, lean_object* v_lowerBound_1074_, lean_object* v_upperBound_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1072_, v_t_1073_, v_lowerBound_1074_, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_upperBound_1075_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_inst_1081_, lean_object* v_t_1082_, lean_object* v_lowerBound_1083_, lean_object* v_upperBound_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1081_, v_t_1082_, v_lowerBound_1083_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_upperBound_1084_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1088_, lean_object* v_range_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_carrier_1088_);
lean_ctor_set(v___x_1090_, 1, v_range_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1093_; 
v___f_1093_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_inst_1098_){
_start:
{
lean_object* v___f_1099_; 
v___f_1099_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1100_, lean_object* v_00_u03b2_1101_, lean_object* v_inst_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_1100_, v_00_u03b2_1101_, v_inst_1102_);
lean_dec_ref(v_inst_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v_range_1106_; lean_object* v_treeMap_1107_; lean_object* v_lower_1108_; lean_object* v_upper_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1118_; 
v_range_1106_ = lean_ctor_get(v_x_1105_, 1);
lean_inc_ref(v_range_1106_);
v_treeMap_1107_ = lean_ctor_get(v_x_1105_, 0);
lean_inc(v_treeMap_1107_);
lean_dec_ref(v_x_1105_);
v_lower_1108_ = lean_ctor_get(v_range_1106_, 0);
v_upper_1109_ = lean_ctor_get(v_range_1106_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_range_1106_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1111_ = v_range_1106_;
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_upper_1109_);
lean_inc(v_lower_1108_);
lean_dec(v_range_1106_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1104_, v_treeMap_1107_, v_lower_1108_, v___x_1113_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1114_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_upper_1109_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_1119_){
_start:
{
lean_object* v___f_1120_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1120_, 0, v_inst_1119_);
return v___f_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_inst_1123_){
_start:
{
lean_object* v___f_1124_; 
v___f_1124_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1124_, 0, v_inst_1123_);
return v___f_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0(lean_object* v_carrier_1125_, lean_object* v_range_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_carrier_1125_);
lean_ctor_set(v___x_1127_, 1, v_range_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg(){
_start:
{
lean_object* v___f_1130_; 
v___f_1130_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___boxed(lean_object* v___dummy_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_1133_, lean_object* v_inst_1134_){
_start:
{
lean_object* v___f_1135_; 
v___f_1135_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_inst_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_1136_, v_inst_1137_);
lean_dec_ref(v_inst_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_range_1141_; lean_object* v_treeMap_1142_; lean_object* v_lower_1143_; lean_object* v_upper_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1153_; 
v_range_1141_ = lean_ctor_get(v_x_1140_, 1);
lean_inc_ref(v_range_1141_);
v_treeMap_1142_ = lean_ctor_get(v_x_1140_, 0);
lean_inc(v_treeMap_1142_);
lean_dec_ref(v_x_1140_);
v_lower_1143_ = lean_ctor_get(v_range_1141_, 0);
v_upper_1144_ = lean_ctor_get(v_range_1141_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_range_1141_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1146_ = v_range_1141_;
v_isShared_1147_ = v_isSharedCheck_1153_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_upper_1144_);
lean_inc(v_lower_1143_);
lean_dec(v_range_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1153_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_box(0);
v___x_1149_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1139_, v_treeMap_1142_, v_lower_1143_, v___x_1148_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_upper_1144_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_1154_){
_start:
{
lean_object* v___f_1155_; 
v___f_1155_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1155_, 0, v_inst_1154_);
return v___f_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v___f_1158_; 
v___f_1158_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1158_, 0, v_inst_1157_);
return v___f_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1159_, lean_object* v_range_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_carrier_1159_);
lean_ctor_set(v___x_1161_, 1, v_range_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1164_; 
v___f_1164_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_1167_, lean_object* v_00_u03b2_1168_, lean_object* v_inst_1169_){
_start:
{
lean_object* v___f_1170_; 
v___f_1170_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_1171_, v_00_u03b2_1172_, v_inst_1173_);
lean_dec_ref(v_inst_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v_range_1177_; lean_object* v_treeMap_1178_; lean_object* v_lower_1179_; lean_object* v_upper_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_range_1177_ = lean_ctor_get(v_x_1176_, 1);
lean_inc_ref(v_range_1177_);
v_treeMap_1178_ = lean_ctor_get(v_x_1176_, 0);
lean_inc(v_treeMap_1178_);
lean_dec_ref(v_x_1176_);
v_lower_1179_ = lean_ctor_get(v_range_1177_, 0);
v_upper_1180_ = lean_ctor_get(v_range_1177_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_range_1177_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v_range_1177_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_upper_1180_);
lean_inc(v_lower_1179_);
lean_dec(v_range_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1175_, v_treeMap_1178_, v_lower_1179_, v___x_1184_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1185_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_upper_1180_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_1190_){
_start:
{
lean_object* v___f_1191_; 
v___f_1191_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1191_, 0, v_inst_1190_);
return v___f_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_inst_1194_){
_start:
{
lean_object* v___f_1195_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1195_, 0, v_inst_1194_);
return v___f_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_1196_, lean_object* v_t_1197_, lean_object* v_lowerBound_1198_, lean_object* v_upperBound_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1196_, v_t_1197_, v_lowerBound_1198_, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_upperBound_1199_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_inst_1205_, lean_object* v_t_1206_, lean_object* v_lowerBound_1207_, lean_object* v_upperBound_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1205_, v_t_1206_, v_lowerBound_1207_, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v_upperBound_1208_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1212_, lean_object* v_range_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v_carrier_1212_);
lean_ctor_set(v___x_1214_, 1, v_range_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1217_; 
v___f_1217_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_){
_start:
{
lean_object* v___f_1223_; 
v___f_1223_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_inst_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_1224_, v_00_u03b2_1225_, v_inst_1226_);
lean_dec_ref(v_inst_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1228_, lean_object* v_x_1229_){
_start:
{
lean_object* v_range_1230_; lean_object* v_treeMap_1231_; lean_object* v_lower_1232_; lean_object* v_upper_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1242_; 
v_range_1230_ = lean_ctor_get(v_x_1229_, 1);
lean_inc_ref(v_range_1230_);
v_treeMap_1231_ = lean_ctor_get(v_x_1229_, 0);
lean_inc(v_treeMap_1231_);
lean_dec_ref(v_x_1229_);
v_lower_1232_ = lean_ctor_get(v_range_1230_, 0);
v_upper_1233_ = lean_ctor_get(v_range_1230_, 1);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_range_1230_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1235_ = v_range_1230_;
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_upper_1233_);
lean_inc(v_lower_1232_);
lean_dec(v_range_1230_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1237_ = lean_box(0);
v___x_1238_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1228_, v_treeMap_1231_, v_lower_1232_, v___x_1237_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_upper_1233_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_1243_){
_start:
{
lean_object* v___f_1244_; 
v___f_1244_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1244_, 0, v_inst_1243_);
return v___f_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v___f_1248_; 
v___f_1248_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1248_, 0, v_inst_1247_);
return v___f_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0(lean_object* v_carrier_1249_, lean_object* v_range_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_carrier_1249_);
lean_ctor_set(v___x_1251_, 1, v_range_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg(){
_start:
{
lean_object* v___f_1254_; 
v___f_1254_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___boxed(lean_object* v___dummy_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___f_1259_; 
v___f_1259_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_inst_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_1260_, v_inst_1261_);
lean_dec_ref(v_inst_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1263_, lean_object* v_x_1264_){
_start:
{
lean_object* v_range_1265_; lean_object* v_treeMap_1266_; lean_object* v_lower_1267_; lean_object* v_upper_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1277_; 
v_range_1265_ = lean_ctor_get(v_x_1264_, 1);
lean_inc_ref(v_range_1265_);
v_treeMap_1266_ = lean_ctor_get(v_x_1264_, 0);
lean_inc(v_treeMap_1266_);
lean_dec_ref(v_x_1264_);
v_lower_1267_ = lean_ctor_get(v_range_1265_, 0);
v_upper_1268_ = lean_ctor_get(v_range_1265_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_range_1265_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1270_ = v_range_1265_;
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_upper_1268_);
lean_inc(v_lower_1267_);
lean_dec(v_range_1265_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = lean_box(0);
v___x_1273_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1263_, v_treeMap_1266_, v_lower_1267_, v___x_1272_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_upper_1268_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1278_){
_start:
{
lean_object* v___f_1279_; 
v___f_1279_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1279_, 0, v_inst_1278_);
return v___f_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v___f_1282_; 
v___f_1282_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1282_, 0, v_inst_1281_);
return v___f_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1283_, lean_object* v_range_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_carrier_1283_);
lean_ctor_set(v___x_1285_, 1, v_range_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1288_; 
v___f_1288_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1291_, lean_object* v_00_u03b2_1292_, lean_object* v_inst_1293_){
_start:
{
lean_object* v___f_1294_; 
v___f_1294_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_inst_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1295_, v_00_u03b2_1296_, v_inst_1297_);
lean_dec_ref(v_inst_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v_range_1301_; lean_object* v_treeMap_1302_; lean_object* v_lower_1303_; lean_object* v_upper_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1313_; 
v_range_1301_ = lean_ctor_get(v_x_1300_, 1);
lean_inc_ref(v_range_1301_);
v_treeMap_1302_ = lean_ctor_get(v_x_1300_, 0);
lean_inc(v_treeMap_1302_);
lean_dec_ref(v_x_1300_);
v_lower_1303_ = lean_ctor_get(v_range_1301_, 0);
v_upper_1304_ = lean_ctor_get(v_range_1301_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_range_1301_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1306_ = v_range_1301_;
v_isShared_1307_ = v_isSharedCheck_1313_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_upper_1304_);
lean_inc(v_lower_1303_);
lean_dec(v_range_1301_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1313_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1308_ = lean_box(0);
v___x_1309_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1299_, v_treeMap_1302_, v_lower_1303_, v___x_1308_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1309_);
v___x_1311_ = v___x_1306_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_upper_1304_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1314_){
_start:
{
lean_object* v___f_1315_; 
v___f_1315_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1315_, 0, v_inst_1314_);
return v___f_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1316_, lean_object* v_00_u03b2_1317_, lean_object* v_inst_1318_){
_start:
{
lean_object* v___f_1319_; 
v___f_1319_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1319_, 0, v_inst_1318_);
return v___f_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1320_, lean_object* v_t_1321_, lean_object* v_lowerBound_1322_, lean_object* v_upperBound_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1320_, v_t_1321_, v_lowerBound_1322_, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v_upperBound_1323_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_inst_1329_, lean_object* v_t_1330_, lean_object* v_lowerBound_1331_, lean_object* v_upperBound_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1329_, v_t_1330_, v_lowerBound_1331_, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v_upperBound_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1336_, lean_object* v_range_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v_carrier_1336_);
lean_ctor_set(v___x_1338_, 1, v_range_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1341_; 
v___f_1341_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1344_, lean_object* v_00_u03b2_1345_, lean_object* v_inst_1346_){
_start:
{
lean_object* v___f_1347_; 
v___f_1347_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_inst_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1348_, v_00_u03b2_1349_, v_inst_1350_);
lean_dec_ref(v_inst_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v_range_1354_; lean_object* v_treeMap_1355_; lean_object* v_lower_1356_; lean_object* v_upper_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1366_; 
v_range_1354_ = lean_ctor_get(v_x_1353_, 1);
lean_inc_ref(v_range_1354_);
v_treeMap_1355_ = lean_ctor_get(v_x_1353_, 0);
lean_inc(v_treeMap_1355_);
lean_dec_ref(v_x_1353_);
v_lower_1356_ = lean_ctor_get(v_range_1354_, 0);
v_upper_1357_ = lean_ctor_get(v_range_1354_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_range_1354_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1359_ = v_range_1354_;
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_upper_1357_);
lean_inc(v_lower_1356_);
lean_dec(v_range_1354_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1352_, v_treeMap_1355_, v_lower_1356_, v___x_1361_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_upper_1357_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1367_){
_start:
{
lean_object* v___f_1368_; 
v___f_1368_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1368_, 0, v_inst_1367_);
return v___f_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_inst_1371_){
_start:
{
lean_object* v___f_1372_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1371_);
return v___f_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0(lean_object* v_carrier_1373_, lean_object* v_range_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_carrier_1373_);
lean_ctor_set(v___x_1375_, 1, v_range_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg(){
_start:
{
lean_object* v___f_1378_; 
v___f_1378_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___boxed(lean_object* v___dummy_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1381_, lean_object* v_inst_1382_){
_start:
{
lean_object* v___f_1383_; 
v___f_1383_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_inst_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1384_, v_inst_1385_);
lean_dec_ref(v_inst_1385_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v_range_1389_; lean_object* v_treeMap_1390_; lean_object* v_lower_1391_; lean_object* v_upper_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1401_; 
v_range_1389_ = lean_ctor_get(v_x_1388_, 1);
lean_inc_ref(v_range_1389_);
v_treeMap_1390_ = lean_ctor_get(v_x_1388_, 0);
lean_inc(v_treeMap_1390_);
lean_dec_ref(v_x_1388_);
v_lower_1391_ = lean_ctor_get(v_range_1389_, 0);
v_upper_1392_ = lean_ctor_get(v_range_1389_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_range_1389_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1394_ = v_range_1389_;
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_upper_1392_);
lean_inc(v_lower_1391_);
lean_dec(v_range_1389_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(0);
v___x_1397_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1387_, v_treeMap_1390_, v_lower_1391_, v___x_1396_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_upper_1392_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1402_){
_start:
{
lean_object* v___f_1403_; 
v___f_1403_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1403_, 0, v_inst_1402_);
return v___f_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1404_, lean_object* v_inst_1405_){
_start:
{
lean_object* v___f_1406_; 
v___f_1406_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1406_, 0, v_inst_1405_);
return v___f_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1407_, lean_object* v_range_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_carrier_1407_);
lean_ctor_set(v___x_1409_, 1, v_range_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1412_; 
v___f_1412_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_inst_1417_){
_start:
{
lean_object* v___f_1418_; 
v___f_1418_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_inst_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1419_, v_00_u03b2_1420_, v_inst_1421_);
lean_dec_ref(v_inst_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v_range_1425_; lean_object* v_treeMap_1426_; lean_object* v_lower_1427_; lean_object* v_upper_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1437_; 
v_range_1425_ = lean_ctor_get(v_x_1424_, 1);
lean_inc_ref(v_range_1425_);
v_treeMap_1426_ = lean_ctor_get(v_x_1424_, 0);
lean_inc(v_treeMap_1426_);
lean_dec_ref(v_x_1424_);
v_lower_1427_ = lean_ctor_get(v_range_1425_, 0);
v_upper_1428_ = lean_ctor_get(v_range_1425_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_range_1425_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1430_ = v_range_1425_;
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_upper_1428_);
lean_inc(v_lower_1427_);
lean_dec(v_range_1425_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1437_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1423_, v_treeMap_1426_, v_lower_1427_, v___x_1432_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1433_);
v___x_1435_ = v___x_1430_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_upper_1428_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1438_){
_start:
{
lean_object* v___f_1439_; 
v___f_1439_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1439_, 0, v_inst_1438_);
return v___f_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_inst_1442_){
_start:
{
lean_object* v___f_1443_; 
v___f_1443_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1443_, 0, v_inst_1442_);
return v___f_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1444_, lean_object* v_t_1445_, lean_object* v_lowerBound_1446_, lean_object* v_upperBound_1447_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1444_, v_t_1445_, v_lowerBound_1446_, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_upperBound_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_inst_1453_, lean_object* v_t_1454_, lean_object* v_lowerBound_1455_, lean_object* v_upperBound_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1453_, v_t_1454_, v_lowerBound_1455_, v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v_upperBound_1456_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1460_, lean_object* v_range_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_carrier_1460_);
lean_ctor_set(v___x_1462_, 1, v_range_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1465_; 
v___f_1465_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_inst_1470_){
_start:
{
lean_object* v___f_1471_; 
v___f_1471_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_inst_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1472_, v_00_u03b2_1473_, v_inst_1474_);
lean_dec_ref(v_inst_1474_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1476_, lean_object* v_x_1477_){
_start:
{
lean_object* v_range_1478_; lean_object* v_treeMap_1479_; lean_object* v_lower_1480_; lean_object* v_upper_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1490_; 
v_range_1478_ = lean_ctor_get(v_x_1477_, 1);
lean_inc_ref(v_range_1478_);
v_treeMap_1479_ = lean_ctor_get(v_x_1477_, 0);
lean_inc(v_treeMap_1479_);
lean_dec_ref(v_x_1477_);
v_lower_1480_ = lean_ctor_get(v_range_1478_, 0);
v_upper_1481_ = lean_ctor_get(v_range_1478_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_range_1478_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1483_ = v_range_1478_;
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_upper_1481_);
lean_inc(v_lower_1480_);
lean_dec(v_range_1478_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1485_ = lean_box(0);
v___x_1486_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1476_, v_treeMap_1479_, v_lower_1480_, v___x_1485_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1488_ = v___x_1483_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_upper_1481_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1491_){
_start:
{
lean_object* v___f_1492_; 
v___f_1492_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1492_, 0, v_inst_1491_);
return v___f_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_inst_1495_){
_start:
{
lean_object* v___f_1496_; 
v___f_1496_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1496_, 0, v_inst_1495_);
return v___f_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0(lean_object* v_carrier_1497_, lean_object* v_range_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_carrier_1497_);
lean_ctor_set(v___x_1499_, 1, v_range_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg(){
_start:
{
lean_object* v___f_1502_; 
v___f_1502_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___boxed(lean_object* v___dummy_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1505_, lean_object* v_inst_1506_){
_start:
{
lean_object* v___f_1507_; 
v___f_1507_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_inst_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1508_, v_inst_1509_);
lean_dec_ref(v_inst_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v_range_1513_; lean_object* v_treeMap_1514_; lean_object* v_lower_1515_; lean_object* v_upper_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1525_; 
v_range_1513_ = lean_ctor_get(v_x_1512_, 1);
lean_inc_ref(v_range_1513_);
v_treeMap_1514_ = lean_ctor_get(v_x_1512_, 0);
lean_inc(v_treeMap_1514_);
lean_dec_ref(v_x_1512_);
v_lower_1515_ = lean_ctor_get(v_range_1513_, 0);
v_upper_1516_ = lean_ctor_get(v_range_1513_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_range_1513_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1518_ = v_range_1513_;
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_upper_1516_);
lean_inc(v_lower_1515_);
lean_dec(v_range_1513_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1511_, v_treeMap_1514_, v_lower_1515_, v___x_1520_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_upper_1516_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1526_){
_start:
{
lean_object* v___f_1527_; 
v___f_1527_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1527_, 0, v_inst_1526_);
return v___f_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1528_, lean_object* v_inst_1529_){
_start:
{
lean_object* v___f_1530_; 
v___f_1530_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1530_, 0, v_inst_1529_);
return v___f_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1531_, lean_object* v_range_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_carrier_1531_);
lean_ctor_set(v___x_1533_, 1, v_range_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1536_; 
v___f_1536_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1539_, lean_object* v_00_u03b2_1540_, lean_object* v_inst_1541_){
_start:
{
lean_object* v___f_1542_; 
v___f_1542_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_00_u03b2_1544_, lean_object* v_inst_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1543_, v_00_u03b2_1544_, v_inst_1545_);
lean_dec_ref(v_inst_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v_range_1549_; lean_object* v_treeMap_1550_; lean_object* v_lower_1551_; lean_object* v_upper_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1561_; 
v_range_1549_ = lean_ctor_get(v_x_1548_, 1);
lean_inc_ref(v_range_1549_);
v_treeMap_1550_ = lean_ctor_get(v_x_1548_, 0);
lean_inc(v_treeMap_1550_);
lean_dec_ref(v_x_1548_);
v_lower_1551_ = lean_ctor_get(v_range_1549_, 0);
v_upper_1552_ = lean_ctor_get(v_range_1549_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_range_1549_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1554_ = v_range_1549_;
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_upper_1552_);
lean_inc(v_lower_1551_);
lean_dec(v_range_1549_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1561_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = lean_box(0);
v___x_1557_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1547_, v_treeMap_1550_, v_lower_1551_, v___x_1556_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_upper_1552_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1562_){
_start:
{
lean_object* v___f_1563_; 
v___f_1563_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1563_, 0, v_inst_1562_);
return v___f_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_inst_1566_){
_start:
{
lean_object* v___f_1567_; 
v___f_1567_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1567_, 0, v_inst_1566_);
return v___f_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1568_, lean_object* v_t_1569_, lean_object* v_lowerBound_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1568_, v_t_1569_, v_lowerBound_1570_, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_inst_1575_, lean_object* v_t_1576_, lean_object* v_lowerBound_1577_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1575_, v_t_1576_, v_lowerBound_1577_, v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1580_, lean_object* v_range_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_carrier_1580_);
lean_ctor_set(v___x_1582_, 1, v_range_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1585_; 
v___f_1585_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_inst_1590_){
_start:
{
lean_object* v___f_1591_; 
v___f_1591_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_00_u03b2_1593_, lean_object* v_inst_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1592_, v_00_u03b2_1593_, v_inst_1594_);
lean_dec_ref(v_inst_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v_treeMap_1598_; lean_object* v_range_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_treeMap_1598_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_treeMap_1598_);
v_range_1599_ = lean_ctor_get(v_x_1597_, 1);
lean_inc(v_range_1599_);
lean_dec_ref(v_x_1597_);
v___x_1600_ = lean_box(0);
v___x_1601_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1596_, v_treeMap_1598_, v_range_1599_, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1602_){
_start:
{
lean_object* v___f_1603_; 
v___f_1603_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1603_, 0, v_inst_1602_);
return v___f_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1604_, lean_object* v_00_u03b2_1605_, lean_object* v_inst_1606_){
_start:
{
lean_object* v___f_1607_; 
v___f_1607_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1607_, 0, v_inst_1606_);
return v___f_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0(lean_object* v_carrier_1608_, lean_object* v_range_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_carrier_1608_);
lean_ctor_set(v___x_1610_, 1, v_range_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg(){
_start:
{
lean_object* v___f_1613_; 
v___f_1613_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___boxed(lean_object* v___dummy_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1616_, lean_object* v_inst_1617_){
_start:
{
lean_object* v___f_1618_; 
v___f_1618_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1619_, lean_object* v_inst_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1619_, v_inst_1620_);
lean_dec_ref(v_inst_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v_treeMap_1624_; lean_object* v_range_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_treeMap_1624_ = lean_ctor_get(v_x_1623_, 0);
lean_inc(v_treeMap_1624_);
v_range_1625_ = lean_ctor_get(v_x_1623_, 1);
lean_inc(v_range_1625_);
lean_dec_ref(v_x_1623_);
v___x_1626_ = lean_box(0);
v___x_1627_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1622_, v_treeMap_1624_, v_range_1625_, v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1628_){
_start:
{
lean_object* v___f_1629_; 
v___f_1629_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1629_, 0, v_inst_1628_);
return v___f_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1630_, lean_object* v_inst_1631_){
_start:
{
lean_object* v___f_1632_; 
v___f_1632_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1632_, 0, v_inst_1631_);
return v___f_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1633_, lean_object* v_range_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_carrier_1633_);
lean_ctor_set(v___x_1635_, 1, v_range_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1638_; 
v___f_1638_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_inst_1643_){
_start:
{
lean_object* v___f_1644_; 
v___f_1644_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_inst_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1645_, v_00_u03b2_1646_, v_inst_1647_);
lean_dec_ref(v_inst_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_treeMap_1651_; lean_object* v_range_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_treeMap_1651_ = lean_ctor_get(v_x_1650_, 0);
lean_inc(v_treeMap_1651_);
v_range_1652_ = lean_ctor_get(v_x_1650_, 1);
lean_inc(v_range_1652_);
lean_dec_ref(v_x_1650_);
v___x_1653_ = lean_box(0);
v___x_1654_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1649_, v_treeMap_1651_, v_range_1652_, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1655_){
_start:
{
lean_object* v___f_1656_; 
v___f_1656_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1656_, 0, v_inst_1655_);
return v___f_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1657_, lean_object* v_00_u03b2_1658_, lean_object* v_inst_1659_){
_start:
{
lean_object* v___f_1660_; 
v___f_1660_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1660_, 0, v_inst_1659_);
return v___f_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1661_, lean_object* v_t_1662_, lean_object* v_lowerBound_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_box(0);
v___x_1665_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1661_, v_t_1662_, v_lowerBound_1663_, v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_inst_1668_, lean_object* v_t_1669_, lean_object* v_lowerBound_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_box(0);
v___x_1672_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1668_, v_t_1669_, v_lowerBound_1670_, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1673_, lean_object* v_range_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_carrier_1673_);
lean_ctor_set(v___x_1675_, 1, v_range_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1678_; 
v___f_1678_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_inst_1683_){
_start:
{
lean_object* v___f_1684_; 
v___f_1684_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_inst_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1685_, v_00_u03b2_1686_, v_inst_1687_);
lean_dec_ref(v_inst_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v_treeMap_1691_; lean_object* v_range_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_treeMap_1691_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_treeMap_1691_);
v_range_1692_ = lean_ctor_get(v_x_1690_, 1);
lean_inc(v_range_1692_);
lean_dec_ref(v_x_1690_);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1689_, v_treeMap_1691_, v_range_1692_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1695_){
_start:
{
lean_object* v___f_1696_; 
v___f_1696_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1696_, 0, v_inst_1695_);
return v___f_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_inst_1699_){
_start:
{
lean_object* v___f_1700_; 
v___f_1700_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1700_, 0, v_inst_1699_);
return v___f_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0(lean_object* v_carrier_1701_, lean_object* v_range_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_carrier_1701_);
lean_ctor_set(v___x_1703_, 1, v_range_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg(){
_start:
{
lean_object* v___f_1706_; 
v___f_1706_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___boxed(lean_object* v___dummy_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1709_, lean_object* v_inst_1710_){
_start:
{
lean_object* v___f_1711_; 
v___f_1711_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_inst_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1712_, v_inst_1713_);
lean_dec_ref(v_inst_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v_treeMap_1717_; lean_object* v_range_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_treeMap_1717_ = lean_ctor_get(v_x_1716_, 0);
lean_inc(v_treeMap_1717_);
v_range_1718_ = lean_ctor_get(v_x_1716_, 1);
lean_inc(v_range_1718_);
lean_dec_ref(v_x_1716_);
v___x_1719_ = lean_box(0);
v___x_1720_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1715_, v_treeMap_1717_, v_range_1718_, v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1721_){
_start:
{
lean_object* v___f_1722_; 
v___f_1722_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1722_, 0, v_inst_1721_);
return v___f_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1723_, lean_object* v_inst_1724_){
_start:
{
lean_object* v___f_1725_; 
v___f_1725_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1725_, 0, v_inst_1724_);
return v___f_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1726_, lean_object* v_range_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_carrier_1726_);
lean_ctor_set(v___x_1728_, 1, v_range_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1731_; 
v___f_1731_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_inst_1736_){
_start:
{
lean_object* v___f_1737_; 
v___f_1737_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_inst_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1738_, v_00_u03b2_1739_, v_inst_1740_);
lean_dec_ref(v_inst_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v_treeMap_1744_; lean_object* v_range_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_treeMap_1744_ = lean_ctor_get(v_x_1743_, 0);
lean_inc(v_treeMap_1744_);
v_range_1745_ = lean_ctor_get(v_x_1743_, 1);
lean_inc(v_range_1745_);
lean_dec_ref(v_x_1743_);
v___x_1746_ = lean_box(0);
v___x_1747_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1742_, v_treeMap_1744_, v_range_1745_, v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1748_){
_start:
{
lean_object* v___f_1749_; 
v___f_1749_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1749_, 0, v_inst_1748_);
return v___f_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1750_, lean_object* v_00_u03b2_1751_, lean_object* v_inst_1752_){
_start:
{
lean_object* v___f_1753_; 
v___f_1753_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1753_, 0, v_inst_1752_);
return v___f_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1754_, v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1757_);
lean_dec(v_t_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_t_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_t_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1763_, v_00_u03b2_1764_, v_t_1765_);
lean_dec(v_t_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1767_, lean_object* v_range_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_carrier_1767_);
lean_ctor_set(v___x_1769_, 1, v_range_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1772_; 
v___f_1772_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1775_, lean_object* v_00_u03b2_1776_){
_start:
{
lean_object* v___f_1777_; 
v___f_1777_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1778_){
_start:
{
lean_object* v_treeMap_1779_; lean_object* v___x_1780_; 
v_treeMap_1779_ = lean_ctor_get(v_x_1778_, 0);
v___x_1780_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(v_x_1781_);
lean_dec_ref(v_x_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1785_; 
v___f_1785_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1788_, lean_object* v_00_u03b2_1789_){
_start:
{
lean_object* v___f_1790_; 
v___f_1790_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0(lean_object* v_carrier_1791_, lean_object* v_range_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_carrier_1791_);
lean_ctor_set(v___x_1793_, 1, v_range_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg(){
_start:
{
lean_object* v___f_1796_; 
v___f_1796_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___boxed(lean_object* v___dummy_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1799_){
_start:
{
lean_object* v___f_1800_; 
v___f_1800_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1801_){
_start:
{
lean_object* v_treeMap_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_treeMap_1802_ = lean_ctor_get(v_x_1801_, 0);
v___x_1803_ = lean_box(0);
v___x_1804_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(v_x_1805_);
lean_dec_ref(v_x_1805_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1809_; 
v___f_1809_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1812_){
_start:
{
lean_object* v___f_1813_; 
v___f_1813_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1814_, lean_object* v_range_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_carrier_1814_);
lean_ctor_set(v___x_1816_, 1, v_range_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1819_; 
v___f_1819_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1822_, lean_object* v_00_u03b2_1823_){
_start:
{
lean_object* v___f_1824_; 
v___f_1824_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1825_){
_start:
{
lean_object* v_treeMap_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_treeMap_1826_ = lean_ctor_get(v_x_1825_, 0);
v___x_1827_ = lean_box(0);
v___x_1828_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1826_, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(v_x_1829_);
lean_dec_ref(v_x_1829_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1833_; 
v___f_1833_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_){
_start:
{
lean_object* v___f_1838_; 
v___f_1838_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1838_;
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
