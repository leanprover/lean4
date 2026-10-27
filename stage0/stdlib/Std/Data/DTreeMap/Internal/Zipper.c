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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Zipper_step___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_){
_start:
{
switch(v_x_55_)
{
case 0:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_h__3_58_);
lean_dec(v_h__2_57_);
v___x_59_ = lean_box(0);
v___x_60_ = lean_apply_1(v_h__1_56_, v___x_59_);
return v___x_60_;
}
case 1:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec(v_h__3_58_);
lean_dec(v_h__1_56_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_apply_1(v_h__2_57_, v___x_61_);
return v___x_62_;
}
default: 
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_h__2_57_);
lean_dec(v_h__1_56_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_apply_1(v_h__3_58_, v___x_63_);
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_, lean_object* v_h__3_68_){
_start:
{
uint8_t v_x_33__boxed_69_; lean_object* v_res_70_; 
v_x_33__boxed_69_ = lean_unbox(v_x_65_);
v_res_70_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_33__boxed_69_, v_h__1_66_, v_h__2_67_, v_h__3_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object* v_motive_71_, uint8_t v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_, lean_object* v_h__3_75_){
_start:
{
switch(v_x_72_)
{
case 0:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_h__3_75_);
lean_dec(v_h__2_74_);
v___x_76_ = lean_box(0);
v___x_77_ = lean_apply_1(v_h__1_73_, v___x_76_);
return v___x_77_;
}
case 1:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__3_75_);
lean_dec(v_h__1_73_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__2_74_, v___x_78_);
return v___x_79_;
}
default: 
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_h__2_74_);
lean_dec(v_h__1_73_);
v___x_80_ = lean_box(0);
v___x_81_ = lean_apply_1(v_h__3_75_, v___x_80_);
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object* v_motive_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_, lean_object* v_h__3_86_){
_start:
{
uint8_t v_x_48__boxed_87_; lean_object* v_res_88_; 
v_x_48__boxed_87_ = lean_unbox(v_x_83_);
v_res_88_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_82_, v_x_48__boxed_87_, v_h__1_84_, v_h__2_85_, v_h__3_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t v_x_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
if (v_x_89_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_apply_1(v_h__2_91_, v___x_92_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__2_91_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__1_90_, v___x_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
uint8_t v_x_24__boxed_99_; lean_object* v_res_100_; 
v_x_24__boxed_99_ = lean_unbox(v_x_96_);
v_res_100_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_99_, v_h__1_97_, v_h__2_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object* v_motive_101_, uint8_t v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
_start:
{
if (v_x_102_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_103_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__2_104_, v___x_105_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_h__2_104_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_1(v_h__1_103_, v___x_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_){
_start:
{
uint8_t v_x_35__boxed_113_; lean_object* v_res_114_; 
v_x_35__boxed_113_ = lean_unbox(v_x_110_);
v_res_114_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(v_motive_109_, v_x_35__boxed_113_, v_h__1_111_, v_h__2_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_tag_nat(v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_tag_nat(v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(v_00_u03b1_123_, v_00_u03b2_124_, v_x_125_);
lean_dec(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* v_t_127_, lean_object* v_k_128_){
_start:
{
if (lean_obj_tag(v_t_127_) == 0)
{
return v_k_128_;
}
else
{
lean_object* v_k_129_; lean_object* v_v_130_; lean_object* v_tree_131_; lean_object* v_next_132_; lean_object* v___x_133_; 
v_k_129_ = lean_ctor_get(v_t_127_, 0);
lean_inc(v_k_129_);
v_v_130_ = lean_ctor_get(v_t_127_, 1);
lean_inc(v_v_130_);
v_tree_131_ = lean_ctor_get(v_t_127_, 2);
lean_inc(v_tree_131_);
v_next_132_ = lean_ctor_get(v_t_127_, 3);
lean_inc(v_next_132_);
lean_dec_ref_known(v_t_127_, 4);
v___x_133_ = lean_apply_4(v_k_128_, v_k_129_, v_v_130_, v_tree_131_, v_next_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_138_, v_k_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(v_00_u03b1_142_, v_00_u03b2_143_, v_motive_144_, v_ctorIdx_145_, v_t_146_, v_h_147_, v_k_148_);
lean_dec(v_ctorIdx_145_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* v_t_150_, lean_object* v_done_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_150_, v_done_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_done_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_156_, v_done_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* v_t_160_, lean_object* v_cons_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_160_, v_cons_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_cons_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_166_, v_cons_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* v_init_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v_k_172_; lean_object* v_v_173_; lean_object* v_l_174_; lean_object* v_r_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_k_172_ = lean_ctor_get(v_x_171_, 1);
v_v_173_ = lean_ctor_get(v_x_171_, 2);
v_l_174_ = lean_ctor_get(v_x_171_, 3);
v_r_175_ = lean_ctor_get(v_x_171_, 4);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_170_, v_r_175_);
lean_inc(v_v_173_);
lean_inc(v_k_172_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_k_172_);
lean_ctor_set(v___x_177_, 1, v_v_173_);
v___x_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
v_init_170_ = v___x_178_;
v_x_171_ = v_l_174_;
goto _start;
}
else
{
return v_init_170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* v_init_180_, lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_180_, v_x_181_);
lean_dec(v_x_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v_k_185_; lean_object* v_v_186_; lean_object* v_tree_187_; lean_object* v_next_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_k_185_ = lean_ctor_get(v_x_183_, 0);
v_v_186_ = lean_ctor_get(v_x_183_, 1);
v_tree_187_ = lean_ctor_get(v_x_183_, 2);
v_next_188_ = lean_ctor_get(v_x_183_, 3);
lean_inc(v_v_186_);
lean_inc(v_k_185_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_k_185_);
lean_ctor_set(v___x_189_, 1, v_v_186_);
v___x_190_ = lean_box(0);
v___x_191_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_190_, v_tree_187_);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_189_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_188_);
v___x_194_ = l_List_appendTR___redArg(v___x_192_, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* v_x_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_195_);
lean_dec(v_x_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_201_, v_00_u03b2_202_, v_x_203_);
lean_dec(v_x_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_init_207_, lean_object* v_x_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_207_, v_x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_init_212_, lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(v_00_u03b1_210_, v_00_u03b2_211_, v_init_212_, v_x_213_);
lean_dec(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(0u);
return v___x_216_;
}
else
{
lean_object* v_tree_217_; lean_object* v_next_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_tree_217_ = lean_ctor_get(v_x_215_, 2);
v_next_218_ = lean_ctor_get(v_x_215_, 3);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_217_);
v___x_221_ = lean_nat_add(v___x_219_, v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_218_);
v___x_223_ = lean_nat_add(v___x_221_, v___x_222_);
lean_dec(v___x_222_);
lean_dec(v___x_221_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_x_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_x_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(v_00_u03b1_230_, v_00_u03b2_231_, v_x_232_);
lean_dec(v_x_232_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_l_238_; lean_object* v_r_239_; lean_object* v___x_240_; 
v_k_236_ = lean_ctor_get(v_x_234_, 1);
v_v_237_ = lean_ctor_get(v_x_234_, 2);
v_l_238_ = lean_ctor_get(v_x_234_, 3);
v_r_239_ = lean_ctor_get(v_x_234_, 4);
lean_inc(v_r_239_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
v___x_240_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_240_, 0, v_k_236_);
lean_ctor_set(v___x_240_, 1, v_v_237_);
lean_ctor_set(v___x_240_, 2, v_r_239_);
lean_ctor_set(v___x_240_, 3, v_x_235_);
v_x_234_ = v_l_238_;
v_x_235_ = v___x_240_;
goto _start;
}
else
{
return v_x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_242_, v_x_243_);
lean_dec(v_x_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_247_, v_x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_DTreeMap_Internal_Zipper_prependMap(v_00_u03b1_250_, v_00_u03b2_251_, v_x_252_, v_x_253_);
lean_dec(v_x_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* v_inst_255_, lean_object* v_t_256_, lean_object* v_lowerBound_257_, lean_object* v_it_258_){
_start:
{
if (lean_obj_tag(v_t_256_) == 0)
{
lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_l_261_; lean_object* v_r_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_k_259_ = lean_ctor_get(v_t_256_, 1);
lean_inc_n(v_k_259_, 2);
v_v_260_ = lean_ctor_get(v_t_256_, 2);
lean_inc(v_v_260_);
v_l_261_ = lean_ctor_get(v_t_256_, 3);
lean_inc(v_l_261_);
v_r_262_ = lean_ctor_get(v_t_256_, 4);
lean_inc(v_r_262_);
lean_dec_ref_known(v_t_256_, 5);
lean_inc_ref(v_inst_255_);
lean_inc(v_lowerBound_257_);
v___x_263_ = lean_apply_2(v_inst_255_, v_lowerBound_257_, v_k_259_);
v___x_264_ = lean_unbox(v___x_263_);
switch(v___x_264_)
{
case 0:
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_265_, 0, v_k_259_);
lean_ctor_set(v___x_265_, 1, v_v_260_);
lean_ctor_set(v___x_265_, 2, v_r_262_);
lean_ctor_set(v___x_265_, 3, v_it_258_);
v_t_256_ = v_l_261_;
v_it_258_ = v___x_265_;
goto _start;
}
case 1:
{
lean_object* v___x_267_; 
lean_dec(v_l_261_);
lean_dec(v_lowerBound_257_);
lean_dec_ref(v_inst_255_);
v___x_267_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_267_, 0, v_k_259_);
lean_ctor_set(v___x_267_, 1, v_v_260_);
lean_ctor_set(v___x_267_, 2, v_r_262_);
lean_ctor_set(v___x_267_, 3, v_it_258_);
return v___x_267_;
}
default: 
{
lean_dec(v_l_261_);
lean_dec(v_v_260_);
lean_dec(v_k_259_);
v_t_256_ = v_r_262_;
goto _start;
}
}
}
else
{
lean_dec(v_lowerBound_257_);
lean_dec_ref(v_inst_255_);
return v_it_258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_t_272_, lean_object* v_lowerBound_273_, lean_object* v_it_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_271_, v_t_272_, v_lowerBound_273_, v_it_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* v_inst_276_, lean_object* v_t_277_, lean_object* v_lowerBound_278_, lean_object* v_it_279_){
_start:
{
if (lean_obj_tag(v_t_277_) == 0)
{
lean_object* v_k_280_; lean_object* v_v_281_; lean_object* v_l_282_; lean_object* v_r_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_k_280_ = lean_ctor_get(v_t_277_, 1);
lean_inc_n(v_k_280_, 2);
v_v_281_ = lean_ctor_get(v_t_277_, 2);
lean_inc(v_v_281_);
v_l_282_ = lean_ctor_get(v_t_277_, 3);
lean_inc(v_l_282_);
v_r_283_ = lean_ctor_get(v_t_277_, 4);
lean_inc(v_r_283_);
lean_dec_ref_known(v_t_277_, 5);
lean_inc_ref(v_inst_276_);
lean_inc(v_lowerBound_278_);
v___x_284_ = lean_apply_2(v_inst_276_, v_lowerBound_278_, v_k_280_);
v___x_285_ = lean_unbox(v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_286_, 0, v_k_280_);
lean_ctor_set(v___x_286_, 1, v_v_281_);
lean_ctor_set(v___x_286_, 2, v_r_283_);
lean_ctor_set(v___x_286_, 3, v_it_279_);
v_t_277_ = v_l_282_;
v_it_279_ = v___x_286_;
goto _start;
}
else
{
lean_dec(v_l_282_);
lean_dec(v_v_281_);
lean_dec(v_k_280_);
v_t_277_ = v_r_283_;
goto _start;
}
}
else
{
lean_dec(v_lowerBound_278_);
lean_dec_ref(v_inst_276_);
return v_it_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_inst_291_, lean_object* v_t_292_, lean_object* v_lowerBound_293_, lean_object* v_it_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_291_, v_t_292_, v_lowerBound_293_, v_it_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
lean_object* v_size_300_; lean_object* v_k_301_; lean_object* v_v_302_; lean_object* v_l_303_; lean_object* v_r_304_; lean_object* v___x_305_; 
lean_dec(v_h__1_298_);
v_size_300_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_size_300_);
v_k_301_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_k_301_);
v_v_302_ = lean_ctor_get(v_x_296_, 2);
lean_inc(v_v_302_);
v_l_303_ = lean_ctor_get(v_x_296_, 3);
lean_inc(v_l_303_);
v_r_304_ = lean_ctor_get(v_x_296_, 4);
lean_inc(v_r_304_);
lean_dec_ref_known(v_x_296_, 5);
v___x_305_ = lean_apply_6(v_h__2_299_, v_size_300_, v_k_301_, v_v_302_, v_l_303_, v_r_304_, v_x_297_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec(v_h__2_299_);
v___x_306_ = lean_apply_1(v_h__1_298_, v_x_297_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* v_00_u03b1_307_, lean_object* v_00_u03b2_308_, lean_object* v_motive_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_){
_start:
{
if (lean_obj_tag(v_x_310_) == 0)
{
lean_object* v_size_314_; lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v_l_317_; lean_object* v_r_318_; lean_object* v___x_319_; 
lean_dec(v_h__1_312_);
v_size_314_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_size_314_);
v_k_315_ = lean_ctor_get(v_x_310_, 1);
lean_inc(v_k_315_);
v_v_316_ = lean_ctor_get(v_x_310_, 2);
lean_inc(v_v_316_);
v_l_317_ = lean_ctor_get(v_x_310_, 3);
lean_inc(v_l_317_);
v_r_318_ = lean_ctor_get(v_x_310_, 4);
lean_inc(v_r_318_);
lean_dec_ref_known(v_x_310_, 5);
v___x_319_ = lean_apply_6(v_h__2_313_, v_size_314_, v_k_315_, v_v_316_, v_l_317_, v_r_318_, v_x_311_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; 
lean_dec(v_h__2_313_);
v___x_320_ = lean_apply_1(v_h__1_312_, v_x_311_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(2);
return v___x_322_;
}
else
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_tree_325_; lean_object* v_next_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_k_323_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_k_323_);
v_v_324_ = lean_ctor_get(v_x_321_, 1);
lean_inc(v_v_324_);
v_tree_325_ = lean_ctor_get(v_x_321_, 2);
lean_inc(v_tree_325_);
v_next_326_ = lean_ctor_get(v_x_321_, 3);
lean_inc(v_next_326_);
lean_dec_ref_known(v_x_321_, 4);
v___x_327_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_325_, v_next_326_);
lean_dec(v_tree_325_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_k_323_);
lean_ctor_set(v___x_328_, 1, v_v_324_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg(){
_start:
{
lean_object* v___f_336_; 
v___f_336_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object* v___dummy_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_){
_start:
{
lean_object* v___f_341_; 
v___f_341_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object* v_x_342_, lean_object* v_h__1_343_, lean_object* v_h__2_344_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_h__2_344_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_apply_1(v_h__1_343_, v___x_345_);
return v___x_346_;
}
else
{
lean_object* v_k_347_; lean_object* v_v_348_; lean_object* v_tree_349_; lean_object* v_next_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_343_);
v_k_347_ = lean_ctor_get(v_x_342_, 0);
lean_inc(v_k_347_);
v_v_348_ = lean_ctor_get(v_x_342_, 1);
lean_inc(v_v_348_);
v_tree_349_ = lean_ctor_get(v_x_342_, 2);
lean_inc(v_tree_349_);
v_next_350_ = lean_ctor_get(v_x_342_, 3);
lean_inc(v_next_350_);
lean_dec_ref_known(v_x_342_, 4);
v___x_351_ = lean_apply_4(v_h__2_344_, v_k_347_, v_v_348_, v_tree_349_, v_next_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object* v_00_u03b1_352_, lean_object* v_00_u03b2_353_, lean_object* v_motive_354_, lean_object* v_x_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_h__2_357_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_apply_1(v_h__1_356_, v___x_358_);
return v___x_359_;
}
else
{
lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v_tree_362_; lean_object* v_next_363_; lean_object* v___x_364_; 
lean_dec(v_h__1_356_);
v_k_360_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_k_360_);
v_v_361_ = lean_ctor_get(v_x_355_, 1);
lean_inc(v_v_361_);
v_tree_362_ = lean_ctor_get(v_x_355_, 2);
lean_inc(v_tree_362_);
v_next_363_ = lean_ctor_get(v_x_355_, 3);
lean_inc(v_next_363_);
lean_dec_ref_known(v_x_355_, 4);
v___x_364_ = lean_apply_4(v_h__2_357_, v_k_360_, v_v_361_, v_tree_362_, v_next_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg___boxed(lean_object* v___dummy_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_372_, lean_object* v_recur_373_, lean_object* v_it_374_, lean_object* v_____do__lift_375_){
_start:
{
if (lean_obj_tag(v_____do__lift_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; 
lean_dec(v_it_374_);
lean_dec(v_recur_373_);
v_a_376_ = lean_ctor_get(v_____do__lift_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v_____do__lift_375_, 1);
v___x_377_ = lean_apply_2(v_toPure_372_, lean_box(0), v_a_376_);
return v___x_377_;
}
else
{
lean_object* v_a_378_; lean_object* v___x_379_; 
lean_dec(v_toPure_372_);
v_a_378_ = lean_ctor_get(v_____do__lift_375_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v_____do__lift_375_, 1);
v___x_379_ = lean_apply_4(v_recur_373_, v_it_374_, v_a_378_, lean_box(0), lean_box(0));
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_380_, lean_object* v_recur_381_, lean_object* v___y_382_, lean_object* v_acc_383_, lean_object* v_toBind_384_, lean_object* v_s_385_){
_start:
{
switch(lean_obj_tag(v_s_385_))
{
case 0:
{
lean_object* v_it_386_; lean_object* v_out_387_; lean_object* v___f_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_it_386_ = lean_ctor_get(v_s_385_, 0);
lean_inc(v_it_386_);
v_out_387_ = lean_ctor_get(v_s_385_, 1);
lean_inc(v_out_387_);
lean_dec_ref_known(v_s_385_, 2);
v___f_388_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_388_, 0, v_toPure_380_);
lean_closure_set(v___f_388_, 1, v_recur_381_);
lean_closure_set(v___f_388_, 2, v_it_386_);
v___x_389_ = lean_apply_3(v___y_382_, v_out_387_, lean_box(0), v_acc_383_);
v___x_390_ = lean_apply_4(v_toBind_384_, lean_box(0), lean_box(0), v___x_389_, v___f_388_);
return v___x_390_;
}
case 1:
{
lean_object* v_it_391_; lean_object* v___x_392_; 
lean_dec(v_toBind_384_);
lean_dec(v___y_382_);
lean_dec(v_toPure_380_);
v_it_391_ = lean_ctor_get(v_s_385_, 0);
lean_inc(v_it_391_);
lean_dec_ref_known(v_s_385_, 1);
v___x_392_ = lean_apply_4(v_recur_381_, v_it_391_, v_acc_383_, lean_box(0), lean_box(0));
return v___x_392_;
}
default: 
{
lean_object* v___x_393_; 
lean_dec(v_toBind_384_);
lean_dec(v___y_382_);
lean_dec(v_recur_381_);
v___x_393_ = lean_apply_2(v_toPure_380_, lean_box(0), v_acc_383_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_394_, lean_object* v___y_395_, lean_object* v_toBind_396_, lean_object* v_lift_397_, lean_object* v_it_398_, lean_object* v_acc_399_, lean_object* v_hP_400_, lean_object* v_recur_401_){
_start:
{
lean_object* v___f_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___f_402_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_402_, 0, v_toPure_394_);
lean_closure_set(v___f_402_, 1, v_recur_401_);
lean_closure_set(v___f_402_, 2, v___y_395_);
lean_closure_set(v___f_402_, 3, v_acc_399_);
lean_closure_set(v___f_402_, 4, v_toBind_396_);
v___x_403_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_it_398_);
v___x_404_ = lean_apply_4(v_lift_397_, lean_box(0), lean_box(0), v___f_402_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_405_, lean_object* v_lift_406_, lean_object* v_00_u03b3_407_, lean_object* v_Pl_408_, lean_object* v_it_409_, lean_object* v_init_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_toApplicative_412_; lean_object* v_toBind_413_; lean_object* v_toPure_414_; lean_object* v___f_415_; lean_object* v___x_416_; 
v_toApplicative_412_ = lean_ctor_get(v_inst_405_, 0);
lean_inc_ref(v_toApplicative_412_);
v_toBind_413_ = lean_ctor_get(v_inst_405_, 1);
lean_inc(v_toBind_413_);
lean_dec_ref(v_inst_405_);
v_toPure_414_ = lean_ctor_get(v_toApplicative_412_, 1);
lean_inc(v_toPure_414_);
lean_dec_ref(v_toApplicative_412_);
v___f_415_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_415_, 0, v_toPure_414_);
lean_closure_set(v___f_415_, 1, v___y_411_);
lean_closure_set(v___f_415_, 2, v_toBind_413_);
lean_closure_set(v___f_415_, 3, v_lift_406_);
v___x_416_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_415_, v_it_409_, v_init_410_, lean_box(0));
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object* v_inst_417_){
_start:
{
lean_object* v___f_418_; 
v___f_418_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_418_, 0, v_inst_417_);
return v___f_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v___f_423_; 
v___f_423_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_423_, 0, v_inst_422_);
return v___f_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_424_){
_start:
{
lean_inc(v_t_424_);
return v_t_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_425_);
lean_dec(v_t_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_t_429_){
_start:
{
lean_inc(v_t_429_);
return v_t_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_t_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_430_, v_00_u03b2_431_, v_t_432_);
lean_dec(v_t_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_box(0);
v___x_436_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_437_);
lean_dec(v_t_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b2_440_, lean_object* v_t_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_443_, lean_object* v_00_u03b2_444_, lean_object* v_t_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_443_, v_00_u03b2_444_, v_t_445_);
lean_dec(v_t_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(lean_object* v_x_447_){
_start:
{
lean_inc(v_x_447_);
return v_x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed(lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(v_x_448_);
lean_dec(v_x_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg(){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___boxed(lean_object* v___dummy_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_){
_start:
{
lean_object* v___f_457_; 
v___f_457_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_, lean_object* v_h__3_461_){
_start:
{
switch(lean_obj_tag(v_x_458_))
{
case 0:
{
lean_object* v_it_462_; lean_object* v_out_463_; lean_object* v___x_464_; 
lean_dec(v_h__3_461_);
lean_dec(v_h__2_460_);
v_it_462_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_it_462_);
v_out_463_ = lean_ctor_get(v_x_458_, 1);
lean_inc(v_out_463_);
lean_dec_ref_known(v_x_458_, 2);
v___x_464_ = lean_apply_2(v_h__1_459_, v_it_462_, v_out_463_);
return v___x_464_;
}
case 1:
{
lean_object* v_it_465_; lean_object* v___x_466_; 
lean_dec(v_h__3_461_);
lean_dec(v_h__1_459_);
v_it_465_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_it_465_);
lean_dec_ref_known(v_x_458_, 1);
v___x_466_ = lean_apply_1(v_h__2_460_, v_it_465_);
return v___x_466_;
}
default: 
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_h__2_460_);
lean_dec(v_h__1_459_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_apply_1(v_h__3_461_, v___x_467_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_m_471_, lean_object* v_motive_472_, lean_object* v_x_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_, lean_object* v_h__3_476_){
_start:
{
switch(lean_obj_tag(v_x_473_))
{
case 0:
{
lean_object* v_it_477_; lean_object* v_out_478_; lean_object* v___x_479_; 
lean_dec(v_h__3_476_);
lean_dec(v_h__2_475_);
v_it_477_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_it_477_);
v_out_478_ = lean_ctor_get(v_x_473_, 1);
lean_inc(v_out_478_);
lean_dec_ref_known(v_x_473_, 2);
v___x_479_ = lean_apply_2(v_h__1_474_, v_it_477_, v_out_478_);
return v___x_479_;
}
case 1:
{
lean_object* v_it_480_; lean_object* v___x_481_; 
lean_dec(v_h__3_476_);
lean_dec(v_h__1_474_);
v_it_480_ = lean_ctor_get(v_x_473_, 0);
lean_inc(v_it_480_);
lean_dec_ref_known(v_x_473_, 1);
v___x_481_ = lean_apply_1(v_h__2_475_, v_it_480_);
return v___x_481_;
}
default: 
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v_h__2_475_);
lean_dec(v_h__1_474_);
v___x_482_ = lean_box(0);
v___x_483_ = lean_apply_1(v_h__3_476_, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_iter_486_; 
v_iter_486_ = lean_ctor_get(v_x_485_, 0);
lean_inc(v_iter_486_);
if (lean_obj_tag(v_iter_486_) == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_x_485_);
lean_dec_ref(v_inst_484_);
v___x_487_ = lean_box(2);
return v___x_487_;
}
else
{
lean_object* v_upper_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_505_; 
v_upper_488_ = lean_ctor_get(v_x_485_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_x_485_, 0);
lean_dec(v_unused_506_);
v___x_490_ = v_x_485_;
v_isShared_491_ = v_isSharedCheck_505_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_upper_488_);
lean_dec(v_x_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_505_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_k_492_; lean_object* v_v_493_; lean_object* v_tree_494_; lean_object* v_next_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_k_492_ = lean_ctor_get(v_iter_486_, 0);
lean_inc_n(v_k_492_, 2);
v_v_493_ = lean_ctor_get(v_iter_486_, 1);
lean_inc(v_v_493_);
v_tree_494_ = lean_ctor_get(v_iter_486_, 2);
lean_inc(v_tree_494_);
v_next_495_ = lean_ctor_get(v_iter_486_, 3);
lean_inc(v_next_495_);
lean_dec_ref_known(v_iter_486_, 4);
lean_inc(v_upper_488_);
v___x_496_ = lean_apply_2(v_inst_484_, v_k_492_, v_upper_488_);
v___x_497_ = lean_unbox(v___x_496_);
if (v___x_497_ == 2)
{
lean_object* v___x_498_; 
lean_dec(v_next_495_);
lean_dec(v_tree_494_);
lean_dec(v_v_493_);
lean_dec(v_k_492_);
lean_del_object(v___x_490_);
lean_dec(v_upper_488_);
v___x_498_ = lean_box(2);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_494_, v_next_495_);
lean_dec(v_tree_494_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_499_);
v___x_501_ = v___x_490_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_upper_488_);
v___x_501_ = v_reuseFailAlloc_504_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_k_492_);
lean_ctor_set(v___x_502_, 1, v_v_493_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_inst_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_509_, v_x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_512_, lean_object* v_it_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_512_, v_it_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_515_){
_start:
{
lean_object* v___f_516_; 
v___f_516_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_516_, 0, v_inst_515_);
return v___f_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_inst_519_){
_start:
{
lean_object* v___f_520_; 
v___f_520_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_520_, 0, v_inst_519_);
return v___f_520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_521_, lean_object* v_h__1_522_, lean_object* v_h__2_523_){
_start:
{
lean_object* v_iter_524_; 
v_iter_524_ = lean_ctor_get(v_x_521_, 0);
if (lean_obj_tag(v_iter_524_) == 0)
{
lean_object* v_upper_525_; lean_object* v___x_526_; 
lean_dec(v_h__2_523_);
v_upper_525_ = lean_ctor_get(v_x_521_, 1);
lean_inc(v_upper_525_);
lean_dec_ref(v_x_521_);
v___x_526_ = lean_apply_1(v_h__1_522_, v_upper_525_);
return v___x_526_;
}
else
{
lean_object* v_upper_527_; lean_object* v_k_528_; lean_object* v_v_529_; lean_object* v_tree_530_; lean_object* v_next_531_; lean_object* v___x_532_; 
lean_inc_ref(v_iter_524_);
lean_dec(v_h__1_522_);
v_upper_527_ = lean_ctor_get(v_x_521_, 1);
lean_inc(v_upper_527_);
lean_dec_ref(v_x_521_);
v_k_528_ = lean_ctor_get(v_iter_524_, 0);
lean_inc(v_k_528_);
v_v_529_ = lean_ctor_get(v_iter_524_, 1);
lean_inc(v_v_529_);
v_tree_530_ = lean_ctor_get(v_iter_524_, 2);
lean_inc(v_tree_530_);
v_next_531_ = lean_ctor_get(v_iter_524_, 3);
lean_inc(v_next_531_);
lean_dec_ref_known(v_iter_524_, 4);
v___x_532_ = lean_apply_5(v_h__2_523_, v_k_528_, v_v_529_, v_tree_530_, v_next_531_, v_upper_527_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_inst_535_, lean_object* v_motive_536_, lean_object* v_x_537_, lean_object* v_h__1_538_, lean_object* v_h__2_539_){
_start:
{
lean_object* v_iter_540_; 
v_iter_540_ = lean_ctor_get(v_x_537_, 0);
if (lean_obj_tag(v_iter_540_) == 0)
{
lean_object* v_upper_541_; lean_object* v___x_542_; 
lean_dec(v_h__2_539_);
v_upper_541_ = lean_ctor_get(v_x_537_, 1);
lean_inc(v_upper_541_);
lean_dec_ref(v_x_537_);
v___x_542_ = lean_apply_1(v_h__1_538_, v_upper_541_);
return v___x_542_;
}
else
{
lean_object* v_upper_543_; lean_object* v_k_544_; lean_object* v_v_545_; lean_object* v_tree_546_; lean_object* v_next_547_; lean_object* v___x_548_; 
lean_inc_ref(v_iter_540_);
lean_dec(v_h__1_538_);
v_upper_543_ = lean_ctor_get(v_x_537_, 1);
lean_inc(v_upper_543_);
lean_dec_ref(v_x_537_);
v_k_544_ = lean_ctor_get(v_iter_540_, 0);
lean_inc(v_k_544_);
v_v_545_ = lean_ctor_get(v_iter_540_, 1);
lean_inc(v_v_545_);
v_tree_546_ = lean_ctor_get(v_iter_540_, 2);
lean_inc(v_tree_546_);
v_next_547_ = lean_ctor_get(v_iter_540_, 3);
lean_inc(v_next_547_);
lean_dec_ref_known(v_iter_540_, 4);
v___x_548_ = lean_apply_5(v_h__2_539_, v_k_544_, v_v_545_, v_tree_546_, v_next_547_, v_upper_543_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_inst_551_, lean_object* v_motive_552_, lean_object* v_x_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_549_, v_00_u03b2_550_, v_inst_551_, v_motive_552_, v_x_553_, v_h__1_554_, v_h__2_555_);
lean_dec_ref(v_inst_551_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg___boxed(lean_object* v___dummy_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_inst_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_box(0);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_565_, lean_object* v_00_u03b2_566_, lean_object* v_inst_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_565_, v_00_u03b2_566_, v_inst_567_);
lean_dec_ref(v_inst_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_569_, lean_object* v_recur_570_, lean_object* v_it_571_, lean_object* v_____do__lift_572_){
_start:
{
if (lean_obj_tag(v_____do__lift_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
lean_dec_ref(v_it_571_);
lean_dec(v_recur_570_);
v_a_573_ = lean_ctor_get(v_____do__lift_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v_____do__lift_572_, 1);
v___x_574_ = lean_apply_2(v_toPure_569_, lean_box(0), v_a_573_);
return v___x_574_;
}
else
{
lean_object* v_a_575_; lean_object* v___x_576_; 
lean_dec(v_toPure_569_);
v_a_575_ = lean_ctor_get(v_____do__lift_572_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v_____do__lift_572_, 1);
v___x_576_ = lean_apply_4(v_recur_570_, v_it_571_, v_a_575_, lean_box(0), lean_box(0));
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_577_, lean_object* v_recur_578_, lean_object* v___y_579_, lean_object* v_acc_580_, lean_object* v_toBind_581_, lean_object* v_s_582_){
_start:
{
switch(lean_obj_tag(v_s_582_))
{
case 0:
{
lean_object* v_it_583_; lean_object* v_out_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_it_583_ = lean_ctor_get(v_s_582_, 0);
lean_inc(v_it_583_);
v_out_584_ = lean_ctor_get(v_s_582_, 1);
lean_inc(v_out_584_);
lean_dec_ref_known(v_s_582_, 2);
v___f_585_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_585_, 0, v_toPure_577_);
lean_closure_set(v___f_585_, 1, v_recur_578_);
lean_closure_set(v___f_585_, 2, v_it_583_);
v___x_586_ = lean_apply_3(v___y_579_, v_out_584_, lean_box(0), v_acc_580_);
v___x_587_ = lean_apply_4(v_toBind_581_, lean_box(0), lean_box(0), v___x_586_, v___f_585_);
return v___x_587_;
}
case 1:
{
lean_object* v_it_588_; lean_object* v___x_589_; 
lean_dec(v_toBind_581_);
lean_dec(v___y_579_);
lean_dec(v_toPure_577_);
v_it_588_ = lean_ctor_get(v_s_582_, 0);
lean_inc(v_it_588_);
lean_dec_ref_known(v_s_582_, 1);
v___x_589_ = lean_apply_4(v_recur_578_, v_it_588_, v_acc_580_, lean_box(0), lean_box(0));
return v___x_589_;
}
default: 
{
lean_object* v___x_590_; 
lean_dec(v_toBind_581_);
lean_dec(v___y_579_);
lean_dec(v_recur_578_);
v___x_590_ = lean_apply_2(v_toPure_577_, lean_box(0), v_acc_580_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_591_, lean_object* v___y_592_, lean_object* v_toBind_593_, lean_object* v_inst_594_, lean_object* v_lift_595_, lean_object* v_it_596_, lean_object* v_acc_597_, lean_object* v_hP_598_, lean_object* v_recur_599_){
_start:
{
lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___f_600_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_600_, 0, v_toPure_591_);
lean_closure_set(v___f_600_, 1, v_recur_599_);
lean_closure_set(v___f_600_, 2, v___y_592_);
lean_closure_set(v___f_600_, 3, v_acc_597_);
lean_closure_set(v___f_600_, 4, v_toBind_593_);
v___x_601_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_594_, v_it_596_);
v___x_602_ = lean_apply_4(v_lift_595_, lean_box(0), lean_box(0), v___f_600_, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_lift_605_, lean_object* v_00_u03b3_606_, lean_object* v_Pl_607_, lean_object* v_it_608_, lean_object* v_init_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_toApplicative_611_; lean_object* v_toBind_612_; lean_object* v_toPure_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
v_toApplicative_611_ = lean_ctor_get(v_inst_603_, 0);
lean_inc_ref(v_toApplicative_611_);
v_toBind_612_ = lean_ctor_get(v_inst_603_, 1);
lean_inc(v_toBind_612_);
lean_dec_ref(v_inst_603_);
v_toPure_613_ = lean_ctor_get(v_toApplicative_611_, 1);
lean_inc(v_toPure_613_);
lean_dec_ref(v_toApplicative_611_);
v___f_614_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_614_, 0, v_toPure_613_);
lean_closure_set(v___f_614_, 1, v___y_610_);
lean_closure_set(v___f_614_, 2, v_toBind_612_);
lean_closure_set(v___f_614_, 3, v_inst_604_);
lean_closure_set(v___f_614_, 4, v_lift_605_);
v___x_615_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_614_, v_it_608_, v_init_609_, lean_box(0));
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object* v_inst_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v___f_618_; 
v___f_618_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_618_, 0, v_inst_617_);
lean_closure_set(v___f_618_, 1, v_inst_616_);
return v___f_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_inst_621_, lean_object* v_m_622_, lean_object* v_inst_623_){
_start:
{
lean_object* v___f_624_; 
v___f_624_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_624_, 0, v_inst_623_);
lean_closure_set(v___f_624_, 1, v_inst_621_);
return v___f_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_iter_627_; 
v_iter_627_ = lean_ctor_get(v_x_626_, 0);
lean_inc(v_iter_627_);
if (lean_obj_tag(v_iter_627_) == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v_x_626_);
lean_dec_ref(v_inst_625_);
v___x_628_ = lean_box(2);
return v___x_628_;
}
else
{
lean_object* v_upper_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_646_; 
v_upper_629_ = lean_ctor_get(v_x_626_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_626_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v_x_626_, 0);
lean_dec(v_unused_647_);
v___x_631_ = v_x_626_;
v_isShared_632_ = v_isSharedCheck_646_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_upper_629_);
lean_dec(v_x_626_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_646_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_k_633_; lean_object* v_v_634_; lean_object* v_tree_635_; lean_object* v_next_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_k_633_ = lean_ctor_get(v_iter_627_, 0);
lean_inc_n(v_k_633_, 2);
v_v_634_ = lean_ctor_get(v_iter_627_, 1);
lean_inc(v_v_634_);
v_tree_635_ = lean_ctor_get(v_iter_627_, 2);
lean_inc(v_tree_635_);
v_next_636_ = lean_ctor_get(v_iter_627_, 3);
lean_inc(v_next_636_);
lean_dec_ref_known(v_iter_627_, 4);
lean_inc(v_upper_629_);
v___x_637_ = lean_apply_2(v_inst_625_, v_k_633_, v_upper_629_);
v___x_638_ = lean_unbox(v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_635_, v_next_636_);
lean_dec(v_tree_635_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_639_);
v___x_641_ = v___x_631_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_upper_629_);
v___x_641_ = v_reuseFailAlloc_644_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_k_633_);
lean_ctor_set(v___x_642_, 1, v_v_634_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
return v___x_643_;
}
}
else
{
lean_object* v___x_645_; 
lean_dec(v_next_636_);
lean_dec(v_tree_635_);
lean_dec(v_v_634_);
lean_dec(v_k_633_);
lean_del_object(v___x_631_);
lean_dec(v_upper_629_);
v___x_645_ = lean_box(2);
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_inst_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_653_, lean_object* v_it_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_653_, v_it_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_656_){
_start:
{
lean_object* v___f_657_; 
v___f_657_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_657_, 0, v_inst_656_);
return v___f_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_inst_660_){
_start:
{
lean_object* v___f_661_; 
v___f_661_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_661_, 0, v_inst_660_);
return v___f_661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_662_, lean_object* v_h__1_663_, lean_object* v_h__2_664_){
_start:
{
lean_object* v_iter_665_; 
v_iter_665_ = lean_ctor_get(v_x_662_, 0);
if (lean_obj_tag(v_iter_665_) == 0)
{
lean_object* v_upper_666_; lean_object* v___x_667_; 
lean_dec(v_h__2_664_);
v_upper_666_ = lean_ctor_get(v_x_662_, 1);
lean_inc(v_upper_666_);
lean_dec_ref(v_x_662_);
v___x_667_ = lean_apply_1(v_h__1_663_, v_upper_666_);
return v___x_667_;
}
else
{
lean_object* v_upper_668_; lean_object* v_k_669_; lean_object* v_v_670_; lean_object* v_tree_671_; lean_object* v_next_672_; lean_object* v___x_673_; 
lean_inc_ref(v_iter_665_);
lean_dec(v_h__1_663_);
v_upper_668_ = lean_ctor_get(v_x_662_, 1);
lean_inc(v_upper_668_);
lean_dec_ref(v_x_662_);
v_k_669_ = lean_ctor_get(v_iter_665_, 0);
lean_inc(v_k_669_);
v_v_670_ = lean_ctor_get(v_iter_665_, 1);
lean_inc(v_v_670_);
v_tree_671_ = lean_ctor_get(v_iter_665_, 2);
lean_inc(v_tree_671_);
v_next_672_ = lean_ctor_get(v_iter_665_, 3);
lean_inc(v_next_672_);
lean_dec_ref_known(v_iter_665_, 4);
v___x_673_ = lean_apply_5(v_h__2_664_, v_k_669_, v_v_670_, v_tree_671_, v_next_672_, v_upper_668_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_inst_676_, lean_object* v_motive_677_, lean_object* v_x_678_, lean_object* v_h__1_679_, lean_object* v_h__2_680_){
_start:
{
lean_object* v_iter_681_; 
v_iter_681_ = lean_ctor_get(v_x_678_, 0);
if (lean_obj_tag(v_iter_681_) == 0)
{
lean_object* v_upper_682_; lean_object* v___x_683_; 
lean_dec(v_h__2_680_);
v_upper_682_ = lean_ctor_get(v_x_678_, 1);
lean_inc(v_upper_682_);
lean_dec_ref(v_x_678_);
v___x_683_ = lean_apply_1(v_h__1_679_, v_upper_682_);
return v___x_683_;
}
else
{
lean_object* v_upper_684_; lean_object* v_k_685_; lean_object* v_v_686_; lean_object* v_tree_687_; lean_object* v_next_688_; lean_object* v___x_689_; 
lean_inc_ref(v_iter_681_);
lean_dec(v_h__1_679_);
v_upper_684_ = lean_ctor_get(v_x_678_, 1);
lean_inc(v_upper_684_);
lean_dec_ref(v_x_678_);
v_k_685_ = lean_ctor_get(v_iter_681_, 0);
lean_inc(v_k_685_);
v_v_686_ = lean_ctor_get(v_iter_681_, 1);
lean_inc(v_v_686_);
v_tree_687_ = lean_ctor_get(v_iter_681_, 2);
lean_inc(v_tree_687_);
v_next_688_ = lean_ctor_get(v_iter_681_, 3);
lean_inc(v_next_688_);
lean_dec_ref_known(v_iter_681_, 4);
v___x_689_ = lean_apply_5(v_h__2_680_, v_k_685_, v_v_686_, v_tree_687_, v_next_688_, v_upper_684_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b2_691_, lean_object* v_inst_692_, lean_object* v_motive_693_, lean_object* v_x_694_, lean_object* v_h__1_695_, lean_object* v_h__2_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_690_, v_00_u03b2_691_, v_inst_692_, v_motive_693_, v_x_694_, v_h__1_695_, v_h__2_696_);
lean_dec_ref(v_inst_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_box(0);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(0);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_inst_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_706_, v_00_u03b2_707_, v_inst_708_);
lean_dec_ref(v_inst_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_710_, lean_object* v_recur_711_, lean_object* v_it_712_, lean_object* v_____do__lift_713_){
_start:
{
if (lean_obj_tag(v_____do__lift_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
lean_dec_ref(v_it_712_);
lean_dec(v_recur_711_);
v_a_714_ = lean_ctor_get(v_____do__lift_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v_____do__lift_713_, 1);
v___x_715_ = lean_apply_2(v_toPure_710_, lean_box(0), v_a_714_);
return v___x_715_;
}
else
{
lean_object* v_a_716_; lean_object* v___x_717_; 
lean_dec(v_toPure_710_);
v_a_716_ = lean_ctor_get(v_____do__lift_713_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v_____do__lift_713_, 1);
v___x_717_ = lean_apply_4(v_recur_711_, v_it_712_, v_a_716_, lean_box(0), lean_box(0));
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_718_, lean_object* v_recur_719_, lean_object* v___y_720_, lean_object* v_acc_721_, lean_object* v_toBind_722_, lean_object* v_s_723_){
_start:
{
switch(lean_obj_tag(v_s_723_))
{
case 0:
{
lean_object* v_it_724_; lean_object* v_out_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_it_724_ = lean_ctor_get(v_s_723_, 0);
lean_inc(v_it_724_);
v_out_725_ = lean_ctor_get(v_s_723_, 1);
lean_inc(v_out_725_);
lean_dec_ref_known(v_s_723_, 2);
v___f_726_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_726_, 0, v_toPure_718_);
lean_closure_set(v___f_726_, 1, v_recur_719_);
lean_closure_set(v___f_726_, 2, v_it_724_);
v___x_727_ = lean_apply_3(v___y_720_, v_out_725_, lean_box(0), v_acc_721_);
v___x_728_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_727_, v___f_726_);
return v___x_728_;
}
case 1:
{
lean_object* v_it_729_; lean_object* v___x_730_; 
lean_dec(v_toBind_722_);
lean_dec(v___y_720_);
lean_dec(v_toPure_718_);
v_it_729_ = lean_ctor_get(v_s_723_, 0);
lean_inc(v_it_729_);
lean_dec_ref_known(v_s_723_, 1);
v___x_730_ = lean_apply_4(v_recur_719_, v_it_729_, v_acc_721_, lean_box(0), lean_box(0));
return v___x_730_;
}
default: 
{
lean_object* v___x_731_; 
lean_dec(v_toBind_722_);
lean_dec(v___y_720_);
lean_dec(v_recur_719_);
v___x_731_ = lean_apply_2(v_toPure_718_, lean_box(0), v_acc_721_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_732_, lean_object* v___y_733_, lean_object* v_toBind_734_, lean_object* v_inst_735_, lean_object* v_lift_736_, lean_object* v_it_737_, lean_object* v_acc_738_, lean_object* v_hP_739_, lean_object* v_recur_740_){
_start:
{
lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___f_741_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_741_, 0, v_toPure_732_);
lean_closure_set(v___f_741_, 1, v_recur_740_);
lean_closure_set(v___f_741_, 2, v___y_733_);
lean_closure_set(v___f_741_, 3, v_acc_738_);
lean_closure_set(v___f_741_, 4, v_toBind_734_);
v___x_742_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_735_, v_it_737_);
v___x_743_ = lean_apply_4(v_lift_736_, lean_box(0), lean_box(0), v___f_741_, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_lift_746_, lean_object* v_00_u03b3_747_, lean_object* v_Pl_748_, lean_object* v_it_749_, lean_object* v_init_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_toApplicative_752_; lean_object* v_toBind_753_; lean_object* v_toPure_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
v_toApplicative_752_ = lean_ctor_get(v_inst_744_, 0);
lean_inc_ref(v_toApplicative_752_);
v_toBind_753_ = lean_ctor_get(v_inst_744_, 1);
lean_inc(v_toBind_753_);
lean_dec_ref(v_inst_744_);
v_toPure_754_ = lean_ctor_get(v_toApplicative_752_, 1);
lean_inc(v_toPure_754_);
lean_dec_ref(v_toApplicative_752_);
v___f_755_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_755_, 0, v_toPure_754_);
lean_closure_set(v___f_755_, 1, v___y_751_);
lean_closure_set(v___f_755_, 2, v_toBind_753_);
lean_closure_set(v___f_755_, 3, v_inst_745_);
lean_closure_set(v___f_755_, 4, v_lift_746_);
v___x_756_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_755_, v_it_749_, v_init_750_, lean_box(0));
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v___f_759_; 
v___f_759_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_759_, 0, v_inst_758_);
lean_closure_set(v___f_759_, 1, v_inst_757_);
return v___f_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_inst_762_, lean_object* v_m_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v___f_765_; 
v___f_765_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_765_, 0, v_inst_764_);
lean_closure_set(v___f_765_, 1, v_inst_762_);
return v___f_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_766_, lean_object* v_range_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v_carrier_766_);
lean_ctor_set(v___x_768_, 1, v_range_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_771_; 
v___f_771_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_inst_776_){
_start:
{
lean_object* v___f_777_; 
v___f_777_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_778_, lean_object* v_00_u03b2_779_, lean_object* v_inst_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_778_, v_00_u03b2_779_, v_inst_780_);
lean_dec_ref(v_inst_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_782_){
_start:
{
lean_object* v_treeMap_783_; lean_object* v_range_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_793_; 
v_treeMap_783_ = lean_ctor_get(v_x_782_, 0);
v_range_784_ = lean_ctor_get(v_x_782_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_793_ == 0)
{
v___x_786_ = v_x_782_;
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_range_784_);
lean_inc(v_treeMap_783_);
lean_dec(v_x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_793_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = lean_box(0);
v___x_789_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_783_, v___x_788_);
lean_dec(v_treeMap_783_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_range_784_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_796_; 
v___f_796_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_799_, lean_object* v_00_u03b2_800_, lean_object* v_inst_801_){
_start:
{
lean_object* v___f_802_; 
v___f_802_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_inst_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_803_, v_00_u03b2_804_, v_inst_805_);
lean_dec_ref(v_inst_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0(lean_object* v_carrier_807_, lean_object* v_range_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_carrier_807_);
lean_ctor_set(v___x_809_, 1, v_range_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg(){
_start:
{
lean_object* v___f_812_; 
v___f_812_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___boxed(lean_object* v___dummy_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_815_, lean_object* v_inst_816_){
_start:
{
lean_object* v___f_817_; 
v___f_817_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_818_, lean_object* v_inst_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_818_, v_inst_819_);
lean_dec_ref(v_inst_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_821_){
_start:
{
lean_object* v_treeMap_822_; lean_object* v_range_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_832_; 
v_treeMap_822_ = lean_ctor_get(v_x_821_, 0);
v_range_823_ = lean_ctor_get(v_x_821_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_821_);
if (v_isSharedCheck_832_ == 0)
{
v___x_825_ = v_x_821_;
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_range_823_);
lean_inc(v_treeMap_822_);
lean_dec(v_x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_box(0);
v___x_828_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_822_, v___x_827_);
lean_dec(v_treeMap_822_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_range_823_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_835_; 
v___f_835_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_838_, lean_object* v_inst_839_){
_start:
{
lean_object* v___f_840_; 
v___f_840_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_841_, v_inst_842_);
lean_dec_ref(v_inst_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_844_, lean_object* v_range_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_carrier_844_);
lean_ctor_set(v___x_846_, 1, v_range_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_849_; 
v___f_849_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_inst_854_){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_inst_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_856_, v_00_u03b2_857_, v_inst_858_);
lean_dec_ref(v_inst_858_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_860_){
_start:
{
lean_object* v_treeMap_861_; lean_object* v_range_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_871_; 
v_treeMap_861_ = lean_ctor_get(v_x_860_, 0);
v_range_862_ = lean_ctor_get(v_x_860_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_860_);
if (v_isSharedCheck_871_ == 0)
{
v___x_864_ = v_x_860_;
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_range_862_);
lean_inc(v_treeMap_861_);
lean_dec(v_x_860_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = lean_box(0);
v___x_867_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_861_, v___x_866_);
lean_dec(v_treeMap_861_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_range_862_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_874_; 
v___f_874_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v_inst_879_){
_start:
{
lean_object* v___f_880_; 
v___f_880_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_881_, v_00_u03b2_882_, v_inst_883_);
lean_dec_ref(v_inst_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_885_, lean_object* v_range_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_carrier_885_);
lean_ctor_set(v___x_887_, 1, v_range_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_890_; 
v___f_890_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_inst_895_){
_start:
{
lean_object* v___f_896_; 
v___f_896_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_897_, v_00_u03b2_898_, v_inst_899_);
lean_dec_ref(v_inst_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_901_){
_start:
{
lean_object* v_treeMap_902_; lean_object* v_range_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_912_; 
v_treeMap_902_ = lean_ctor_get(v_x_901_, 0);
v_range_903_ = lean_ctor_get(v_x_901_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_x_901_);
if (v_isSharedCheck_912_ == 0)
{
v___x_905_ = v_x_901_;
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_range_903_);
lean_inc(v_treeMap_902_);
lean_dec(v_x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_907_ = lean_box(0);
v___x_908_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_902_, v___x_907_);
lean_dec(v_treeMap_902_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_range_903_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_915_; 
v___f_915_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_918_, lean_object* v_00_u03b2_919_, lean_object* v_inst_920_){
_start:
{
lean_object* v___f_921_; 
v___f_921_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_inst_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_922_, v_00_u03b2_923_, v_inst_924_);
lean_dec_ref(v_inst_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0(lean_object* v_carrier_926_, lean_object* v_range_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_carrier_926_);
lean_ctor_set(v___x_928_, 1, v_range_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg(){
_start:
{
lean_object* v___f_931_; 
v___f_931_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___boxed(lean_object* v___dummy_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_934_, lean_object* v_inst_935_){
_start:
{
lean_object* v___f_936_; 
v___f_936_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_937_, v_inst_938_);
lean_dec_ref(v_inst_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_940_){
_start:
{
lean_object* v_treeMap_941_; lean_object* v_range_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_951_; 
v_treeMap_941_ = lean_ctor_get(v_x_940_, 0);
v_range_942_ = lean_ctor_get(v_x_940_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_951_ == 0)
{
v___x_944_ = v_x_940_;
v_isShared_945_ = v_isSharedCheck_951_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_range_942_);
lean_inc(v_treeMap_941_);
lean_dec(v_x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_951_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = lean_box(0);
v___x_947_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_941_, v___x_946_);
lean_dec(v_treeMap_941_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_range_942_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_954_; 
v___f_954_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_){
_start:
{
lean_object* v___f_959_; 
v___f_959_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_960_, v_inst_961_);
lean_dec_ref(v_inst_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_963_, lean_object* v_range_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_carrier_963_);
lean_ctor_set(v___x_965_, 1, v_range_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_968_; 
v___f_968_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_inst_973_){
_start:
{
lean_object* v___f_974_; 
v___f_974_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_975_, lean_object* v_00_u03b2_976_, lean_object* v_inst_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_975_, v_00_u03b2_976_, v_inst_977_);
lean_dec_ref(v_inst_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_979_){
_start:
{
lean_object* v_treeMap_980_; lean_object* v_range_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
v_treeMap_980_ = lean_ctor_get(v_x_979_, 0);
v_range_981_ = lean_ctor_get(v_x_979_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_x_979_);
if (v_isSharedCheck_990_ == 0)
{
v___x_983_ = v_x_979_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_range_981_);
lean_inc(v_treeMap_980_);
lean_dec(v_x_979_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_985_ = lean_box(0);
v___x_986_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_980_, v___x_985_);
lean_dec(v_treeMap_980_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_986_);
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_range_981_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_993_; 
v___f_993_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_inst_998_){
_start:
{
lean_object* v___f_999_; 
v___f_999_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1000_, lean_object* v_00_u03b2_1001_, lean_object* v_inst_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_1000_, v_00_u03b2_1001_, v_inst_1002_);
lean_dec_ref(v_inst_1002_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_1004_, lean_object* v_t_1005_, lean_object* v_lowerBound_1006_, lean_object* v_upperBound_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1004_, v_t_1005_, v_lowerBound_1006_, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_upperBound_1007_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_, lean_object* v_t_1014_, lean_object* v_lowerBound_1015_, lean_object* v_upperBound_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1013_, v_t_1014_, v_lowerBound_1015_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_upperBound_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1020_, lean_object* v_range_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_carrier_1020_);
lean_ctor_set(v___x_1022_, 1, v_range_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1025_; 
v___f_1025_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_inst_1030_){
_start:
{
lean_object* v___f_1031_; 
v___f_1031_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_inst_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_1032_, v_00_u03b2_1033_, v_inst_1034_);
lean_dec_ref(v_inst_1034_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v_range_1038_; lean_object* v_treeMap_1039_; lean_object* v_lower_1040_; lean_object* v_upper_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1050_; 
v_range_1038_ = lean_ctor_get(v_x_1037_, 1);
lean_inc_ref(v_range_1038_);
v_treeMap_1039_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_treeMap_1039_);
lean_dec_ref(v_x_1037_);
v_lower_1040_ = lean_ctor_get(v_range_1038_, 0);
v_upper_1041_ = lean_ctor_get(v_range_1038_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_range_1038_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1043_ = v_range_1038_;
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_upper_1041_);
lean_inc(v_lower_1040_);
lean_dec(v_range_1038_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1036_, v_treeMap_1039_, v_lower_1040_, v___x_1045_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_upper_1041_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_1051_){
_start:
{
lean_object* v___f_1052_; 
v___f_1052_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1052_, 0, v_inst_1051_);
return v___f_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_1053_, lean_object* v_00_u03b2_1054_, lean_object* v_inst_1055_){
_start:
{
lean_object* v___f_1056_; 
v___f_1056_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1056_, 0, v_inst_1055_);
return v___f_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0(lean_object* v_carrier_1057_, lean_object* v_range_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_carrier_1057_);
lean_ctor_set(v___x_1059_, 1, v_range_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg(){
_start:
{
lean_object* v___f_1062_; 
v___f_1062_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___boxed(lean_object* v___dummy_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v___f_1067_; 
v___f_1067_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_inst_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_1068_, v_inst_1069_);
lean_dec_ref(v_inst_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v_range_1073_; lean_object* v_treeMap_1074_; lean_object* v_lower_1075_; lean_object* v_upper_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1085_; 
v_range_1073_ = lean_ctor_get(v_x_1072_, 1);
lean_inc_ref(v_range_1073_);
v_treeMap_1074_ = lean_ctor_get(v_x_1072_, 0);
lean_inc(v_treeMap_1074_);
lean_dec_ref(v_x_1072_);
v_lower_1075_ = lean_ctor_get(v_range_1073_, 0);
v_upper_1076_ = lean_ctor_get(v_range_1073_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_range_1073_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1078_ = v_range_1073_;
v_isShared_1079_ = v_isSharedCheck_1085_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_upper_1076_);
lean_inc(v_lower_1075_);
lean_dec(v_range_1073_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1085_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1071_, v_treeMap_1074_, v_lower_1075_, v___x_1080_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_upper_1076_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_1086_){
_start:
{
lean_object* v___f_1087_; 
v___f_1087_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1087_, 0, v_inst_1086_);
return v___f_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_1088_, lean_object* v_inst_1089_){
_start:
{
lean_object* v___f_1090_; 
v___f_1090_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1090_, 0, v_inst_1089_);
return v___f_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1091_, lean_object* v_range_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_carrier_1091_);
lean_ctor_set(v___x_1093_, 1, v_range_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1096_; 
v___f_1096_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v___f_1102_; 
v___f_1102_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1103_, lean_object* v_00_u03b2_1104_, lean_object* v_inst_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_1103_, v_00_u03b2_1104_, v_inst_1105_);
lean_dec_ref(v_inst_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v_range_1109_; lean_object* v_treeMap_1110_; lean_object* v_lower_1111_; lean_object* v_upper_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1121_; 
v_range_1109_ = lean_ctor_get(v_x_1108_, 1);
lean_inc_ref(v_range_1109_);
v_treeMap_1110_ = lean_ctor_get(v_x_1108_, 0);
lean_inc(v_treeMap_1110_);
lean_dec_ref(v_x_1108_);
v_lower_1111_ = lean_ctor_get(v_range_1109_, 0);
v_upper_1112_ = lean_ctor_get(v_range_1109_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_range_1109_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1114_ = v_range_1109_;
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_upper_1112_);
lean_inc(v_lower_1111_);
lean_dec(v_range_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1107_, v_treeMap_1110_, v_lower_1111_, v___x_1116_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1117_);
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_upper_1112_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_1122_){
_start:
{
lean_object* v___f_1123_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1123_, 0, v_inst_1122_);
return v___f_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_inst_1126_){
_start:
{
lean_object* v___f_1127_; 
v___f_1127_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1127_, 0, v_inst_1126_);
return v___f_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_1128_, lean_object* v_t_1129_, lean_object* v_lowerBound_1130_, lean_object* v_upperBound_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1128_, v_t_1129_, v_lowerBound_1130_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_upperBound_1131_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_inst_1137_, lean_object* v_t_1138_, lean_object* v_lowerBound_1139_, lean_object* v_upperBound_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1137_, v_t_1138_, v_lowerBound_1139_, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_upperBound_1140_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1144_, lean_object* v_range_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_carrier_1144_);
lean_ctor_set(v___x_1146_, 1, v_range_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1149_; 
v___f_1149_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_inst_1154_){
_start:
{
lean_object* v___f_1155_; 
v___f_1155_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_00_u03b2_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_1156_, v_00_u03b2_1157_, v_inst_1158_);
lean_dec_ref(v_inst_1158_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_range_1162_; lean_object* v_treeMap_1163_; lean_object* v_lower_1164_; lean_object* v_upper_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
v_range_1162_ = lean_ctor_get(v_x_1161_, 1);
lean_inc_ref(v_range_1162_);
v_treeMap_1163_ = lean_ctor_get(v_x_1161_, 0);
lean_inc(v_treeMap_1163_);
lean_dec_ref(v_x_1161_);
v_lower_1164_ = lean_ctor_get(v_range_1162_, 0);
v_upper_1165_ = lean_ctor_get(v_range_1162_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_range_1162_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v_range_1162_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_upper_1165_);
lean_inc(v_lower_1164_);
lean_dec(v_range_1162_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = lean_box(0);
v___x_1170_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1160_, v_treeMap_1163_, v_lower_1164_, v___x_1169_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_upper_1165_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_1175_){
_start:
{
lean_object* v___f_1176_; 
v___f_1176_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1176_, 0, v_inst_1175_);
return v___f_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v___f_1180_; 
v___f_1180_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1180_, 0, v_inst_1179_);
return v___f_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0(lean_object* v_carrier_1181_, lean_object* v_range_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_carrier_1181_);
lean_ctor_set(v___x_1183_, 1, v_range_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg(){
_start:
{
lean_object* v___f_1186_; 
v___f_1186_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___boxed(lean_object* v___dummy_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_1189_, lean_object* v_inst_1190_){
_start:
{
lean_object* v___f_1191_; 
v___f_1191_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_1192_, v_inst_1193_);
lean_dec_ref(v_inst_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v_range_1197_; lean_object* v_treeMap_1198_; lean_object* v_lower_1199_; lean_object* v_upper_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1209_; 
v_range_1197_ = lean_ctor_get(v_x_1196_, 1);
lean_inc_ref(v_range_1197_);
v_treeMap_1198_ = lean_ctor_get(v_x_1196_, 0);
lean_inc(v_treeMap_1198_);
lean_dec_ref(v_x_1196_);
v_lower_1199_ = lean_ctor_get(v_range_1197_, 0);
v_upper_1200_ = lean_ctor_get(v_range_1197_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_range_1197_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1202_ = v_range_1197_;
v_isShared_1203_ = v_isSharedCheck_1209_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_upper_1200_);
lean_inc(v_lower_1199_);
lean_dec(v_range_1197_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1209_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1195_, v_treeMap_1198_, v_lower_1199_, v___x_1204_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1205_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_upper_1200_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1210_){
_start:
{
lean_object* v___f_1211_; 
v___f_1211_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1211_, 0, v_inst_1210_);
return v___f_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1212_, lean_object* v_inst_1213_){
_start:
{
lean_object* v___f_1214_; 
v___f_1214_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1214_, 0, v_inst_1213_);
return v___f_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1215_, lean_object* v_range_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_carrier_1215_);
lean_ctor_set(v___x_1217_, 1, v_range_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1220_; 
v___f_1220_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_inst_1225_){
_start:
{
lean_object* v___f_1226_; 
v___f_1226_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1227_, v_00_u03b2_1228_, v_inst_1229_);
lean_dec_ref(v_inst_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v_range_1233_; lean_object* v_treeMap_1234_; lean_object* v_lower_1235_; lean_object* v_upper_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1245_; 
v_range_1233_ = lean_ctor_get(v_x_1232_, 1);
lean_inc_ref(v_range_1233_);
v_treeMap_1234_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_treeMap_1234_);
lean_dec_ref(v_x_1232_);
v_lower_1235_ = lean_ctor_get(v_range_1233_, 0);
v_upper_1236_ = lean_ctor_get(v_range_1233_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_range_1233_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1238_ = v_range_1233_;
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_upper_1236_);
lean_inc(v_lower_1235_);
lean_dec(v_range_1233_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1231_, v_treeMap_1234_, v_lower_1235_, v___x_1240_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1241_);
v___x_1243_ = v___x_1238_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_upper_1236_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1246_){
_start:
{
lean_object* v___f_1247_; 
v___f_1247_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1247_, 0, v_inst_1246_);
return v___f_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v___f_1251_; 
v___f_1251_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1251_, 0, v_inst_1250_);
return v___f_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1252_, lean_object* v_t_1253_, lean_object* v_lowerBound_1254_, lean_object* v_upperBound_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1252_, v_t_1253_, v_lowerBound_1254_, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_upperBound_1255_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1259_, lean_object* v_00_u03b2_1260_, lean_object* v_inst_1261_, lean_object* v_t_1262_, lean_object* v_lowerBound_1263_, lean_object* v_upperBound_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1261_, v_t_1262_, v_lowerBound_1263_, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v_upperBound_1264_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1268_, lean_object* v_range_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_carrier_1268_);
lean_ctor_set(v___x_1270_, 1, v_range_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1273_; 
v___f_1273_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_inst_1278_){
_start:
{
lean_object* v___f_1279_; 
v___f_1279_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1280_, v_00_u03b2_1281_, v_inst_1282_);
lean_dec_ref(v_inst_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v_range_1286_; lean_object* v_treeMap_1287_; lean_object* v_lower_1288_; lean_object* v_upper_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1298_; 
v_range_1286_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_range_1286_);
v_treeMap_1287_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_treeMap_1287_);
lean_dec_ref(v_x_1285_);
v_lower_1288_ = lean_ctor_get(v_range_1286_, 0);
v_upper_1289_ = lean_ctor_get(v_range_1286_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_range_1286_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1291_ = v_range_1286_;
v_isShared_1292_ = v_isSharedCheck_1298_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_upper_1289_);
lean_inc(v_lower_1288_);
lean_dec(v_range_1286_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1298_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1284_, v_treeMap_1287_, v_lower_1288_, v___x_1293_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_upper_1289_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1299_){
_start:
{
lean_object* v___f_1300_; 
v___f_1300_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1300_, 0, v_inst_1299_);
return v___f_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1301_, lean_object* v_00_u03b2_1302_, lean_object* v_inst_1303_){
_start:
{
lean_object* v___f_1304_; 
v___f_1304_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1304_, 0, v_inst_1303_);
return v___f_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0(lean_object* v_carrier_1305_, lean_object* v_range_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_carrier_1305_);
lean_ctor_set(v___x_1307_, 1, v_range_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg(){
_start:
{
lean_object* v___f_1310_; 
v___f_1310_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___boxed(lean_object* v___dummy_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1313_, lean_object* v_inst_1314_){
_start:
{
lean_object* v___f_1315_; 
v___f_1315_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_inst_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1316_, v_inst_1317_);
lean_dec_ref(v_inst_1317_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v_range_1321_; lean_object* v_treeMap_1322_; lean_object* v_lower_1323_; lean_object* v_upper_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1333_; 
v_range_1321_ = lean_ctor_get(v_x_1320_, 1);
lean_inc_ref(v_range_1321_);
v_treeMap_1322_ = lean_ctor_get(v_x_1320_, 0);
lean_inc(v_treeMap_1322_);
lean_dec_ref(v_x_1320_);
v_lower_1323_ = lean_ctor_get(v_range_1321_, 0);
v_upper_1324_ = lean_ctor_get(v_range_1321_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_range_1321_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1326_ = v_range_1321_;
v_isShared_1327_ = v_isSharedCheck_1333_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_upper_1324_);
lean_inc(v_lower_1323_);
lean_dec(v_range_1321_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1333_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_box(0);
v___x_1329_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1319_, v_treeMap_1322_, v_lower_1323_, v___x_1328_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1329_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_upper_1324_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1334_){
_start:
{
lean_object* v___f_1335_; 
v___f_1335_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1335_, 0, v_inst_1334_);
return v___f_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1336_, lean_object* v_inst_1337_){
_start:
{
lean_object* v___f_1338_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1338_, 0, v_inst_1337_);
return v___f_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1339_, lean_object* v_range_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_carrier_1339_);
lean_ctor_set(v___x_1341_, 1, v_range_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1344_; 
v___f_1344_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_inst_1349_){
_start:
{
lean_object* v___f_1350_; 
v___f_1350_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_inst_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1351_, v_00_u03b2_1352_, v_inst_1353_);
lean_dec_ref(v_inst_1353_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_range_1357_; lean_object* v_treeMap_1358_; lean_object* v_lower_1359_; lean_object* v_upper_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1369_; 
v_range_1357_ = lean_ctor_get(v_x_1356_, 1);
lean_inc_ref(v_range_1357_);
v_treeMap_1358_ = lean_ctor_get(v_x_1356_, 0);
lean_inc(v_treeMap_1358_);
lean_dec_ref(v_x_1356_);
v_lower_1359_ = lean_ctor_get(v_range_1357_, 0);
v_upper_1360_ = lean_ctor_get(v_range_1357_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_range_1357_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1362_ = v_range_1357_;
v_isShared_1363_ = v_isSharedCheck_1369_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_upper_1360_);
lean_inc(v_lower_1359_);
lean_dec(v_range_1357_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1369_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1355_, v_treeMap_1358_, v_lower_1359_, v___x_1364_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_upper_1360_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1370_){
_start:
{
lean_object* v___f_1371_; 
v___f_1371_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1371_, 0, v_inst_1370_);
return v___f_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_inst_1374_){
_start:
{
lean_object* v___f_1375_; 
v___f_1375_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1375_, 0, v_inst_1374_);
return v___f_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1376_, lean_object* v_t_1377_, lean_object* v_lowerBound_1378_, lean_object* v_upperBound_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1376_, v_t_1377_, v_lowerBound_1378_, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v_upperBound_1379_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_inst_1385_, lean_object* v_t_1386_, lean_object* v_lowerBound_1387_, lean_object* v_upperBound_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1385_, v_t_1386_, v_lowerBound_1387_, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_upperBound_1388_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1392_, lean_object* v_range_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_carrier_1392_);
lean_ctor_set(v___x_1394_, 1, v_range_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1397_; 
v___f_1397_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1400_, lean_object* v_00_u03b2_1401_, lean_object* v_inst_1402_){
_start:
{
lean_object* v___f_1403_; 
v___f_1403_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_00_u03b2_1405_, lean_object* v_inst_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1404_, v_00_u03b2_1405_, v_inst_1406_);
lean_dec_ref(v_inst_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_range_1410_; lean_object* v_treeMap_1411_; lean_object* v_lower_1412_; lean_object* v_upper_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1422_; 
v_range_1410_ = lean_ctor_get(v_x_1409_, 1);
lean_inc_ref(v_range_1410_);
v_treeMap_1411_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_treeMap_1411_);
lean_dec_ref(v_x_1409_);
v_lower_1412_ = lean_ctor_get(v_range_1410_, 0);
v_upper_1413_ = lean_ctor_get(v_range_1410_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_range_1410_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1415_ = v_range_1410_;
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_upper_1413_);
lean_inc(v_lower_1412_);
lean_dec(v_range_1410_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1408_, v_treeMap_1411_, v_lower_1412_, v___x_1417_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1418_);
v___x_1420_ = v___x_1415_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_upper_1413_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1423_){
_start:
{
lean_object* v___f_1424_; 
v___f_1424_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1424_, 0, v_inst_1423_);
return v___f_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_inst_1427_){
_start:
{
lean_object* v___f_1428_; 
v___f_1428_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1428_, 0, v_inst_1427_);
return v___f_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0(lean_object* v_carrier_1429_, lean_object* v_range_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_carrier_1429_);
lean_ctor_set(v___x_1431_, 1, v_range_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg(){
_start:
{
lean_object* v___f_1434_; 
v___f_1434_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___boxed(lean_object* v___dummy_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1437_, lean_object* v_inst_1438_){
_start:
{
lean_object* v___f_1439_; 
v___f_1439_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1440_, lean_object* v_inst_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1440_, v_inst_1441_);
lean_dec_ref(v_inst_1441_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v_range_1445_; lean_object* v_treeMap_1446_; lean_object* v_lower_1447_; lean_object* v_upper_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1457_; 
v_range_1445_ = lean_ctor_get(v_x_1444_, 1);
lean_inc_ref(v_range_1445_);
v_treeMap_1446_ = lean_ctor_get(v_x_1444_, 0);
lean_inc(v_treeMap_1446_);
lean_dec_ref(v_x_1444_);
v_lower_1447_ = lean_ctor_get(v_range_1445_, 0);
v_upper_1448_ = lean_ctor_get(v_range_1445_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_range_1445_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1450_ = v_range_1445_;
v_isShared_1451_ = v_isSharedCheck_1457_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_upper_1448_);
lean_inc(v_lower_1447_);
lean_dec(v_range_1445_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1457_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1452_ = lean_box(0);
v___x_1453_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1443_, v_treeMap_1446_, v_lower_1447_, v___x_1452_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_upper_1448_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1458_){
_start:
{
lean_object* v___f_1459_; 
v___f_1459_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1459_, 0, v_inst_1458_);
return v___f_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1460_, lean_object* v_inst_1461_){
_start:
{
lean_object* v___f_1462_; 
v___f_1462_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1462_, 0, v_inst_1461_);
return v___f_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1463_, lean_object* v_range_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_carrier_1463_);
lean_ctor_set(v___x_1465_, 1, v_range_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1468_; 
v___f_1468_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_inst_1473_){
_start:
{
lean_object* v___f_1474_; 
v___f_1474_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1475_, lean_object* v_00_u03b2_1476_, lean_object* v_inst_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1475_, v_00_u03b2_1476_, v_inst_1477_);
lean_dec_ref(v_inst_1477_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v_range_1481_; lean_object* v_treeMap_1482_; lean_object* v_lower_1483_; lean_object* v_upper_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1493_; 
v_range_1481_ = lean_ctor_get(v_x_1480_, 1);
lean_inc_ref(v_range_1481_);
v_treeMap_1482_ = lean_ctor_get(v_x_1480_, 0);
lean_inc(v_treeMap_1482_);
lean_dec_ref(v_x_1480_);
v_lower_1483_ = lean_ctor_get(v_range_1481_, 0);
v_upper_1484_ = lean_ctor_get(v_range_1481_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_range_1481_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1486_ = v_range_1481_;
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_upper_1484_);
lean_inc(v_lower_1483_);
lean_dec(v_range_1481_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1488_ = lean_box(0);
v___x_1489_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1479_, v_treeMap_1482_, v_lower_1483_, v___x_1488_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1489_);
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_upper_1484_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1494_){
_start:
{
lean_object* v___f_1495_; 
v___f_1495_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1495_, 0, v_inst_1494_);
return v___f_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___f_1499_; 
v___f_1499_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1499_, 0, v_inst_1498_);
return v___f_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1500_, lean_object* v_t_1501_, lean_object* v_lowerBound_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1500_, v_t_1501_, v_lowerBound_1502_, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_inst_1507_, lean_object* v_t_1508_, lean_object* v_lowerBound_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1507_, v_t_1508_, v_lowerBound_1509_, v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1512_, lean_object* v_range_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_carrier_1512_);
lean_ctor_set(v___x_1514_, 1, v_range_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1517_; 
v___f_1517_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1520_, lean_object* v_00_u03b2_1521_, lean_object* v_inst_1522_){
_start:
{
lean_object* v___f_1523_; 
v___f_1523_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_inst_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1524_, v_00_u03b2_1525_, v_inst_1526_);
lean_dec_ref(v_inst_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v_treeMap_1530_; lean_object* v_range_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_treeMap_1530_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_treeMap_1530_);
v_range_1531_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_range_1531_);
lean_dec_ref(v_x_1529_);
v___x_1532_ = lean_box(0);
v___x_1533_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1528_, v_treeMap_1530_, v_range_1531_, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1534_){
_start:
{
lean_object* v___f_1535_; 
v___f_1535_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1535_, 0, v_inst_1534_);
return v___f_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_inst_1538_){
_start:
{
lean_object* v___f_1539_; 
v___f_1539_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1539_, 0, v_inst_1538_);
return v___f_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0(lean_object* v_carrier_1540_, lean_object* v_range_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_carrier_1540_);
lean_ctor_set(v___x_1542_, 1, v_range_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg(){
_start:
{
lean_object* v___f_1545_; 
v___f_1545_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___boxed(lean_object* v___dummy_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1548_, lean_object* v_inst_1549_){
_start:
{
lean_object* v___f_1550_; 
v___f_1550_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1551_, lean_object* v_inst_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1551_, v_inst_1552_);
lean_dec_ref(v_inst_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v_treeMap_1556_; lean_object* v_range_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_treeMap_1556_ = lean_ctor_get(v_x_1555_, 0);
lean_inc(v_treeMap_1556_);
v_range_1557_ = lean_ctor_get(v_x_1555_, 1);
lean_inc(v_range_1557_);
lean_dec_ref(v_x_1555_);
v___x_1558_ = lean_box(0);
v___x_1559_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1554_, v_treeMap_1556_, v_range_1557_, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1560_){
_start:
{
lean_object* v___f_1561_; 
v___f_1561_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1561_, 0, v_inst_1560_);
return v___f_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1562_, lean_object* v_inst_1563_){
_start:
{
lean_object* v___f_1564_; 
v___f_1564_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1564_, 0, v_inst_1563_);
return v___f_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1565_, lean_object* v_range_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_carrier_1565_);
lean_ctor_set(v___x_1567_, 1, v_range_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1570_; 
v___f_1570_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_inst_1575_){
_start:
{
lean_object* v___f_1576_; 
v___f_1576_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_inst_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1577_, v_00_u03b2_1578_, v_inst_1579_);
lean_dec_ref(v_inst_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1581_, lean_object* v_x_1582_){
_start:
{
lean_object* v_treeMap_1583_; lean_object* v_range_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_treeMap_1583_ = lean_ctor_get(v_x_1582_, 0);
lean_inc(v_treeMap_1583_);
v_range_1584_ = lean_ctor_get(v_x_1582_, 1);
lean_inc(v_range_1584_);
lean_dec_ref(v_x_1582_);
v___x_1585_ = lean_box(0);
v___x_1586_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1581_, v_treeMap_1583_, v_range_1584_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1587_){
_start:
{
lean_object* v___f_1588_; 
v___f_1588_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1588_, 0, v_inst_1587_);
return v___f_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_inst_1591_){
_start:
{
lean_object* v___f_1592_; 
v___f_1592_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1592_, 0, v_inst_1591_);
return v___f_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1593_, lean_object* v_t_1594_, lean_object* v_lowerBound_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_box(0);
v___x_1597_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1593_, v_t_1594_, v_lowerBound_1595_, v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1598_, lean_object* v_00_u03b2_1599_, lean_object* v_inst_1600_, lean_object* v_t_1601_, lean_object* v_lowerBound_1602_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_box(0);
v___x_1604_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1600_, v_t_1601_, v_lowerBound_1602_, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1605_, lean_object* v_range_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_carrier_1605_);
lean_ctor_set(v___x_1607_, 1, v_range_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1610_; 
v___f_1610_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_inst_1615_){
_start:
{
lean_object* v___f_1616_; 
v___f_1616_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1617_, lean_object* v_00_u03b2_1618_, lean_object* v_inst_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1617_, v_00_u03b2_1618_, v_inst_1619_);
lean_dec_ref(v_inst_1619_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v_treeMap_1623_; lean_object* v_range_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_treeMap_1623_ = lean_ctor_get(v_x_1622_, 0);
lean_inc(v_treeMap_1623_);
v_range_1624_ = lean_ctor_get(v_x_1622_, 1);
lean_inc(v_range_1624_);
lean_dec_ref(v_x_1622_);
v___x_1625_ = lean_box(0);
v___x_1626_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1621_, v_treeMap_1623_, v_range_1624_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1627_){
_start:
{
lean_object* v___f_1628_; 
v___f_1628_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1628_, 0, v_inst_1627_);
return v___f_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_inst_1631_){
_start:
{
lean_object* v___f_1632_; 
v___f_1632_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1632_, 0, v_inst_1631_);
return v___f_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0(lean_object* v_carrier_1633_, lean_object* v_range_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_carrier_1633_);
lean_ctor_set(v___x_1635_, 1, v_range_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg(){
_start:
{
lean_object* v___f_1638_; 
v___f_1638_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___boxed(lean_object* v___dummy_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1641_, lean_object* v_inst_1642_){
_start:
{
lean_object* v___f_1643_; 
v___f_1643_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_inst_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1644_, v_inst_1645_);
lean_dec_ref(v_inst_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v_treeMap_1649_; lean_object* v_range_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_treeMap_1649_ = lean_ctor_get(v_x_1648_, 0);
lean_inc(v_treeMap_1649_);
v_range_1650_ = lean_ctor_get(v_x_1648_, 1);
lean_inc(v_range_1650_);
lean_dec_ref(v_x_1648_);
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1647_, v_treeMap_1649_, v_range_1650_, v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1653_){
_start:
{
lean_object* v___f_1654_; 
v___f_1654_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1654_, 0, v_inst_1653_);
return v___f_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1655_, lean_object* v_inst_1656_){
_start:
{
lean_object* v___f_1657_; 
v___f_1657_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1657_, 0, v_inst_1656_);
return v___f_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1658_, lean_object* v_range_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v_carrier_1658_);
lean_ctor_set(v___x_1660_, 1, v_range_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1663_; 
v___f_1663_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_inst_1668_){
_start:
{
lean_object* v___f_1669_; 
v___f_1669_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_inst_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1670_, v_00_u03b2_1671_, v_inst_1672_);
lean_dec_ref(v_inst_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_treeMap_1676_; lean_object* v_range_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_treeMap_1676_ = lean_ctor_get(v_x_1675_, 0);
lean_inc(v_treeMap_1676_);
v_range_1677_ = lean_ctor_get(v_x_1675_, 1);
lean_inc(v_range_1677_);
lean_dec_ref(v_x_1675_);
v___x_1678_ = lean_box(0);
v___x_1679_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1674_, v_treeMap_1676_, v_range_1677_, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1680_){
_start:
{
lean_object* v___f_1681_; 
v___f_1681_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1681_, 0, v_inst_1680_);
return v___f_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03b2_1683_, lean_object* v_inst_1684_){
_start:
{
lean_object* v___f_1685_; 
v___f_1685_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1685_, 0, v_inst_1684_);
return v___f_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1686_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1689_);
lean_dec(v_t_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1691_, lean_object* v_00_u03b2_1692_, lean_object* v_t_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_t_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1695_, v_00_u03b2_1696_, v_t_1697_);
lean_dec(v_t_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1699_, lean_object* v_range_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_carrier_1699_);
lean_ctor_set(v___x_1701_, 1, v_range_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1704_; 
v___f_1704_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1707_, lean_object* v_00_u03b2_1708_){
_start:
{
lean_object* v___f_1709_; 
v___f_1709_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1710_){
_start:
{
lean_object* v_treeMap_1711_; lean_object* v___x_1712_; 
v_treeMap_1711_ = lean_ctor_get(v_x_1710_, 0);
v___x_1712_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(v_x_1713_);
lean_dec_ref(v_x_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1717_; 
v___f_1717_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_){
_start:
{
lean_object* v___f_1722_; 
v___f_1722_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0(lean_object* v_carrier_1723_, lean_object* v_range_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_carrier_1723_);
lean_ctor_set(v___x_1725_, 1, v_range_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg(){
_start:
{
lean_object* v___f_1728_; 
v___f_1728_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___boxed(lean_object* v___dummy_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1731_){
_start:
{
lean_object* v___f_1732_; 
v___f_1732_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1733_){
_start:
{
lean_object* v_treeMap_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_treeMap_1734_ = lean_ctor_get(v_x_1733_, 0);
v___x_1735_ = lean_box(0);
v___x_1736_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1734_, v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(v_x_1737_);
lean_dec_ref(v_x_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1741_; 
v___f_1741_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1744_){
_start:
{
lean_object* v___f_1745_; 
v___f_1745_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1746_, lean_object* v_range_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_carrier_1746_);
lean_ctor_set(v___x_1748_, 1, v_range_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1751_; 
v___f_1751_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_){
_start:
{
lean_object* v___f_1756_; 
v___f_1756_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1757_){
_start:
{
lean_object* v_treeMap_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_treeMap_1758_ = lean_ctor_get(v_x_1757_, 0);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1758_, v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(v_x_1761_);
lean_dec_ref(v_x_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1765_; 
v___f_1765_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1768_, lean_object* v_00_u03b2_1769_){
_start:
{
lean_object* v___f_1770_; 
v___f_1770_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1770_;
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
