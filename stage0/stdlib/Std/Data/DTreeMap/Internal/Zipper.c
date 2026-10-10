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
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_){
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
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_55_ = stack[0].m_num;
lean_object* v_h__1_56_ = stack[1].m_obj;
lean_object* v_h__2_57_ = stack[2].m_obj;
lean_object* v_h__3_58_ = stack[3].m_obj;
lean_object* v_res_65_;
v_res_65_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_55_, v_h__1_56_, v_h__2_57_, v_h__3_58_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object* v_x_66_, lean_object* v_h__1_67_, lean_object* v_h__2_68_, lean_object* v_h__3_69_){
_start:
{
uint8_t v_x_33__boxed_70_; lean_object* v_res_71_; 
v_x_33__boxed_70_ = lean_unbox(v_x_66_);
v_res_71_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_33__boxed_70_, v_h__1_67_, v_h__2_68_, v_h__3_69_);
return v_res_71_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object* v_motive_72_, uint8_t v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
_start:
{
switch(v_x_73_)
{
case 0:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_h__3_76_);
lean_dec(v_h__2_75_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_apply_1(v_h__1_74_, v___x_77_);
return v___x_78_;
}
case 1:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_h__3_76_);
lean_dec(v_h__1_74_);
v___x_79_ = lean_box(0);
v___x_80_ = lean_apply_1(v_h__2_75_, v___x_79_);
return v___x_80_;
}
default: 
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_75_);
lean_dec(v_h__1_74_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__3_76_, v___x_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_73_ = stack[1].m_num;
lean_object* v_h__1_74_ = stack[2].m_obj;
lean_object* v_h__2_75_ = stack[3].m_obj;
lean_object* v_h__3_76_ = stack[4].m_obj;
lean_object* v_res_83_;
v_res_83_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_box(0), v_x_73_, v_h__1_74_, v_h__2_75_, v_h__3_76_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object* v_motive_84_, lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_, lean_object* v_h__3_88_){
_start:
{
uint8_t v_x_56__boxed_89_; lean_object* v_res_90_; 
v_x_56__boxed_89_ = lean_unbox(v_x_85_);
v_res_90_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_84_, v_x_56__boxed_89_, v_h__1_86_, v_h__2_87_, v_h__3_88_);
return v_res_90_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t v_x_91_, lean_object* v_h__1_92_, lean_object* v_h__2_93_){
_start:
{
if (v_x_91_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_h__1_92_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_1(v_h__2_93_, v___x_94_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v_h__2_93_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_apply_1(v_h__1_92_, v___x_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_91_ = stack[0].m_num;
lean_object* v_h__1_92_ = stack[1].m_obj;
lean_object* v_h__2_93_ = stack[2].m_obj;
lean_object* v_res_98_;
v_res_98_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_91_, v_h__1_92_, v_h__2_93_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
uint8_t v_x_24__boxed_102_; lean_object* v_res_103_; 
v_x_24__boxed_102_ = lean_unbox(v_x_99_);
v_res_103_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_102_, v_h__1_100_, v_h__2_101_);
return v_res_103_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object* v_motive_104_, uint8_t v_x_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_){
_start:
{
if (v_x_105_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_h__1_106_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_apply_1(v_h__2_107_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v_h__2_107_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_apply_1(v_h__1_106_, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_105_ = stack[1].m_num;
lean_object* v_h__1_106_ = stack[2].m_obj;
lean_object* v_h__2_107_ = stack[3].m_obj;
lean_object* v_res_112_;
v_res_112_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_box(0), v_x_105_, v_h__1_106_, v_h__2_107_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_){
_start:
{
uint8_t v_x_41__boxed_117_; lean_object* v_res_118_; 
v_x_41__boxed_117_ = lean_unbox(v_x_114_);
v_res_118_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(v_motive_113_, v_x_41__boxed_117_, v_h__1_115_, v_h__2_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(lean_object* v_x_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_tag_nat(v_x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg___boxed(lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___redArg(v_x_121_);
lean_dec(v_x_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_tag_nat(v_x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl___boxed(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___impl(v_00_u03b1_127_, v_00_u03b2_128_, v_x_129_);
lean_dec(v_x_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* v_t_131_, lean_object* v_k_132_){
_start:
{
if (lean_obj_tag(v_t_131_) == 0)
{
return v_k_132_;
}
else
{
lean_object* v_k_133_; lean_object* v_v_134_; lean_object* v_tree_135_; lean_object* v_next_136_; lean_object* v___x_137_; 
v_k_133_ = lean_ctor_get(v_t_131_, 0);
lean_inc(v_k_133_);
v_v_134_ = lean_ctor_get(v_t_131_, 1);
lean_inc(v_v_134_);
v_tree_135_ = lean_ctor_get(v_t_131_, 2);
lean_inc(v_tree_135_);
v_next_136_ = lean_ctor_get(v_t_131_, 3);
lean_inc(v_next_136_);
lean_dec_ref_known(v_t_131_, 4);
v___x_137_ = lean_apply_4(v_k_132_, v_k_133_, v_v_134_, v_tree_135_, v_next_136_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* v_00_u03b1_138_, lean_object* v_00_u03b2_139_, lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_142_, v_k_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_motive_148_, lean_object* v_ctorIdx_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(v_00_u03b1_146_, v_00_u03b2_147_, v_motive_148_, v_ctorIdx_149_, v_t_150_, v_h_151_, v_k_152_);
lean_dec(v_ctorIdx_149_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* v_t_154_, lean_object* v_done_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_154_, v_done_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_done_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_160_, v_done_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* v_t_164_, lean_object* v_cons_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_164_, v_cons_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* v_00_u03b1_167_, lean_object* v_00_u03b2_168_, lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_cons_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_170_, v_cons_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* v_init_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v_k_176_; lean_object* v_v_177_; lean_object* v_l_178_; lean_object* v_r_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_k_176_ = lean_ctor_get(v_x_175_, 1);
v_v_177_ = lean_ctor_get(v_x_175_, 2);
v_l_178_ = lean_ctor_get(v_x_175_, 3);
v_r_179_ = lean_ctor_get(v_x_175_, 4);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_174_, v_r_179_);
lean_inc(v_v_177_);
lean_inc(v_k_176_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_k_176_);
lean_ctor_set(v___x_181_, 1, v_v_177_);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
v_init_174_ = v___x_182_;
v_x_175_ = v_l_178_;
goto _start;
}
else
{
return v_init_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* v_init_184_, lean_object* v_x_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_184_, v_x_185_);
lean_dec(v_x_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
lean_object* v_k_189_; lean_object* v_v_190_; lean_object* v_tree_191_; lean_object* v_next_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_k_189_ = lean_ctor_get(v_x_187_, 0);
v_v_190_ = lean_ctor_get(v_x_187_, 1);
v_tree_191_ = lean_ctor_get(v_x_187_, 2);
v_next_192_ = lean_ctor_get(v_x_187_, 3);
lean_inc(v_v_190_);
lean_inc(v_k_189_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_k_189_);
lean_ctor_set(v___x_193_, 1, v_v_190_);
v___x_194_ = lean_box(0);
v___x_195_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_194_, v_tree_191_);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_193_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_192_);
v___x_198_ = l_List_appendTR___redArg(v___x_196_, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_199_);
lean_dec(v_x_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_205_, v_00_u03b2_206_, v_x_207_);
lean_dec(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_init_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_211_, v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_init_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(v_00_u03b1_214_, v_00_u03b2_215_, v_init_216_, v_x_217_);
lean_dec(v_x_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(0u);
return v___x_220_;
}
else
{
lean_object* v_tree_221_; lean_object* v_next_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_tree_221_ = lean_ctor_get(v_x_219_, 2);
v_next_222_ = lean_ctor_get(v_x_219_, 3);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_221_);
v___x_225_ = lean_nat_add(v___x_223_, v___x_224_);
lean_dec(v___x_224_);
v___x_226_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_222_);
v___x_227_ = lean_nat_add(v___x_225_, v___x_226_);
lean_dec(v___x_226_);
lean_dec(v___x_225_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_228_);
lean_dec(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* v_00_u03b1_230_, lean_object* v_00_u03b2_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(v_00_u03b1_234_, v_00_u03b2_235_, v_x_236_);
lean_dec(v_x_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_object* v_k_240_; lean_object* v_v_241_; lean_object* v_l_242_; lean_object* v_r_243_; lean_object* v___x_244_; 
v_k_240_ = lean_ctor_get(v_x_238_, 1);
v_v_241_ = lean_ctor_get(v_x_238_, 2);
v_l_242_ = lean_ctor_get(v_x_238_, 3);
v_r_243_ = lean_ctor_get(v_x_238_, 4);
lean_inc(v_r_243_);
lean_inc(v_v_241_);
lean_inc(v_k_240_);
v___x_244_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_244_, 0, v_k_240_);
lean_ctor_set(v___x_244_, 1, v_v_241_);
lean_ctor_set(v___x_244_, 2, v_r_243_);
lean_ctor_set(v___x_244_, 3, v_x_239_);
v_x_238_ = v_l_242_;
v_x_239_ = v___x_244_;
goto _start;
}
else
{
return v_x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_246_, v_x_247_);
lean_dec(v_x_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_251_, v_x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_DTreeMap_Internal_Zipper_prependMap(v_00_u03b1_254_, v_00_u03b2_255_, v_x_256_, v_x_257_);
lean_dec(v_x_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* v_inst_259_, lean_object* v_t_260_, lean_object* v_lowerBound_261_, lean_object* v_it_262_){
_start:
{
if (lean_obj_tag(v_t_260_) == 0)
{
lean_object* v_k_263_; lean_object* v_v_264_; lean_object* v_l_265_; lean_object* v_r_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_k_263_ = lean_ctor_get(v_t_260_, 1);
lean_inc_n(v_k_263_, 2);
v_v_264_ = lean_ctor_get(v_t_260_, 2);
lean_inc(v_v_264_);
v_l_265_ = lean_ctor_get(v_t_260_, 3);
lean_inc(v_l_265_);
v_r_266_ = lean_ctor_get(v_t_260_, 4);
lean_inc(v_r_266_);
lean_dec_ref_known(v_t_260_, 5);
lean_inc_ref(v_inst_259_);
lean_inc(v_lowerBound_261_);
v___x_267_ = lean_apply_2(v_inst_259_, v_lowerBound_261_, v_k_263_);
v___x_268_ = lean_unbox(v___x_267_);
switch(v___x_268_)
{
case 0:
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_269_, 0, v_k_263_);
lean_ctor_set(v___x_269_, 1, v_v_264_);
lean_ctor_set(v___x_269_, 2, v_r_266_);
lean_ctor_set(v___x_269_, 3, v_it_262_);
v_t_260_ = v_l_265_;
v_it_262_ = v___x_269_;
goto _start;
}
case 1:
{
lean_object* v___x_271_; 
lean_dec(v_l_265_);
lean_dec(v_lowerBound_261_);
lean_dec_ref(v_inst_259_);
v___x_271_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_271_, 0, v_k_263_);
lean_ctor_set(v___x_271_, 1, v_v_264_);
lean_ctor_set(v___x_271_, 2, v_r_266_);
lean_ctor_set(v___x_271_, 3, v_it_262_);
return v___x_271_;
}
default: 
{
lean_dec(v_l_265_);
lean_dec(v_v_264_);
lean_dec(v_k_263_);
v_t_260_ = v_r_266_;
goto _start;
}
}
}
else
{
lean_dec(v_lowerBound_261_);
lean_dec_ref(v_inst_259_);
return v_it_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* v_00_u03b1_273_, lean_object* v_00_u03b2_274_, lean_object* v_inst_275_, lean_object* v_t_276_, lean_object* v_lowerBound_277_, lean_object* v_it_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_275_, v_t_276_, v_lowerBound_277_, v_it_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* v_inst_280_, lean_object* v_t_281_, lean_object* v_lowerBound_282_, lean_object* v_it_283_){
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
if (v___x_289_ == 0)
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
else
{
lean_dec(v_l_286_);
lean_dec(v_v_285_);
lean_dec(v_k_284_);
v_t_281_ = v_r_287_;
goto _start;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_inst_295_, lean_object* v_t_296_, lean_object* v_lowerBound_297_, lean_object* v_it_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_295_, v_t_296_, v_lowerBound_297_, v_it_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v_size_304_; lean_object* v_k_305_; lean_object* v_v_306_; lean_object* v_l_307_; lean_object* v_r_308_; lean_object* v___x_309_; 
lean_dec(v_h__1_302_);
v_size_304_ = lean_ctor_get(v_x_300_, 0);
lean_inc(v_size_304_);
v_k_305_ = lean_ctor_get(v_x_300_, 1);
lean_inc(v_k_305_);
v_v_306_ = lean_ctor_get(v_x_300_, 2);
lean_inc(v_v_306_);
v_l_307_ = lean_ctor_get(v_x_300_, 3);
lean_inc(v_l_307_);
v_r_308_ = lean_ctor_get(v_x_300_, 4);
lean_inc(v_r_308_);
lean_dec_ref_known(v_x_300_, 5);
v___x_309_ = lean_apply_6(v_h__2_303_, v_size_304_, v_k_305_, v_v_306_, v_l_307_, v_r_308_, v_x_301_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
lean_dec(v_h__2_303_);
v___x_310_ = lean_apply_1(v_h__1_302_, v_x_301_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_motive_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v_size_318_; lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v_l_321_; lean_object* v_r_322_; lean_object* v___x_323_; 
lean_dec(v_h__1_316_);
v_size_318_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_size_318_);
v_k_319_ = lean_ctor_get(v_x_314_, 1);
lean_inc(v_k_319_);
v_v_320_ = lean_ctor_get(v_x_314_, 2);
lean_inc(v_v_320_);
v_l_321_ = lean_ctor_get(v_x_314_, 3);
lean_inc(v_l_321_);
v_r_322_ = lean_ctor_get(v_x_314_, 4);
lean_inc(v_r_322_);
lean_dec_ref_known(v_x_314_, 5);
v___x_323_ = lean_apply_6(v_h__2_317_, v_size_318_, v_k_319_, v_v_320_, v_l_321_, v_r_322_, v_x_315_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v_h__2_317_);
v___x_324_ = lean_apply_1(v_h__1_316_, v_x_315_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_box(2);
return v___x_326_;
}
else
{
lean_object* v_k_327_; lean_object* v_v_328_; lean_object* v_tree_329_; lean_object* v_next_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_k_327_ = lean_ctor_get(v_x_325_, 0);
lean_inc(v_k_327_);
v_v_328_ = lean_ctor_get(v_x_325_, 1);
lean_inc(v_v_328_);
v_tree_329_ = lean_ctor_get(v_x_325_, 2);
lean_inc(v_tree_329_);
v_next_330_ = lean_ctor_get(v_x_325_, 3);
lean_inc(v_next_330_);
lean_dec_ref_known(v_x_325_, 4);
v___x_331_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_329_, v_next_330_);
lean_dec(v_tree_329_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_k_327_);
lean_ctor_set(v___x_332_, 1, v_v_328_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b2_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_336_);
return v___x_337_;
}
}
lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg(){
_start:
{
lean_object* v___f_340_; 
v___f_340_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_340_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_341_;
v_res_341_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___boxed(lean_object* v___dummy_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg();
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_){
_start:
{
lean_object* v___f_346_; 
v___f_346_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___redArg___closed__0));
return v___f_346_;
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
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_372_;
v_res_372_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg___boxed(lean_object* v___dummy_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation___redArg();
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_378_, lean_object* v_recur_379_, lean_object* v_it_380_, lean_object* v_____do__lift_381_){
_start:
{
if (lean_obj_tag(v_____do__lift_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; 
lean_dec(v_it_380_);
lean_dec(v_recur_379_);
v_a_382_ = lean_ctor_get(v_____do__lift_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v_____do__lift_381_, 1);
v___x_383_ = lean_apply_2(v_toPure_378_, lean_box(0), v_a_382_);
return v___x_383_;
}
else
{
lean_object* v_a_384_; lean_object* v___x_385_; 
lean_dec(v_toPure_378_);
v_a_384_ = lean_ctor_get(v_____do__lift_381_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v_____do__lift_381_, 1);
v___x_385_ = lean_apply_4(v_recur_379_, v_it_380_, v_a_384_, lean_box(0), lean_box(0));
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_386_, lean_object* v_recur_387_, lean_object* v___y_388_, lean_object* v_acc_389_, lean_object* v_toBind_390_, lean_object* v_s_391_){
_start:
{
switch(lean_obj_tag(v_s_391_))
{
case 0:
{
lean_object* v_it_392_; lean_object* v_out_393_; lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_it_392_ = lean_ctor_get(v_s_391_, 0);
lean_inc(v_it_392_);
v_out_393_ = lean_ctor_get(v_s_391_, 1);
lean_inc(v_out_393_);
lean_dec_ref_known(v_s_391_, 2);
v___f_394_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_394_, 0, v_toPure_386_);
lean_closure_set(v___f_394_, 1, v_recur_387_);
lean_closure_set(v___f_394_, 2, v_it_392_);
v___x_395_ = lean_apply_3(v___y_388_, v_out_393_, lean_box(0), v_acc_389_);
v___x_396_ = lean_apply_4(v_toBind_390_, lean_box(0), lean_box(0), v___x_395_, v___f_394_);
return v___x_396_;
}
case 1:
{
lean_object* v_it_397_; lean_object* v___x_398_; 
lean_dec(v_toBind_390_);
lean_dec(v___y_388_);
lean_dec(v_toPure_386_);
v_it_397_ = lean_ctor_get(v_s_391_, 0);
lean_inc(v_it_397_);
lean_dec_ref_known(v_s_391_, 1);
v___x_398_ = lean_apply_4(v_recur_387_, v_it_397_, v_acc_389_, lean_box(0), lean_box(0));
return v___x_398_;
}
default: 
{
lean_object* v___x_399_; 
lean_dec(v_toBind_390_);
lean_dec(v___y_388_);
lean_dec(v_recur_387_);
v___x_399_ = lean_apply_2(v_toPure_386_, lean_box(0), v_acc_389_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_400_, lean_object* v___y_401_, lean_object* v_toBind_402_, lean_object* v_lift_403_, lean_object* v_it_404_, lean_object* v_acc_405_, lean_object* v_hP_406_, lean_object* v_recur_407_){
_start:
{
lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___f_408_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_408_, 0, v_toPure_400_);
lean_closure_set(v___f_408_, 1, v_recur_407_);
lean_closure_set(v___f_408_, 2, v___y_401_);
lean_closure_set(v___f_408_, 3, v_acc_405_);
lean_closure_set(v___f_408_, 4, v_toBind_402_);
v___x_409_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_it_404_);
v___x_410_ = lean_apply_4(v_lift_403_, lean_box(0), lean_box(0), v___f_408_, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_411_, lean_object* v_lift_412_, lean_object* v_00_u03b3_413_, lean_object* v_Pl_414_, lean_object* v_it_415_, lean_object* v_init_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_toApplicative_418_; lean_object* v_toBind_419_; lean_object* v_toPure_420_; lean_object* v___f_421_; lean_object* v___x_422_; 
v_toApplicative_418_ = lean_ctor_get(v_inst_411_, 0);
lean_inc_ref(v_toApplicative_418_);
v_toBind_419_ = lean_ctor_get(v_inst_411_, 1);
lean_inc(v_toBind_419_);
lean_dec_ref(v_inst_411_);
v_toPure_420_ = lean_ctor_get(v_toApplicative_418_, 1);
lean_inc(v_toPure_420_);
lean_dec_ref(v_toApplicative_418_);
v___f_421_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_421_, 0, v_toPure_420_);
lean_closure_set(v___f_421_, 1, v___y_417_);
lean_closure_set(v___f_421_, 2, v_toBind_419_);
lean_closure_set(v___f_421_, 3, v_lift_412_);
v___x_422_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_421_, v_it_415_, v_init_416_, lean_box(0));
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object* v_inst_423_){
_start:
{
lean_object* v___f_424_; 
v___f_424_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_424_, 0, v_inst_423_);
return v___f_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_m_427_, lean_object* v_inst_428_){
_start:
{
lean_object* v___f_429_; 
v___f_429_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_429_, 0, v_inst_428_);
return v___f_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_430_){
_start:
{
lean_inc(v_t_430_);
return v_t_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_431_);
lean_dec(v_t_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_433_, lean_object* v_00_u03b2_434_, lean_object* v_t_435_){
_start:
{
lean_inc(v_t_435_);
return v_t_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_t_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_436_, v_00_u03b2_437_, v_t_438_);
lean_dec(v_t_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_box(0);
v___x_442_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_443_);
lean_dec(v_t_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_445_, lean_object* v_00_u03b2_446_, lean_object* v_t_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_449_, lean_object* v_00_u03b2_450_, lean_object* v_t_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_449_, v_00_u03b2_450_, v_t_451_);
lean_dec(v_t_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(lean_object* v_x_453_){
_start:
{
lean_inc(v_x_453_);
return v_x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0___boxed(lean_object* v_x_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___lam__0(v_x_454_);
lean_dec(v_x_454_);
return v_res_455_;
}
}
lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg(){
_start:
{
lean_object* v___f_458_; 
v___f_458_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_458_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_459_;
v_res_459_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___boxed(lean_object* v___dummy_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg();
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_){
_start:
{
lean_object* v___f_464_; 
v___f_464_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___redArg___closed__0));
return v___f_464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_, lean_object* v_h__3_468_){
_start:
{
switch(lean_obj_tag(v_x_465_))
{
case 0:
{
lean_object* v_it_469_; lean_object* v_out_470_; lean_object* v___x_471_; 
lean_dec(v_h__3_468_);
lean_dec(v_h__2_467_);
v_it_469_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_it_469_);
v_out_470_ = lean_ctor_get(v_x_465_, 1);
lean_inc(v_out_470_);
lean_dec_ref_known(v_x_465_, 2);
v___x_471_ = lean_apply_2(v_h__1_466_, v_it_469_, v_out_470_);
return v___x_471_;
}
case 1:
{
lean_object* v_it_472_; lean_object* v___x_473_; 
lean_dec(v_h__3_468_);
lean_dec(v_h__1_466_);
v_it_472_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_it_472_);
lean_dec_ref_known(v_x_465_, 1);
v___x_473_ = lean_apply_1(v_h__2_467_, v_it_472_);
return v___x_473_;
}
default: 
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_h__2_467_);
lean_dec(v_h__1_466_);
v___x_474_ = lean_box(0);
v___x_475_ = lean_apply_1(v_h__3_468_, v___x_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_m_478_, lean_object* v_motive_479_, lean_object* v_x_480_, lean_object* v_h__1_481_, lean_object* v_h__2_482_, lean_object* v_h__3_483_){
_start:
{
switch(lean_obj_tag(v_x_480_))
{
case 0:
{
lean_object* v_it_484_; lean_object* v_out_485_; lean_object* v___x_486_; 
lean_dec(v_h__3_483_);
lean_dec(v_h__2_482_);
v_it_484_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_it_484_);
v_out_485_ = lean_ctor_get(v_x_480_, 1);
lean_inc(v_out_485_);
lean_dec_ref_known(v_x_480_, 2);
v___x_486_ = lean_apply_2(v_h__1_481_, v_it_484_, v_out_485_);
return v___x_486_;
}
case 1:
{
lean_object* v_it_487_; lean_object* v___x_488_; 
lean_dec(v_h__3_483_);
lean_dec(v_h__1_481_);
v_it_487_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_it_487_);
lean_dec_ref_known(v_x_480_, 1);
v___x_488_ = lean_apply_1(v_h__2_482_, v_it_487_);
return v___x_488_;
}
default: 
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_h__2_482_);
lean_dec(v_h__1_481_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_apply_1(v_h__3_483_, v___x_489_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_iter_493_; 
v_iter_493_ = lean_ctor_get(v_x_492_, 0);
lean_inc(v_iter_493_);
if (lean_obj_tag(v_iter_493_) == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v_x_492_);
lean_dec_ref(v_inst_491_);
v___x_494_ = lean_box(2);
return v___x_494_;
}
else
{
lean_object* v_upper_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_512_; 
v_upper_495_ = lean_ctor_get(v_x_492_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_492_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v_x_492_, 0);
lean_dec(v_unused_513_);
v___x_497_ = v_x_492_;
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_upper_495_);
lean_dec(v_x_492_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_k_499_; lean_object* v_v_500_; lean_object* v_tree_501_; lean_object* v_next_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_k_499_ = lean_ctor_get(v_iter_493_, 0);
lean_inc_n(v_k_499_, 2);
v_v_500_ = lean_ctor_get(v_iter_493_, 1);
lean_inc(v_v_500_);
v_tree_501_ = lean_ctor_get(v_iter_493_, 2);
lean_inc(v_tree_501_);
v_next_502_ = lean_ctor_get(v_iter_493_, 3);
lean_inc(v_next_502_);
lean_dec_ref_known(v_iter_493_, 4);
lean_inc(v_upper_495_);
v___x_503_ = lean_apply_2(v_inst_491_, v_k_499_, v_upper_495_);
v___x_504_ = lean_unbox(v___x_503_);
if (v___x_504_ == 2)
{
lean_object* v___x_505_; 
lean_dec(v_next_502_);
lean_dec(v_tree_501_);
lean_dec(v_v_500_);
lean_dec(v_k_499_);
lean_del_object(v___x_497_);
lean_dec(v_upper_495_);
v___x_505_ = lean_box(2);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_501_, v_next_502_);
lean_dec(v_tree_501_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_506_);
v___x_508_ = v___x_497_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_upper_495_);
v___x_508_ = v_reuseFailAlloc_511_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_k_499_);
lean_ctor_set(v___x_509_, 1, v_v_500_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_inst_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_519_, lean_object* v_it_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_519_, v_it_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_522_){
_start:
{
lean_object* v___f_523_; 
v___f_523_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_523_, 0, v_inst_522_);
return v___f_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_inst_526_){
_start:
{
lean_object* v___f_527_; 
v___f_527_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_527_, 0, v_inst_526_);
return v___f_527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_){
_start:
{
lean_object* v_iter_531_; 
v_iter_531_ = lean_ctor_get(v_x_528_, 0);
if (lean_obj_tag(v_iter_531_) == 0)
{
lean_object* v_upper_532_; lean_object* v___x_533_; 
lean_dec(v_h__2_530_);
v_upper_532_ = lean_ctor_get(v_x_528_, 1);
lean_inc(v_upper_532_);
lean_dec_ref(v_x_528_);
v___x_533_ = lean_apply_1(v_h__1_529_, v_upper_532_);
return v___x_533_;
}
else
{
lean_object* v_upper_534_; lean_object* v_k_535_; lean_object* v_v_536_; lean_object* v_tree_537_; lean_object* v_next_538_; lean_object* v___x_539_; 
lean_inc_ref(v_iter_531_);
lean_dec(v_h__1_529_);
v_upper_534_ = lean_ctor_get(v_x_528_, 1);
lean_inc(v_upper_534_);
lean_dec_ref(v_x_528_);
v_k_535_ = lean_ctor_get(v_iter_531_, 0);
lean_inc(v_k_535_);
v_v_536_ = lean_ctor_get(v_iter_531_, 1);
lean_inc(v_v_536_);
v_tree_537_ = lean_ctor_get(v_iter_531_, 2);
lean_inc(v_tree_537_);
v_next_538_ = lean_ctor_get(v_iter_531_, 3);
lean_inc(v_next_538_);
lean_dec_ref_known(v_iter_531_, 4);
v___x_539_ = lean_apply_5(v_h__2_530_, v_k_535_, v_v_536_, v_tree_537_, v_next_538_, v_upper_534_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, lean_object* v_inst_542_, lean_object* v_motive_543_, lean_object* v_x_544_, lean_object* v_h__1_545_, lean_object* v_h__2_546_){
_start:
{
lean_object* v_iter_547_; 
v_iter_547_ = lean_ctor_get(v_x_544_, 0);
if (lean_obj_tag(v_iter_547_) == 0)
{
lean_object* v_upper_548_; lean_object* v___x_549_; 
lean_dec(v_h__2_546_);
v_upper_548_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_upper_548_);
lean_dec_ref(v_x_544_);
v___x_549_ = lean_apply_1(v_h__1_545_, v_upper_548_);
return v___x_549_;
}
else
{
lean_object* v_upper_550_; lean_object* v_k_551_; lean_object* v_v_552_; lean_object* v_tree_553_; lean_object* v_next_554_; lean_object* v___x_555_; 
lean_inc_ref(v_iter_547_);
lean_dec(v_h__1_545_);
v_upper_550_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_upper_550_);
lean_dec_ref(v_x_544_);
v_k_551_ = lean_ctor_get(v_iter_547_, 0);
lean_inc(v_k_551_);
v_v_552_ = lean_ctor_get(v_iter_547_, 1);
lean_inc(v_v_552_);
v_tree_553_ = lean_ctor_get(v_iter_547_, 2);
lean_inc(v_tree_553_);
v_next_554_ = lean_ctor_get(v_iter_547_, 3);
lean_inc(v_next_554_);
lean_dec_ref_known(v_iter_547_, 4);
v___x_555_ = lean_apply_5(v_h__2_546_, v_k_551_, v_v_552_, v_tree_553_, v_next_554_, v_upper_550_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_, lean_object* v_motive_559_, lean_object* v_x_560_, lean_object* v_h__1_561_, lean_object* v_h__2_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_556_, v_00_u03b2_557_, v_inst_558_, v_motive_559_, v_x_560_, v_h__1_561_, v_h__2_562_);
lean_dec_ref(v_inst_558_);
return v_res_563_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg(){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_box(0);
return v___x_565_;
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_566_;
v_res_566_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg___boxed(lean_object* v___dummy_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___redArg();
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_569_, lean_object* v_00_u03b2_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_inst_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_573_, v_00_u03b2_574_, v_inst_575_);
lean_dec_ref(v_inst_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_577_, lean_object* v_recur_578_, lean_object* v_it_579_, lean_object* v_____do__lift_580_){
_start:
{
if (lean_obj_tag(v_____do__lift_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
lean_dec_ref(v_it_579_);
lean_dec(v_recur_578_);
v_a_581_ = lean_ctor_get(v_____do__lift_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v_____do__lift_580_, 1);
v___x_582_ = lean_apply_2(v_toPure_577_, lean_box(0), v_a_581_);
return v___x_582_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_584_; 
lean_dec(v_toPure_577_);
v_a_583_ = lean_ctor_get(v_____do__lift_580_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v_____do__lift_580_, 1);
v___x_584_ = lean_apply_4(v_recur_578_, v_it_579_, v_a_583_, lean_box(0), lean_box(0));
return v___x_584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_585_, lean_object* v_recur_586_, lean_object* v___y_587_, lean_object* v_acc_588_, lean_object* v_toBind_589_, lean_object* v_s_590_){
_start:
{
switch(lean_obj_tag(v_s_590_))
{
case 0:
{
lean_object* v_it_591_; lean_object* v_out_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_it_591_ = lean_ctor_get(v_s_590_, 0);
lean_inc(v_it_591_);
v_out_592_ = lean_ctor_get(v_s_590_, 1);
lean_inc(v_out_592_);
lean_dec_ref_known(v_s_590_, 2);
v___f_593_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_593_, 0, v_toPure_585_);
lean_closure_set(v___f_593_, 1, v_recur_586_);
lean_closure_set(v___f_593_, 2, v_it_591_);
v___x_594_ = lean_apply_3(v___y_587_, v_out_592_, lean_box(0), v_acc_588_);
v___x_595_ = lean_apply_4(v_toBind_589_, lean_box(0), lean_box(0), v___x_594_, v___f_593_);
return v___x_595_;
}
case 1:
{
lean_object* v_it_596_; lean_object* v___x_597_; 
lean_dec(v_toBind_589_);
lean_dec(v___y_587_);
lean_dec(v_toPure_585_);
v_it_596_ = lean_ctor_get(v_s_590_, 0);
lean_inc(v_it_596_);
lean_dec_ref_known(v_s_590_, 1);
v___x_597_ = lean_apply_4(v_recur_586_, v_it_596_, v_acc_588_, lean_box(0), lean_box(0));
return v___x_597_;
}
default: 
{
lean_object* v___x_598_; 
lean_dec(v_toBind_589_);
lean_dec(v___y_587_);
lean_dec(v_recur_586_);
v___x_598_ = lean_apply_2(v_toPure_585_, lean_box(0), v_acc_588_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_599_, lean_object* v___y_600_, lean_object* v_toBind_601_, lean_object* v_inst_602_, lean_object* v_lift_603_, lean_object* v_it_604_, lean_object* v_acc_605_, lean_object* v_hP_606_, lean_object* v_recur_607_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___f_608_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_608_, 0, v_toPure_599_);
lean_closure_set(v___f_608_, 1, v_recur_607_);
lean_closure_set(v___f_608_, 2, v___y_600_);
lean_closure_set(v___f_608_, 3, v_acc_605_);
lean_closure_set(v___f_608_, 4, v_toBind_601_);
v___x_609_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_602_, v_it_604_);
v___x_610_ = lean_apply_4(v_lift_603_, lean_box(0), lean_box(0), v___f_608_, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_lift_613_, lean_object* v_00_u03b3_614_, lean_object* v_Pl_615_, lean_object* v_it_616_, lean_object* v_init_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_toApplicative_619_; lean_object* v_toBind_620_; lean_object* v_toPure_621_; lean_object* v___f_622_; lean_object* v___x_623_; 
v_toApplicative_619_ = lean_ctor_get(v_inst_611_, 0);
lean_inc_ref(v_toApplicative_619_);
v_toBind_620_ = lean_ctor_get(v_inst_611_, 1);
lean_inc(v_toBind_620_);
lean_dec_ref(v_inst_611_);
v_toPure_621_ = lean_ctor_get(v_toApplicative_619_, 1);
lean_inc(v_toPure_621_);
lean_dec_ref(v_toApplicative_619_);
v___f_622_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_622_, 0, v_toPure_621_);
lean_closure_set(v___f_622_, 1, v___y_618_);
lean_closure_set(v___f_622_, 2, v_toBind_620_);
lean_closure_set(v___f_622_, 3, v_inst_612_);
lean_closure_set(v___f_622_, 4, v_lift_613_);
v___x_623_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_622_, v_it_616_, v_init_617_, lean_box(0));
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object* v_inst_624_, lean_object* v_inst_625_){
_start:
{
lean_object* v___f_626_; 
v___f_626_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_626_, 0, v_inst_625_);
lean_closure_set(v___f_626_, 1, v_inst_624_);
return v___f_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_inst_629_, lean_object* v_m_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v___f_632_; 
v___f_632_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_632_, 0, v_inst_631_);
lean_closure_set(v___f_632_, 1, v_inst_629_);
return v___f_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_iter_635_; 
v_iter_635_ = lean_ctor_get(v_x_634_, 0);
lean_inc(v_iter_635_);
if (lean_obj_tag(v_iter_635_) == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v_x_634_);
lean_dec_ref(v_inst_633_);
v___x_636_ = lean_box(2);
return v___x_636_;
}
else
{
lean_object* v_upper_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_654_; 
v_upper_637_ = lean_ctor_get(v_x_634_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_634_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_x_634_, 0);
lean_dec(v_unused_655_);
v___x_639_ = v_x_634_;
v_isShared_640_ = v_isSharedCheck_654_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_upper_637_);
lean_dec(v_x_634_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_654_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_k_641_; lean_object* v_v_642_; lean_object* v_tree_643_; lean_object* v_next_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_k_641_ = lean_ctor_get(v_iter_635_, 0);
lean_inc_n(v_k_641_, 2);
v_v_642_ = lean_ctor_get(v_iter_635_, 1);
lean_inc(v_v_642_);
v_tree_643_ = lean_ctor_get(v_iter_635_, 2);
lean_inc(v_tree_643_);
v_next_644_ = lean_ctor_get(v_iter_635_, 3);
lean_inc(v_next_644_);
lean_dec_ref_known(v_iter_635_, 4);
lean_inc(v_upper_637_);
v___x_645_ = lean_apply_2(v_inst_633_, v_k_641_, v_upper_637_);
v___x_646_ = lean_unbox(v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_643_, v_next_644_);
lean_dec(v_tree_643_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_647_);
v___x_649_ = v___x_639_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_upper_637_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_k_641_);
lean_ctor_set(v___x_650_, 1, v_v_642_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
return v___x_651_;
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v_next_644_);
lean_dec(v_tree_643_);
lean_dec(v_v_642_);
lean_dec(v_k_641_);
lean_del_object(v___x_639_);
lean_dec(v_upper_637_);
v___x_653_ = lean_box(2);
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_inst_658_, lean_object* v_x_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_658_, v_x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_661_, lean_object* v_it_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_661_, v_it_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_664_){
_start:
{
lean_object* v___f_665_; 
v___f_665_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_665_, 0, v_inst_664_);
return v___f_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_inst_668_){
_start:
{
lean_object* v___f_669_; 
v___f_669_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_669_, 0, v_inst_668_);
return v___f_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_670_, lean_object* v_h__1_671_, lean_object* v_h__2_672_){
_start:
{
lean_object* v_iter_673_; 
v_iter_673_ = lean_ctor_get(v_x_670_, 0);
if (lean_obj_tag(v_iter_673_) == 0)
{
lean_object* v_upper_674_; lean_object* v___x_675_; 
lean_dec(v_h__2_672_);
v_upper_674_ = lean_ctor_get(v_x_670_, 1);
lean_inc(v_upper_674_);
lean_dec_ref(v_x_670_);
v___x_675_ = lean_apply_1(v_h__1_671_, v_upper_674_);
return v___x_675_;
}
else
{
lean_object* v_upper_676_; lean_object* v_k_677_; lean_object* v_v_678_; lean_object* v_tree_679_; lean_object* v_next_680_; lean_object* v___x_681_; 
lean_inc_ref(v_iter_673_);
lean_dec(v_h__1_671_);
v_upper_676_ = lean_ctor_get(v_x_670_, 1);
lean_inc(v_upper_676_);
lean_dec_ref(v_x_670_);
v_k_677_ = lean_ctor_get(v_iter_673_, 0);
lean_inc(v_k_677_);
v_v_678_ = lean_ctor_get(v_iter_673_, 1);
lean_inc(v_v_678_);
v_tree_679_ = lean_ctor_get(v_iter_673_, 2);
lean_inc(v_tree_679_);
v_next_680_ = lean_ctor_get(v_iter_673_, 3);
lean_inc(v_next_680_);
lean_dec_ref_known(v_iter_673_, 4);
v___x_681_ = lean_apply_5(v_h__2_672_, v_k_677_, v_v_678_, v_tree_679_, v_next_680_, v_upper_676_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_inst_684_, lean_object* v_motive_685_, lean_object* v_x_686_, lean_object* v_h__1_687_, lean_object* v_h__2_688_){
_start:
{
lean_object* v_iter_689_; 
v_iter_689_ = lean_ctor_get(v_x_686_, 0);
if (lean_obj_tag(v_iter_689_) == 0)
{
lean_object* v_upper_690_; lean_object* v___x_691_; 
lean_dec(v_h__2_688_);
v_upper_690_ = lean_ctor_get(v_x_686_, 1);
lean_inc(v_upper_690_);
lean_dec_ref(v_x_686_);
v___x_691_ = lean_apply_1(v_h__1_687_, v_upper_690_);
return v___x_691_;
}
else
{
lean_object* v_upper_692_; lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v_tree_695_; lean_object* v_next_696_; lean_object* v___x_697_; 
lean_inc_ref(v_iter_689_);
lean_dec(v_h__1_687_);
v_upper_692_ = lean_ctor_get(v_x_686_, 1);
lean_inc(v_upper_692_);
lean_dec_ref(v_x_686_);
v_k_693_ = lean_ctor_get(v_iter_689_, 0);
lean_inc(v_k_693_);
v_v_694_ = lean_ctor_get(v_iter_689_, 1);
lean_inc(v_v_694_);
v_tree_695_ = lean_ctor_get(v_iter_689_, 2);
lean_inc(v_tree_695_);
v_next_696_ = lean_ctor_get(v_iter_689_, 3);
lean_inc(v_next_696_);
lean_dec_ref_known(v_iter_689_, 4);
v___x_697_ = lean_apply_5(v_h__2_688_, v_k_693_, v_v_694_, v_tree_695_, v_next_696_, v_upper_692_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_698_, lean_object* v_00_u03b2_699_, lean_object* v_inst_700_, lean_object* v_motive_701_, lean_object* v_x_702_, lean_object* v_h__1_703_, lean_object* v_h__2_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_698_, v_00_u03b2_699_, v_inst_700_, v_motive_701_, v_x_702_, v_h__1_703_, v_h__2_704_);
lean_dec_ref(v_inst_700_);
return v_res_705_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_box(0);
return v___x_707_;
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_708_;
v_res_708_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___redArg();
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_inst_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_box(0);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_715_, lean_object* v_00_u03b2_716_, lean_object* v_inst_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_715_, v_00_u03b2_716_, v_inst_717_);
lean_dec_ref(v_inst_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_719_, lean_object* v_recur_720_, lean_object* v_it_721_, lean_object* v_____do__lift_722_){
_start:
{
if (lean_obj_tag(v_____do__lift_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; 
lean_dec_ref(v_it_721_);
lean_dec(v_recur_720_);
v_a_723_ = lean_ctor_get(v_____do__lift_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v_____do__lift_722_, 1);
v___x_724_ = lean_apply_2(v_toPure_719_, lean_box(0), v_a_723_);
return v___x_724_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_726_; 
lean_dec(v_toPure_719_);
v_a_725_ = lean_ctor_get(v_____do__lift_722_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v_____do__lift_722_, 1);
v___x_726_ = lean_apply_4(v_recur_720_, v_it_721_, v_a_725_, lean_box(0), lean_box(0));
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_727_, lean_object* v_recur_728_, lean_object* v___y_729_, lean_object* v_acc_730_, lean_object* v_toBind_731_, lean_object* v_s_732_){
_start:
{
switch(lean_obj_tag(v_s_732_))
{
case 0:
{
lean_object* v_it_733_; lean_object* v_out_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v_it_733_ = lean_ctor_get(v_s_732_, 0);
lean_inc(v_it_733_);
v_out_734_ = lean_ctor_get(v_s_732_, 1);
lean_inc(v_out_734_);
lean_dec_ref_known(v_s_732_, 2);
v___f_735_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_735_, 0, v_toPure_727_);
lean_closure_set(v___f_735_, 1, v_recur_728_);
lean_closure_set(v___f_735_, 2, v_it_733_);
v___x_736_ = lean_apply_3(v___y_729_, v_out_734_, lean_box(0), v_acc_730_);
v___x_737_ = lean_apply_4(v_toBind_731_, lean_box(0), lean_box(0), v___x_736_, v___f_735_);
return v___x_737_;
}
case 1:
{
lean_object* v_it_738_; lean_object* v___x_739_; 
lean_dec(v_toBind_731_);
lean_dec(v___y_729_);
lean_dec(v_toPure_727_);
v_it_738_ = lean_ctor_get(v_s_732_, 0);
lean_inc(v_it_738_);
lean_dec_ref_known(v_s_732_, 1);
v___x_739_ = lean_apply_4(v_recur_728_, v_it_738_, v_acc_730_, lean_box(0), lean_box(0));
return v___x_739_;
}
default: 
{
lean_object* v___x_740_; 
lean_dec(v_toBind_731_);
lean_dec(v___y_729_);
lean_dec(v_recur_728_);
v___x_740_ = lean_apply_2(v_toPure_727_, lean_box(0), v_acc_730_);
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_741_, lean_object* v___y_742_, lean_object* v_toBind_743_, lean_object* v_inst_744_, lean_object* v_lift_745_, lean_object* v_it_746_, lean_object* v_acc_747_, lean_object* v_hP_748_, lean_object* v_recur_749_){
_start:
{
lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___f_750_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_750_, 0, v_toPure_741_);
lean_closure_set(v___f_750_, 1, v_recur_749_);
lean_closure_set(v___f_750_, 2, v___y_742_);
lean_closure_set(v___f_750_, 3, v_acc_747_);
lean_closure_set(v___f_750_, 4, v_toBind_743_);
v___x_751_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_744_, v_it_746_);
v___x_752_ = lean_apply_4(v_lift_745_, lean_box(0), lean_box(0), v___f_750_, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_lift_755_, lean_object* v_00_u03b3_756_, lean_object* v_Pl_757_, lean_object* v_it_758_, lean_object* v_init_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_toApplicative_761_; lean_object* v_toBind_762_; lean_object* v_toPure_763_; lean_object* v___f_764_; lean_object* v___x_765_; 
v_toApplicative_761_ = lean_ctor_get(v_inst_753_, 0);
lean_inc_ref(v_toApplicative_761_);
v_toBind_762_ = lean_ctor_get(v_inst_753_, 1);
lean_inc(v_toBind_762_);
lean_dec_ref(v_inst_753_);
v_toPure_763_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_inc(v_toPure_763_);
lean_dec_ref(v_toApplicative_761_);
v___f_764_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_764_, 0, v_toPure_763_);
lean_closure_set(v___f_764_, 1, v___y_760_);
lean_closure_set(v___f_764_, 2, v_toBind_762_);
lean_closure_set(v___f_764_, 3, v_inst_754_);
lean_closure_set(v___f_764_, 4, v_lift_755_);
v___x_765_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_764_, v_it_758_, v_init_759_, lean_box(0));
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object* v_inst_766_, lean_object* v_inst_767_){
_start:
{
lean_object* v___f_768_; 
v___f_768_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_768_, 0, v_inst_767_);
lean_closure_set(v___f_768_, 1, v_inst_766_);
return v___f_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_inst_771_, lean_object* v_m_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v___f_774_; 
v___f_774_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_774_, 0, v_inst_773_);
lean_closure_set(v___f_774_, 1, v_inst_771_);
return v___f_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_775_, lean_object* v_range_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_carrier_775_);
lean_ctor_set(v___x_777_, 1, v_range_776_);
return v___x_777_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_780_; 
v___f_780_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_780_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_781_;
v_res_781_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg();
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_784_, lean_object* v_00_u03b2_785_, lean_object* v_inst_786_){
_start:
{
lean_object* v___f_787_; 
v___f_787_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___redArg___closed__0));
return v___f_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_inst_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_788_, v_00_u03b2_789_, v_inst_790_);
lean_dec_ref(v_inst_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_792_){
_start:
{
lean_object* v_treeMap_793_; lean_object* v_range_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_803_; 
v_treeMap_793_ = lean_ctor_get(v_x_792_, 0);
v_range_794_ = lean_ctor_get(v_x_792_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_803_ == 0)
{
v___x_796_ = v_x_792_;
v_isShared_797_ = v_isSharedCheck_803_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_range_794_);
lean_inc(v_treeMap_793_);
lean_dec(v_x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_803_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_798_ = lean_box(0);
v___x_799_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_793_, v___x_798_);
lean_dec(v_treeMap_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_799_);
v___x_801_ = v___x_796_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_range_794_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_806_; 
v___f_806_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_806_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_807_;
v_res_807_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg();
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_inst_812_){
_start:
{
lean_object* v___f_813_; 
v___f_813_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___redArg___closed__0));
return v___f_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_inst_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_814_, v_00_u03b2_815_, v_inst_816_);
lean_dec_ref(v_inst_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___lam__0(lean_object* v_carrier_818_, lean_object* v_range_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_carrier_818_);
lean_ctor_set(v___x_820_, 1, v_range_819_);
return v___x_820_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg(){
_start:
{
lean_object* v___f_823_; 
v___f_823_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_823_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_824_;
v_res_824_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___boxed(lean_object* v___dummy_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg();
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v___f_829_; 
v___f_829_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___redArg___closed__0));
return v___f_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_830_, lean_object* v_inst_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_830_, v_inst_831_);
lean_dec_ref(v_inst_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_833_){
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
lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_847_; 
v___f_847_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_847_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_848_;
v_res_848_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
stack->m_obj
 = v_res_848_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg();
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___f_853_; 
v___f_853_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___redArg___closed__0));
return v___f_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_854_, lean_object* v_inst_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_854_, v_inst_855_);
lean_dec_ref(v_inst_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___lam__0(lean_object* v_carrier_857_, lean_object* v_range_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_carrier_857_);
lean_ctor_set(v___x_859_, 1, v_range_858_);
return v___x_859_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg(){
_start:
{
lean_object* v___f_862_; 
v___f_862_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_862_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_863_;
v_res_863_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___boxed(lean_object* v___dummy_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg();
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_866_, lean_object* v_00_u03b2_867_, lean_object* v_inst_868_){
_start:
{
lean_object* v___f_869_; 
v___f_869_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___redArg___closed__0));
return v___f_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_inst_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_870_, v_00_u03b2_871_, v_inst_872_);
lean_dec_ref(v_inst_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___lam__0(lean_object* v_x_874_){
_start:
{
lean_object* v_treeMap_875_; lean_object* v_range_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_885_; 
v_treeMap_875_ = lean_ctor_get(v_x_874_, 0);
v_range_876_ = lean_ctor_get(v_x_874_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_874_);
if (v_isSharedCheck_885_ == 0)
{
v___x_878_ = v_x_874_;
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_range_876_);
lean_inc(v_treeMap_875_);
lean_dec(v_x_874_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_885_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = lean_box(0);
v___x_881_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_875_, v___x_880_);
lean_dec(v_treeMap_875_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_range_876_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_888_; 
v___f_888_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_888_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_889_;
v_res_889_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
stack->m_obj
 = v_res_889_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___boxed(lean_object* v___dummy_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg();
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_892_, lean_object* v_00_u03b2_893_, lean_object* v_inst_894_){
_start:
{
lean_object* v___f_895_; 
v___f_895_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___redArg___closed__0));
return v___f_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_inst_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_896_, v_00_u03b2_897_, v_inst_898_);
lean_dec_ref(v_inst_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_900_, lean_object* v_range_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v_carrier_900_);
lean_ctor_set(v___x_902_, 1, v_range_901_);
return v___x_902_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_905_; 
v___f_905_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_905_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_906_;
v_res_906_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg();
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_inst_911_){
_start:
{
lean_object* v___f_912_; 
v___f_912_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___redArg___closed__0));
return v___f_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_913_, lean_object* v_00_u03b2_914_, lean_object* v_inst_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_913_, v_00_u03b2_914_, v_inst_915_);
lean_dec_ref(v_inst_915_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_917_){
_start:
{
lean_object* v_treeMap_918_; lean_object* v_range_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_928_; 
v_treeMap_918_ = lean_ctor_get(v_x_917_, 0);
v_range_919_ = lean_ctor_get(v_x_917_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_x_917_);
if (v_isSharedCheck_928_ == 0)
{
v___x_921_ = v_x_917_;
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_range_919_);
lean_inc(v_treeMap_918_);
lean_dec(v_x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v___x_924_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_918_, v___x_923_);
lean_dec(v_treeMap_918_);
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
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_range_919_);
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
lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_931_; 
v___f_931_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_931_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_932_;
v_res_932_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
stack->m_obj
 = v_res_932_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg();
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_inst_937_){
_start:
{
lean_object* v___f_938_; 
v___f_938_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___redArg___closed__0));
return v___f_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_939_, lean_object* v_00_u03b2_940_, lean_object* v_inst_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_939_, v_00_u03b2_940_, v_inst_941_);
lean_dec_ref(v_inst_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___lam__0(lean_object* v_carrier_943_, lean_object* v_range_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_carrier_943_);
lean_ctor_set(v___x_945_, 1, v_range_944_);
return v___x_945_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg(){
_start:
{
lean_object* v___f_948_; 
v___f_948_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_948_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_949_;
v_res_949_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___boxed(lean_object* v___dummy_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg();
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_952_, lean_object* v_inst_953_){
_start:
{
lean_object* v___f_954_; 
v___f_954_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___redArg___closed__0));
return v___f_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_955_, v_inst_956_);
lean_dec_ref(v_inst_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_958_){
_start:
{
lean_object* v_treeMap_959_; lean_object* v_range_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_969_; 
v_treeMap_959_ = lean_ctor_get(v_x_958_, 0);
v_range_960_ = lean_ctor_get(v_x_958_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_958_);
if (v_isSharedCheck_969_ == 0)
{
v___x_962_ = v_x_958_;
v_isShared_963_ = v_isSharedCheck_969_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_range_960_);
lean_inc(v_treeMap_959_);
lean_dec(v_x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_969_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_964_ = lean_box(0);
v___x_965_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_959_, v___x_964_);
lean_dec(v_treeMap_959_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_965_);
v___x_967_ = v___x_962_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_range_960_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_972_; 
v___f_972_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_972_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_973_;
v_res_973_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg();
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_976_, lean_object* v_inst_977_){
_start:
{
lean_object* v___f_978_; 
v___f_978_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___redArg___closed__0));
return v___f_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_979_, lean_object* v_inst_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_979_, v_inst_980_);
lean_dec_ref(v_inst_980_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___lam__0(lean_object* v_carrier_982_, lean_object* v_range_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_carrier_982_);
lean_ctor_set(v___x_984_, 1, v_range_983_);
return v___x_984_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg(){
_start:
{
lean_object* v___f_987_; 
v___f_987_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_987_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_988_;
v_res_988_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___boxed(lean_object* v___dummy_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg();
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_inst_993_){
_start:
{
lean_object* v___f_994_; 
v___f_994_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___redArg___closed__0));
return v___f_994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_inst_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_995_, v_00_u03b2_996_, v_inst_997_);
lean_dec_ref(v_inst_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___lam__0(lean_object* v_x_999_){
_start:
{
lean_object* v_treeMap_1000_; lean_object* v_range_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1010_; 
v_treeMap_1000_ = lean_ctor_get(v_x_999_, 0);
v_range_1001_ = lean_ctor_get(v_x_999_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1003_ = v_x_999_;
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_range_1001_);
lean_inc(v_treeMap_1000_);
lean_dec(v_x_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1000_, v___x_1005_);
lean_dec(v_treeMap_1000_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1006_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_range_1001_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1013_; 
v___f_1013_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1013_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1014_;
v_res_1014_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg();
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_inst_1019_){
_start:
{
lean_object* v___f_1020_; 
v___f_1020_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___redArg___closed__0));
return v___f_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_1021_, lean_object* v_00_u03b2_1022_, lean_object* v_inst_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_1021_, v_00_u03b2_1022_, v_inst_1023_);
lean_dec_ref(v_inst_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_1025_, lean_object* v_t_1026_, lean_object* v_lowerBound_1027_, lean_object* v_upperBound_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1025_, v_t_1026_, v_lowerBound_1027_, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v_upperBound_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_inst_1034_, lean_object* v_t_1035_, lean_object* v_lowerBound_1036_, lean_object* v_upperBound_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1034_, v_t_1035_, v_lowerBound_1036_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_upperBound_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1041_, lean_object* v_range_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_carrier_1041_);
lean_ctor_set(v___x_1043_, 1, v_range_1042_);
return v___x_1043_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1046_; 
v___f_1046_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1046_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1047_;
v_res_1047_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg();
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v___f_1053_; 
v___f_1053_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_inst_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_1054_, v_00_u03b2_1055_, v_inst_1056_);
lean_dec_ref(v_inst_1056_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_range_1060_; lean_object* v_treeMap_1061_; lean_object* v_lower_1062_; lean_object* v_upper_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1072_; 
v_range_1060_ = lean_ctor_get(v_x_1059_, 1);
lean_inc_ref(v_range_1060_);
v_treeMap_1061_ = lean_ctor_get(v_x_1059_, 0);
lean_inc(v_treeMap_1061_);
lean_dec_ref(v_x_1059_);
v_lower_1062_ = lean_ctor_get(v_range_1060_, 0);
v_upper_1063_ = lean_ctor_get(v_range_1060_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_range_1060_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1065_ = v_range_1060_;
v_isShared_1066_ = v_isSharedCheck_1072_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_upper_1063_);
lean_inc(v_lower_1062_);
lean_dec(v_range_1060_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1072_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1058_, v_treeMap_1061_, v_lower_1062_, v___x_1067_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1068_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_upper_1063_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_1073_){
_start:
{
lean_object* v___f_1074_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1074_, 0, v_inst_1073_);
return v___f_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_1075_, lean_object* v_00_u03b2_1076_, lean_object* v_inst_1077_){
_start:
{
lean_object* v___f_1078_; 
v___f_1078_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1078_, 0, v_inst_1077_);
return v___f_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___lam__0(lean_object* v_carrier_1079_, lean_object* v_range_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_carrier_1079_);
lean_ctor_set(v___x_1081_, 1, v_range_1080_);
return v___x_1081_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg(){
_start:
{
lean_object* v___f_1084_; 
v___f_1084_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1084_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1085_;
v_res_1085_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
stack->m_obj
 = v_res_1085_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___boxed(lean_object* v___dummy_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg();
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_1088_, lean_object* v_inst_1089_){
_start:
{
lean_object* v___f_1090_; 
v___f_1090_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___redArg___closed__0));
return v___f_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_inst_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_1091_, v_inst_1092_);
lean_dec_ref(v_inst_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v_range_1096_; lean_object* v_treeMap_1097_; lean_object* v_lower_1098_; lean_object* v_upper_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1108_; 
v_range_1096_ = lean_ctor_get(v_x_1095_, 1);
lean_inc_ref(v_range_1096_);
v_treeMap_1097_ = lean_ctor_get(v_x_1095_, 0);
lean_inc(v_treeMap_1097_);
lean_dec_ref(v_x_1095_);
v_lower_1098_ = lean_ctor_get(v_range_1096_, 0);
v_upper_1099_ = lean_ctor_get(v_range_1096_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_range_1096_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1101_ = v_range_1096_;
v_isShared_1102_ = v_isSharedCheck_1108_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_upper_1099_);
lean_inc(v_lower_1098_);
lean_dec(v_range_1096_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1108_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1094_, v_treeMap_1097_, v_lower_1098_, v___x_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_upper_1099_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_1109_){
_start:
{
lean_object* v___f_1110_; 
v___f_1110_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1110_, 0, v_inst_1109_);
return v___f_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_1111_, lean_object* v_inst_1112_){
_start:
{
lean_object* v___f_1113_; 
v___f_1113_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1113_, 0, v_inst_1112_);
return v___f_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___lam__0(lean_object* v_carrier_1114_, lean_object* v_range_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_carrier_1114_);
lean_ctor_set(v___x_1116_, 1, v_range_1115_);
return v___x_1116_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg(){
_start:
{
lean_object* v___f_1119_; 
v___f_1119_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1119_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1120_;
v_res_1120_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___boxed(lean_object* v___dummy_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg();
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_inst_1125_){
_start:
{
lean_object* v___f_1126_; 
v___f_1126_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___redArg___closed__0));
return v___f_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_inst_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_1127_, v_00_u03b2_1128_, v_inst_1129_);
lean_dec_ref(v_inst_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_range_1133_; lean_object* v_treeMap_1134_; lean_object* v_lower_1135_; lean_object* v_upper_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1145_; 
v_range_1133_ = lean_ctor_get(v_x_1132_, 1);
lean_inc_ref(v_range_1133_);
v_treeMap_1134_ = lean_ctor_get(v_x_1132_, 0);
lean_inc(v_treeMap_1134_);
lean_dec_ref(v_x_1132_);
v_lower_1135_ = lean_ctor_get(v_range_1133_, 0);
v_upper_1136_ = lean_ctor_get(v_range_1133_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_range_1133_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1138_ = v_range_1133_;
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_upper_1136_);
lean_inc(v_lower_1135_);
lean_dec(v_range_1133_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1131_, v_treeMap_1134_, v_lower_1135_, v___x_1140_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_upper_1136_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_1146_){
_start:
{
lean_object* v___f_1147_; 
v___f_1147_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1147_, 0, v_inst_1146_);
return v___f_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v___f_1151_; 
v___f_1151_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1151_, 0, v_inst_1150_);
return v___f_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_1152_, lean_object* v_t_1153_, lean_object* v_lowerBound_1154_, lean_object* v_upperBound_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1152_, v_t_1153_, v_lowerBound_1154_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v_upperBound_1155_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_inst_1161_, lean_object* v_t_1162_, lean_object* v_lowerBound_1163_, lean_object* v_upperBound_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1161_, v_t_1162_, v_lowerBound_1163_, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_upperBound_1164_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1168_, lean_object* v_range_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_carrier_1168_);
lean_ctor_set(v___x_1170_, 1, v_range_1169_);
return v___x_1170_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1173_; 
v___f_1173_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1173_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1174_;
v_res_1174_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg();
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v___f_1180_; 
v___f_1180_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_inst_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_1181_, v_00_u03b2_1182_, v_inst_1183_);
lean_dec_ref(v_inst_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v_range_1187_; lean_object* v_treeMap_1188_; lean_object* v_lower_1189_; lean_object* v_upper_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1199_; 
v_range_1187_ = lean_ctor_get(v_x_1186_, 1);
lean_inc_ref(v_range_1187_);
v_treeMap_1188_ = lean_ctor_get(v_x_1186_, 0);
lean_inc(v_treeMap_1188_);
lean_dec_ref(v_x_1186_);
v_lower_1189_ = lean_ctor_get(v_range_1187_, 0);
v_upper_1190_ = lean_ctor_get(v_range_1187_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_range_1187_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1192_ = v_range_1187_;
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_upper_1190_);
lean_inc(v_lower_1189_);
lean_dec(v_range_1187_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1185_, v_treeMap_1188_, v_lower_1189_, v___x_1194_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_upper_1190_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_1200_){
_start:
{
lean_object* v___f_1201_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1201_, 0, v_inst_1200_);
return v___f_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___f_1205_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1205_, 0, v_inst_1204_);
return v___f_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___lam__0(lean_object* v_carrier_1206_, lean_object* v_range_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_carrier_1206_);
lean_ctor_set(v___x_1208_, 1, v_range_1207_);
return v___x_1208_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg(){
_start:
{
lean_object* v___f_1211_; 
v___f_1211_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1211_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1212_;
v_res_1212_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___boxed(lean_object* v___dummy_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg();
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v___f_1217_; 
v___f_1217_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___redArg___closed__0));
return v___f_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_inst_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_1218_, v_inst_1219_);
lean_dec_ref(v_inst_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_range_1223_; lean_object* v_treeMap_1224_; lean_object* v_lower_1225_; lean_object* v_upper_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1235_; 
v_range_1223_ = lean_ctor_get(v_x_1222_, 1);
lean_inc_ref(v_range_1223_);
v_treeMap_1224_ = lean_ctor_get(v_x_1222_, 0);
lean_inc(v_treeMap_1224_);
lean_dec_ref(v_x_1222_);
v_lower_1225_ = lean_ctor_get(v_range_1223_, 0);
v_upper_1226_ = lean_ctor_get(v_range_1223_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_range_1223_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1228_ = v_range_1223_;
v_isShared_1229_ = v_isSharedCheck_1235_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_upper_1226_);
lean_inc(v_lower_1225_);
lean_dec(v_range_1223_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1235_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1221_, v_treeMap_1224_, v_lower_1225_, v___x_1230_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_upper_1226_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1236_){
_start:
{
lean_object* v___f_1237_; 
v___f_1237_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1237_, 0, v_inst_1236_);
return v___f_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1238_, lean_object* v_inst_1239_){
_start:
{
lean_object* v___f_1240_; 
v___f_1240_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1240_, 0, v_inst_1239_);
return v___f_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___lam__0(lean_object* v_carrier_1241_, lean_object* v_range_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_carrier_1241_);
lean_ctor_set(v___x_1243_, 1, v_range_1242_);
return v___x_1243_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg(){
_start:
{
lean_object* v___f_1246_; 
v___f_1246_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1246_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1247_;
v_res_1247_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___boxed(lean_object* v___dummy_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg();
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_inst_1252_){
_start:
{
lean_object* v___f_1253_; 
v___f_1253_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___redArg___closed__0));
return v___f_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_inst_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1254_, v_00_u03b2_1255_, v_inst_1256_);
lean_dec_ref(v_inst_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v_range_1260_; lean_object* v_treeMap_1261_; lean_object* v_lower_1262_; lean_object* v_upper_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1272_; 
v_range_1260_ = lean_ctor_get(v_x_1259_, 1);
lean_inc_ref(v_range_1260_);
v_treeMap_1261_ = lean_ctor_get(v_x_1259_, 0);
lean_inc(v_treeMap_1261_);
lean_dec_ref(v_x_1259_);
v_lower_1262_ = lean_ctor_get(v_range_1260_, 0);
v_upper_1263_ = lean_ctor_get(v_range_1260_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_range_1260_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1265_ = v_range_1260_;
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_upper_1263_);
lean_inc(v_lower_1262_);
lean_dec(v_range_1260_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1258_, v_treeMap_1261_, v_lower_1262_, v___x_1267_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1268_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_upper_1263_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1273_){
_start:
{
lean_object* v___f_1274_; 
v___f_1274_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1274_, 0, v_inst_1273_);
return v___f_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1275_, lean_object* v_00_u03b2_1276_, lean_object* v_inst_1277_){
_start:
{
lean_object* v___f_1278_; 
v___f_1278_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1278_, 0, v_inst_1277_);
return v___f_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1279_, lean_object* v_t_1280_, lean_object* v_lowerBound_1281_, lean_object* v_upperBound_1282_){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1279_, v_t_1280_, v_lowerBound_1281_, v___x_1283_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v_upperBound_1282_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_inst_1288_, lean_object* v_t_1289_, lean_object* v_lowerBound_1290_, lean_object* v_upperBound_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1288_, v_t_1289_, v_lowerBound_1290_, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_upperBound_1291_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1295_, lean_object* v_range_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_carrier_1295_);
lean_ctor_set(v___x_1297_, 1, v_range_1296_);
return v___x_1297_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1300_; 
v___f_1300_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1300_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1301_;
v_res_1301_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
stack->m_obj
 = v_res_1301_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg();
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_inst_1306_){
_start:
{
lean_object* v___f_1307_; 
v___f_1307_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_inst_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1308_, v_00_u03b2_1309_, v_inst_1310_);
lean_dec_ref(v_inst_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v_range_1314_; lean_object* v_treeMap_1315_; lean_object* v_lower_1316_; lean_object* v_upper_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1326_; 
v_range_1314_ = lean_ctor_get(v_x_1313_, 1);
lean_inc_ref(v_range_1314_);
v_treeMap_1315_ = lean_ctor_get(v_x_1313_, 0);
lean_inc(v_treeMap_1315_);
lean_dec_ref(v_x_1313_);
v_lower_1316_ = lean_ctor_get(v_range_1314_, 0);
v_upper_1317_ = lean_ctor_get(v_range_1314_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_range_1314_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1319_ = v_range_1314_;
v_isShared_1320_ = v_isSharedCheck_1326_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_upper_1317_);
lean_inc(v_lower_1316_);
lean_dec(v_range_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1326_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1312_, v_treeMap_1315_, v_lower_1316_, v___x_1321_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1322_);
v___x_1324_ = v___x_1319_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_upper_1317_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1327_){
_start:
{
lean_object* v___f_1328_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1328_, 0, v_inst_1327_);
return v___f_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_inst_1331_){
_start:
{
lean_object* v___f_1332_; 
v___f_1332_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1332_, 0, v_inst_1331_);
return v___f_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___lam__0(lean_object* v_carrier_1333_, lean_object* v_range_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v_carrier_1333_);
lean_ctor_set(v___x_1335_, 1, v_range_1334_);
return v___x_1335_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg(){
_start:
{
lean_object* v___f_1338_; 
v___f_1338_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1338_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1339_;
v_res_1339_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
stack->m_obj
 = v_res_1339_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___boxed(lean_object* v___dummy_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg();
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1342_, lean_object* v_inst_1343_){
_start:
{
lean_object* v___f_1344_; 
v___f_1344_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___redArg___closed__0));
return v___f_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_inst_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1345_, v_inst_1346_);
lean_dec_ref(v_inst_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1348_, lean_object* v_x_1349_){
_start:
{
lean_object* v_range_1350_; lean_object* v_treeMap_1351_; lean_object* v_lower_1352_; lean_object* v_upper_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1362_; 
v_range_1350_ = lean_ctor_get(v_x_1349_, 1);
lean_inc_ref(v_range_1350_);
v_treeMap_1351_ = lean_ctor_get(v_x_1349_, 0);
lean_inc(v_treeMap_1351_);
lean_dec_ref(v_x_1349_);
v_lower_1352_ = lean_ctor_get(v_range_1350_, 0);
v_upper_1353_ = lean_ctor_get(v_range_1350_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_range_1350_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1355_ = v_range_1350_;
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_upper_1353_);
lean_inc(v_lower_1352_);
lean_dec(v_range_1350_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1348_, v_treeMap_1351_, v_lower_1352_, v___x_1357_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_upper_1353_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1363_){
_start:
{
lean_object* v___f_1364_; 
v___f_1364_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1364_, 0, v_inst_1363_);
return v___f_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1365_, lean_object* v_inst_1366_){
_start:
{
lean_object* v___f_1367_; 
v___f_1367_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1367_, 0, v_inst_1366_);
return v___f_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___lam__0(lean_object* v_carrier_1368_, lean_object* v_range_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_carrier_1368_);
lean_ctor_set(v___x_1370_, 1, v_range_1369_);
return v___x_1370_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg(){
_start:
{
lean_object* v___f_1373_; 
v___f_1373_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1373_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1374_;
v_res_1374_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___boxed(lean_object* v___dummy_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg();
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_inst_1379_){
_start:
{
lean_object* v___f_1380_; 
v___f_1380_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___redArg___closed__0));
return v___f_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_inst_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1381_, v_00_u03b2_1382_, v_inst_1383_);
lean_dec_ref(v_inst_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v_range_1387_; lean_object* v_treeMap_1388_; lean_object* v_lower_1389_; lean_object* v_upper_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1399_; 
v_range_1387_ = lean_ctor_get(v_x_1386_, 1);
lean_inc_ref(v_range_1387_);
v_treeMap_1388_ = lean_ctor_get(v_x_1386_, 0);
lean_inc(v_treeMap_1388_);
lean_dec_ref(v_x_1386_);
v_lower_1389_ = lean_ctor_get(v_range_1387_, 0);
v_upper_1390_ = lean_ctor_get(v_range_1387_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_range_1387_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1392_ = v_range_1387_;
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_upper_1390_);
lean_inc(v_lower_1389_);
lean_dec(v_range_1387_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1385_, v_treeMap_1388_, v_lower_1389_, v___x_1394_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1395_);
v___x_1397_ = v___x_1392_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_upper_1390_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1400_){
_start:
{
lean_object* v___f_1401_; 
v___f_1401_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1401_, 0, v_inst_1400_);
return v___f_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_inst_1404_){
_start:
{
lean_object* v___f_1405_; 
v___f_1405_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1405_, 0, v_inst_1404_);
return v___f_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1406_, lean_object* v_t_1407_, lean_object* v_lowerBound_1408_, lean_object* v_upperBound_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1406_, v_t_1407_, v_lowerBound_1408_, v___x_1410_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_upperBound_1409_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1413_, lean_object* v_00_u03b2_1414_, lean_object* v_inst_1415_, lean_object* v_t_1416_, lean_object* v_lowerBound_1417_, lean_object* v_upperBound_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1415_, v_t_1416_, v_lowerBound_1417_, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v_upperBound_1418_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1422_, lean_object* v_range_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_carrier_1422_);
lean_ctor_set(v___x_1424_, 1, v_range_1423_);
return v___x_1424_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1427_; 
v___f_1427_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1427_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1428_;
v_res_1428_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
stack->m_obj
 = v_res_1428_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg();
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_inst_1433_){
_start:
{
lean_object* v___f_1434_; 
v___f_1434_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_inst_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1435_, v_00_u03b2_1436_, v_inst_1437_);
lean_dec_ref(v_inst_1437_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_range_1441_; lean_object* v_treeMap_1442_; lean_object* v_lower_1443_; lean_object* v_upper_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1453_; 
v_range_1441_ = lean_ctor_get(v_x_1440_, 1);
lean_inc_ref(v_range_1441_);
v_treeMap_1442_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_treeMap_1442_);
lean_dec_ref(v_x_1440_);
v_lower_1443_ = lean_ctor_get(v_range_1441_, 0);
v_upper_1444_ = lean_ctor_get(v_range_1441_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_range_1441_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1446_ = v_range_1441_;
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_upper_1444_);
lean_inc(v_lower_1443_);
lean_dec(v_range_1441_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1453_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1439_, v_treeMap_1442_, v_lower_1443_, v___x_1448_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1449_);
v___x_1451_ = v___x_1446_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_upper_1444_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1454_){
_start:
{
lean_object* v___f_1455_; 
v___f_1455_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1455_, 0, v_inst_1454_);
return v___f_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_inst_1458_){
_start:
{
lean_object* v___f_1459_; 
v___f_1459_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1459_, 0, v_inst_1458_);
return v___f_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___lam__0(lean_object* v_carrier_1460_, lean_object* v_range_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_carrier_1460_);
lean_ctor_set(v___x_1462_, 1, v_range_1461_);
return v___x_1462_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg(){
_start:
{
lean_object* v___f_1465_; 
v___f_1465_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1465_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1466_;
v_res_1466_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
stack->m_obj
 = v_res_1466_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___boxed(lean_object* v___dummy_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg();
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1469_, lean_object* v_inst_1470_){
_start:
{
lean_object* v___f_1471_; 
v___f_1471_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___redArg___closed__0));
return v___f_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1472_, lean_object* v_inst_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1472_, v_inst_1473_);
lean_dec_ref(v_inst_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_range_1477_; lean_object* v_treeMap_1478_; lean_object* v_lower_1479_; lean_object* v_upper_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
v_range_1477_ = lean_ctor_get(v_x_1476_, 1);
lean_inc_ref(v_range_1477_);
v_treeMap_1478_ = lean_ctor_get(v_x_1476_, 0);
lean_inc(v_treeMap_1478_);
lean_dec_ref(v_x_1476_);
v_lower_1479_ = lean_ctor_get(v_range_1477_, 0);
v_upper_1480_ = lean_ctor_get(v_range_1477_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_range_1477_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v_range_1477_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_upper_1480_);
lean_inc(v_lower_1479_);
lean_dec(v_range_1477_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_box(0);
v___x_1485_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1475_, v_treeMap_1478_, v_lower_1479_, v___x_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1485_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_upper_1480_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1490_){
_start:
{
lean_object* v___f_1491_; 
v___f_1491_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1491_, 0, v_inst_1490_);
return v___f_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1492_, lean_object* v_inst_1493_){
_start:
{
lean_object* v___f_1494_; 
v___f_1494_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1494_, 0, v_inst_1493_);
return v___f_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___lam__0(lean_object* v_carrier_1495_, lean_object* v_range_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_carrier_1495_);
lean_ctor_set(v___x_1497_, 1, v_range_1496_);
return v___x_1497_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg(){
_start:
{
lean_object* v___f_1500_; 
v___f_1500_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1500_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1501_;
v_res_1501_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
stack->m_obj
 = v_res_1501_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___boxed(lean_object* v___dummy_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg();
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1504_, lean_object* v_00_u03b2_1505_, lean_object* v_inst_1506_){
_start:
{
lean_object* v___f_1507_; 
v___f_1507_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___redArg___closed__0));
return v___f_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_00_u03b2_1509_, lean_object* v_inst_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1508_, v_00_u03b2_1509_, v_inst_1510_);
lean_dec_ref(v_inst_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v_range_1514_; lean_object* v_treeMap_1515_; lean_object* v_lower_1516_; lean_object* v_upper_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1526_; 
v_range_1514_ = lean_ctor_get(v_x_1513_, 1);
lean_inc_ref(v_range_1514_);
v_treeMap_1515_ = lean_ctor_get(v_x_1513_, 0);
lean_inc(v_treeMap_1515_);
lean_dec_ref(v_x_1513_);
v_lower_1516_ = lean_ctor_get(v_range_1514_, 0);
v_upper_1517_ = lean_ctor_get(v_range_1514_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_range_1514_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1519_ = v_range_1514_;
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_upper_1517_);
lean_inc(v_lower_1516_);
lean_dec(v_range_1514_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1512_, v_treeMap_1515_, v_lower_1516_, v___x_1521_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1522_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_upper_1517_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1527_){
_start:
{
lean_object* v___f_1528_; 
v___f_1528_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1528_, 0, v_inst_1527_);
return v___f_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1529_, lean_object* v_00_u03b2_1530_, lean_object* v_inst_1531_){
_start:
{
lean_object* v___f_1532_; 
v___f_1532_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1532_, 0, v_inst_1531_);
return v___f_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1533_, lean_object* v_t_1534_, lean_object* v_lowerBound_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_box(0);
v___x_1537_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1533_, v_t_1534_, v_lowerBound_1535_, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1538_, lean_object* v_00_u03b2_1539_, lean_object* v_inst_1540_, lean_object* v_t_1541_, lean_object* v_lowerBound_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_box(0);
v___x_1544_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1540_, v_t_1541_, v_lowerBound_1542_, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1545_, lean_object* v_range_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_carrier_1545_);
lean_ctor_set(v___x_1547_, 1, v_range_1546_);
return v___x_1547_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1550_; 
v___f_1550_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1550_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1551_;
v_res_1551_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
stack->m_obj
 = v_res_1551_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg();
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1554_, lean_object* v_00_u03b2_1555_, lean_object* v_inst_1556_){
_start:
{
lean_object* v___f_1557_; 
v___f_1557_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_00_u03b2_1559_, lean_object* v_inst_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1558_, v_00_u03b2_1559_, v_inst_1560_);
lean_dec_ref(v_inst_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v_treeMap_1564_; lean_object* v_range_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_treeMap_1564_ = lean_ctor_get(v_x_1563_, 0);
lean_inc(v_treeMap_1564_);
v_range_1565_ = lean_ctor_get(v_x_1563_, 1);
lean_inc(v_range_1565_);
lean_dec_ref(v_x_1563_);
v___x_1566_ = lean_box(0);
v___x_1567_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1562_, v_treeMap_1564_, v_range_1565_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1568_){
_start:
{
lean_object* v___f_1569_; 
v___f_1569_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1569_, 0, v_inst_1568_);
return v___f_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1570_, lean_object* v_00_u03b2_1571_, lean_object* v_inst_1572_){
_start:
{
lean_object* v___f_1573_; 
v___f_1573_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1573_, 0, v_inst_1572_);
return v___f_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___lam__0(lean_object* v_carrier_1574_, lean_object* v_range_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_carrier_1574_);
lean_ctor_set(v___x_1576_, 1, v_range_1575_);
return v___x_1576_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg(){
_start:
{
lean_object* v___f_1579_; 
v___f_1579_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1579_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1580_;
v_res_1580_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
stack->m_obj
 = v_res_1580_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___boxed(lean_object* v___dummy_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg();
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1583_, lean_object* v_inst_1584_){
_start:
{
lean_object* v___f_1585_; 
v___f_1585_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___redArg___closed__0));
return v___f_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1586_, lean_object* v_inst_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1586_, v_inst_1587_);
lean_dec_ref(v_inst_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v_treeMap_1591_; lean_object* v_range_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_treeMap_1591_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_treeMap_1591_);
v_range_1592_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_range_1592_);
lean_dec_ref(v_x_1590_);
v___x_1593_ = lean_box(0);
v___x_1594_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1589_, v_treeMap_1591_, v_range_1592_, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1595_){
_start:
{
lean_object* v___f_1596_; 
v___f_1596_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1596_, 0, v_inst_1595_);
return v___f_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1597_, lean_object* v_inst_1598_){
_start:
{
lean_object* v___f_1599_; 
v___f_1599_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1599_, 0, v_inst_1598_);
return v___f_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___lam__0(lean_object* v_carrier_1600_, lean_object* v_range_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_carrier_1600_);
lean_ctor_set(v___x_1602_, 1, v_range_1601_);
return v___x_1602_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg(){
_start:
{
lean_object* v___f_1605_; 
v___f_1605_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1605_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1606_;
v_res_1606_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
stack->m_obj
 = v_res_1606_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___boxed(lean_object* v___dummy_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg();
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_inst_1611_){
_start:
{
lean_object* v___f_1612_; 
v___f_1612_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___redArg___closed__0));
return v___f_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_inst_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1613_, v_00_u03b2_1614_, v_inst_1615_);
lean_dec_ref(v_inst_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v_treeMap_1619_; lean_object* v_range_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_treeMap_1619_ = lean_ctor_get(v_x_1618_, 0);
lean_inc(v_treeMap_1619_);
v_range_1620_ = lean_ctor_get(v_x_1618_, 1);
lean_inc(v_range_1620_);
lean_dec_ref(v_x_1618_);
v___x_1621_ = lean_box(0);
v___x_1622_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1617_, v_treeMap_1619_, v_range_1620_, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1623_){
_start:
{
lean_object* v___f_1624_; 
v___f_1624_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1624_, 0, v_inst_1623_);
return v___f_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_inst_1627_){
_start:
{
lean_object* v___f_1628_; 
v___f_1628_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1628_, 0, v_inst_1627_);
return v___f_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1629_, lean_object* v_t_1630_, lean_object* v_lowerBound_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1629_, v_t_1630_, v_lowerBound_1631_, v___x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_inst_1636_, lean_object* v_t_1637_, lean_object* v_lowerBound_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_box(0);
v___x_1640_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1636_, v_t_1637_, v_lowerBound_1638_, v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1641_, lean_object* v_range_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_carrier_1641_);
lean_ctor_set(v___x_1643_, 1, v_range_1642_);
return v___x_1643_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1646_; 
v___f_1646_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1646_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1647_;
v_res_1647_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
stack->m_obj
 = v_res_1647_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg();
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1650_, lean_object* v_00_u03b2_1651_, lean_object* v_inst_1652_){
_start:
{
lean_object* v___f_1653_; 
v___f_1653_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_inst_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1654_, v_00_u03b2_1655_, v_inst_1656_);
lean_dec_ref(v_inst_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_treeMap_1660_; lean_object* v_range_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_treeMap_1660_ = lean_ctor_get(v_x_1659_, 0);
lean_inc(v_treeMap_1660_);
v_range_1661_ = lean_ctor_get(v_x_1659_, 1);
lean_inc(v_range_1661_);
lean_dec_ref(v_x_1659_);
v___x_1662_ = lean_box(0);
v___x_1663_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1658_, v_treeMap_1660_, v_range_1661_, v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1664_){
_start:
{
lean_object* v___f_1665_; 
v___f_1665_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1665_, 0, v_inst_1664_);
return v___f_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_inst_1668_){
_start:
{
lean_object* v___f_1669_; 
v___f_1669_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1669_, 0, v_inst_1668_);
return v___f_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___lam__0(lean_object* v_carrier_1670_, lean_object* v_range_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v_carrier_1670_);
lean_ctor_set(v___x_1672_, 1, v_range_1671_);
return v___x_1672_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg(){
_start:
{
lean_object* v___f_1675_; 
v___f_1675_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1675_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1676_;
v_res_1676_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
stack->m_obj
 = v_res_1676_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___boxed(lean_object* v___dummy_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg();
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1679_, lean_object* v_inst_1680_){
_start:
{
lean_object* v___f_1681_; 
v___f_1681_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___redArg___closed__0));
return v___f_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_inst_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1682_, v_inst_1683_);
lean_dec_ref(v_inst_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v_treeMap_1687_; lean_object* v_range_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_treeMap_1687_ = lean_ctor_get(v_x_1686_, 0);
lean_inc(v_treeMap_1687_);
v_range_1688_ = lean_ctor_get(v_x_1686_, 1);
lean_inc(v_range_1688_);
lean_dec_ref(v_x_1686_);
v___x_1689_ = lean_box(0);
v___x_1690_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1685_, v_treeMap_1687_, v_range_1688_, v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1691_){
_start:
{
lean_object* v___f_1692_; 
v___f_1692_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1692_, 0, v_inst_1691_);
return v___f_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1693_, lean_object* v_inst_1694_){
_start:
{
lean_object* v___f_1695_; 
v___f_1695_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1695_, 0, v_inst_1694_);
return v___f_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___lam__0(lean_object* v_carrier_1696_, lean_object* v_range_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_carrier_1696_);
lean_ctor_set(v___x_1698_, 1, v_range_1697_);
return v___x_1698_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg(){
_start:
{
lean_object* v___f_1701_; 
v___f_1701_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1701_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1702_;
v_res_1702_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
stack->m_obj
 = v_res_1702_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___boxed(lean_object* v___dummy_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg();
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_inst_1707_){
_start:
{
lean_object* v___f_1708_; 
v___f_1708_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___redArg___closed__0));
return v___f_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_00_u03b2_1710_, lean_object* v_inst_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1709_, v_00_u03b2_1710_, v_inst_1711_);
lean_dec_ref(v_inst_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_treeMap_1715_; lean_object* v_range_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_treeMap_1715_ = lean_ctor_get(v_x_1714_, 0);
lean_inc(v_treeMap_1715_);
v_range_1716_ = lean_ctor_get(v_x_1714_, 1);
lean_inc(v_range_1716_);
lean_dec_ref(v_x_1714_);
v___x_1717_ = lean_box(0);
v___x_1718_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1713_, v_treeMap_1715_, v_range_1716_, v___x_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1719_){
_start:
{
lean_object* v___f_1720_; 
v___f_1720_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1720_, 0, v_inst_1719_);
return v___f_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_inst_1723_){
_start:
{
lean_object* v___f_1724_; 
v___f_1724_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1724_, 0, v_inst_1723_);
return v___f_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1725_, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1728_);
lean_dec(v_t_1728_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_t_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_t_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1734_, v_00_u03b2_1735_, v_t_1736_);
lean_dec(v_t_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1738_, lean_object* v_range_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_carrier_1738_);
lean_ctor_set(v___x_1740_, 1, v_range_1739_);
return v___x_1740_;
}
}
lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1743_; 
v___f_1743_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1743_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1744_;
v_res_1744_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
stack->m_obj
 = v_res_1744_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg();
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1747_, lean_object* v_00_u03b2_1748_){
_start:
{
lean_object* v___f_1749_; 
v___f_1749_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1750_){
_start:
{
lean_object* v_treeMap_1751_; lean_object* v___x_1752_; 
v_treeMap_1751_ = lean_ctor_get(v_x_1750_, 0);
v___x_1752_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___lam__0(v_x_1753_);
lean_dec_ref(v_x_1753_);
return v_res_1754_;
}
}
lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1757_; 
v___f_1757_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1757_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1758_;
v_res_1758_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
stack->m_obj
 = v_res_1758_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg();
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_){
_start:
{
lean_object* v___f_1763_; 
v___f_1763_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___lam__0(lean_object* v_carrier_1764_, lean_object* v_range_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_carrier_1764_);
lean_ctor_set(v___x_1766_, 1, v_range_1765_);
return v___x_1766_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg(){
_start:
{
lean_object* v___f_1769_; 
v___f_1769_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1769_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1770_;
v_res_1770_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
stack->m_obj
 = v_res_1770_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___boxed(lean_object* v___dummy_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg();
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1773_){
_start:
{
lean_object* v___f_1774_; 
v___f_1774_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___redArg___closed__0));
return v___f_1774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1775_){
_start:
{
lean_object* v_treeMap_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_treeMap_1776_ = lean_ctor_get(v_x_1775_, 0);
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1776_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___lam__0(v_x_1779_);
lean_dec_ref(v_x_1779_);
return v_res_1780_;
}
}
lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1783_; 
v___f_1783_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1783_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1784_;
v_res_1784_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
stack->m_obj
 = v_res_1784_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg();
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1787_){
_start:
{
lean_object* v___f_1788_; 
v___f_1788_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___lam__0(lean_object* v_carrier_1789_, lean_object* v_range_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_carrier_1789_);
lean_ctor_set(v___x_1791_, 1, v_range_1790_);
return v___x_1791_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg(){
_start:
{
lean_object* v___f_1794_; 
v___f_1794_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1794_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1795_;
v_res_1795_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
stack->m_obj
 = v_res_1795_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___boxed(lean_object* v___dummy_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg();
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_){
_start:
{
lean_object* v___f_1800_; 
v___f_1800_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___redArg___closed__0));
return v___f_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(lean_object* v_x_1801_){
_start:
{
lean_object* v_treeMap_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_treeMap_1802_ = lean_ctor_get(v_x_1801_, 0);
v___x_1803_ = lean_box(0);
v___x_1804_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0___boxed(lean_object* v_x_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___lam__0(v_x_1805_);
lean_dec_ref(v_x_1805_);
return v_res_1806_;
}
}
lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg(){
_start:
{
lean_object* v___f_1809_; 
v___f_1809_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1809_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1810_;
v_res_1810_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
stack->m_obj
 = v_res_1810_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___boxed(lean_object* v___dummy_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg();
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_){
_start:
{
lean_object* v___f_1815_; 
v___f_1815_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___redArg___closed__0));
return v___f_1815_;
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
