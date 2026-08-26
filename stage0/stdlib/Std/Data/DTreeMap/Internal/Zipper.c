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
static const lean_closure_object l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Zipper_step___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_415_, lean_object* v_recur_416_, lean_object* v_it_417_, lean_object* v_____do__lift_418_){
_start:
{
if (lean_obj_tag(v_____do__lift_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
lean_dec(v_it_417_);
lean_dec(v_recur_416_);
v_a_419_ = lean_ctor_get(v_____do__lift_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v_____do__lift_418_, 1);
v___x_420_ = lean_apply_2(v_toPure_415_, lean_box(0), v_a_419_);
return v___x_420_;
}
else
{
lean_object* v_a_421_; lean_object* v___x_422_; 
lean_dec(v_toPure_415_);
v_a_421_ = lean_ctor_get(v_____do__lift_418_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v_____do__lift_418_, 1);
v___x_422_ = lean_apply_4(v_recur_416_, v_it_417_, v_a_421_, lean_box(0), lean_box(0));
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_423_, lean_object* v_recur_424_, lean_object* v___y_425_, lean_object* v_acc_426_, lean_object* v_toBind_427_, lean_object* v_s_428_){
_start:
{
switch(lean_obj_tag(v_s_428_))
{
case 0:
{
lean_object* v_it_429_; lean_object* v_out_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_it_429_ = lean_ctor_get(v_s_428_, 0);
lean_inc(v_it_429_);
v_out_430_ = lean_ctor_get(v_s_428_, 1);
lean_inc(v_out_430_);
lean_dec_ref_known(v_s_428_, 2);
v___f_431_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_431_, 0, v_toPure_423_);
lean_closure_set(v___f_431_, 1, v_recur_424_);
lean_closure_set(v___f_431_, 2, v_it_429_);
v___x_432_ = lean_apply_3(v___y_425_, v_out_430_, lean_box(0), v_acc_426_);
v___x_433_ = lean_apply_4(v_toBind_427_, lean_box(0), lean_box(0), v___x_432_, v___f_431_);
return v___x_433_;
}
case 1:
{
lean_object* v_it_434_; lean_object* v___x_435_; 
lean_dec(v_toBind_427_);
lean_dec(v___y_425_);
lean_dec(v_toPure_423_);
v_it_434_ = lean_ctor_get(v_s_428_, 0);
lean_inc(v_it_434_);
lean_dec_ref_known(v_s_428_, 1);
v___x_435_ = lean_apply_4(v_recur_424_, v_it_434_, v_acc_426_, lean_box(0), lean_box(0));
return v___x_435_;
}
default: 
{
lean_object* v___x_436_; 
lean_dec(v_toBind_427_);
lean_dec(v___y_425_);
lean_dec(v_recur_424_);
v___x_436_ = lean_apply_2(v_toPure_423_, lean_box(0), v_acc_426_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_437_, lean_object* v___y_438_, lean_object* v_toBind_439_, lean_object* v_lift_440_, lean_object* v_it_441_, lean_object* v_acc_442_, lean_object* v_hP_443_, lean_object* v_recur_444_){
_start:
{
lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___f_445_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_445_, 0, v_toPure_437_);
lean_closure_set(v___f_445_, 1, v_recur_444_);
lean_closure_set(v___f_445_, 2, v___y_438_);
lean_closure_set(v___f_445_, 3, v_acc_442_);
lean_closure_set(v___f_445_, 4, v_toBind_439_);
v___x_446_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_it_441_);
v___x_447_ = lean_apply_4(v_lift_440_, lean_box(0), lean_box(0), v___f_445_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3(lean_object* v_inst_448_, lean_object* v_lift_449_, lean_object* v_00_u03b3_450_, lean_object* v_Pl_451_, lean_object* v_it_452_, lean_object* v_init_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_toApplicative_455_; lean_object* v_toBind_456_; lean_object* v_toPure_457_; lean_object* v___f_458_; lean_object* v___x_459_; 
v_toApplicative_455_ = lean_ctor_get(v_inst_448_, 0);
lean_inc_ref(v_toApplicative_455_);
v_toBind_456_ = lean_ctor_get(v_inst_448_, 1);
lean_inc(v_toBind_456_);
lean_dec_ref(v_inst_448_);
v_toPure_457_ = lean_ctor_get(v_toApplicative_455_, 1);
lean_inc(v_toPure_457_);
lean_dec_ref(v_toApplicative_455_);
v___f_458_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__2), 8, 4);
lean_closure_set(v___f_458_, 0, v_toPure_457_);
lean_closure_set(v___f_458_, 1, v___y_454_);
lean_closure_set(v___f_458_, 2, v_toBind_456_);
lean_closure_set(v___f_458_, 3, v_lift_449_);
v___x_459_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_458_, v_it_452_, v_init_453_, lean_box(0));
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg(lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; 
v___f_461_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_461_, 0, v_inst_460_);
return v___f_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instIteratorLoop(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_, lean_object* v_m_464_, lean_object* v_inst_465_){
_start:
{
lean_object* v___f_466_; 
v___f_466_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instIteratorLoop___redArg___lam__3), 7, 1);
lean_closure_set(v___f_466_, 0, v_inst_465_);
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_467_){
_start:
{
lean_inc(v_t_467_);
return v_t_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_468_);
lean_dec(v_t_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_t_472_){
_start:
{
lean_inc(v_t_472_);
return v_t_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_t_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_473_, v_00_u03b2_474_, v_t_475_);
lean_dec(v_t_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_box(0);
v___x_479_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_477_, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_480_);
lean_dec(v_t_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_t_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_t_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_486_, v_00_u03b2_487_, v_t_488_);
lean_dec(v_t_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(lean_object* v_x_490_){
_start:
{
lean_inc(v_x_490_);
return v_x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(lean_object* v_x_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(v_x_491_);
lean_dec(v_x_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_){
_start:
{
lean_object* v___f_496_; 
v___f_496_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0));
return v___f_496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_497_, lean_object* v_h__1_498_, lean_object* v_h__2_499_, lean_object* v_h__3_500_){
_start:
{
switch(lean_obj_tag(v_x_497_))
{
case 0:
{
lean_object* v_it_501_; lean_object* v_out_502_; lean_object* v___x_503_; 
lean_dec(v_h__3_500_);
lean_dec(v_h__2_499_);
v_it_501_ = lean_ctor_get(v_x_497_, 0);
lean_inc(v_it_501_);
v_out_502_ = lean_ctor_get(v_x_497_, 1);
lean_inc(v_out_502_);
lean_dec_ref_known(v_x_497_, 2);
v___x_503_ = lean_apply_2(v_h__1_498_, v_it_501_, v_out_502_);
return v___x_503_;
}
case 1:
{
lean_object* v_it_504_; lean_object* v___x_505_; 
lean_dec(v_h__3_500_);
lean_dec(v_h__1_498_);
v_it_504_ = lean_ctor_get(v_x_497_, 0);
lean_inc(v_it_504_);
lean_dec_ref_known(v_x_497_, 1);
v___x_505_ = lean_apply_1(v_h__2_499_, v_it_504_);
return v___x_505_;
}
default: 
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_h__2_499_);
lean_dec(v_h__1_498_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_apply_1(v_h__3_500_, v___x_506_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_motive_511_, lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_, lean_object* v_h__3_515_){
_start:
{
switch(lean_obj_tag(v_x_512_))
{
case 0:
{
lean_object* v_it_516_; lean_object* v_out_517_; lean_object* v___x_518_; 
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
v_it_516_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_it_516_);
v_out_517_ = lean_ctor_get(v_x_512_, 1);
lean_inc(v_out_517_);
lean_dec_ref_known(v_x_512_, 2);
v___x_518_ = lean_apply_2(v_h__1_513_, v_it_516_, v_out_517_);
return v___x_518_;
}
case 1:
{
lean_object* v_it_519_; lean_object* v___x_520_; 
lean_dec(v_h__3_515_);
lean_dec(v_h__1_513_);
v_it_519_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_it_519_);
lean_dec_ref_known(v_x_512_, 1);
v___x_520_ = lean_apply_1(v_h__2_514_, v_it_519_);
return v___x_520_;
}
default: 
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_apply_1(v_h__3_515_, v___x_521_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_iter_525_; 
v_iter_525_ = lean_ctor_get(v_x_524_, 0);
lean_inc(v_iter_525_);
if (lean_obj_tag(v_iter_525_) == 0)
{
lean_object* v___x_526_; 
lean_dec_ref(v_x_524_);
lean_dec_ref(v_inst_523_);
v___x_526_ = lean_box(2);
return v___x_526_;
}
else
{
lean_object* v_upper_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_544_; 
v_upper_527_ = lean_ctor_get(v_x_524_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_x_524_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_x_524_, 0);
lean_dec(v_unused_545_);
v___x_529_ = v_x_524_;
v_isShared_530_ = v_isSharedCheck_544_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_upper_527_);
lean_dec(v_x_524_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_544_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v_tree_533_; lean_object* v_next_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_k_531_ = lean_ctor_get(v_iter_525_, 0);
lean_inc_n(v_k_531_, 2);
v_v_532_ = lean_ctor_get(v_iter_525_, 1);
lean_inc(v_v_532_);
v_tree_533_ = lean_ctor_get(v_iter_525_, 2);
lean_inc(v_tree_533_);
v_next_534_ = lean_ctor_get(v_iter_525_, 3);
lean_inc(v_next_534_);
lean_dec_ref_known(v_iter_525_, 4);
lean_inc(v_upper_527_);
v___x_535_ = lean_apply_2(v_inst_523_, v_k_531_, v_upper_527_);
v___x_536_ = lean_unbox(v___x_535_);
if (v___x_536_ == 2)
{
lean_object* v___x_537_; 
lean_dec(v_next_534_);
lean_dec(v_tree_533_);
lean_dec(v_v_532_);
lean_dec(v_k_531_);
lean_del_object(v___x_529_);
lean_dec(v_upper_527_);
v___x_537_ = lean_box(2);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_533_, v_next_534_);
lean_dec(v_tree_533_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_538_);
v___x_540_ = v___x_529_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_upper_527_);
v___x_540_ = v_reuseFailAlloc_543_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_k_531_);
lean_ctor_set(v___x_541_, 1, v_v_532_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_inst_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_551_, lean_object* v_it_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_551_, v_it_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_554_){
_start:
{
lean_object* v___f_555_; 
v___f_555_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_555_, 0, v_inst_554_);
return v___f_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_inst_558_){
_start:
{
lean_object* v___f_559_; 
v___f_559_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_559_, 0, v_inst_558_);
return v___f_559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_560_, lean_object* v_h__1_561_, lean_object* v_h__2_562_){
_start:
{
lean_object* v_iter_563_; 
v_iter_563_ = lean_ctor_get(v_x_560_, 0);
if (lean_obj_tag(v_iter_563_) == 0)
{
lean_object* v_upper_564_; lean_object* v___x_565_; 
lean_dec(v_h__2_562_);
v_upper_564_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_upper_564_);
lean_dec_ref(v_x_560_);
v___x_565_ = lean_apply_1(v_h__1_561_, v_upper_564_);
return v___x_565_;
}
else
{
lean_object* v_upper_566_; lean_object* v_k_567_; lean_object* v_v_568_; lean_object* v_tree_569_; lean_object* v_next_570_; lean_object* v___x_571_; 
lean_inc_ref(v_iter_563_);
lean_dec(v_h__1_561_);
v_upper_566_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_upper_566_);
lean_dec_ref(v_x_560_);
v_k_567_ = lean_ctor_get(v_iter_563_, 0);
lean_inc(v_k_567_);
v_v_568_ = lean_ctor_get(v_iter_563_, 1);
lean_inc(v_v_568_);
v_tree_569_ = lean_ctor_get(v_iter_563_, 2);
lean_inc(v_tree_569_);
v_next_570_ = lean_ctor_get(v_iter_563_, 3);
lean_inc(v_next_570_);
lean_dec_ref_known(v_iter_563_, 4);
v___x_571_ = lean_apply_5(v_h__2_562_, v_k_567_, v_v_568_, v_tree_569_, v_next_570_, v_upper_566_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_inst_574_, lean_object* v_motive_575_, lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
lean_object* v_iter_579_; 
v_iter_579_ = lean_ctor_get(v_x_576_, 0);
if (lean_obj_tag(v_iter_579_) == 0)
{
lean_object* v_upper_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_578_);
v_upper_580_ = lean_ctor_get(v_x_576_, 1);
lean_inc(v_upper_580_);
lean_dec_ref(v_x_576_);
v___x_581_ = lean_apply_1(v_h__1_577_, v_upper_580_);
return v___x_581_;
}
else
{
lean_object* v_upper_582_; lean_object* v_k_583_; lean_object* v_v_584_; lean_object* v_tree_585_; lean_object* v_next_586_; lean_object* v___x_587_; 
lean_inc_ref(v_iter_579_);
lean_dec(v_h__1_577_);
v_upper_582_ = lean_ctor_get(v_x_576_, 1);
lean_inc(v_upper_582_);
lean_dec_ref(v_x_576_);
v_k_583_ = lean_ctor_get(v_iter_579_, 0);
lean_inc(v_k_583_);
v_v_584_ = lean_ctor_get(v_iter_579_, 1);
lean_inc(v_v_584_);
v_tree_585_ = lean_ctor_get(v_iter_579_, 2);
lean_inc(v_tree_585_);
v_next_586_ = lean_ctor_get(v_iter_579_, 3);
lean_inc(v_next_586_);
lean_dec_ref_known(v_iter_579_, 4);
v___x_587_ = lean_apply_5(v_h__2_578_, v_k_583_, v_v_584_, v_tree_585_, v_next_586_, v_upper_582_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_inst_590_, lean_object* v_motive_591_, lean_object* v_x_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_588_, v_00_u03b2_589_, v_inst_590_, v_motive_591_, v_x_592_, v_h__1_593_, v_h__2_594_);
lean_dec_ref(v_inst_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_inst_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_600_, lean_object* v_00_u03b2_601_, lean_object* v_inst_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_600_, v_00_u03b2_601_, v_inst_602_);
lean_dec_ref(v_inst_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_604_, lean_object* v_recur_605_, lean_object* v_it_606_, lean_object* v_____do__lift_607_){
_start:
{
if (lean_obj_tag(v_____do__lift_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; 
lean_dec_ref(v_it_606_);
lean_dec(v_recur_605_);
v_a_608_ = lean_ctor_get(v_____do__lift_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v_____do__lift_607_, 1);
v___x_609_ = lean_apply_2(v_toPure_604_, lean_box(0), v_a_608_);
return v___x_609_;
}
else
{
lean_object* v_a_610_; lean_object* v___x_611_; 
lean_dec(v_toPure_604_);
v_a_610_ = lean_ctor_get(v_____do__lift_607_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v_____do__lift_607_, 1);
v___x_611_ = lean_apply_4(v_recur_605_, v_it_606_, v_a_610_, lean_box(0), lean_box(0));
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_612_, lean_object* v_recur_613_, lean_object* v___y_614_, lean_object* v_acc_615_, lean_object* v_toBind_616_, lean_object* v_s_617_){
_start:
{
switch(lean_obj_tag(v_s_617_))
{
case 0:
{
lean_object* v_it_618_; lean_object* v_out_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_it_618_ = lean_ctor_get(v_s_617_, 0);
lean_inc(v_it_618_);
v_out_619_ = lean_ctor_get(v_s_617_, 1);
lean_inc(v_out_619_);
lean_dec_ref_known(v_s_617_, 2);
v___f_620_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_620_, 0, v_toPure_612_);
lean_closure_set(v___f_620_, 1, v_recur_613_);
lean_closure_set(v___f_620_, 2, v_it_618_);
v___x_621_ = lean_apply_3(v___y_614_, v_out_619_, lean_box(0), v_acc_615_);
v___x_622_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_621_, v___f_620_);
return v___x_622_;
}
case 1:
{
lean_object* v_it_623_; lean_object* v___x_624_; 
lean_dec(v_toBind_616_);
lean_dec(v___y_614_);
lean_dec(v_toPure_612_);
v_it_623_ = lean_ctor_get(v_s_617_, 0);
lean_inc(v_it_623_);
lean_dec_ref_known(v_s_617_, 1);
v___x_624_ = lean_apply_4(v_recur_613_, v_it_623_, v_acc_615_, lean_box(0), lean_box(0));
return v___x_624_;
}
default: 
{
lean_object* v___x_625_; 
lean_dec(v_toBind_616_);
lean_dec(v___y_614_);
lean_dec(v_recur_613_);
v___x_625_ = lean_apply_2(v_toPure_612_, lean_box(0), v_acc_615_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_626_, lean_object* v___y_627_, lean_object* v_toBind_628_, lean_object* v_inst_629_, lean_object* v_lift_630_, lean_object* v_it_631_, lean_object* v_acc_632_, lean_object* v_hP_633_, lean_object* v_recur_634_){
_start:
{
lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___f_635_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_635_, 0, v_toPure_626_);
lean_closure_set(v___f_635_, 1, v_recur_634_);
lean_closure_set(v___f_635_, 2, v___y_627_);
lean_closure_set(v___f_635_, 3, v_acc_632_);
lean_closure_set(v___f_635_, 4, v_toBind_628_);
v___x_636_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_629_, v_it_631_);
v___x_637_ = lean_apply_4(v_lift_630_, lean_box(0), lean_box(0), v___f_635_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_lift_640_, lean_object* v_00_u03b3_641_, lean_object* v_Pl_642_, lean_object* v_it_643_, lean_object* v_init_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_toApplicative_646_; lean_object* v_toBind_647_; lean_object* v_toPure_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v_toApplicative_646_ = lean_ctor_get(v_inst_638_, 0);
lean_inc_ref(v_toApplicative_646_);
v_toBind_647_ = lean_ctor_get(v_inst_638_, 1);
lean_inc(v_toBind_647_);
lean_dec_ref(v_inst_638_);
v_toPure_648_ = lean_ctor_get(v_toApplicative_646_, 1);
lean_inc(v_toPure_648_);
lean_dec_ref(v_toApplicative_646_);
v___f_649_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_649_, 0, v_toPure_648_);
lean_closure_set(v___f_649_, 1, v___y_645_);
lean_closure_set(v___f_649_, 2, v_toBind_647_);
lean_closure_set(v___f_649_, 3, v_inst_639_);
lean_closure_set(v___f_649_, 4, v_lift_640_);
v___x_650_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_649_, v_it_643_, v_init_644_, lean_box(0));
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg(lean_object* v_inst_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v___f_653_; 
v___f_653_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_653_, 0, v_inst_652_);
lean_closure_set(v___f_653_, 1, v_inst_651_);
return v___f_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_inst_656_, lean_object* v_m_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___f_659_; 
v___f_659_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxcIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_659_, 0, v_inst_658_);
lean_closure_set(v___f_659_, 1, v_inst_656_);
return v___f_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_iter_662_; 
v_iter_662_ = lean_ctor_get(v_x_661_, 0);
lean_inc(v_iter_662_);
if (lean_obj_tag(v_iter_662_) == 0)
{
lean_object* v___x_663_; 
lean_dec_ref(v_x_661_);
lean_dec_ref(v_inst_660_);
v___x_663_ = lean_box(2);
return v___x_663_;
}
else
{
lean_object* v_upper_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_681_; 
v_upper_664_ = lean_ctor_get(v_x_661_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_661_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v_x_661_, 0);
lean_dec(v_unused_682_);
v___x_666_ = v_x_661_;
v_isShared_667_ = v_isSharedCheck_681_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_upper_664_);
lean_dec(v_x_661_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_681_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_k_668_; lean_object* v_v_669_; lean_object* v_tree_670_; lean_object* v_next_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_k_668_ = lean_ctor_get(v_iter_662_, 0);
lean_inc_n(v_k_668_, 2);
v_v_669_ = lean_ctor_get(v_iter_662_, 1);
lean_inc(v_v_669_);
v_tree_670_ = lean_ctor_get(v_iter_662_, 2);
lean_inc(v_tree_670_);
v_next_671_ = lean_ctor_get(v_iter_662_, 3);
lean_inc(v_next_671_);
lean_dec_ref_known(v_iter_662_, 4);
lean_inc(v_upper_664_);
v___x_672_ = lean_apply_2(v_inst_660_, v_k_668_, v_upper_664_);
v___x_673_ = lean_unbox(v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_670_, v_next_671_);
lean_dec(v_tree_670_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_674_);
v___x_676_ = v___x_666_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_upper_664_);
v___x_676_ = v_reuseFailAlloc_679_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_k_668_);
lean_ctor_set(v___x_677_, 1, v_v_669_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
return v___x_678_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v_next_671_);
lean_dec(v_tree_670_);
lean_dec(v_v_669_);
lean_dec(v_k_668_);
lean_del_object(v___x_666_);
lean_dec(v_upper_664_);
v___x_680_ = lean_box(2);
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_688_, lean_object* v_it_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_688_, v_it_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_691_){
_start:
{
lean_object* v___f_692_; 
v___f_692_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_692_, 0, v_inst_691_);
return v___f_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_693_, lean_object* v_00_u03b2_694_, lean_object* v_inst_695_){
_start:
{
lean_object* v___f_696_; 
v___f_696_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_696_, 0, v_inst_695_);
return v___f_696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_697_, lean_object* v_h__1_698_, lean_object* v_h__2_699_){
_start:
{
lean_object* v_iter_700_; 
v_iter_700_ = lean_ctor_get(v_x_697_, 0);
if (lean_obj_tag(v_iter_700_) == 0)
{
lean_object* v_upper_701_; lean_object* v___x_702_; 
lean_dec(v_h__2_699_);
v_upper_701_ = lean_ctor_get(v_x_697_, 1);
lean_inc(v_upper_701_);
lean_dec_ref(v_x_697_);
v___x_702_ = lean_apply_1(v_h__1_698_, v_upper_701_);
return v___x_702_;
}
else
{
lean_object* v_upper_703_; lean_object* v_k_704_; lean_object* v_v_705_; lean_object* v_tree_706_; lean_object* v_next_707_; lean_object* v___x_708_; 
lean_inc_ref(v_iter_700_);
lean_dec(v_h__1_698_);
v_upper_703_ = lean_ctor_get(v_x_697_, 1);
lean_inc(v_upper_703_);
lean_dec_ref(v_x_697_);
v_k_704_ = lean_ctor_get(v_iter_700_, 0);
lean_inc(v_k_704_);
v_v_705_ = lean_ctor_get(v_iter_700_, 1);
lean_inc(v_v_705_);
v_tree_706_ = lean_ctor_get(v_iter_700_, 2);
lean_inc(v_tree_706_);
v_next_707_ = lean_ctor_get(v_iter_700_, 3);
lean_inc(v_next_707_);
lean_dec_ref_known(v_iter_700_, 4);
v___x_708_ = lean_apply_5(v_h__2_699_, v_k_704_, v_v_705_, v_tree_706_, v_next_707_, v_upper_703_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_709_, lean_object* v_00_u03b2_710_, lean_object* v_inst_711_, lean_object* v_motive_712_, lean_object* v_x_713_, lean_object* v_h__1_714_, lean_object* v_h__2_715_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_725_, lean_object* v_00_u03b2_726_, lean_object* v_inst_727_, lean_object* v_motive_728_, lean_object* v_x_729_, lean_object* v_h__1_730_, lean_object* v_h__2_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_725_, v_00_u03b2_726_, v_inst_727_, v_motive_728_, v_x_729_, v_h__1_730_, v_h__2_731_);
lean_dec_ref(v_inst_727_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_inst_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_box(0);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_737_, lean_object* v_00_u03b2_738_, lean_object* v_inst_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_737_, v_00_u03b2_738_, v_inst_739_);
lean_dec_ref(v_inst_739_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_741_, lean_object* v_recur_742_, lean_object* v_it_743_, lean_object* v_____do__lift_744_){
_start:
{
if (lean_obj_tag(v_____do__lift_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
lean_dec_ref(v_it_743_);
lean_dec(v_recur_742_);
v_a_745_ = lean_ctor_get(v_____do__lift_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v_____do__lift_744_, 1);
v___x_746_ = lean_apply_2(v_toPure_741_, lean_box(0), v_a_745_);
return v___x_746_;
}
else
{
lean_object* v_a_747_; lean_object* v___x_748_; 
lean_dec(v_toPure_741_);
v_a_747_ = lean_ctor_get(v_____do__lift_744_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v_____do__lift_744_, 1);
v___x_748_ = lean_apply_4(v_recur_742_, v_it_743_, v_a_747_, lean_box(0), lean_box(0));
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_749_, lean_object* v_recur_750_, lean_object* v___y_751_, lean_object* v_acc_752_, lean_object* v_toBind_753_, lean_object* v_s_754_){
_start:
{
switch(lean_obj_tag(v_s_754_))
{
case 0:
{
lean_object* v_it_755_; lean_object* v_out_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_it_755_ = lean_ctor_get(v_s_754_, 0);
lean_inc(v_it_755_);
v_out_756_ = lean_ctor_get(v_s_754_, 1);
lean_inc(v_out_756_);
lean_dec_ref_known(v_s_754_, 2);
v___f_757_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_757_, 0, v_toPure_749_);
lean_closure_set(v___f_757_, 1, v_recur_750_);
lean_closure_set(v___f_757_, 2, v_it_755_);
v___x_758_ = lean_apply_3(v___y_751_, v_out_756_, lean_box(0), v_acc_752_);
v___x_759_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_758_, v___f_757_);
return v___x_759_;
}
case 1:
{
lean_object* v_it_760_; lean_object* v___x_761_; 
lean_dec(v_toBind_753_);
lean_dec(v___y_751_);
lean_dec(v_toPure_749_);
v_it_760_ = lean_ctor_get(v_s_754_, 0);
lean_inc(v_it_760_);
lean_dec_ref_known(v_s_754_, 1);
v___x_761_ = lean_apply_4(v_recur_750_, v_it_760_, v_acc_752_, lean_box(0), lean_box(0));
return v___x_761_;
}
default: 
{
lean_object* v___x_762_; 
lean_dec(v_toBind_753_);
lean_dec(v___y_751_);
lean_dec(v_recur_750_);
v___x_762_ = lean_apply_2(v_toPure_749_, lean_box(0), v_acc_752_);
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_763_, lean_object* v___y_764_, lean_object* v_toBind_765_, lean_object* v_inst_766_, lean_object* v_lift_767_, lean_object* v_it_768_, lean_object* v_acc_769_, lean_object* v_hP_770_, lean_object* v_recur_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___f_772_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_772_, 0, v_toPure_763_);
lean_closure_set(v___f_772_, 1, v_recur_771_);
lean_closure_set(v___f_772_, 2, v___y_764_);
lean_closure_set(v___f_772_, 3, v_acc_769_);
lean_closure_set(v___f_772_, 4, v_toBind_765_);
v___x_773_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_766_, v_it_768_);
v___x_774_ = lean_apply_4(v_lift_767_, lean_box(0), lean_box(0), v___f_772_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_775_, lean_object* v_inst_776_, lean_object* v_lift_777_, lean_object* v_00_u03b3_778_, lean_object* v_Pl_779_, lean_object* v_it_780_, lean_object* v_init_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_toApplicative_783_; lean_object* v_toBind_784_; lean_object* v_toPure_785_; lean_object* v___f_786_; lean_object* v___x_787_; 
v_toApplicative_783_ = lean_ctor_get(v_inst_775_, 0);
lean_inc_ref(v_toApplicative_783_);
v_toBind_784_ = lean_ctor_get(v_inst_775_, 1);
lean_inc(v_toBind_784_);
lean_dec_ref(v_inst_775_);
v_toPure_785_ = lean_ctor_get(v_toApplicative_783_, 1);
lean_inc(v_toPure_785_);
lean_dec_ref(v_toApplicative_783_);
v___f_786_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_786_, 0, v_toPure_785_);
lean_closure_set(v___f_786_, 1, v___y_782_);
lean_closure_set(v___f_786_, 2, v_toBind_784_);
lean_closure_set(v___f_786_, 3, v_inst_776_);
lean_closure_set(v___f_786_, 4, v_lift_777_);
v___x_787_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_786_, v_it_780_, v_init_781_, lean_box(0));
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg(lean_object* v_inst_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v___f_790_; 
v___f_790_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_790_, 0, v_inst_789_);
lean_closure_set(v___f_790_, 1, v_inst_788_);
return v___f_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_inst_793_, lean_object* v_m_794_, lean_object* v_inst_795_){
_start:
{
lean_object* v___f_796_; 
v___f_796_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RxoIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_796_, 0, v_inst_795_);
lean_closure_set(v___f_796_, 1, v_inst_793_);
return v___f_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(lean_object* v_carrier_797_, lean_object* v_range_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v_carrier_797_);
lean_ctor_set(v___x_799_, 1, v_range_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_){
_start:
{
lean_object* v___f_804_; 
v___f_804_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0));
return v___f_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_inst_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_805_, v_00_u03b2_806_, v_inst_807_);
lean_dec_ref(v_inst_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(lean_object* v_x_809_){
_start:
{
lean_object* v_treeMap_810_; lean_object* v_range_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_820_; 
v_treeMap_810_ = lean_ctor_get(v_x_809_, 0);
v_range_811_ = lean_ctor_get(v_x_809_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_820_ == 0)
{
v___x_813_ = v_x_809_;
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_range_811_);
lean_inc(v_treeMap_810_);
lean_dec(v_x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_820_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = lean_box(0);
v___x_816_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_810_, v___x_815_);
lean_dec(v_treeMap_810_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_range_811_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_inst_824_){
_start:
{
lean_object* v___f_825_; 
v___f_825_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0));
return v___f_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_826_, v_00_u03b2_827_, v_inst_828_);
lean_dec_ref(v_inst_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(lean_object* v_carrier_830_, lean_object* v_range_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_carrier_830_);
lean_ctor_set(v___x_832_, 1, v_range_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_834_, lean_object* v_inst_835_){
_start:
{
lean_object* v___f_836_; 
v___f_836_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0));
return v___f_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_837_, lean_object* v_inst_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_837_, v_inst_838_);
lean_dec_ref(v_inst_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(lean_object* v_x_840_){
_start:
{
lean_object* v_treeMap_841_; lean_object* v_range_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_851_; 
v_treeMap_841_ = lean_ctor_get(v_x_840_, 0);
v_range_842_ = lean_ctor_get(v_x_840_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_840_);
if (v_isSharedCheck_851_ == 0)
{
v___x_844_ = v_x_840_;
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_range_842_);
lean_inc(v_treeMap_841_);
lean_dec(v_x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_851_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_box(0);
v___x_847_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_841_, v___x_846_);
lean_dec(v_treeMap_841_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_847_);
v___x_849_ = v___x_844_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_range_842_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_853_, lean_object* v_inst_854_){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0));
return v___f_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_856_, lean_object* v_inst_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_856_, v_inst_857_);
lean_dec_ref(v_inst_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(lean_object* v_carrier_859_, lean_object* v_range_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_carrier_859_);
lean_ctor_set(v___x_861_, 1, v_range_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_inst_865_){
_start:
{
lean_object* v___f_866_; 
v___f_866_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0));
return v___f_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_867_, lean_object* v_00_u03b2_868_, lean_object* v_inst_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_867_, v_00_u03b2_868_, v_inst_869_);
lean_dec_ref(v_inst_869_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(lean_object* v_x_871_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_884_, lean_object* v_00_u03b2_885_, lean_object* v_inst_886_){
_start:
{
lean_object* v___f_887_; 
v___f_887_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0));
return v___f_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_888_, lean_object* v_00_u03b2_889_, lean_object* v_inst_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_888_, v_00_u03b2_889_, v_inst_890_);
lean_dec_ref(v_inst_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(lean_object* v_carrier_892_, lean_object* v_range_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_carrier_892_);
lean_ctor_set(v___x_894_, 1, v_range_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_inst_898_){
_start:
{
lean_object* v___f_899_; 
v___f_899_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0));
return v___f_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_inst_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_900_, v_00_u03b2_901_, v_inst_902_);
lean_dec_ref(v_inst_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(lean_object* v_x_904_){
_start:
{
lean_object* v_treeMap_905_; lean_object* v_range_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_915_; 
v_treeMap_905_ = lean_ctor_get(v_x_904_, 0);
v_range_906_ = lean_ctor_get(v_x_904_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_915_ == 0)
{
v___x_908_ = v_x_904_;
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_range_906_);
lean_inc(v_treeMap_905_);
lean_dec(v_x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = lean_box(0);
v___x_911_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_905_, v___x_910_);
lean_dec(v_treeMap_905_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_range_906_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_917_, lean_object* v_00_u03b2_918_, lean_object* v_inst_919_){
_start:
{
lean_object* v___f_920_; 
v___f_920_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0));
return v___f_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_inst_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_921_, v_00_u03b2_922_, v_inst_923_);
lean_dec_ref(v_inst_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(lean_object* v_carrier_925_, lean_object* v_range_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_carrier_925_);
lean_ctor_set(v___x_927_, 1, v_range_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_929_, lean_object* v_inst_930_){
_start:
{
lean_object* v___f_931_; 
v___f_931_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0));
return v___f_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_932_, lean_object* v_inst_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_932_, v_inst_933_);
lean_dec_ref(v_inst_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(lean_object* v_x_935_){
_start:
{
lean_object* v_treeMap_936_; lean_object* v_range_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_946_; 
v_treeMap_936_ = lean_ctor_get(v_x_935_, 0);
v_range_937_ = lean_ctor_get(v_x_935_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v_x_935_);
if (v_isSharedCheck_946_ == 0)
{
v___x_939_ = v_x_935_;
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_range_937_);
lean_inc(v_treeMap_936_);
lean_dec(v_x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_946_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_936_, v___x_941_);
lean_dec(v_treeMap_936_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_range_937_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_948_, lean_object* v_inst_949_){
_start:
{
lean_object* v___f_950_; 
v___f_950_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0));
return v___f_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_951_, lean_object* v_inst_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_951_, v_inst_952_);
lean_dec_ref(v_inst_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(lean_object* v_carrier_954_, lean_object* v_range_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v_carrier_954_);
lean_ctor_set(v___x_956_, 1, v_range_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_inst_960_){
_start:
{
lean_object* v___f_961_; 
v___f_961_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0));
return v___f_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_962_, lean_object* v_00_u03b2_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_962_, v_00_u03b2_963_, v_inst_964_);
lean_dec_ref(v_inst_964_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(lean_object* v_x_966_){
_start:
{
lean_object* v_treeMap_967_; lean_object* v_range_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_treeMap_967_ = lean_ctor_get(v_x_966_, 0);
v_range_968_ = lean_ctor_get(v_x_966_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_x_966_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v_x_966_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_range_968_);
lean_inc(v_treeMap_967_);
lean_dec(v_x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_972_ = lean_box(0);
v___x_973_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_967_, v___x_972_);
lean_dec(v_treeMap_967_);
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
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_range_968_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_inst_981_){
_start:
{
lean_object* v___f_982_; 
v___f_982_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0));
return v___f_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_983_, v_00_u03b2_984_, v_inst_985_);
lean_dec_ref(v_inst_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_987_, lean_object* v_t_988_, lean_object* v_lowerBound_989_, lean_object* v_upperBound_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
v___x_992_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_987_, v_t_988_, v_lowerBound_989_, v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v_upperBound_990_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_inst_996_, lean_object* v_t_997_, lean_object* v_lowerBound_998_, lean_object* v_upperBound_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(0);
v___x_1001_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_996_, v_t_997_, v_lowerBound_998_, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_upperBound_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(lean_object* v_carrier_1003_, lean_object* v_range_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_carrier_1003_);
lean_ctor_set(v___x_1005_, 1, v_range_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_inst_1009_){
_start:
{
lean_object* v___f_1010_; 
v___f_1010_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0));
return v___f_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_1011_, v_00_u03b2_1012_, v_inst_1013_);
lean_dec_ref(v_inst_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_range_1017_; lean_object* v_treeMap_1018_; lean_object* v_lower_1019_; lean_object* v_upper_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1029_; 
v_range_1017_ = lean_ctor_get(v_x_1016_, 1);
lean_inc_ref(v_range_1017_);
v_treeMap_1018_ = lean_ctor_get(v_x_1016_, 0);
lean_inc(v_treeMap_1018_);
lean_dec_ref(v_x_1016_);
v_lower_1019_ = lean_ctor_get(v_range_1017_, 0);
v_upper_1020_ = lean_ctor_get(v_range_1017_, 1);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_range_1017_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1022_ = v_range_1017_;
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_upper_1020_);
lean_inc(v_lower_1019_);
lean_dec(v_range_1017_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1015_, v_treeMap_1018_, v_lower_1019_, v___x_1024_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_upper_1020_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_1030_){
_start:
{
lean_object* v___f_1031_; 
v___f_1031_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1031_, 0, v_inst_1030_);
return v___f_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_inst_1034_){
_start:
{
lean_object* v___f_1035_; 
v___f_1035_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1035_, 0, v_inst_1034_);
return v___f_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(lean_object* v_carrier_1036_, lean_object* v_range_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_carrier_1036_);
lean_ctor_set(v___x_1038_, 1, v_range_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_1040_, lean_object* v_inst_1041_){
_start:
{
lean_object* v___f_1042_; 
v___f_1042_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0));
return v___f_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_inst_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_1043_, v_inst_1044_);
lean_dec_ref(v_inst_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v_range_1048_; lean_object* v_treeMap_1049_; lean_object* v_lower_1050_; lean_object* v_upper_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1060_; 
v_range_1048_ = lean_ctor_get(v_x_1047_, 1);
lean_inc_ref(v_range_1048_);
v_treeMap_1049_ = lean_ctor_get(v_x_1047_, 0);
lean_inc(v_treeMap_1049_);
lean_dec_ref(v_x_1047_);
v_lower_1050_ = lean_ctor_get(v_range_1048_, 0);
v_upper_1051_ = lean_ctor_get(v_range_1048_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_range_1048_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1053_ = v_range_1048_;
v_isShared_1054_ = v_isSharedCheck_1060_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_upper_1051_);
lean_inc(v_lower_1050_);
lean_dec(v_range_1048_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1060_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1046_, v_treeMap_1049_, v_lower_1050_, v___x_1055_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1056_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_upper_1051_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_1061_){
_start:
{
lean_object* v___f_1062_; 
v___f_1062_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1062_, 0, v_inst_1061_);
return v___f_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_1063_, lean_object* v_inst_1064_){
_start:
{
lean_object* v___f_1065_; 
v___f_1065_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1065_, 0, v_inst_1064_);
return v___f_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(lean_object* v_carrier_1066_, lean_object* v_range_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_carrier_1066_);
lean_ctor_set(v___x_1068_, 1, v_range_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_inst_1072_){
_start:
{
lean_object* v___f_1073_; 
v___f_1073_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0));
return v___f_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_inst_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_1074_, v_00_u03b2_1075_, v_inst_1076_);
lean_dec_ref(v_inst_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v_range_1080_; lean_object* v_treeMap_1081_; lean_object* v_lower_1082_; lean_object* v_upper_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1092_; 
v_range_1080_ = lean_ctor_get(v_x_1079_, 1);
lean_inc_ref(v_range_1080_);
v_treeMap_1081_ = lean_ctor_get(v_x_1079_, 0);
lean_inc(v_treeMap_1081_);
lean_dec_ref(v_x_1079_);
v_lower_1082_ = lean_ctor_get(v_range_1080_, 0);
v_upper_1083_ = lean_ctor_get(v_range_1080_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_range_1080_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1085_ = v_range_1080_;
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_upper_1083_);
lean_inc(v_lower_1082_);
lean_dec(v_range_1080_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1078_, v_treeMap_1081_, v_lower_1082_, v___x_1087_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1088_);
v___x_1090_ = v___x_1085_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_upper_1083_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_1093_){
_start:
{
lean_object* v___f_1094_; 
v___f_1094_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1094_, 0, v_inst_1093_);
return v___f_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_inst_1097_){
_start:
{
lean_object* v___f_1098_; 
v___f_1098_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1098_, 0, v_inst_1097_);
return v___f_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_1099_, lean_object* v_t_1100_, lean_object* v_lowerBound_1101_, lean_object* v_upperBound_1102_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(0);
v___x_1104_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1099_, v_t_1100_, v_lowerBound_1101_, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_upperBound_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_inst_1108_, lean_object* v_t_1109_, lean_object* v_lowerBound_1110_, lean_object* v_upperBound_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1108_, v_t_1109_, v_lowerBound_1110_, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_upperBound_1111_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(lean_object* v_carrier_1115_, lean_object* v_range_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_carrier_1115_);
lean_ctor_set(v___x_1117_, 1, v_range_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_inst_1121_){
_start:
{
lean_object* v___f_1122_; 
v___f_1122_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0));
return v___f_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_inst_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_1123_, v_00_u03b2_1124_, v_inst_1125_);
lean_dec_ref(v_inst_1125_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_range_1129_; lean_object* v_treeMap_1130_; lean_object* v_lower_1131_; lean_object* v_upper_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1141_; 
v_range_1129_ = lean_ctor_get(v_x_1128_, 1);
lean_inc_ref(v_range_1129_);
v_treeMap_1130_ = lean_ctor_get(v_x_1128_, 0);
lean_inc(v_treeMap_1130_);
lean_dec_ref(v_x_1128_);
v_lower_1131_ = lean_ctor_get(v_range_1129_, 0);
v_upper_1132_ = lean_ctor_get(v_range_1129_, 1);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_range_1129_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1134_ = v_range_1129_;
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_upper_1132_);
lean_inc(v_lower_1131_);
lean_dec(v_range_1129_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1141_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1127_, v_treeMap_1130_, v_lower_1131_, v___x_1136_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_upper_1132_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_1142_){
_start:
{
lean_object* v___f_1143_; 
v___f_1143_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1143_, 0, v_inst_1142_);
return v___f_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_inst_1146_){
_start:
{
lean_object* v___f_1147_; 
v___f_1147_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1147_, 0, v_inst_1146_);
return v___f_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(lean_object* v_carrier_1148_, lean_object* v_range_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_carrier_1148_);
lean_ctor_set(v___x_1150_, 1, v_range_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_1152_, lean_object* v_inst_1153_){
_start:
{
lean_object* v___f_1154_; 
v___f_1154_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0));
return v___f_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_inst_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_1155_, v_inst_1156_);
lean_dec_ref(v_inst_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1158_, lean_object* v_x_1159_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_1173_){
_start:
{
lean_object* v___f_1174_; 
v___f_1174_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1174_, 0, v_inst_1173_);
return v___f_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_1175_, lean_object* v_inst_1176_){
_start:
{
lean_object* v___f_1177_; 
v___f_1177_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1177_, 0, v_inst_1176_);
return v___f_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(lean_object* v_carrier_1178_, lean_object* v_range_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_carrier_1178_);
lean_ctor_set(v___x_1180_, 1, v_range_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_inst_1184_){
_start:
{
lean_object* v___f_1185_; 
v___f_1185_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0));
return v___f_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_inst_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_1186_, v_00_u03b2_1187_, v_inst_1188_);
lean_dec_ref(v_inst_1188_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1190_, lean_object* v_x_1191_){
_start:
{
lean_object* v_range_1192_; lean_object* v_treeMap_1193_; lean_object* v_lower_1194_; lean_object* v_upper_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
v_range_1192_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_range_1192_);
v_treeMap_1193_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_treeMap_1193_);
lean_dec_ref(v_x_1191_);
v_lower_1194_ = lean_ctor_get(v_range_1192_, 0);
v_upper_1195_ = lean_ctor_get(v_range_1192_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_range_1192_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v_range_1192_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_upper_1195_);
lean_inc(v_lower_1194_);
lean_dec(v_range_1192_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1190_, v_treeMap_1193_, v_lower_1194_, v___x_1199_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_upper_1195_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_1205_){
_start:
{
lean_object* v___f_1206_; 
v___f_1206_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1206_, 0, v_inst_1205_);
return v___f_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_inst_1209_){
_start:
{
lean_object* v___f_1210_; 
v___f_1210_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1210_, 0, v_inst_1209_);
return v___f_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_1211_, lean_object* v_t_1212_, lean_object* v_lowerBound_1213_, lean_object* v_upperBound_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1211_, v_t_1212_, v_lowerBound_1213_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_upperBound_1214_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_inst_1220_, lean_object* v_t_1221_, lean_object* v_lowerBound_1222_, lean_object* v_upperBound_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1220_, v_t_1221_, v_lowerBound_1222_, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_upperBound_1223_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(lean_object* v_carrier_1227_, lean_object* v_range_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_carrier_1227_);
lean_ctor_set(v___x_1229_, 1, v_range_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___f_1234_; 
v___f_1234_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0));
return v___f_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_inst_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1235_, v_00_u03b2_1236_, v_inst_1237_);
lean_dec_ref(v_inst_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1239_, lean_object* v_x_1240_){
_start:
{
lean_object* v_range_1241_; lean_object* v_treeMap_1242_; lean_object* v_lower_1243_; lean_object* v_upper_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1253_; 
v_range_1241_ = lean_ctor_get(v_x_1240_, 1);
lean_inc_ref(v_range_1241_);
v_treeMap_1242_ = lean_ctor_get(v_x_1240_, 0);
lean_inc(v_treeMap_1242_);
lean_dec_ref(v_x_1240_);
v_lower_1243_ = lean_ctor_get(v_range_1241_, 0);
v_upper_1244_ = lean_ctor_get(v_range_1241_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_range_1241_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1246_ = v_range_1241_;
v_isShared_1247_ = v_isSharedCheck_1253_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_upper_1244_);
lean_inc(v_lower_1243_);
lean_dec(v_range_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1253_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1239_, v_treeMap_1242_, v_lower_1243_, v___x_1248_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1249_);
v___x_1251_ = v___x_1246_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_upper_1244_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1254_){
_start:
{
lean_object* v___f_1255_; 
v___f_1255_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1255_, 0, v_inst_1254_);
return v___f_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___f_1259_; 
v___f_1259_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1259_, 0, v_inst_1258_);
return v___f_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(lean_object* v_carrier_1260_, lean_object* v_range_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_carrier_1260_);
lean_ctor_set(v___x_1262_, 1, v_range_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1264_, lean_object* v_inst_1265_){
_start:
{
lean_object* v___f_1266_; 
v___f_1266_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0));
return v___f_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_inst_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1267_, v_inst_1268_);
lean_dec_ref(v_inst_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v_range_1272_; lean_object* v_treeMap_1273_; lean_object* v_lower_1274_; lean_object* v_upper_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1284_; 
v_range_1272_ = lean_ctor_get(v_x_1271_, 1);
lean_inc_ref(v_range_1272_);
v_treeMap_1273_ = lean_ctor_get(v_x_1271_, 0);
lean_inc(v_treeMap_1273_);
lean_dec_ref(v_x_1271_);
v_lower_1274_ = lean_ctor_get(v_range_1272_, 0);
v_upper_1275_ = lean_ctor_get(v_range_1272_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_range_1272_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1277_ = v_range_1272_;
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_upper_1275_);
lean_inc(v_lower_1274_);
lean_dec(v_range_1272_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1270_, v_treeMap_1273_, v_lower_1274_, v___x_1279_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_upper_1275_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1285_){
_start:
{
lean_object* v___f_1286_; 
v___f_1286_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1286_, 0, v_inst_1285_);
return v___f_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1287_, lean_object* v_inst_1288_){
_start:
{
lean_object* v___f_1289_; 
v___f_1289_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1289_, 0, v_inst_1288_);
return v___f_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(lean_object* v_carrier_1290_, lean_object* v_range_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_carrier_1290_);
lean_ctor_set(v___x_1292_, 1, v_range_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1294_, lean_object* v_00_u03b2_1295_, lean_object* v_inst_1296_){
_start:
{
lean_object* v___f_1297_; 
v___f_1297_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0));
return v___f_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_inst_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1298_, v_00_u03b2_1299_, v_inst_1300_);
lean_dec_ref(v_inst_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v_range_1304_; lean_object* v_treeMap_1305_; lean_object* v_lower_1306_; lean_object* v_upper_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1316_; 
v_range_1304_ = lean_ctor_get(v_x_1303_, 1);
lean_inc_ref(v_range_1304_);
v_treeMap_1305_ = lean_ctor_get(v_x_1303_, 0);
lean_inc(v_treeMap_1305_);
lean_dec_ref(v_x_1303_);
v_lower_1306_ = lean_ctor_get(v_range_1304_, 0);
v_upper_1307_ = lean_ctor_get(v_range_1304_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_range_1304_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1309_ = v_range_1304_;
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_upper_1307_);
lean_inc(v_lower_1306_);
lean_dec(v_range_1304_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1302_, v_treeMap_1305_, v_lower_1306_, v___x_1311_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1312_);
v___x_1314_ = v___x_1309_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_upper_1307_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1317_){
_start:
{
lean_object* v___f_1318_; 
v___f_1318_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1318_, 0, v_inst_1317_);
return v___f_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1319_, lean_object* v_00_u03b2_1320_, lean_object* v_inst_1321_){
_start:
{
lean_object* v___f_1322_; 
v___f_1322_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1322_, 0, v_inst_1321_);
return v___f_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1323_, lean_object* v_t_1324_, lean_object* v_lowerBound_1325_, lean_object* v_upperBound_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1323_, v_t_1324_, v_lowerBound_1325_, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v_upperBound_1326_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_inst_1332_, lean_object* v_t_1333_, lean_object* v_lowerBound_1334_, lean_object* v_upperBound_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1332_, v_t_1333_, v_lowerBound_1334_, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v_upperBound_1335_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(lean_object* v_carrier_1339_, lean_object* v_range_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_carrier_1339_);
lean_ctor_set(v___x_1341_, 1, v_range_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1343_, lean_object* v_00_u03b2_1344_, lean_object* v_inst_1345_){
_start:
{
lean_object* v___f_1346_; 
v___f_1346_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0));
return v___f_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_inst_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1347_, v_00_u03b2_1348_, v_inst_1349_);
lean_dec_ref(v_inst_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_range_1353_; lean_object* v_treeMap_1354_; lean_object* v_lower_1355_; lean_object* v_upper_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1365_; 
v_range_1353_ = lean_ctor_get(v_x_1352_, 1);
lean_inc_ref(v_range_1353_);
v_treeMap_1354_ = lean_ctor_get(v_x_1352_, 0);
lean_inc(v_treeMap_1354_);
lean_dec_ref(v_x_1352_);
v_lower_1355_ = lean_ctor_get(v_range_1353_, 0);
v_upper_1356_ = lean_ctor_get(v_range_1353_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_range_1353_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1358_ = v_range_1353_;
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_upper_1356_);
lean_inc(v_lower_1355_);
lean_dec(v_range_1353_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1365_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1351_, v_treeMap_1354_, v_lower_1355_, v___x_1360_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1361_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_upper_1356_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1366_){
_start:
{
lean_object* v___f_1367_; 
v___f_1367_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1367_, 0, v_inst_1366_);
return v___f_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_inst_1370_){
_start:
{
lean_object* v___f_1371_; 
v___f_1371_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1371_, 0, v_inst_1370_);
return v___f_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(lean_object* v_carrier_1372_, lean_object* v_range_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_carrier_1372_);
lean_ctor_set(v___x_1374_, 1, v_range_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1376_, lean_object* v_inst_1377_){
_start:
{
lean_object* v___f_1378_; 
v___f_1378_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0));
return v___f_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_inst_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1379_, v_inst_1380_);
lean_dec_ref(v_inst_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v_range_1384_; lean_object* v_treeMap_1385_; lean_object* v_lower_1386_; lean_object* v_upper_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1396_; 
v_range_1384_ = lean_ctor_get(v_x_1383_, 1);
lean_inc_ref(v_range_1384_);
v_treeMap_1385_ = lean_ctor_get(v_x_1383_, 0);
lean_inc(v_treeMap_1385_);
lean_dec_ref(v_x_1383_);
v_lower_1386_ = lean_ctor_get(v_range_1384_, 0);
v_upper_1387_ = lean_ctor_get(v_range_1384_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_range_1384_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1389_ = v_range_1384_;
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_upper_1387_);
lean_inc(v_lower_1386_);
lean_dec(v_range_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1382_, v_treeMap_1385_, v_lower_1386_, v___x_1391_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_upper_1387_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1397_){
_start:
{
lean_object* v___f_1398_; 
v___f_1398_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1398_, 0, v_inst_1397_);
return v___f_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1399_, lean_object* v_inst_1400_){
_start:
{
lean_object* v___f_1401_; 
v___f_1401_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1401_, 0, v_inst_1400_);
return v___f_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(lean_object* v_carrier_1402_, lean_object* v_range_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_carrier_1402_);
lean_ctor_set(v___x_1404_, 1, v_range_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_inst_1408_){
_start:
{
lean_object* v___f_1409_; 
v___f_1409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0));
return v___f_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_00_u03b2_1411_, lean_object* v_inst_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1410_, v_00_u03b2_1411_, v_inst_1412_);
lean_dec_ref(v_inst_1412_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_range_1416_; lean_object* v_treeMap_1417_; lean_object* v_lower_1418_; lean_object* v_upper_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1428_; 
v_range_1416_ = lean_ctor_get(v_x_1415_, 1);
lean_inc_ref(v_range_1416_);
v_treeMap_1417_ = lean_ctor_get(v_x_1415_, 0);
lean_inc(v_treeMap_1417_);
lean_dec_ref(v_x_1415_);
v_lower_1418_ = lean_ctor_get(v_range_1416_, 0);
v_upper_1419_ = lean_ctor_get(v_range_1416_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_range_1416_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1421_ = v_range_1416_;
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_upper_1419_);
lean_inc(v_lower_1418_);
lean_dec(v_range_1416_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1414_, v_treeMap_1417_, v_lower_1418_, v___x_1423_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_upper_1419_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1429_){
_start:
{
lean_object* v___f_1430_; 
v___f_1430_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1430_, 0, v_inst_1429_);
return v___f_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1431_, lean_object* v_00_u03b2_1432_, lean_object* v_inst_1433_){
_start:
{
lean_object* v___f_1434_; 
v___f_1434_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1434_, 0, v_inst_1433_);
return v___f_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1435_, lean_object* v_t_1436_, lean_object* v_lowerBound_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1435_, v_t_1436_, v_lowerBound_1437_, v___x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_inst_1442_, lean_object* v_t_1443_, lean_object* v_lowerBound_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_box(0);
v___x_1446_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1442_, v_t_1443_, v_lowerBound_1444_, v___x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(lean_object* v_carrier_1447_, lean_object* v_range_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_carrier_1447_);
lean_ctor_set(v___x_1449_, 1, v_range_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_inst_1453_){
_start:
{
lean_object* v___f_1454_; 
v___f_1454_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0));
return v___f_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_inst_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1455_, v_00_u03b2_1456_, v_inst_1457_);
lean_dec_ref(v_inst_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v_treeMap_1461_; lean_object* v_range_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_treeMap_1461_ = lean_ctor_get(v_x_1460_, 0);
lean_inc(v_treeMap_1461_);
v_range_1462_ = lean_ctor_get(v_x_1460_, 1);
lean_inc(v_range_1462_);
lean_dec_ref(v_x_1460_);
v___x_1463_ = lean_box(0);
v___x_1464_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1459_, v_treeMap_1461_, v_range_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1465_){
_start:
{
lean_object* v___f_1466_; 
v___f_1466_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1466_, 0, v_inst_1465_);
return v___f_1466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1467_, lean_object* v_00_u03b2_1468_, lean_object* v_inst_1469_){
_start:
{
lean_object* v___f_1470_; 
v___f_1470_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1470_, 0, v_inst_1469_);
return v___f_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(lean_object* v_carrier_1471_, lean_object* v_range_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_carrier_1471_);
lean_ctor_set(v___x_1473_, 1, v_range_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1475_, lean_object* v_inst_1476_){
_start:
{
lean_object* v___f_1477_; 
v___f_1477_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0));
return v___f_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_inst_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1478_, v_inst_1479_);
lean_dec_ref(v_inst_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1481_, lean_object* v_x_1482_){
_start:
{
lean_object* v_treeMap_1483_; lean_object* v_range_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_treeMap_1483_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_treeMap_1483_);
v_range_1484_ = lean_ctor_get(v_x_1482_, 1);
lean_inc(v_range_1484_);
lean_dec_ref(v_x_1482_);
v___x_1485_ = lean_box(0);
v___x_1486_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1481_, v_treeMap_1483_, v_range_1484_, v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1487_){
_start:
{
lean_object* v___f_1488_; 
v___f_1488_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1488_, 0, v_inst_1487_);
return v___f_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1489_, lean_object* v_inst_1490_){
_start:
{
lean_object* v___f_1491_; 
v___f_1491_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1491_, 0, v_inst_1490_);
return v___f_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(lean_object* v_carrier_1492_, lean_object* v_range_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_carrier_1492_);
lean_ctor_set(v___x_1494_, 1, v_range_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___f_1499_; 
v___f_1499_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0));
return v___f_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_inst_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1500_, v_00_u03b2_1501_, v_inst_1502_);
lean_dec_ref(v_inst_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_treeMap_1506_; lean_object* v_range_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_treeMap_1506_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_treeMap_1506_);
v_range_1507_ = lean_ctor_get(v_x_1505_, 1);
lean_inc(v_range_1507_);
lean_dec_ref(v_x_1505_);
v___x_1508_ = lean_box(0);
v___x_1509_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1504_, v_treeMap_1506_, v_range_1507_, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1510_){
_start:
{
lean_object* v___f_1511_; 
v___f_1511_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1511_, 0, v_inst_1510_);
return v___f_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_inst_1514_){
_start:
{
lean_object* v___f_1515_; 
v___f_1515_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1515_, 0, v_inst_1514_);
return v___f_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1516_, lean_object* v_t_1517_, lean_object* v_lowerBound_1518_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1516_, v_t_1517_, v_lowerBound_1518_, v___x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1521_, lean_object* v_00_u03b2_1522_, lean_object* v_inst_1523_, lean_object* v_t_1524_, lean_object* v_lowerBound_1525_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1523_, v_t_1524_, v_lowerBound_1525_, v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(lean_object* v_carrier_1528_, lean_object* v_range_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_carrier_1528_);
lean_ctor_set(v___x_1530_, 1, v_range_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1532_, lean_object* v_00_u03b2_1533_, lean_object* v_inst_1534_){
_start:
{
lean_object* v___f_1535_; 
v___f_1535_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0));
return v___f_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_inst_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1536_, v_00_u03b2_1537_, v_inst_1538_);
lean_dec_ref(v_inst_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1540_, lean_object* v_x_1541_){
_start:
{
lean_object* v_treeMap_1542_; lean_object* v_range_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_treeMap_1542_ = lean_ctor_get(v_x_1541_, 0);
lean_inc(v_treeMap_1542_);
v_range_1543_ = lean_ctor_get(v_x_1541_, 1);
lean_inc(v_range_1543_);
lean_dec_ref(v_x_1541_);
v___x_1544_ = lean_box(0);
v___x_1545_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1540_, v_treeMap_1542_, v_range_1543_, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1546_){
_start:
{
lean_object* v___f_1547_; 
v___f_1547_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1547_, 0, v_inst_1546_);
return v___f_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1548_, lean_object* v_00_u03b2_1549_, lean_object* v_inst_1550_){
_start:
{
lean_object* v___f_1551_; 
v___f_1551_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1551_, 0, v_inst_1550_);
return v___f_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(lean_object* v_carrier_1552_, lean_object* v_range_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_carrier_1552_);
lean_ctor_set(v___x_1554_, 1, v_range_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1556_, lean_object* v_inst_1557_){
_start:
{
lean_object* v___f_1558_; 
v___f_1558_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0));
return v___f_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_inst_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1559_, v_inst_1560_);
lean_dec_ref(v_inst_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1562_, lean_object* v_x_1563_){
_start:
{
lean_object* v_treeMap_1564_; lean_object* v_range_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_treeMap_1564_ = lean_ctor_get(v_x_1563_, 0);
lean_inc(v_treeMap_1564_);
v_range_1565_ = lean_ctor_get(v_x_1563_, 1);
lean_inc(v_range_1565_);
lean_dec_ref(v_x_1563_);
v___x_1566_ = lean_box(0);
v___x_1567_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1562_, v_treeMap_1564_, v_range_1565_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1568_){
_start:
{
lean_object* v___f_1569_; 
v___f_1569_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1569_, 0, v_inst_1568_);
return v___f_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1570_, lean_object* v_inst_1571_){
_start:
{
lean_object* v___f_1572_; 
v___f_1572_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1572_, 0, v_inst_1571_);
return v___f_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(lean_object* v_carrier_1573_, lean_object* v_range_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_carrier_1573_);
lean_ctor_set(v___x_1575_, 1, v_range_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_inst_1579_){
_start:
{
lean_object* v___f_1580_; 
v___f_1580_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0));
return v___f_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_00_u03b2_1582_, lean_object* v_inst_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1581_, v_00_u03b2_1582_, v_inst_1583_);
lean_dec_ref(v_inst_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v_treeMap_1587_; lean_object* v_range_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_treeMap_1587_ = lean_ctor_get(v_x_1586_, 0);
lean_inc(v_treeMap_1587_);
v_range_1588_ = lean_ctor_get(v_x_1586_, 1);
lean_inc(v_range_1588_);
lean_dec_ref(v_x_1586_);
v___x_1589_ = lean_box(0);
v___x_1590_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1585_, v_treeMap_1587_, v_range_1588_, v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1591_){
_start:
{
lean_object* v___f_1592_; 
v___f_1592_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1592_, 0, v_inst_1591_);
return v___f_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_inst_1595_){
_start:
{
lean_object* v___f_1596_; 
v___f_1596_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1596_, 0, v_inst_1595_);
return v___f_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1597_, v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1600_);
lean_dec(v_t_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_t_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1606_, lean_object* v_00_u03b2_1607_, lean_object* v_t_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1606_, v_00_u03b2_1607_, v_t_1608_);
lean_dec(v_t_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(lean_object* v_carrier_1610_, lean_object* v_range_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1612_, 0, v_carrier_1610_);
lean_ctor_set(v___x_1612_, 1, v_range_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_){
_start:
{
lean_object* v___f_1616_; 
v___f_1616_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0));
return v___f_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(lean_object* v_x_1617_){
_start:
{
lean_object* v_treeMap_1618_; lean_object* v___x_1619_; 
v_treeMap_1618_ = lean_ctor_get(v_x_1617_, 0);
v___x_1619_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(v_x_1620_);
lean_dec_ref(v_x_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_){
_start:
{
lean_object* v___f_1625_; 
v___f_1625_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0));
return v___f_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(lean_object* v_carrier_1626_, lean_object* v_range_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_carrier_1626_);
lean_ctor_set(v___x_1628_, 1, v_range_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1630_){
_start:
{
lean_object* v___f_1631_; 
v___f_1631_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0));
return v___f_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(lean_object* v_x_1632_){
_start:
{
lean_object* v_treeMap_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_treeMap_1633_ = lean_ctor_get(v_x_1632_, 0);
v___x_1634_ = lean_box(0);
v___x_1635_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1633_, v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(v_x_1636_);
lean_dec_ref(v_x_1636_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1639_){
_start:
{
lean_object* v___f_1640_; 
v___f_1640_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0));
return v___f_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(lean_object* v_carrier_1641_, lean_object* v_range_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v_carrier_1641_);
lean_ctor_set(v___x_1643_, 1, v_range_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_){
_start:
{
lean_object* v___f_1647_; 
v___f_1647_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0));
return v___f_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(lean_object* v_x_1648_){
_start:
{
lean_object* v_treeMap_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_treeMap_1649_ = lean_ctor_get(v_x_1648_, 0);
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1649_, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(v_x_1652_);
lean_dec_ref(v_x_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1655_, lean_object* v_00_u03b2_1656_){
_start:
{
lean_object* v___f_1657_; 
v___f_1657_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0));
return v___f_1657_;
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
