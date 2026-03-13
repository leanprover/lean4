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
lean_object* v___x_72_; 
v___x_72_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(v_t_69_, v_h__1_70_, v_h__2_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t v_x_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_, lean_object* v_h__3_86_){
_start:
{
uint8_t v_x_30__boxed_87_; lean_object* v_res_88_; 
v_x_30__boxed_87_ = lean_unbox(v_x_83_);
v_res_88_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_30__boxed_87_, v_h__1_84_, v_h__2_85_, v_h__3_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object* v_motive_89_, uint8_t v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_, lean_object* v_h__3_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(v_x_90_, v_h__1_91_, v_h__2_92_, v_h__3_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object* v_motive_95_, lean_object* v_x_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_, lean_object* v_h__3_99_){
_start:
{
uint8_t v_x_45__boxed_100_; lean_object* v_res_101_; 
v_x_45__boxed_100_ = lean_unbox(v_x_96_);
v_res_101_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(v_motive_95_, v_x_45__boxed_100_, v_h__1_97_, v_h__2_98_, v_h__3_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t v_x_102_, lean_object* v_h__1_103_, lean_object* v_h__2_104_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
uint8_t v_x_22__boxed_112_; lean_object* v_res_113_; 
v_x_22__boxed_112_ = lean_unbox(v_x_109_);
v_res_113_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_22__boxed_112_, v_h__1_110_, v_h__2_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object* v_motive_114_, uint8_t v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(v_x_115_, v_h__1_116_, v_h__2_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
uint8_t v_x_33__boxed_123_; lean_object* v_res_124_; 
v_x_33__boxed_123_ = lean_unbox(v_x_120_);
v_res_124_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(v_motive_119_, v_x_33__boxed_123_, v_h__1_121_, v_h__2_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_unsigned_to_nat(0u);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(1u);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_128_);
lean_dec(v_x_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_x_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(v_x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_DTreeMap_Internal_Zipper_ctorIdx(v_00_u03b1_134_, v_00_u03b2_135_, v_x_136_);
lean_dec(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* v_t_138_, lean_object* v_k_139_){
_start:
{
if (lean_obj_tag(v_t_138_) == 0)
{
return v_k_139_;
}
else
{
lean_object* v_k_140_; lean_object* v_v_141_; lean_object* v_tree_142_; lean_object* v_next_143_; lean_object* v___x_144_; 
v_k_140_ = lean_ctor_get(v_t_138_, 0);
lean_inc(v_k_140_);
v_v_141_ = lean_ctor_get(v_t_138_, 1);
lean_inc(v_v_141_);
v_tree_142_ = lean_ctor_get(v_t_138_, 2);
lean_inc(v_tree_142_);
v_next_143_ = lean_ctor_get(v_t_138_, 3);
lean_inc(v_next_143_);
lean_dec_ref(v_t_138_);
v___x_144_ = lean_apply_4(v_k_139_, v_k_140_, v_v_141_, v_tree_142_, v_next_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* v_00_u03b1_145_, lean_object* v_00_u03b2_146_, lean_object* v_motive_147_, lean_object* v_ctorIdx_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_k_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_149_, v_k_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_motive_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DTreeMap_Internal_Zipper_ctorElim(v_00_u03b1_153_, v_00_u03b2_154_, v_motive_155_, v_ctorIdx_156_, v_t_157_, v_h_158_, v_k_159_);
lean_dec(v_ctorIdx_156_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* v_t_161_, lean_object* v_done_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_161_, v_done_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* v_00_u03b1_164_, lean_object* v_00_u03b2_165_, lean_object* v_motive_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_done_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_167_, v_done_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* v_t_171_, lean_object* v_cons_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_171_, v_cons_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_cons_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(v_t_177_, v_cons_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* v_init_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v_k_183_; lean_object* v_v_184_; lean_object* v_l_185_; lean_object* v_r_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_k_183_ = lean_ctor_get(v_x_182_, 1);
v_v_184_ = lean_ctor_get(v_x_182_, 2);
v_l_185_ = lean_ctor_get(v_x_182_, 3);
v_r_186_ = lean_ctor_get(v_x_182_, 4);
v___x_187_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_181_, v_r_186_);
lean_inc(v_v_184_);
lean_inc(v_k_183_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_k_183_);
lean_ctor_set(v___x_188_, 1, v_v_184_);
v___x_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
v_init_181_ = v___x_189_;
v_x_182_ = v_l_185_;
goto _start;
}
else
{
return v_init_181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* v_init_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_191_, v_x_192_);
lean_dec(v_x_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v_k_196_; lean_object* v_v_197_; lean_object* v_tree_198_; lean_object* v_next_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_k_196_ = lean_ctor_get(v_x_194_, 0);
v_v_197_ = lean_ctor_get(v_x_194_, 1);
v_tree_198_ = lean_ctor_get(v_x_194_, 2);
v_next_199_ = lean_ctor_get(v_x_194_, 3);
lean_inc(v_v_197_);
lean_inc(v_k_196_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_k_196_);
lean_ctor_set(v___x_200_, 1, v_v_197_);
v___x_201_ = lean_box(0);
v___x_202_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v___x_201_, v_tree_198_);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_200_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_next_199_);
v___x_205_ = l_List_appendTR___redArg(v___x_203_, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Std_DTreeMap_Internal_Zipper_toList___redArg(v_x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Std_DTreeMap_Internal_Zipper_toList(v_00_u03b1_212_, v_00_u03b2_213_, v_x_214_);
lean_dec(v_x_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_init_218_, lean_object* v_x_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(v_init_218_, v_x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_init_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(v_00_u03b1_221_, v_00_u03b2_222_, v_init_223_, v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(0u);
return v___x_227_;
}
else
{
lean_object* v_tree_228_; lean_object* v_next_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_tree_228_ = lean_ctor_get(v_x_226_, 2);
v_next_229_ = lean_ctor_get(v_x_226_, 3);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_tree_228_);
v___x_232_ = lean_nat_add(v___x_230_, v___x_231_);
lean_dec(v___x_231_);
v___x_233_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_next_229_);
v___x_234_ = lean_nat_add(v___x_232_, v___x_233_);
lean_dec(v___x_233_);
lean_dec(v___x_232_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_235_);
lean_dec(v_x_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* v_00_u03b1_237_, lean_object* v_00_u03b2_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(v_00_u03b1_241_, v_00_u03b2_242_, v_x_243_);
lean_dec(v_x_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v_k_247_; lean_object* v_v_248_; lean_object* v_l_249_; lean_object* v_r_250_; lean_object* v___x_251_; 
v_k_247_ = lean_ctor_get(v_x_245_, 1);
v_v_248_ = lean_ctor_get(v_x_245_, 2);
v_l_249_ = lean_ctor_get(v_x_245_, 3);
v_r_250_ = lean_ctor_get(v_x_245_, 4);
lean_inc(v_r_250_);
lean_inc(v_v_248_);
lean_inc(v_k_247_);
v___x_251_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_251_, 0, v_k_247_);
lean_ctor_set(v___x_251_, 1, v_v_248_);
lean_ctor_set(v___x_251_, 2, v_r_250_);
lean_ctor_set(v___x_251_, 3, v_x_246_);
v_x_245_ = v_l_249_;
v_x_246_ = v___x_251_;
goto _start;
}
else
{
return v_x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_253_, v_x_254_);
lean_dec(v_x_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_x_258_, v_x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_DTreeMap_Internal_Zipper_prependMap(v_00_u03b1_261_, v_00_u03b2_262_, v_x_263_, v_x_264_);
lean_dec(v_x_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* v_inst_266_, lean_object* v_t_267_, lean_object* v_lowerBound_268_, lean_object* v_it_269_){
_start:
{
if (lean_obj_tag(v_t_267_) == 0)
{
lean_object* v_k_270_; lean_object* v_v_271_; lean_object* v_l_272_; lean_object* v_r_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_k_270_ = lean_ctor_get(v_t_267_, 1);
lean_inc(v_k_270_);
v_v_271_ = lean_ctor_get(v_t_267_, 2);
lean_inc(v_v_271_);
v_l_272_ = lean_ctor_get(v_t_267_, 3);
lean_inc(v_l_272_);
v_r_273_ = lean_ctor_get(v_t_267_, 4);
lean_inc(v_r_273_);
lean_dec_ref(v_t_267_);
lean_inc_ref(v_inst_266_);
lean_inc(v_k_270_);
lean_inc(v_lowerBound_268_);
v___x_274_ = lean_apply_2(v_inst_266_, v_lowerBound_268_, v_k_270_);
v___x_275_ = lean_unbox(v___x_274_);
switch(v___x_275_)
{
case 0:
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_276_, 0, v_k_270_);
lean_ctor_set(v___x_276_, 1, v_v_271_);
lean_ctor_set(v___x_276_, 2, v_r_273_);
lean_ctor_set(v___x_276_, 3, v_it_269_);
v_t_267_ = v_l_272_;
v_it_269_ = v___x_276_;
goto _start;
}
case 1:
{
lean_object* v___x_278_; 
lean_dec(v_l_272_);
lean_dec(v_lowerBound_268_);
lean_dec_ref(v_inst_266_);
v___x_278_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_278_, 0, v_k_270_);
lean_ctor_set(v___x_278_, 1, v_v_271_);
lean_ctor_set(v___x_278_, 2, v_r_273_);
lean_ctor_set(v___x_278_, 3, v_it_269_);
return v___x_278_;
}
default: 
{
lean_dec(v_l_272_);
lean_dec(v_v_271_);
lean_dec(v_k_270_);
v_t_267_ = v_r_273_;
goto _start;
}
}
}
else
{
lean_dec(v_lowerBound_268_);
lean_dec_ref(v_inst_266_);
return v_it_269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_t_283_, lean_object* v_lowerBound_284_, lean_object* v_it_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_282_, v_t_283_, v_lowerBound_284_, v_it_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* v_inst_287_, lean_object* v_t_288_, lean_object* v_lowerBound_289_, lean_object* v_it_290_){
_start:
{
if (lean_obj_tag(v_t_288_) == 0)
{
lean_object* v_k_291_; lean_object* v_v_292_; lean_object* v_l_293_; lean_object* v_r_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_k_291_ = lean_ctor_get(v_t_288_, 1);
lean_inc(v_k_291_);
v_v_292_ = lean_ctor_get(v_t_288_, 2);
lean_inc(v_v_292_);
v_l_293_ = lean_ctor_get(v_t_288_, 3);
lean_inc(v_l_293_);
v_r_294_ = lean_ctor_get(v_t_288_, 4);
lean_inc(v_r_294_);
lean_dec_ref(v_t_288_);
lean_inc_ref(v_inst_287_);
lean_inc(v_k_291_);
lean_inc(v_lowerBound_289_);
v___x_295_ = lean_apply_2(v_inst_287_, v_lowerBound_289_, v_k_291_);
v___x_296_ = lean_unbox(v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_297_, 0, v_k_291_);
lean_ctor_set(v___x_297_, 1, v_v_292_);
lean_ctor_set(v___x_297_, 2, v_r_294_);
lean_ctor_set(v___x_297_, 3, v_it_290_);
v_t_288_ = v_l_293_;
v_it_290_ = v___x_297_;
goto _start;
}
else
{
lean_dec(v_l_293_);
lean_dec(v_v_292_);
lean_dec(v_k_291_);
v_t_288_ = v_r_294_;
goto _start;
}
}
else
{
lean_dec(v_lowerBound_289_);
lean_dec_ref(v_inst_287_);
return v_it_290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* v_00_u03b1_300_, lean_object* v_00_u03b2_301_, lean_object* v_inst_302_, lean_object* v_t_303_, lean_object* v_lowerBound_304_, lean_object* v_it_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_302_, v_t_303_, v_lowerBound_304_, v_it_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v_size_311_; lean_object* v_k_312_; lean_object* v_v_313_; lean_object* v_l_314_; lean_object* v_r_315_; lean_object* v___x_316_; 
lean_dec(v_h__1_309_);
v_size_311_ = lean_ctor_get(v_x_307_, 0);
lean_inc(v_size_311_);
v_k_312_ = lean_ctor_get(v_x_307_, 1);
lean_inc(v_k_312_);
v_v_313_ = lean_ctor_get(v_x_307_, 2);
lean_inc(v_v_313_);
v_l_314_ = lean_ctor_get(v_x_307_, 3);
lean_inc(v_l_314_);
v_r_315_ = lean_ctor_get(v_x_307_, 4);
lean_inc(v_r_315_);
lean_dec_ref(v_x_307_);
v___x_316_ = lean_apply_6(v_h__2_310_, v_size_311_, v_k_312_, v_v_313_, v_l_314_, v_r_315_, v_x_308_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
lean_dec(v_h__2_310_);
v___x_317_ = lean_apply_1(v_h__1_309_, v_x_308_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_motive_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(v_x_321_, v_x_322_, v_h__1_323_, v_h__2_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object* v_x_326_, lean_object* v_h__1_327_, lean_object* v_h__2_328_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_h__2_328_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_h__1_327_, v___x_329_);
return v___x_330_;
}
else
{
lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v_tree_333_; lean_object* v_next_334_; lean_object* v___x_335_; 
lean_dec(v_h__1_327_);
v_k_331_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_k_331_);
v_v_332_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_v_332_);
v_tree_333_ = lean_ctor_get(v_x_326_, 2);
lean_inc(v_tree_333_);
v_next_334_ = lean_ctor_get(v_x_326_, 3);
lean_inc(v_next_334_);
lean_dec_ref(v_x_326_);
v___x_335_ = lean_apply_4(v_h__2_328_, v_k_331_, v_v_332_, v_tree_333_, v_next_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object* v_00_u03b1_336_, lean_object* v_00_u03b2_337_, lean_object* v_motive_338_, lean_object* v_x_339_, lean_object* v_h__1_340_, lean_object* v_h__2_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(v_x_339_, v_h__1_340_, v_h__2_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object* v_x_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v_size_346_; lean_object* v_k_347_; lean_object* v_v_348_; lean_object* v_l_349_; lean_object* v_r_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_344_);
v_size_346_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_size_346_);
v_k_347_ = lean_ctor_get(v_x_343_, 1);
lean_inc(v_k_347_);
v_v_348_ = lean_ctor_get(v_x_343_, 2);
lean_inc(v_v_348_);
v_l_349_ = lean_ctor_get(v_x_343_, 3);
lean_inc(v_l_349_);
v_r_350_ = lean_ctor_get(v_x_343_, 4);
lean_inc(v_r_350_);
lean_dec_ref(v_x_343_);
v___x_351_ = lean_apply_5(v_h__2_345_, v_size_346_, v_k_347_, v_v_348_, v_l_349_, v_r_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_h__2_345_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_apply_1(v_h__1_344_, v___x_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_motive_356_, lean_object* v_x_357_, lean_object* v_h__1_358_, lean_object* v_h__2_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(v_x_357_, v_h__1_358_, v_h__2_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* v_x_361_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v___x_362_; 
v___x_362_ = lean_box(2);
return v___x_362_;
}
else
{
lean_object* v_k_363_; lean_object* v_v_364_; lean_object* v_tree_365_; lean_object* v_next_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_k_363_ = lean_ctor_get(v_x_361_, 0);
lean_inc(v_k_363_);
v_v_364_ = lean_ctor_get(v_x_361_, 1);
lean_inc(v_v_364_);
v_tree_365_ = lean_ctor_get(v_x_361_, 2);
lean_inc(v_tree_365_);
v_next_366_ = lean_ctor_get(v_x_361_, 3);
lean_inc(v_next_366_);
lean_dec_ref(v_x_361_);
v___x_367_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_365_, v_next_366_);
lean_dec(v_tree_365_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_k_363_);
lean_ctor_set(v___x_368_, 1, v_v_364_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_DTreeMap_Internal_Zipper_step___redArg(v_x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_){
_start:
{
lean_object* v___f_377_; 
v___f_377_ = ((lean_object*)(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0));
return v___f_377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* v_00_u03b1_378_, lean_object* v_00_u03b2_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* v_t_381_){
_start:
{
lean_inc(v_t_381_);
return v_t_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* v_t_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_DTreeMap_Internal_Zipper_iter___redArg(v_t_382_);
lean_dec(v_t_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_t_386_){
_start:
{
lean_inc(v_t_386_);
return v_t_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_t_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DTreeMap_Internal_Zipper_iter(v_00_u03b1_387_, v_00_u03b2_388_, v_t_389_);
lean_dec(v_t_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* v_t_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_box(0);
v___x_393_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_391_, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* v_t_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_394_);
lean_dec(v_t_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_t_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_t_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* v_00_u03b1_400_, lean_object* v_00_u03b2_401_, lean_object* v_t_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree(v_00_u03b1_400_, v_00_u03b2_401_, v_t_402_);
lean_dec(v_t_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(lean_object* v_x_404_){
_start:
{
lean_inc(v_x_404_);
return v_x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(lean_object* v_x_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(v_x_405_);
lean_dec(v_x_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_){
_start:
{
lean_object* v___f_410_; 
v___f_410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0));
return v___f_410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_, lean_object* v_h__3_414_){
_start:
{
switch(lean_obj_tag(v_x_411_))
{
case 0:
{
lean_object* v_it_415_; lean_object* v_out_416_; lean_object* v___x_417_; 
lean_dec(v_h__3_414_);
lean_dec(v_h__2_413_);
v_it_415_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_it_415_);
v_out_416_ = lean_ctor_get(v_x_411_, 1);
lean_inc(v_out_416_);
lean_dec_ref(v_x_411_);
v___x_417_ = lean_apply_2(v_h__1_412_, v_it_415_, v_out_416_);
return v___x_417_;
}
case 1:
{
lean_object* v_it_418_; lean_object* v___x_419_; 
lean_dec(v_h__3_414_);
lean_dec(v_h__1_412_);
v_it_418_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_it_418_);
lean_dec_ref(v_x_411_);
v___x_419_ = lean_apply_1(v_h__2_413_, v_it_418_);
return v___x_419_;
}
default: 
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_h__2_413_);
lean_dec(v_h__1_412_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_apply_1(v_h__3_414_, v___x_420_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_m_424_, lean_object* v_motive_425_, lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_, lean_object* v_h__3_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(v_x_426_, v_h__1_427_, v_h__2_428_, v_h__3_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* v_inst_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_iter_433_; 
v_iter_433_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_iter_433_);
if (lean_obj_tag(v_iter_433_) == 0)
{
lean_object* v___x_434_; 
lean_dec_ref(v_x_432_);
lean_dec_ref(v_inst_431_);
v___x_434_ = lean_box(2);
return v___x_434_;
}
else
{
lean_object* v_upper_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_452_; 
v_upper_435_ = lean_ctor_get(v_x_432_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v_x_432_, 0);
lean_dec(v_unused_453_);
v___x_437_ = v_x_432_;
v_isShared_438_ = v_isSharedCheck_452_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_upper_435_);
lean_dec(v_x_432_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_452_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_k_439_; lean_object* v_v_440_; lean_object* v_tree_441_; lean_object* v_next_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_k_439_ = lean_ctor_get(v_iter_433_, 0);
lean_inc(v_k_439_);
v_v_440_ = lean_ctor_get(v_iter_433_, 1);
lean_inc(v_v_440_);
v_tree_441_ = lean_ctor_get(v_iter_433_, 2);
lean_inc(v_tree_441_);
v_next_442_ = lean_ctor_get(v_iter_433_, 3);
lean_inc(v_next_442_);
lean_dec_ref(v_iter_433_);
lean_inc(v_upper_435_);
lean_inc(v_k_439_);
v___x_443_ = lean_apply_2(v_inst_431_, v_k_439_, v_upper_435_);
v___x_444_ = lean_unbox(v___x_443_);
if (v___x_444_ == 2)
{
lean_object* v___x_445_; 
lean_dec(v_next_442_);
lean_dec(v_tree_441_);
lean_dec(v_v_440_);
lean_dec(v_k_439_);
lean_del_object(v___x_437_);
lean_dec(v_upper_435_);
v___x_445_ = lean_box(2);
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_441_, v_next_442_);
lean_dec(v_tree_441_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_446_);
v___x_448_ = v___x_437_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_upper_435_);
v___x_448_ = v_reuseFailAlloc_451_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_k_439_);
lean_ctor_set(v___x_449_, 1, v_v_440_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
return v___x_450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_inst_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* v_inst_459_, lean_object* v_it_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(v_inst_459_, v_it_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* v_inst_462_){
_start:
{
lean_object* v___f_463_; 
v___f_463_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_463_, 0, v_inst_462_);
return v___f_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_inst_466_){
_start:
{
lean_object* v___f_467_; 
v___f_467_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_467_, 0, v_inst_466_);
return v___f_467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* v_x_468_, lean_object* v_h__1_469_, lean_object* v_h__2_470_){
_start:
{
lean_object* v_iter_471_; 
v_iter_471_ = lean_ctor_get(v_x_468_, 0);
if (lean_obj_tag(v_iter_471_) == 0)
{
lean_object* v_upper_472_; lean_object* v___x_473_; 
lean_dec(v_h__2_470_);
v_upper_472_ = lean_ctor_get(v_x_468_, 1);
lean_inc(v_upper_472_);
lean_dec_ref(v_x_468_);
v___x_473_ = lean_apply_1(v_h__1_469_, v_upper_472_);
return v___x_473_;
}
else
{
lean_object* v_upper_474_; lean_object* v_k_475_; lean_object* v_v_476_; lean_object* v_tree_477_; lean_object* v_next_478_; lean_object* v___x_479_; 
lean_inc_ref(v_iter_471_);
lean_dec(v_h__1_469_);
v_upper_474_ = lean_ctor_get(v_x_468_, 1);
lean_inc(v_upper_474_);
lean_dec_ref(v_x_468_);
v_k_475_ = lean_ctor_get(v_iter_471_, 0);
lean_inc(v_k_475_);
v_v_476_ = lean_ctor_get(v_iter_471_, 1);
lean_inc(v_v_476_);
v_tree_477_ = lean_ctor_get(v_iter_471_, 2);
lean_inc(v_tree_477_);
v_next_478_ = lean_ctor_get(v_iter_471_, 3);
lean_inc(v_next_478_);
lean_dec_ref(v_iter_471_);
v___x_479_ = lean_apply_5(v_h__2_470_, v_k_475_, v_v_476_, v_tree_477_, v_next_478_, v_upper_474_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_inst_482_, lean_object* v_motive_483_, lean_object* v_x_484_, lean_object* v_h__1_485_, lean_object* v_h__2_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(v_x_484_, v_h__1_485_, v_h__2_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_inst_490_, lean_object* v_motive_491_, lean_object* v_x_492_, lean_object* v_h__1_493_, lean_object* v_h__2_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(v_00_u03b1_488_, v_00_u03b2_489_, v_inst_490_, v_motive_491_, v_x_492_, v_h__1_493_, v_h__2_494_);
lean_dec_ref(v_inst_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* v_00_u03b1_496_, lean_object* v_00_u03b2_497_, lean_object* v_inst_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* v_00_u03b1_500_, lean_object* v_00_u03b2_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(v_00_u03b1_500_, v_00_u03b2_501_, v_inst_502_);
lean_dec_ref(v_inst_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* v_inst_504_, lean_object* v_x_505_){
_start:
{
lean_object* v_iter_506_; 
v_iter_506_ = lean_ctor_get(v_x_505_, 0);
lean_inc(v_iter_506_);
if (lean_obj_tag(v_iter_506_) == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v_x_505_);
lean_dec_ref(v_inst_504_);
v___x_507_ = lean_box(2);
return v___x_507_;
}
else
{
lean_object* v_upper_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_525_; 
v_upper_508_ = lean_ctor_get(v_x_505_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_x_505_, 0);
lean_dec(v_unused_526_);
v___x_510_ = v_x_505_;
v_isShared_511_ = v_isSharedCheck_525_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_upper_508_);
lean_dec(v_x_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_525_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_k_512_; lean_object* v_v_513_; lean_object* v_tree_514_; lean_object* v_next_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_k_512_ = lean_ctor_get(v_iter_506_, 0);
lean_inc(v_k_512_);
v_v_513_ = lean_ctor_get(v_iter_506_, 1);
lean_inc(v_v_513_);
v_tree_514_ = lean_ctor_get(v_iter_506_, 2);
lean_inc(v_tree_514_);
v_next_515_ = lean_ctor_get(v_iter_506_, 3);
lean_inc(v_next_515_);
lean_dec_ref(v_iter_506_);
lean_inc(v_upper_508_);
lean_inc(v_k_512_);
v___x_516_ = lean_apply_2(v_inst_504_, v_k_512_, v_upper_508_);
v___x_517_ = lean_unbox(v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_tree_514_, v_next_515_);
lean_dec(v_tree_514_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_518_);
v___x_520_ = v___x_510_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_upper_508_);
v___x_520_ = v_reuseFailAlloc_523_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v_k_512_);
lean_ctor_set(v___x_521_, 1, v_v_513_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
}
else
{
lean_object* v___x_524_; 
lean_dec(v_next_515_);
lean_dec(v_tree_514_);
lean_dec(v_v_513_);
lean_dec(v_k_512_);
lean_del_object(v___x_510_);
lean_dec(v_upper_508_);
v___x_524_ = lean_box(2);
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_inst_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* v_inst_532_, lean_object* v_it_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(v_inst_532_, v_it_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* v_inst_535_){
_start:
{
lean_object* v___f_536_; 
v___f_536_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_536_, 0, v_inst_535_);
return v___f_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* v_00_u03b1_537_, lean_object* v_00_u03b2_538_, lean_object* v_inst_539_){
_start:
{
lean_object* v___f_540_; 
v___f_540_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(v___f_540_, 0, v_inst_539_);
return v___f_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* v_x_541_, lean_object* v_h__1_542_, lean_object* v_h__2_543_){
_start:
{
lean_object* v_iter_544_; 
v_iter_544_ = lean_ctor_get(v_x_541_, 0);
if (lean_obj_tag(v_iter_544_) == 0)
{
lean_object* v_upper_545_; lean_object* v___x_546_; 
lean_dec(v_h__2_543_);
v_upper_545_ = lean_ctor_get(v_x_541_, 1);
lean_inc(v_upper_545_);
lean_dec_ref(v_x_541_);
v___x_546_ = lean_apply_1(v_h__1_542_, v_upper_545_);
return v___x_546_;
}
else
{
lean_object* v_upper_547_; lean_object* v_k_548_; lean_object* v_v_549_; lean_object* v_tree_550_; lean_object* v_next_551_; lean_object* v___x_552_; 
lean_inc_ref(v_iter_544_);
lean_dec(v_h__1_542_);
v_upper_547_ = lean_ctor_get(v_x_541_, 1);
lean_inc(v_upper_547_);
lean_dec_ref(v_x_541_);
v_k_548_ = lean_ctor_get(v_iter_544_, 0);
lean_inc(v_k_548_);
v_v_549_ = lean_ctor_get(v_iter_544_, 1);
lean_inc(v_v_549_);
v_tree_550_ = lean_ctor_get(v_iter_544_, 2);
lean_inc(v_tree_550_);
v_next_551_ = lean_ctor_get(v_iter_544_, 3);
lean_inc(v_next_551_);
lean_dec_ref(v_iter_544_);
v___x_552_ = lean_apply_5(v_h__2_543_, v_k_548_, v_v_549_, v_tree_550_, v_next_551_, v_upper_547_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* v_00_u03b1_553_, lean_object* v_00_u03b2_554_, lean_object* v_inst_555_, lean_object* v_motive_556_, lean_object* v_x_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(v_x_557_, v_h__1_558_, v_h__2_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_inst_563_, lean_object* v_motive_564_, lean_object* v_x_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(v_00_u03b1_561_, v_00_u03b2_562_, v_inst_563_, v_motive_564_, v_x_565_, v_h__1_566_, v_h__2_567_);
lean_dec_ref(v_inst_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* v_00_u03b1_569_, lean_object* v_00_u03b2_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_box(0);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_inst_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(v_00_u03b1_573_, v_00_u03b2_574_, v_inst_575_);
lean_dec_ref(v_inst_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(lean_object* v_carrier_577_, lean_object* v_range_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_carrier_577_);
lean_ctor_set(v___x_579_, 1, v_range_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_inst_583_){
_start:
{
lean_object* v___f_584_; 
v___f_584_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0));
return v___f_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_585_, lean_object* v_00_u03b2_586_, lean_object* v_inst_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(v_00_u03b1_585_, v_00_u03b2_586_, v_inst_587_);
lean_dec_ref(v_inst_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(lean_object* v_x_589_){
_start:
{
lean_object* v_treeMap_590_; lean_object* v_range_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_600_; 
v_treeMap_590_ = lean_ctor_get(v_x_589_, 0);
v_range_591_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_600_ == 0)
{
v___x_593_ = v_x_589_;
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_range_591_);
lean_inc(v_treeMap_590_);
lean_dec(v_x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_600_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_595_ = lean_box(0);
v___x_596_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_590_, v___x_595_);
lean_dec(v_treeMap_590_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_range_591_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_inst_604_){
_start:
{
lean_object* v___f_605_; 
v___f_605_ = ((lean_object*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0));
return v___f_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_606_, lean_object* v_00_u03b2_607_, lean_object* v_inst_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_DTreeMap_Internal_RicSlice_instToIterator(v_00_u03b1_606_, v_00_u03b2_607_, v_inst_608_);
lean_dec_ref(v_inst_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(lean_object* v_carrier_610_, lean_object* v_range_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_carrier_610_);
lean_ctor_set(v___x_612_, 1, v_range_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* v_00_u03b1_614_, lean_object* v_inst_615_){
_start:
{
lean_object* v___f_616_; 
v___f_616_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0));
return v___f_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* v_00_u03b1_617_, lean_object* v_inst_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(v_00_u03b1_617_, v_inst_618_);
lean_dec_ref(v_inst_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(lean_object* v_x_620_){
_start:
{
lean_object* v_treeMap_621_; lean_object* v_range_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_631_; 
v_treeMap_621_ = lean_ctor_get(v_x_620_, 0);
v_range_622_ = lean_ctor_get(v_x_620_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_631_ == 0)
{
v___x_624_ = v_x_620_;
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_range_622_);
lean_inc(v_treeMap_621_);
lean_dec(v_x_620_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_631_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_626_ = lean_box(0);
v___x_627_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_621_, v___x_626_);
lean_dec(v_treeMap_621_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_range_622_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* v_00_u03b1_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v___f_635_; 
v___f_635_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0));
return v___f_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_636_, lean_object* v_inst_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(v_00_u03b1_636_, v_inst_637_);
lean_dec_ref(v_inst_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(lean_object* v_carrier_639_, lean_object* v_range_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_carrier_639_);
lean_ctor_set(v___x_641_, 1, v_range_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_inst_645_){
_start:
{
lean_object* v___f_646_; 
v___f_646_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0));
return v___f_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_inst_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(v_00_u03b1_647_, v_00_u03b2_648_, v_inst_649_);
lean_dec_ref(v_inst_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(lean_object* v_x_651_){
_start:
{
lean_object* v_treeMap_652_; lean_object* v_range_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_662_; 
v_treeMap_652_ = lean_ctor_get(v_x_651_, 0);
v_range_653_ = lean_ctor_get(v_x_651_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_662_ == 0)
{
v___x_655_ = v_x_651_;
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_range_653_);
lean_inc(v_treeMap_652_);
lean_dec(v_x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_657_ = lean_box(0);
v___x_658_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_652_, v___x_657_);
lean_dec(v_treeMap_652_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_range_653_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* v_00_u03b1_664_, lean_object* v_00_u03b2_665_, lean_object* v_inst_666_){
_start:
{
lean_object* v___f_667_; 
v___f_667_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0));
return v___f_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* v_00_u03b1_668_, lean_object* v_00_u03b2_669_, lean_object* v_inst_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(v_00_u03b1_668_, v_00_u03b2_669_, v_inst_670_);
lean_dec_ref(v_inst_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(lean_object* v_carrier_672_, lean_object* v_range_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v_carrier_672_);
lean_ctor_set(v___x_674_, 1, v_range_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_inst_678_){
_start:
{
lean_object* v___f_679_; 
v___f_679_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0));
return v___f_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(v_00_u03b1_680_, v_00_u03b2_681_, v_inst_682_);
lean_dec_ref(v_inst_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(lean_object* v_x_684_){
_start:
{
lean_object* v_treeMap_685_; lean_object* v_range_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_treeMap_685_ = lean_ctor_get(v_x_684_, 0);
v_range_686_ = lean_ctor_get(v_x_684_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v_x_684_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_range_686_);
lean_inc(v_treeMap_685_);
lean_dec(v_x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_685_, v___x_690_);
lean_dec(v_treeMap_685_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_range_686_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_inst_699_){
_start:
{
lean_object* v___f_700_; 
v___f_700_ = ((lean_object*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0));
return v___f_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_inst_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DTreeMap_Internal_RioSlice_instToIterator(v_00_u03b1_701_, v_00_u03b2_702_, v_inst_703_);
lean_dec_ref(v_inst_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(lean_object* v_carrier_705_, lean_object* v_range_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_carrier_705_);
lean_ctor_set(v___x_707_, 1, v_range_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* v_00_u03b1_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v___f_711_; 
v___f_711_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0));
return v___f_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* v_00_u03b1_712_, lean_object* v_inst_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(v_00_u03b1_712_, v_inst_713_);
lean_dec_ref(v_inst_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(lean_object* v_x_715_){
_start:
{
lean_object* v_treeMap_716_; lean_object* v_range_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_treeMap_716_ = lean_ctor_get(v_x_715_, 0);
v_range_717_ = lean_ctor_get(v_x_715_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_726_ == 0)
{
v___x_719_ = v_x_715_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_range_717_);
lean_inc(v_treeMap_716_);
lean_dec(v_x_715_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = lean_box(0);
v___x_722_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_716_, v___x_721_);
lean_dec(v_treeMap_716_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_range_717_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* v_00_u03b1_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v___f_730_; 
v___f_730_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0));
return v___f_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_731_, lean_object* v_inst_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(v_00_u03b1_731_, v_inst_732_);
lean_dec_ref(v_inst_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(lean_object* v_carrier_734_, lean_object* v_range_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_carrier_734_);
lean_ctor_set(v___x_736_, 1, v_range_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_inst_740_){
_start:
{
lean_object* v___f_741_; 
v___f_741_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0));
return v___f_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_inst_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(v_00_u03b1_742_, v_00_u03b2_743_, v_inst_744_);
lean_dec_ref(v_inst_744_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(lean_object* v_x_746_){
_start:
{
lean_object* v_treeMap_747_; lean_object* v_range_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_757_; 
v_treeMap_747_ = lean_ctor_get(v_x_746_, 0);
v_range_748_ = lean_ctor_get(v_x_746_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_757_ == 0)
{
v___x_750_ = v_x_746_;
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_range_748_);
lean_inc(v_treeMap_747_);
lean_dec(v_x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_752_ = lean_box(0);
v___x_753_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_747_, v___x_752_);
lean_dec(v_treeMap_747_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_753_);
v___x_755_ = v___x_750_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_range_748_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_inst_761_){
_start:
{
lean_object* v___f_762_; 
v___f_762_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0));
return v___f_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_inst_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(v_00_u03b1_763_, v_00_u03b2_764_, v_inst_765_);
lean_dec_ref(v_inst_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* v_inst_767_, lean_object* v_t_768_, lean_object* v_lowerBound_769_, lean_object* v_upperBound_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_box(0);
v___x_772_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_767_, v_t_768_, v_lowerBound_769_, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_upperBound_770_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_inst_776_, lean_object* v_t_777_, lean_object* v_lowerBound_778_, lean_object* v_upperBound_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_776_, v_t_777_, v_lowerBound_778_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_upperBound_779_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(lean_object* v_carrier_783_, lean_object* v_range_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_carrier_783_);
lean_ctor_set(v___x_785_, 1, v_range_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v___f_790_; 
v___f_790_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0));
return v___f_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(v_00_u03b1_791_, v_00_u03b2_792_, v_inst_793_);
lean_dec_ref(v_inst_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_range_797_; lean_object* v_treeMap_798_; lean_object* v_lower_799_; lean_object* v_upper_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_809_; 
v_range_797_ = lean_ctor_get(v_x_796_, 1);
lean_inc_ref(v_range_797_);
v_treeMap_798_ = lean_ctor_get(v_x_796_, 0);
lean_inc(v_treeMap_798_);
lean_dec_ref(v_x_796_);
v_lower_799_ = lean_ctor_get(v_range_797_, 0);
v_upper_800_ = lean_ctor_get(v_range_797_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_range_797_);
if (v_isSharedCheck_809_ == 0)
{
v___x_802_ = v_range_797_;
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_upper_800_);
lean_inc(v_lower_799_);
lean_dec(v_range_797_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_804_ = lean_box(0);
v___x_805_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_795_, v_treeMap_798_, v_lower_799_, v___x_804_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_805_);
v___x_807_ = v___x_802_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_upper_800_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* v_inst_810_){
_start:
{
lean_object* v___f_811_; 
v___f_811_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_811_, 0, v_inst_810_);
return v___f_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v___f_815_; 
v___f_815_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_815_, 0, v_inst_814_);
return v___f_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(lean_object* v_carrier_816_, lean_object* v_range_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_carrier_816_);
lean_ctor_set(v___x_818_, 1, v_range_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* v_00_u03b1_820_, lean_object* v_inst_821_){
_start:
{
lean_object* v___f_822_; 
v___f_822_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0));
return v___f_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* v_00_u03b1_823_, lean_object* v_inst_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(v_00_u03b1_823_, v_inst_824_);
lean_dec_ref(v_inst_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_range_828_; lean_object* v_treeMap_829_; lean_object* v_lower_830_; lean_object* v_upper_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_840_; 
v_range_828_ = lean_ctor_get(v_x_827_, 1);
lean_inc_ref(v_range_828_);
v_treeMap_829_ = lean_ctor_get(v_x_827_, 0);
lean_inc(v_treeMap_829_);
lean_dec_ref(v_x_827_);
v_lower_830_ = lean_ctor_get(v_range_828_, 0);
v_upper_831_ = lean_ctor_get(v_range_828_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_range_828_);
if (v_isSharedCheck_840_ == 0)
{
v___x_833_ = v_range_828_;
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_upper_831_);
lean_inc(v_lower_830_);
lean_dec(v_range_828_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_835_ = lean_box(0);
v___x_836_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_826_, v_treeMap_829_, v_lower_830_, v___x_835_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_upper_831_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* v_inst_841_){
_start:
{
lean_object* v___f_842_; 
v___f_842_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_842_, 0, v_inst_841_);
return v___f_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* v_00_u03b1_843_, lean_object* v_inst_844_){
_start:
{
lean_object* v___f_845_; 
v___f_845_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_845_, 0, v_inst_844_);
return v___f_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(lean_object* v_carrier_846_, lean_object* v_range_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_carrier_846_);
lean_ctor_set(v___x_848_, 1, v_range_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___f_853_; 
v___f_853_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0));
return v___f_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_inst_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(v_00_u03b1_854_, v_00_u03b2_855_, v_inst_856_);
lean_dec_ref(v_inst_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* v_inst_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_range_860_; lean_object* v_treeMap_861_; lean_object* v_lower_862_; lean_object* v_upper_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_872_; 
v_range_860_ = lean_ctor_get(v_x_859_, 1);
lean_inc_ref(v_range_860_);
v_treeMap_861_ = lean_ctor_get(v_x_859_, 0);
lean_inc(v_treeMap_861_);
lean_dec_ref(v_x_859_);
v_lower_862_ = lean_ctor_get(v_range_860_, 0);
v_upper_863_ = lean_ctor_get(v_range_860_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_range_860_);
if (v_isSharedCheck_872_ == 0)
{
v___x_865_ = v_range_860_;
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_upper_863_);
lean_inc(v_lower_862_);
lean_dec(v_range_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_867_ = lean_box(0);
v___x_868_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_858_, v_treeMap_861_, v_lower_862_, v___x_867_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_868_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_upper_863_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* v_inst_873_){
_start:
{
lean_object* v___f_874_; 
v___f_874_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_874_, 0, v_inst_873_);
return v___f_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_inst_877_){
_start:
{
lean_object* v___f_878_; 
v___f_878_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_878_, 0, v_inst_877_);
return v___f_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* v_inst_879_, lean_object* v_t_880_, lean_object* v_lowerBound_881_, lean_object* v_upperBound_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
v___x_884_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_879_, v_t_880_, v_lowerBound_881_, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_upperBound_882_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_inst_888_, lean_object* v_t_889_, lean_object* v_lowerBound_890_, lean_object* v_upperBound_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_888_, v_t_889_, v_lowerBound_890_, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_upperBound_891_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(lean_object* v_carrier_895_, lean_object* v_range_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_carrier_895_);
lean_ctor_set(v___x_897_, 1, v_range_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* v_00_u03b1_899_, lean_object* v_00_u03b2_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v___f_902_; 
v___f_902_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0));
return v___f_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_inst_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(v_00_u03b1_903_, v_00_u03b2_904_, v_inst_905_);
lean_dec_ref(v_inst_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_range_909_; lean_object* v_treeMap_910_; lean_object* v_lower_911_; lean_object* v_upper_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
v_range_909_ = lean_ctor_get(v_x_908_, 1);
lean_inc_ref(v_range_909_);
v_treeMap_910_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_treeMap_910_);
lean_dec_ref(v_x_908_);
v_lower_911_ = lean_ctor_get(v_range_909_, 0);
v_upper_912_ = lean_ctor_get(v_range_909_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_range_909_);
if (v_isSharedCheck_921_ == 0)
{
v___x_914_ = v_range_909_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_upper_912_);
lean_inc(v_lower_911_);
lean_dec(v_range_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = lean_box(0);
v___x_917_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_907_, v_treeMap_910_, v_lower_911_, v___x_916_);
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
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_upper_912_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* v_inst_922_){
_start:
{
lean_object* v___f_923_; 
v___f_923_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_923_, 0, v_inst_922_);
return v___f_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v___f_927_; 
v___f_927_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_927_, 0, v_inst_926_);
return v___f_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(lean_object* v_carrier_928_, lean_object* v_range_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_carrier_928_);
lean_ctor_set(v___x_930_, 1, v_range_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* v_00_u03b1_932_, lean_object* v_inst_933_){
_start:
{
lean_object* v___f_934_; 
v___f_934_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0));
return v___f_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* v_00_u03b1_935_, lean_object* v_inst_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(v_00_u03b1_935_, v_inst_936_);
lean_dec_ref(v_inst_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_938_, lean_object* v_x_939_){
_start:
{
lean_object* v_range_940_; lean_object* v_treeMap_941_; lean_object* v_lower_942_; lean_object* v_upper_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_952_; 
v_range_940_ = lean_ctor_get(v_x_939_, 1);
lean_inc_ref(v_range_940_);
v_treeMap_941_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_treeMap_941_);
lean_dec_ref(v_x_939_);
v_lower_942_ = lean_ctor_get(v_range_940_, 0);
v_upper_943_ = lean_ctor_get(v_range_940_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_range_940_);
if (v_isSharedCheck_952_ == 0)
{
v___x_945_ = v_range_940_;
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_upper_943_);
lean_inc(v_lower_942_);
lean_dec(v_range_940_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_952_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_947_ = lean_box(0);
v___x_948_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_938_, v_treeMap_941_, v_lower_942_, v___x_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_948_);
v___x_950_ = v___x_945_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_upper_943_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* v_inst_953_){
_start:
{
lean_object* v___f_954_; 
v___f_954_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_954_, 0, v_inst_953_);
return v___f_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_){
_start:
{
lean_object* v___f_957_; 
v___f_957_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_957_, 0, v_inst_956_);
return v___f_957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(lean_object* v_carrier_958_, lean_object* v_range_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v_carrier_958_);
lean_ctor_set(v___x_960_, 1, v_range_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* v_00_u03b1_962_, lean_object* v_00_u03b2_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v___f_965_; 
v___f_965_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0));
return v___f_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* v_00_u03b1_966_, lean_object* v_00_u03b2_967_, lean_object* v_inst_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(v_00_u03b1_966_, v_00_u03b2_967_, v_inst_968_);
lean_dec_ref(v_inst_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* v_inst_970_, lean_object* v_x_971_){
_start:
{
lean_object* v_range_972_; lean_object* v_treeMap_973_; lean_object* v_lower_974_; lean_object* v_upper_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_984_; 
v_range_972_ = lean_ctor_get(v_x_971_, 1);
lean_inc_ref(v_range_972_);
v_treeMap_973_ = lean_ctor_get(v_x_971_, 0);
lean_inc(v_treeMap_973_);
lean_dec_ref(v_x_971_);
v_lower_974_ = lean_ctor_get(v_range_972_, 0);
v_upper_975_ = lean_ctor_get(v_range_972_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v_range_972_);
if (v_isSharedCheck_984_ == 0)
{
v___x_977_ = v_range_972_;
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_upper_975_);
lean_inc(v_lower_974_);
lean_dec(v_range_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = lean_box(0);
v___x_980_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_970_, v_treeMap_973_, v_lower_974_, v___x_979_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_upper_975_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* v_inst_985_){
_start:
{
lean_object* v___f_986_; 
v___f_986_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_986_, 0, v_inst_985_);
return v___f_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v___f_990_; 
v___f_990_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_990_, 0, v_inst_989_);
return v___f_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* v_inst_991_, lean_object* v_t_992_, lean_object* v_lowerBound_993_, lean_object* v_upperBound_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
v___x_996_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_991_, v_t_992_, v_lowerBound_993_, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_upperBound_994_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_inst_1000_, lean_object* v_t_1001_, lean_object* v_lowerBound_1002_, lean_object* v_upperBound_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1000_, v_t_1001_, v_lowerBound_1002_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v_upperBound_1003_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(lean_object* v_carrier_1007_, lean_object* v_range_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_carrier_1007_);
lean_ctor_set(v___x_1009_, 1, v_range_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_){
_start:
{
lean_object* v___f_1014_; 
v___f_1014_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0));
return v___f_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_inst_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(v_00_u03b1_1015_, v_00_u03b2_1016_, v_inst_1017_);
lean_dec_ref(v_inst_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v_range_1021_; lean_object* v_treeMap_1022_; lean_object* v_lower_1023_; lean_object* v_upper_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1033_; 
v_range_1021_ = lean_ctor_get(v_x_1020_, 1);
lean_inc_ref(v_range_1021_);
v_treeMap_1022_ = lean_ctor_get(v_x_1020_, 0);
lean_inc(v_treeMap_1022_);
lean_dec_ref(v_x_1020_);
v_lower_1023_ = lean_ctor_get(v_range_1021_, 0);
v_upper_1024_ = lean_ctor_get(v_range_1021_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_range_1021_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1026_ = v_range_1021_;
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_upper_1024_);
lean_inc(v_lower_1023_);
lean_dec(v_range_1021_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1033_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1019_, v_treeMap_1022_, v_lower_1023_, v___x_1028_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_upper_1024_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* v_inst_1034_){
_start:
{
lean_object* v___f_1035_; 
v___f_1035_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1035_, 0, v_inst_1034_);
return v___f_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_inst_1038_){
_start:
{
lean_object* v___f_1039_; 
v___f_1039_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1039_, 0, v_inst_1038_);
return v___f_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(lean_object* v_carrier_1040_, lean_object* v_range_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_carrier_1040_);
lean_ctor_set(v___x_1042_, 1, v_range_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* v_00_u03b1_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v___f_1046_; 
v___f_1046_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0));
return v___f_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_inst_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(v_00_u03b1_1047_, v_inst_1048_);
lean_dec_ref(v_inst_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1050_, lean_object* v_x_1051_){
_start:
{
lean_object* v_range_1052_; lean_object* v_treeMap_1053_; lean_object* v_lower_1054_; lean_object* v_upper_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1064_; 
v_range_1052_ = lean_ctor_get(v_x_1051_, 1);
lean_inc_ref(v_range_1052_);
v_treeMap_1053_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_treeMap_1053_);
lean_dec_ref(v_x_1051_);
v_lower_1054_ = lean_ctor_get(v_range_1052_, 0);
v_upper_1055_ = lean_ctor_get(v_range_1052_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_range_1052_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1057_ = v_range_1052_;
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_upper_1055_);
lean_inc(v_lower_1054_);
lean_dec(v_range_1052_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1064_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1050_, v_treeMap_1053_, v_lower_1054_, v___x_1059_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_upper_1055_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* v_inst_1065_){
_start:
{
lean_object* v___f_1066_; 
v___f_1066_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1066_, 0, v_inst_1065_);
return v___f_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* v_00_u03b1_1067_, lean_object* v_inst_1068_){
_start:
{
lean_object* v___f_1069_; 
v___f_1069_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1069_, 0, v_inst_1068_);
return v___f_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(lean_object* v_carrier_1070_, lean_object* v_range_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_carrier_1070_);
lean_ctor_set(v___x_1072_, 1, v_range_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_inst_1076_){
_start:
{
lean_object* v___f_1077_; 
v___f_1077_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0));
return v___f_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(v_00_u03b1_1078_, v_00_u03b2_1079_, v_inst_1080_);
lean_dec_ref(v_inst_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v_range_1084_; lean_object* v_treeMap_1085_; lean_object* v_lower_1086_; lean_object* v_upper_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1096_; 
v_range_1084_ = lean_ctor_get(v_x_1083_, 1);
lean_inc_ref(v_range_1084_);
v_treeMap_1085_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_treeMap_1085_);
lean_dec_ref(v_x_1083_);
v_lower_1086_ = lean_ctor_get(v_range_1084_, 0);
v_upper_1087_ = lean_ctor_get(v_range_1084_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_range_1084_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1089_ = v_range_1084_;
v_isShared_1090_ = v_isSharedCheck_1096_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_upper_1087_);
lean_inc(v_lower_1086_);
lean_dec(v_range_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1096_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1082_, v_treeMap_1085_, v_lower_1086_, v___x_1091_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_upper_1087_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* v_inst_1097_){
_start:
{
lean_object* v___f_1098_; 
v___f_1098_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1098_, 0, v_inst_1097_);
return v___f_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v___f_1102_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1102_, 0, v_inst_1101_);
return v___f_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* v_inst_1103_, lean_object* v_t_1104_, lean_object* v_lowerBound_1105_, lean_object* v_upperBound_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1103_, v_t_1104_, v_lowerBound_1105_, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_upperBound_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* v_00_u03b1_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_inst_1112_, lean_object* v_t_1113_, lean_object* v_lowerBound_1114_, lean_object* v_upperBound_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1112_, v_t_1113_, v_lowerBound_1114_, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_upperBound_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(lean_object* v_carrier_1119_, lean_object* v_range_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_carrier_1119_);
lean_ctor_set(v___x_1121_, 1, v_range_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_inst_1125_){
_start:
{
lean_object* v___f_1126_; 
v___f_1126_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0));
return v___f_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_inst_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(v_00_u03b1_1127_, v_00_u03b2_1128_, v_inst_1129_);
lean_dec_ref(v_inst_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1131_, lean_object* v_x_1132_){
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
v___x_1141_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1131_, v_treeMap_1134_, v_lower_1135_, v___x_1140_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* v_inst_1146_){
_start:
{
lean_object* v___f_1147_; 
v___f_1147_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1147_, 0, v_inst_1146_);
return v___f_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* v_00_u03b1_1148_, lean_object* v_00_u03b2_1149_, lean_object* v_inst_1150_){
_start:
{
lean_object* v___f_1151_; 
v___f_1151_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1151_, 0, v_inst_1150_);
return v___f_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(lean_object* v_carrier_1152_, lean_object* v_range_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_carrier_1152_);
lean_ctor_set(v___x_1154_, 1, v_range_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v___f_1158_; 
v___f_1158_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0));
return v___f_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_inst_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(v_00_u03b1_1159_, v_inst_1160_);
lean_dec_ref(v_inst_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1162_, lean_object* v_x_1163_){
_start:
{
lean_object* v_range_1164_; lean_object* v_treeMap_1165_; lean_object* v_lower_1166_; lean_object* v_upper_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
v_range_1164_ = lean_ctor_get(v_x_1163_, 1);
lean_inc_ref(v_range_1164_);
v_treeMap_1165_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_treeMap_1165_);
lean_dec_ref(v_x_1163_);
v_lower_1166_ = lean_ctor_get(v_range_1164_, 0);
v_upper_1167_ = lean_ctor_get(v_range_1164_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_range_1164_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v_range_1164_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_upper_1167_);
lean_inc(v_lower_1166_);
lean_dec(v_range_1164_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = lean_box(0);
v___x_1172_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1162_, v_treeMap_1165_, v_lower_1166_, v___x_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_upper_1167_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* v_inst_1177_){
_start:
{
lean_object* v___f_1178_; 
v___f_1178_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1178_, 0, v_inst_1177_);
return v___f_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* v_00_u03b1_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v___f_1181_; 
v___f_1181_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1181_, 0, v_inst_1180_);
return v___f_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(lean_object* v_carrier_1182_, lean_object* v_range_1183_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v_carrier_1182_);
lean_ctor_set(v___x_1184_, 1, v_range_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_inst_1188_){
_start:
{
lean_object* v___f_1189_; 
v___f_1189_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0));
return v___f_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(v_00_u03b1_1190_, v_00_u03b2_1191_, v_inst_1192_);
lean_dec_ref(v_inst_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1194_, lean_object* v_x_1195_){
_start:
{
lean_object* v_range_1196_; lean_object* v_treeMap_1197_; lean_object* v_lower_1198_; lean_object* v_upper_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
v_range_1196_ = lean_ctor_get(v_x_1195_, 1);
lean_inc_ref(v_range_1196_);
v_treeMap_1197_ = lean_ctor_get(v_x_1195_, 0);
lean_inc(v_treeMap_1197_);
lean_dec_ref(v_x_1195_);
v_lower_1198_ = lean_ctor_get(v_range_1196_, 0);
v_upper_1199_ = lean_ctor_get(v_range_1196_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_range_1196_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v_range_1196_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_upper_1199_);
lean_inc(v_lower_1198_);
lean_dec(v_range_1196_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1194_, v_treeMap_1197_, v_lower_1198_, v___x_1203_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_upper_1199_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* v_inst_1209_){
_start:
{
lean_object* v___f_1210_; 
v___f_1210_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1210_, 0, v_inst_1209_);
return v___f_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_inst_1213_){
_start:
{
lean_object* v___f_1214_; 
v___f_1214_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1214_, 0, v_inst_1213_);
return v___f_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* v_inst_1215_, lean_object* v_t_1216_, lean_object* v_lowerBound_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1215_, v_t_1216_, v_lowerBound_1217_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_, lean_object* v_t_1223_, lean_object* v_lowerBound_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1222_, v_t_1223_, v_lowerBound_1224_, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(lean_object* v_carrier_1227_, lean_object* v_range_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_carrier_1227_);
lean_ctor_set(v___x_1229_, 1, v_range_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* v_00_u03b1_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___f_1234_; 
v___f_1234_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0));
return v___f_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_inst_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(v_00_u03b1_1235_, v_00_u03b2_1236_, v_inst_1237_);
lean_dec_ref(v_inst_1237_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1239_, lean_object* v_x_1240_){
_start:
{
lean_object* v_treeMap_1241_; lean_object* v_range_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_treeMap_1241_ = lean_ctor_get(v_x_1240_, 0);
lean_inc(v_treeMap_1241_);
v_range_1242_ = lean_ctor_get(v_x_1240_, 1);
lean_inc(v_range_1242_);
lean_dec_ref(v_x_1240_);
v___x_1243_ = lean_box(0);
v___x_1244_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1239_, v_treeMap_1241_, v_range_1242_, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* v_inst_1245_){
_start:
{
lean_object* v___f_1246_; 
v___f_1246_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1246_, 0, v_inst_1245_);
return v___f_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_inst_1249_){
_start:
{
lean_object* v___f_1250_; 
v___f_1250_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1250_, 0, v_inst_1249_);
return v___f_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(lean_object* v_carrier_1251_, lean_object* v_range_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v_carrier_1251_);
lean_ctor_set(v___x_1253_, 1, v_range_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* v_00_u03b1_1255_, lean_object* v_inst_1256_){
_start:
{
lean_object* v___f_1257_; 
v___f_1257_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0));
return v___f_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(v_00_u03b1_1258_, v_inst_1259_);
lean_dec_ref(v_inst_1259_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v_treeMap_1263_; lean_object* v_range_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_treeMap_1263_ = lean_ctor_get(v_x_1262_, 0);
lean_inc(v_treeMap_1263_);
v_range_1264_ = lean_ctor_get(v_x_1262_, 1);
lean_inc(v_range_1264_);
lean_dec_ref(v_x_1262_);
v___x_1265_ = lean_box(0);
v___x_1266_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1261_, v_treeMap_1263_, v_range_1264_, v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* v_inst_1267_){
_start:
{
lean_object* v___f_1268_; 
v___f_1268_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1268_, 0, v_inst_1267_);
return v___f_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* v_00_u03b1_1269_, lean_object* v_inst_1270_){
_start:
{
lean_object* v___f_1271_; 
v___f_1271_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1271_, 0, v_inst_1270_);
return v___f_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(lean_object* v_carrier_1272_, lean_object* v_range_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_carrier_1272_);
lean_ctor_set(v___x_1274_, 1, v_range_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_inst_1278_){
_start:
{
lean_object* v___f_1279_; 
v___f_1279_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0));
return v___f_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(v_00_u03b1_1280_, v_00_u03b2_1281_, v_inst_1282_);
lean_dec_ref(v_inst_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v_treeMap_1286_; lean_object* v_range_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_treeMap_1286_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_treeMap_1286_);
v_range_1287_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_range_1287_);
lean_dec_ref(v_x_1285_);
v___x_1288_ = lean_box(0);
v___x_1289_ = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(v_inst_1284_, v_treeMap_1286_, v_range_1287_, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* v_inst_1290_){
_start:
{
lean_object* v___f_1291_; 
v___f_1291_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1291_, 0, v_inst_1290_);
return v___f_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* v_00_u03b1_1292_, lean_object* v_00_u03b2_1293_, lean_object* v_inst_1294_){
_start:
{
lean_object* v___f_1295_; 
v___f_1295_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1295_, 0, v_inst_1294_);
return v___f_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* v_inst_1296_, lean_object* v_t_1297_, lean_object* v_lowerBound_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_box(0);
v___x_1300_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1296_, v_t_1297_, v_lowerBound_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* v_00_u03b1_1301_, lean_object* v_00_u03b2_1302_, lean_object* v_inst_1303_, lean_object* v_t_1304_, lean_object* v_lowerBound_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1303_, v_t_1304_, v_lowerBound_1305_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(lean_object* v_carrier_1308_, lean_object* v_range_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_carrier_1308_);
lean_ctor_set(v___x_1310_, 1, v_range_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_inst_1314_){
_start:
{
lean_object* v___f_1315_; 
v___f_1315_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0));
return v___f_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_00_u03b2_1317_, lean_object* v_inst_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(v_00_u03b1_1316_, v_00_u03b2_1317_, v_inst_1318_);
lean_dec_ref(v_inst_1318_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1320_, lean_object* v_x_1321_){
_start:
{
lean_object* v_treeMap_1322_; lean_object* v_range_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_treeMap_1322_ = lean_ctor_get(v_x_1321_, 0);
lean_inc(v_treeMap_1322_);
v_range_1323_ = lean_ctor_get(v_x_1321_, 1);
lean_inc(v_range_1323_);
lean_dec_ref(v_x_1321_);
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1320_, v_treeMap_1322_, v_range_1323_, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* v_inst_1326_){
_start:
{
lean_object* v___f_1327_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1327_, 0, v_inst_1326_);
return v___f_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_inst_1330_){
_start:
{
lean_object* v___f_1331_; 
v___f_1331_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1331_, 0, v_inst_1330_);
return v___f_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(lean_object* v_carrier_1332_, lean_object* v_range_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_carrier_1332_);
lean_ctor_set(v___x_1334_, 1, v_range_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* v_00_u03b1_1336_, lean_object* v_inst_1337_){
_start:
{
lean_object* v___f_1338_; 
v___f_1338_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0));
return v___f_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_inst_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(v_00_u03b1_1339_, v_inst_1340_);
lean_dec_ref(v_inst_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v_treeMap_1344_; lean_object* v_range_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_treeMap_1344_ = lean_ctor_get(v_x_1343_, 0);
lean_inc(v_treeMap_1344_);
v_range_1345_ = lean_ctor_get(v_x_1343_, 1);
lean_inc(v_range_1345_);
lean_dec_ref(v_x_1343_);
v___x_1346_ = lean_box(0);
v___x_1347_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1342_, v_treeMap_1344_, v_range_1345_, v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* v_inst_1348_){
_start:
{
lean_object* v___f_1349_; 
v___f_1349_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1349_, 0, v_inst_1348_);
return v___f_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* v_00_u03b1_1350_, lean_object* v_inst_1351_){
_start:
{
lean_object* v___f_1352_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1352_, 0, v_inst_1351_);
return v___f_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(lean_object* v_carrier_1353_, lean_object* v_range_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_carrier_1353_);
lean_ctor_set(v___x_1355_, 1, v_range_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* v_00_u03b1_1357_, lean_object* v_00_u03b2_1358_, lean_object* v_inst_1359_){
_start:
{
lean_object* v___f_1360_; 
v___f_1360_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0));
return v___f_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* v_00_u03b1_1361_, lean_object* v_00_u03b2_1362_, lean_object* v_inst_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(v_00_u03b1_1361_, v_00_u03b2_1362_, v_inst_1363_);
lean_dec_ref(v_inst_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* v_inst_1365_, lean_object* v_x_1366_){
_start:
{
lean_object* v_treeMap_1367_; lean_object* v_range_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_treeMap_1367_ = lean_ctor_get(v_x_1366_, 0);
lean_inc(v_treeMap_1367_);
v_range_1368_ = lean_ctor_get(v_x_1366_, 1);
lean_inc(v_range_1368_);
lean_dec_ref(v_x_1366_);
v___x_1369_ = lean_box(0);
v___x_1370_ = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(v_inst_1365_, v_treeMap_1367_, v_range_1368_, v___x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* v_inst_1371_){
_start:
{
lean_object* v___f_1372_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1371_);
return v___f_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_inst_1375_){
_start:
{
lean_object* v___f_1376_; 
v___f_1376_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1376_, 0, v_inst_1375_);
return v___f_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* v_t_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_t_1377_, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* v_t_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1380_);
lean_dec(v_t_1380_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_t_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_t_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_t_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_DTreeMap_Internal_riiIterator(v_00_u03b1_1386_, v_00_u03b2_1387_, v_t_1388_);
lean_dec(v_t_1388_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(lean_object* v_carrier_1390_, lean_object* v_range_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v_carrier_1390_);
lean_ctor_set(v___x_1392_, 1, v_range_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1394_, lean_object* v_00_u03b2_1395_){
_start:
{
lean_object* v___f_1396_; 
v___f_1396_ = ((lean_object*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0));
return v___f_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(lean_object* v_x_1397_){
_start:
{
lean_object* v_treeMap_1398_; lean_object* v___x_1399_; 
v_treeMap_1398_ = lean_ctor_get(v_x_1397_, 0);
v___x_1399_ = l_Std_DTreeMap_Internal_riiIterator___redArg(v_treeMap_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(v_x_1400_);
lean_dec_ref(v_x_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* v_00_u03b1_1403_, lean_object* v_00_u03b2_1404_){
_start:
{
lean_object* v___f_1405_; 
v___f_1405_ = ((lean_object*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0));
return v___f_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(lean_object* v_carrier_1406_, lean_object* v_range_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_carrier_1406_);
lean_ctor_set(v___x_1408_, 1, v_range_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* v_00_u03b1_1410_){
_start:
{
lean_object* v___f_1411_; 
v___f_1411_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0));
return v___f_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(lean_object* v_x_1412_){
_start:
{
lean_object* v_treeMap_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_treeMap_1413_ = lean_ctor_get(v_x_1412_, 0);
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1413_, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(v_x_1416_);
lean_dec_ref(v_x_1416_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* v_00_u03b1_1419_){
_start:
{
lean_object* v___f_1420_; 
v___f_1420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0));
return v___f_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(lean_object* v_carrier_1421_, lean_object* v_range_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_carrier_1421_);
lean_ctor_set(v___x_1423_, 1, v_range_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_){
_start:
{
lean_object* v___f_1427_; 
v___f_1427_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0));
return v___f_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(lean_object* v_x_1428_){
_start:
{
lean_object* v_treeMap_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_treeMap_1429_ = lean_ctor_get(v_x_1428_, 0);
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(v_treeMap_1429_, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(lean_object* v_x_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(v_x_1432_);
lean_dec_ref(v_x_1432_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_){
_start:
{
lean_object* v___f_1437_; 
v___f_1437_ = ((lean_object*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0));
return v___f_1437_;
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
