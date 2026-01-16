// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Zipper
// Imports: public import Std.Data.Iterators.Lemmas.Producers.Slice public import Init.Data.Slice public import Std.Data.DTreeMap.Internal.Lemmas
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0;
static lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0;
static lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0;
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0;
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0;
static lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_6);
x_11 = lean_unbox(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; 
x_12 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(x_1, x_8, x_3);
lean_ctor_set(x_2, 3, x_12);
return x_2;
}
case 1:
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = lean_box(1);
lean_ctor_set(x_2, 3, x_13);
return x_2;
}
default: 
{
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = lean_ctor_get(x_2, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
lean_inc_ref(x_1);
lean_inc(x_16);
lean_inc(x_3);
x_20 = lean_apply_2(x_1, x_3, x_16);
x_21 = lean_unbox(x_20);
switch (x_21) {
case 0:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(x_1, x_18, x_3);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_19);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec_ref(x_1);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_19);
return x_25;
}
default: 
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_2 = x_19;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_6);
x_11 = lean_unbox(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; 
x_12 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(x_1, x_8, x_3);
lean_ctor_set(x_2, 3, x_12);
return x_2;
}
case 1:
{
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
default: 
{
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc_ref(x_1);
lean_inc(x_15);
lean_inc(x_3);
x_19 = lean_apply_2(x_1, x_3, x_15);
x_20 = lean_unbox(x_19);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(x_1, x_17, x_3);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_18);
return x_22;
}
case 1:
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_18;
}
default: 
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_2 = x_18;
goto _start;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLT___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__3_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_pruneLE_match__1_splitter(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__List_filter_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_ctorIdx___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_ctorIdx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DTreeMap_Internal_Zipper_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_done_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_cons_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Zipper_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(x_1, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(x_8, x_5);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Std_DTreeMap_Internal_Zipper_toList___redArg(x_6);
x_12 = l_List_appendTR___redArg(x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Zipper_toList___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_toList___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_toList(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Std_DTreeMap_Internal_Zipper_toList_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(x_3);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
x_8 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(x_4);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_2);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_5);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_4);
x_2 = x_7;
x_4 = x_11;
goto _start;
}
case 1:
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_4);
return x_13;
}
default: 
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_8;
goto _start;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_5);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_4);
x_2 = x_7;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_2 = x_8;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_prependMapGT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_6(x_4, x_5, x_6, x_7, x_8, x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_1(x_3, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_prependMap_match__1_splitter___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_4(x_3, x_6, x_7, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_toList_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Impl_toListModel_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_5, x_6);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_step(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_step___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_step___redArg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorZipperIdSigma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_Zipper_FinitenessRelation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Zipper_iter___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_iter(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_iterOfTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Zipper_iterOfTree(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Zipper_instToIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Zipper_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_IterM_toArray__eq__match__step_match__1_splitter___redArg(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec_ref(x_3);
lean_inc(x_6);
lean_inc(x_8);
x_12 = lean_apply_2(x_1, x_8, x_6);
x_13 = lean_unbox(x_12);
if (x_13 == 2)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_2);
lean_dec(x_6);
x_14 = lean_box(2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_10, x_11);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 3);
lean_inc(x_22);
lean_dec_ref(x_3);
lean_inc(x_18);
lean_inc(x_19);
x_23 = lean_apply_2(x_1, x_19, x_18);
x_24 = lean_unbox(x_23);
if (x_24 == 2)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_25 = lean_box(2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_21, x_22);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxcIterator_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_RxcIterator_step___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxcIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_apply_5(x_3, x_8, x_9, x_10, x_11, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_step_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxcIterator_FinitenessRelation(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec_ref(x_3);
lean_inc(x_6);
lean_inc(x_8);
x_12 = lean_apply_2(x_1, x_8, x_6);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_10, x_11);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_2);
lean_dec(x_6);
x_17 = lean_box(2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 3);
lean_inc(x_22);
lean_dec_ref(x_3);
lean_inc(x_18);
lean_inc(x_19);
x_23 = lean_apply_2(x_1, x_19, x_18);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_21, x_22);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_29 = lean_box(2);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RxoIterator_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_RxoIterator_step___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instIteratorRxoIteratorIdSigma___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_apply_5(x_3, x_8, x_9, x_10, x_11, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_step_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_DTreeMap_Internal_Zipper_0__Std_DTreeMap_Internal_RxoIterator_instFinitenessRelation(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRicSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRicSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RicSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RicSlice_instToIterator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_RicSlice_instToIterator(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRioSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRioSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RioSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RioSlice_instToIterator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_RioSlice_instToIterator(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rccIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_3, x_4, x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRccSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRccSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RccSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RccSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rcoIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_3, x_4, x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRcoSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RcoSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RcoSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rooIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_3, x_4, x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRooSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRooSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RooSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RooSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rocIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_3, x_4, x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRocSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRocSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RocSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_6, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_4, x_9, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RocSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_rciIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRciSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRciSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RciSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGE___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RciSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_roiIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_instSliceableImplRoiSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RoiSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DTreeMap_Internal_Zipper_prependMapGT___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RoiSlice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_riiIterator___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_riiIterator___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_riiIterator___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_riiIterator(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instSliceableImplRiiSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_DTreeMap_Internal_riiIterator___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_RiiSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = l_Std_DTreeMap_Internal_Zipper_prependMap___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0;
return x_3;
}
}
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Slice(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
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
l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0 = _init_l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instIteratorZipperIdSigma___closed__0);
l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Zipper_instToIterator___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRicSlice___closed__0);
l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_RicSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRicSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_RicSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRicSlice___closed__0);
l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_RicSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRioSlice___closed__0);
l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_RioSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRioSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_RioSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRioSlice___closed__0);
l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_RioSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRccSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRccSlice___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRccSlice___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRcoSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRcoSlice___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRcoSlice___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRooSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRooSlice___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRooSlice___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRocSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRocSlice___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRocSlice___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRciSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRciSlice___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRciSlice___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRoiSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRoiSlice___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRoiSlice___closed__0);
l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0 = _init_l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_instSliceableImplRiiSlice___closed__0);
l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_RiiSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_instSliceableImplUnitRiiSlice___closed__0);
l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Unit_RiiSlice_instToIterator___closed__0);
l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0 = _init_l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_instSliceableImplRiiSlice___closed__0);
l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0 = _init_l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0();
lean_mark_persistent(l_Std_DTreeMap_Internal_Const_RiiSlice_instToIterator___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
