// Lean compiler output
// Module: Lean.Data.RBMap
// Imports: Init.Data.Ord.Basic Init.Data.Nat.Linear
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
static lean_object* l_Lean_RBMap_find_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_toArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_find_x21___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__4;
LEAN_EXPORT uint8_t l_Lean_RBNode_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_toArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_max_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___redArg(lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rbmapOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_RBNode_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_min_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rbmapOf_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_min_x21___redArg___closed__3;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg___lam__0(lean_object*);
static lean_object* l_Lean_RBMap_min_x21___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object*);
static lean_object* l_Lean_RBMap_find_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_fromArray___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object*);
static lean_object* l_Lean_RBMap_max_x21___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_min_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
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
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_RBColor_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBColor_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBColor_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBColor_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_RBColor_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_RBColor_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_ctorIdx___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_ctorIdx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_1);
x_6 = l_Lean_RBNode_depth___redArg(x_1, x_4);
lean_inc_ref(x_1);
x_7 = l_Lean_RBNode_depth___redArg(x_1, x_5);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_depth___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_depth___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_depth(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object* x_1) {
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
x_1 = x_3;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_min___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_min___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_min(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object* x_1) {
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
x_1 = x_3;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_max___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_max___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_max(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___redArg(x_1, x_2, x_4);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_forM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__0), 4, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
lean_inc(x_8);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__1), 6, 5);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_13);
x_15 = l_Lean_RBNode_forM___redArg(x_1, x_2, x_9);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_forM___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___redArg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_3(x_1, x_6, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
lean_dec_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__0), 4, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
lean_inc(x_8);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__1), 6, 5);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_13);
x_15 = l_Lean_RBNode_foldM___redArg(x_1, x_2, x_3, x_9);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_RBNode_foldM___redArg(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_2, x_3, x_4, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_3(x_2, x_3, x_4, x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0), 5, 4);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_15);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_11);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1), 7, 6);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_13);
lean_closure_set(x_17, 3, x_14);
lean_closure_set(x_17, 4, x_10);
lean_closure_set(x_17, 5, x_16);
x_18 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_1, x_2, x_12, x_4);
x_19 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_18, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_1, x_4, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_5, x_8, x_6, x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_revFold___redArg(x_1, x_2, x_7);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_revFold___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_11 = lean_apply_2(x_1, x_5, x_6);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = lean_unbox(x_11);
x_8 = x_13;
goto block_10;
}
else
{
uint8_t x_14; 
lean_inc_ref(x_1);
x_14 = l_Lean_RBNode_all___redArg(x_1, x_4);
x_8 = x_14;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_8;
}
else
{
x_2 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_all___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_all___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBNode_all(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_11 = lean_apply_2(x_1, x_5, x_6);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_RBNode_any___redArg(x_1, x_4);
x_8 = x_13;
goto block_10;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = lean_unbox(x_11);
x_8 = x_14;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_8;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_any___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_any___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBNode_any(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 0;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_singleton___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isSingleton___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_isSingleton___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_isSingleton(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_1) == 0)
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
if (x_12 == 0)
{
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_32; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
lean_ctor_set(x_1, 0, x_16);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 3, x_16);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_12);
x_5 = x_37;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_16, 3);
lean_inc(x_42);
lean_dec_ref(x_16);
x_17 = x_13;
x_18 = x_14;
x_19 = x_15;
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = x_42;
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
goto block_31;
}
else
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_1);
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_13, 3);
lean_inc(x_47);
lean_dec_ref(x_13);
x_17 = x_44;
x_18 = x_45;
x_19 = x_46;
x_20 = x_47;
x_21 = x_14;
x_22 = x_15;
x_23 = x_16;
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
goto block_31;
}
else
{
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_13);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_48; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_1, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_1, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_1, 0);
lean_dec(x_52);
x_53 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_1);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_16, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_16, 3);
lean_inc(x_57);
lean_dec_ref(x_16);
x_17 = x_13;
x_18 = x_14;
x_19 = x_15;
x_20 = x_54;
x_21 = x_55;
x_22 = x_56;
x_23 = x_57;
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
goto block_31;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_53);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
x_61 = lean_ctor_get(x_13, 2);
x_62 = lean_ctor_get(x_13, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_53);
lean_ctor_set(x_1, 0, x_63);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_16, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_16, 3);
lean_inc(x_68);
lean_dec_ref(x_16);
x_17 = x_13;
x_18 = x_14;
x_19 = x_15;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_2;
x_25 = x_3;
x_26 = x_4;
goto block_31;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_13, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_13, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_13, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_73 = x_13;
} else {
 lean_dec_ref(x_13);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 4, 1);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_64);
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_14);
lean_ctor_set(x_75, 2, x_15);
lean_ctor_set(x_75, 3, x_16);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_12);
x_5 = x_75;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
}
}
}
}
}
else
{
lean_dec(x_13);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
block_31:
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 1;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_20);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_27);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_12);
return x_30;
}
}
block_11:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
if (lean_obj_tag(x_3) == 0)
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
if (x_14 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_34; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_3, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_3, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_3, 0);
lean_dec(x_38);
lean_ctor_set(x_3, 0, x_18);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_39; 
lean_dec(x_3);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 3, x_18);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_14);
x_7 = x_39;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
}
else
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_3);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 3);
lean_inc(x_44);
lean_dec_ref(x_18);
x_19 = x_15;
x_20 = x_16;
x_21 = x_17;
x_22 = x_41;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
goto block_33;
}
else
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
}
}
else
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_3);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_15, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_15, 3);
lean_inc(x_49);
lean_dec_ref(x_15);
x_19 = x_46;
x_20 = x_47;
x_21 = x_48;
x_22 = x_49;
x_23 = x_16;
x_24 = x_17;
x_25 = x_18;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
goto block_33;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_15);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
uint8_t x_50; 
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_50 = !lean_is_exclusive(x_3);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_3, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_3, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_3, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_3, 0);
lean_dec(x_54);
x_55 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_3);
x_56 = lean_ctor_get(x_18, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_18, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_18, 3);
lean_inc(x_59);
lean_dec_ref(x_18);
x_19 = x_15;
x_20 = x_16;
x_21 = x_17;
x_22 = x_56;
x_23 = x_57;
x_24 = x_58;
x_25 = x_59;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
goto block_33;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_55);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
x_63 = lean_ctor_get(x_15, 2);
x_64 = lean_ctor_get(x_15, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_55);
lean_ctor_set(x_3, 0, x_65);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_3);
x_66 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_18, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_18, 3);
lean_inc(x_70);
lean_dec_ref(x_18);
x_19 = x_15;
x_20 = x_16;
x_21 = x_17;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
goto block_33;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_15, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_15, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_15, 3);
lean_inc(x_74);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 x_75 = x_15;
} else {
 lean_dec_ref(x_15);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 4, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_66);
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_16);
lean_ctor_set(x_77, 2, x_17);
lean_ctor_set(x_77, 3, x_18);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_14);
x_7 = x_77;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
}
}
}
}
}
else
{
lean_dec(x_15);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
block_33:
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 1;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_29);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_14);
return x_32;
}
}
block_13:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
if (x_12 == 0)
{
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_32; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_4, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_4, 0);
lean_dec(x_36);
lean_ctor_set(x_4, 0, x_16);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_37; 
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 3, x_16);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_12);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_37;
goto block_11;
}
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_4);
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_16, 3);
lean_inc(x_42);
lean_dec_ref(x_16);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_13;
x_21 = x_14;
x_22 = x_15;
x_23 = x_39;
x_24 = x_40;
x_25 = x_41;
x_26 = x_42;
goto block_31;
}
else
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_4);
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_13, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_13, 3);
lean_inc(x_47);
lean_dec_ref(x_13);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_44;
x_21 = x_45;
x_22 = x_46;
x_23 = x_47;
x_24 = x_14;
x_25 = x_15;
x_26 = x_16;
goto block_31;
}
else
{
if (lean_obj_tag(x_16) == 0)
{
lean_dec_ref(x_13);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_48; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_4, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_4, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_4, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_4, 0);
lean_dec(x_52);
x_53 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_4);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_16, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_16, 3);
lean_inc(x_57);
lean_dec_ref(x_16);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_13;
x_21 = x_14;
x_22 = x_15;
x_23 = x_54;
x_24 = x_55;
x_25 = x_56;
x_26 = x_57;
goto block_31;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_13);
if (x_58 == 0)
{
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_53);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_13, 0);
x_60 = lean_ctor_get(x_13, 1);
x_61 = lean_ctor_get(x_13, 2);
x_62 = lean_ctor_get(x_13, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_13);
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_53);
lean_ctor_set(x_4, 0, x_63);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_4);
x_64 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_16, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_16, 3);
lean_inc(x_68);
lean_dec_ref(x_16);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_13;
x_21 = x_14;
x_22 = x_15;
x_23 = x_65;
x_24 = x_66;
x_25 = x_67;
x_26 = x_68;
goto block_31;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_13, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_13, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_13, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_13, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_73 = x_13;
} else {
 lean_dec_ref(x_13);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 4, 1);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_64);
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_14);
lean_ctor_set(x_75, 2, x_15);
lean_ctor_set(x_75, 3, x_16);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_12);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_75;
goto block_11;
}
}
}
}
}
}
else
{
lean_dec(x_13);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
block_31:
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 1;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_20);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_27);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_12);
return x_30;
}
}
block_11:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
if (lean_obj_tag(x_6) == 0)
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
if (x_14 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_34; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_6, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_6, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_6, 0);
lean_dec(x_38);
lean_ctor_set(x_6, 0, x_18);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_39; 
lean_dec(x_6);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 3, x_18);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_14);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_39;
goto block_13;
}
}
else
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_6);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 3);
lean_inc(x_44);
lean_dec_ref(x_18);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = x_41;
x_26 = x_42;
x_27 = x_43;
x_28 = x_44;
goto block_33;
}
else
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
}
}
else
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_6);
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_15, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_15, 3);
lean_inc(x_49);
lean_dec_ref(x_15);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_46;
x_23 = x_47;
x_24 = x_48;
x_25 = x_49;
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
goto block_33;
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_15);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
uint8_t x_50; 
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_6, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_6, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_6, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_6, 0);
lean_dec(x_54);
x_55 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_6);
x_56 = lean_ctor_get(x_18, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_18, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_18, 3);
lean_inc(x_59);
lean_dec_ref(x_18);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = x_56;
x_26 = x_57;
x_27 = x_58;
x_28 = x_59;
goto block_33;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_55);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
x_63 = lean_ctor_get(x_15, 2);
x_64 = lean_ctor_get(x_15, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_55);
lean_ctor_set(x_6, 0, x_65);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_6);
x_66 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_18, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_18, 3);
lean_inc(x_70);
lean_dec_ref(x_18);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = x_67;
x_26 = x_68;
x_27 = x_69;
x_28 = x_70;
goto block_33;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_15, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_15, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_15, 3);
lean_inc(x_74);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 x_75 = x_15;
} else {
 lean_dec_ref(x_15);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 4, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_66);
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_16);
lean_ctor_set(x_77, 2, x_17);
lean_ctor_set(x_77, 3, x_18);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_14);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_77;
goto block_13;
}
}
}
}
}
}
else
{
lean_dec(x_15);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
}
block_33:
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 1;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_29);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_14);
return x_32;
}
}
block_13:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_isRed___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_isRed(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_isBlack___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_isBlack(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; lean_object* x_6; 
lean_dec_ref(x_1);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___redArg(x_1, x_9, x_3, x_4);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
default: 
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_ins___redArg(x_1, x_12, x_3, x_4);
lean_ctor_set(x_2, 3, x_16);
return x_2;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc_ref(x_1);
lean_inc(x_18);
lean_inc(x_3);
x_21 = lean_apply_2(x_1, x_3, x_18);
x_22 = lean_unbox(x_21);
switch (x_22) {
case 0:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___redArg(x_1, x_17, x_3, x_4);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_7);
return x_24;
}
case 1:
{
lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_RBNode_ins___redArg(x_1, x_20, x_3, x_4);
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_7);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_32 = x_2;
} else {
 lean_dec_ref(x_2);
 x_32 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc(x_29);
lean_inc(x_3);
x_33 = lean_apply_2(x_1, x_3, x_29);
x_34 = lean_unbox(x_33);
switch (x_34) {
case 0:
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = l_Lean_RBNode_ins___redArg(x_1, x_28, x_3, x_4);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*4);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
if (x_36 == 0)
{
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_55; 
lean_dec(x_32);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_35, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_35, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_35, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_35, 0);
lean_dec(x_59);
lean_ctor_set(x_35, 0, x_40);
x_60 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_60, 0, x_35);
lean_ctor_set(x_60, 1, x_29);
lean_ctor_set(x_60, 2, x_30);
lean_ctor_set(x_60, 3, x_31);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_7);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_40);
lean_ctor_set(x_61, 1, x_38);
lean_ctor_set(x_61, 2, x_39);
lean_ctor_set(x_61, 3, x_40);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_36);
x_62 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_29);
lean_ctor_set(x_62, 2, x_30);
lean_ctor_set(x_62, 3, x_31);
lean_ctor_set_uint8(x_62, sizeof(void*)*4, x_7);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_35);
x_64 = lean_ctor_get(x_40, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_40, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_40, 3);
lean_inc(x_67);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_68; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_40, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_40, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_40, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_40, 0);
lean_dec(x_72);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_7);
return x_40;
}
else
{
lean_object* x_73; 
lean_dec(x_40);
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_35);
lean_ctor_set(x_73, 1, x_29);
lean_ctor_set(x_73, 2, x_30);
lean_ctor_set(x_73, 3, x_31);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_7);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_35);
x_75 = lean_ctor_get(x_37, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_37, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_37, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_37, 3);
lean_inc(x_78);
lean_dec_ref(x_37);
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_38;
x_46 = x_39;
x_47 = x_40;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_79; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_79 = !lean_is_exclusive(x_37);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_37, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_37, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_37, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_37, 0);
lean_dec(x_83);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_84; 
lean_dec(x_37);
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_35);
lean_ctor_set(x_84, 1, x_29);
lean_ctor_set(x_84, 2, x_30);
lean_ctor_set(x_84, 3, x_31);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_7);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_35);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_35, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_35, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_35, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_35, 0);
lean_dec(x_89);
x_90 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_35);
x_91 = lean_ctor_get(x_40, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_40, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_40, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_40, 3);
lean_inc(x_94);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_91;
x_45 = x_92;
x_46 = x_93;
x_47 = x_94;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_95; 
lean_dec(x_32);
x_95 = !lean_is_exclusive(x_37);
if (x_95 == 0)
{
lean_object* x_96; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_90);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_35);
lean_ctor_set(x_96, 1, x_29);
lean_ctor_set(x_96, 2, x_30);
lean_ctor_set(x_96, 3, x_31);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_37, 0);
x_98 = lean_ctor_get(x_37, 1);
x_99 = lean_ctor_get(x_37, 2);
x_100 = lean_ctor_get(x_37, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_37);
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_90);
lean_ctor_set(x_35, 0, x_101);
x_102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_102, 0, x_35);
lean_ctor_set(x_102, 1, x_29);
lean_ctor_set(x_102, 2, x_30);
lean_ctor_set(x_102, 3, x_31);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_7);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_35);
x_103 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_40, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_40, 3);
lean_inc(x_107);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_104;
x_45 = x_105;
x_46 = x_106;
x_47 = x_107;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_32);
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_37, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_37, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_37, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_112 = x_37;
} else {
 lean_dec_ref(x_37);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 4, 1);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_103);
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_38);
lean_ctor_set(x_114, 2, x_39);
lean_ctor_set(x_114, 3, x_40);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_36);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_29);
lean_ctor_set(x_115, 2, x_30);
lean_ctor_set(x_115, 3, x_31);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_7);
return x_115;
}
}
}
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_35);
lean_ctor_set(x_116, 1, x_29);
lean_ctor_set(x_116, 2, x_30);
lean_ctor_set(x_116, 3, x_31);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_7);
return x_116;
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(1, 4, 1);
} else {
 x_51 = x_32;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_7);
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_7);
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_36);
return x_53;
}
}
case 1:
{
lean_object* x_117; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_1);
if (lean_is_scalar(x_32)) {
 x_117 = lean_alloc_ctor(1, 4, 1);
} else {
 x_117 = x_32;
}
lean_ctor_set(x_117, 0, x_28);
lean_ctor_set(x_117, 1, x_3);
lean_ctor_set(x_117, 2, x_4);
lean_ctor_set(x_117, 3, x_31);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
default: 
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_118 = l_Lean_RBNode_ins___redArg(x_1, x_31, x_3, x_4);
x_119 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc(x_123);
if (x_119 == 0)
{
if (lean_obj_tag(x_120) == 0)
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_138; 
lean_dec(x_32);
x_138 = !lean_is_exclusive(x_118);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_118, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_118, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_118, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_118, 0);
lean_dec(x_142);
lean_ctor_set(x_118, 0, x_123);
x_143 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_143, 0, x_28);
lean_ctor_set(x_143, 1, x_29);
lean_ctor_set(x_143, 2, x_30);
lean_ctor_set(x_143, 3, x_118);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_7);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_118);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_121);
lean_ctor_set(x_144, 2, x_122);
lean_ctor_set(x_144, 3, x_123);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_119);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_28);
lean_ctor_set(x_145, 1, x_29);
lean_ctor_set(x_145, 2, x_30);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_7);
return x_145;
}
}
else
{
uint8_t x_146; 
x_146 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_118);
x_147 = lean_ctor_get(x_123, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_123, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_123, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_123, 3);
lean_inc(x_150);
lean_dec_ref(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_147;
x_131 = x_148;
x_132 = x_149;
x_133 = x_150;
goto block_137;
}
else
{
uint8_t x_151; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_32);
x_151 = !lean_is_exclusive(x_123);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_123, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_123, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_123, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_123, 0);
lean_dec(x_155);
lean_ctor_set(x_123, 3, x_118);
lean_ctor_set(x_123, 2, x_30);
lean_ctor_set(x_123, 1, x_29);
lean_ctor_set(x_123, 0, x_28);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_7);
return x_123;
}
else
{
lean_object* x_156; 
lean_dec(x_123);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_28);
lean_ctor_set(x_156, 1, x_29);
lean_ctor_set(x_156, 2, x_30);
lean_ctor_set(x_156, 3, x_118);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_7);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
x_157 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_118);
x_158 = lean_ctor_get(x_120, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_120, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_120, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_120, 3);
lean_inc(x_161);
lean_dec_ref(x_120);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_158;
x_128 = x_159;
x_129 = x_160;
x_130 = x_161;
x_131 = x_121;
x_132 = x_122;
x_133 = x_123;
goto block_137;
}
else
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_162; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_32);
x_162 = !lean_is_exclusive(x_120);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_120, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_120, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_120, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_120, 0);
lean_dec(x_166);
lean_ctor_set(x_120, 3, x_118);
lean_ctor_set(x_120, 2, x_30);
lean_ctor_set(x_120, 1, x_29);
lean_ctor_set(x_120, 0, x_28);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_167; 
lean_dec(x_120);
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_28);
lean_ctor_set(x_167, 1, x_29);
lean_ctor_set(x_167, 2, x_30);
lean_ctor_set(x_167, 3, x_118);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_7);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_118);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_118, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_118, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_118, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_118, 0);
lean_dec(x_172);
x_173 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_118);
x_174 = lean_ctor_get(x_123, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_123, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_123, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_123, 3);
lean_inc(x_177);
lean_dec_ref(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_174;
x_131 = x_175;
x_132 = x_176;
x_133 = x_177;
goto block_137;
}
else
{
uint8_t x_178; 
lean_dec(x_32);
x_178 = !lean_is_exclusive(x_120);
if (x_178 == 0)
{
lean_object* x_179; 
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_173);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_28);
lean_ctor_set(x_179, 1, x_29);
lean_ctor_set(x_179, 2, x_30);
lean_ctor_set(x_179, 3, x_118);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_7);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_120, 0);
x_181 = lean_ctor_get(x_120, 1);
x_182 = lean_ctor_get(x_120, 2);
x_183 = lean_ctor_get(x_120, 3);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_120);
x_184 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set(x_184, 1, x_181);
lean_ctor_set(x_184, 2, x_182);
lean_ctor_set(x_184, 3, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_173);
lean_ctor_set(x_118, 0, x_184);
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_28);
lean_ctor_set(x_185, 1, x_29);
lean_ctor_set(x_185, 2, x_30);
lean_ctor_set(x_185, 3, x_118);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_7);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_118);
x_186 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_123, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_123, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_123, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_123, 3);
lean_inc(x_190);
lean_dec_ref(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_187;
x_131 = x_188;
x_132 = x_189;
x_133 = x_190;
goto block_137;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_32);
x_191 = lean_ctor_get(x_120, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_120, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_120, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_120, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 x_195 = x_120;
} else {
 lean_dec_ref(x_120);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_186);
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_121);
lean_ctor_set(x_197, 2, x_122);
lean_ctor_set(x_197, 3, x_123);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_119);
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_28);
lean_ctor_set(x_198, 1, x_29);
lean_ctor_set(x_198, 2, x_30);
lean_ctor_set(x_198, 3, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_7);
return x_198;
}
}
}
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_32);
x_199 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_199, 0, x_28);
lean_ctor_set(x_199, 1, x_29);
lean_ctor_set(x_199, 2, x_30);
lean_ctor_set(x_199, 3, x_118);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_7);
return x_199;
}
block_137:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
if (lean_is_scalar(x_32)) {
 x_134 = lean_alloc_ctor(1, 4, 1);
} else {
 x_134 = x_32;
}
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_125);
lean_ctor_set(x_134, 2, x_126);
lean_ctor_set(x_134, 3, x_127);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_7);
x_135 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_7);
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_119);
return x_136;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ins___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___redArg(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___redArg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_insert___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_setRed___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
x_5 = x_4;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_166; 
x_166 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_4, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
x_5 = x_167;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_168; 
x_168 = lean_ctor_get_uint8(x_167, sizeof(void*)*4);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_4);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_4, 0);
lean_dec(x_170);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_168);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_4, 1);
x_172 = lean_ctor_get(x_4, 2);
x_173 = lean_ctor_get(x_4, 3);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_4);
x_174 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_171);
lean_ctor_set(x_174, 2, x_172);
lean_ctor_set(x_174, 3, x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_168);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_174;
goto block_11;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_4, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_4, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_4, 3);
lean_inc(x_177);
lean_dec_ref(x_4);
x_178 = lean_ctor_get(x_167, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_167, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_167, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_167, 3);
lean_inc(x_181);
lean_dec_ref(x_167);
x_44 = x_1;
x_45 = x_2;
x_46 = x_3;
x_47 = x_178;
x_48 = x_179;
x_49 = x_180;
x_50 = x_181;
x_51 = x_175;
x_52 = x_176;
x_53 = x_177;
goto block_108;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_4, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_4, 3);
lean_inc(x_185);
lean_dec_ref(x_4);
x_132 = x_1;
x_133 = x_2;
x_134 = x_3;
x_135 = x_182;
x_136 = x_183;
x_137 = x_184;
x_138 = x_185;
goto block_165;
}
}
}
else
{
uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_186 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_187 = lean_ctor_get(x_1, 0);
x_188 = lean_ctor_get(x_1, 1);
x_189 = lean_ctor_get(x_1, 2);
x_190 = lean_ctor_get(x_1, 3);
if (x_186 == 0)
{
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec_ref(x_1);
if (lean_obj_tag(x_4) == 0)
{
x_191 = x_187;
x_192 = x_188;
x_193 = x_189;
x_194 = x_190;
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
goto block_201;
}
else
{
uint8_t x_202; 
x_202 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_203) == 0)
{
x_191 = x_187;
x_192 = x_188;
x_193 = x_189;
x_194 = x_190;
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
goto block_201;
}
else
{
uint8_t x_204; 
x_204 = lean_ctor_get_uint8(x_203, sizeof(void*)*4);
if (x_204 == 0)
{
uint8_t x_205; 
lean_inc_ref(x_203);
x_205 = !lean_is_exclusive(x_4);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_4, 0);
lean_dec(x_206);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_204);
x_191 = x_187;
x_192 = x_188;
x_193 = x_189;
x_194 = x_190;
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
goto block_201;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_4, 1);
x_208 = lean_ctor_get(x_4, 2);
x_209 = lean_ctor_get(x_4, 3);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_4);
x_210 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_207);
lean_ctor_set(x_210, 2, x_208);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*4, x_204);
x_191 = x_187;
x_192 = x_188;
x_193 = x_189;
x_194 = x_190;
x_195 = x_2;
x_196 = x_3;
x_197 = x_210;
goto block_201;
}
}
else
{
x_191 = x_187;
x_192 = x_188;
x_193 = x_189;
x_194 = x_190;
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
goto block_201;
}
}
}
else
{
x_191 = x_187;
x_192 = x_188;
x_193 = x_189;
x_194 = x_190;
x_195 = x_2;
x_196 = x_3;
x_197 = x_4;
goto block_201;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_211; 
x_211 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_4, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
uint8_t x_213; 
x_213 = lean_ctor_get_uint8(x_212, sizeof(void*)*4);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_4);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_4, 0);
lean_dec(x_215);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_213);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_4, 1);
x_217 = lean_ctor_get(x_4, 2);
x_218 = lean_ctor_get(x_4, 3);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_4);
x_219 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set(x_219, 2, x_217);
lean_ctor_set(x_219, 3, x_218);
lean_ctor_set_uint8(x_219, sizeof(void*)*4, x_213);
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_219;
goto block_11;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec_ref(x_1);
x_220 = lean_ctor_get(x_4, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_4, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_4, 3);
lean_inc(x_222);
lean_dec_ref(x_4);
x_223 = !lean_is_exclusive(x_212);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_212, 0);
x_225 = lean_ctor_get(x_212, 1);
x_226 = lean_ctor_get(x_212, 2);
x_227 = lean_ctor_get(x_212, 3);
lean_ctor_set(x_212, 3, x_190);
lean_ctor_set(x_212, 2, x_189);
lean_ctor_set(x_212, 1, x_188);
lean_ctor_set(x_212, 0, x_187);
x_44 = x_212;
x_45 = x_2;
x_46 = x_3;
x_47 = x_224;
x_48 = x_225;
x_49 = x_226;
x_50 = x_227;
x_51 = x_220;
x_52 = x_221;
x_53 = x_222;
goto block_108;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_212, 0);
x_229 = lean_ctor_get(x_212, 1);
x_230 = lean_ctor_get(x_212, 2);
x_231 = lean_ctor_get(x_212, 3);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_212);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_187);
lean_ctor_set(x_232, 1, x_188);
lean_ctor_set(x_232, 2, x_189);
lean_ctor_set(x_232, 3, x_190);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_213);
x_44 = x_232;
x_45 = x_2;
x_46 = x_3;
x_47 = x_228;
x_48 = x_229;
x_49 = x_230;
x_50 = x_231;
x_51 = x_220;
x_52 = x_221;
x_53 = x_222;
goto block_108;
}
}
}
}
else
{
uint8_t x_233; 
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec_ref(x_1);
x_233 = !lean_is_exclusive(x_4);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_4, 0);
x_235 = lean_ctor_get(x_4, 1);
x_236 = lean_ctor_get(x_4, 2);
x_237 = lean_ctor_get(x_4, 3);
lean_ctor_set(x_4, 3, x_190);
lean_ctor_set(x_4, 2, x_189);
lean_ctor_set(x_4, 1, x_188);
lean_ctor_set(x_4, 0, x_187);
x_132 = x_4;
x_133 = x_2;
x_134 = x_3;
x_135 = x_234;
x_136 = x_235;
x_137 = x_236;
x_138 = x_237;
goto block_165;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_4, 0);
x_239 = lean_ctor_get(x_4, 1);
x_240 = lean_ctor_get(x_4, 2);
x_241 = lean_ctor_get(x_4, 3);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_4);
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_187);
lean_ctor_set(x_242, 1, x_188);
lean_ctor_set(x_242, 2, x_189);
lean_ctor_set(x_242, 3, x_190);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_211);
x_132 = x_242;
x_133 = x_2;
x_134 = x_3;
x_135 = x_238;
x_136 = x_239;
x_137 = x_240;
x_138 = x_241;
goto block_165;
}
}
}
}
block_201:
{
uint8_t x_198; lean_object* x_199; lean_object* x_200; 
x_198 = 1;
x_199 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_192);
lean_ctor_set(x_199, 2, x_193);
lean_ctor_set(x_199, 3, x_194);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_198);
x_200 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_195);
lean_ctor_set(x_200, 2, x_196);
lean_ctor_set(x_200, 3, x_197);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_186);
return x_200;
}
}
block_11:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
return x_10;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_12);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_13);
return x_22;
}
block_43:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_31);
lean_ctor_set(x_39, 3, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_24);
x_40 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_24);
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_25);
x_42 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_27);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_25);
return x_42;
}
block_108:
{
uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = 0;
x_55 = 1;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = l_Lean_RBNode_setRed___redArg(x_53);
if (lean_obj_tag(x_57) == 0)
{
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*4);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_57, 3);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
lean_ctor_set(x_57, 0, x_60);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_57, 1);
x_65 = lean_ctor_get(x_57, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_60);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_58);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_66;
goto block_23;
}
}
else
{
uint8_t x_67; 
x_67 = lean_ctor_get_uint8(x_60, sizeof(void*)*4);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_57, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 2);
lean_inc(x_69);
lean_dec_ref(x_57);
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_60, 3);
lean_inc(x_73);
lean_dec_ref(x_60);
x_24 = x_55;
x_25 = x_54;
x_26 = x_49;
x_27 = x_48;
x_28 = x_56;
x_29 = x_50;
x_30 = x_51;
x_31 = x_52;
x_32 = x_59;
x_33 = x_68;
x_34 = x_69;
x_35 = x_70;
x_36 = x_71;
x_37 = x_72;
x_38 = x_73;
goto block_43;
}
else
{
lean_dec_ref(x_60);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
}
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_59, sizeof(void*)*4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_57, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_57, 3);
lean_inc(x_77);
lean_dec_ref(x_57);
x_78 = lean_ctor_get(x_59, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_59, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_59, 3);
lean_inc(x_81);
lean_dec_ref(x_59);
x_24 = x_55;
x_25 = x_54;
x_26 = x_49;
x_27 = x_48;
x_28 = x_56;
x_29 = x_50;
x_30 = x_51;
x_31 = x_52;
x_32 = x_78;
x_33 = x_79;
x_34 = x_80;
x_35 = x_81;
x_36 = x_75;
x_37 = x_76;
x_38 = x_77;
goto block_43;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_57, 3);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_59);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
else
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_57, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_57, 2);
lean_inc(x_85);
lean_dec_ref(x_57);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 3);
lean_inc(x_89);
lean_dec_ref(x_82);
x_24 = x_55;
x_25 = x_54;
x_26 = x_49;
x_27 = x_48;
x_28 = x_56;
x_29 = x_50;
x_30 = x_51;
x_31 = x_52;
x_32 = x_59;
x_33 = x_84;
x_34 = x_85;
x_35 = x_86;
x_36 = x_87;
x_37 = x_88;
x_38 = x_89;
goto block_43;
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_57);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_57, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_57, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_59);
if (x_93 == 0)
{
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_83);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_59, 0);
x_95 = lean_ctor_get(x_59, 1);
x_96 = lean_ctor_get(x_59, 2);
x_97 = lean_ctor_get(x_59, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_59);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_83);
lean_ctor_set(x_57, 0, x_98);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_ctor_get(x_57, 1);
x_100 = lean_ctor_get(x_57, 2);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_57);
x_101 = lean_ctor_get(x_59, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_59, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_59, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_59, 3);
lean_inc(x_104);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 x_105 = x_59;
} else {
 lean_dec_ref(x_59);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 4, 1);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_102);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_83);
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_99);
lean_ctor_set(x_107, 2, x_100);
lean_ctor_set(x_107, 3, x_82);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_58);
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_107;
goto block_23;
}
}
}
}
}
}
else
{
x_12 = x_55;
x_13 = x_54;
x_14 = x_49;
x_15 = x_48;
x_16 = x_56;
x_17 = x_50;
x_18 = x_51;
x_19 = x_52;
x_20 = x_57;
goto block_23;
}
}
}
block_124:
{
uint8_t x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = 0;
x_120 = 1;
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set(x_121, 1, x_110);
lean_ctor_set(x_121, 2, x_111);
lean_ctor_set(x_121, 3, x_112);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_120);
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_115);
lean_ctor_set(x_122, 1, x_116);
lean_ctor_set(x_122, 2, x_117);
lean_ctor_set(x_122, 3, x_118);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_120);
x_123 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_113);
lean_ctor_set(x_123, 2, x_114);
lean_ctor_set(x_123, 3, x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_119);
return x_123;
}
block_131:
{
uint8_t x_129; lean_object* x_130; 
x_129 = 1;
x_130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_129);
return x_130;
}
block_165:
{
uint8_t x_139; lean_object* x_140; 
x_139 = 0;
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_136);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_139);
if (lean_obj_tag(x_135) == 0)
{
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_141; 
lean_dec_ref(x_140);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_137);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_139);
x_125 = x_132;
x_126 = x_133;
x_127 = x_134;
x_128 = x_141;
goto block_131;
}
else
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_138, sizeof(void*)*4);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_140);
x_143 = lean_ctor_get(x_138, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_138, 3);
lean_inc(x_146);
lean_dec_ref(x_138);
x_109 = x_132;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_143;
x_116 = x_144;
x_117 = x_145;
x_118 = x_146;
goto block_124;
}
else
{
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
x_125 = x_132;
x_126 = x_133;
x_127 = x_134;
x_128 = x_140;
goto block_131;
}
}
}
else
{
uint8_t x_147; 
x_147 = lean_ctor_get_uint8(x_135, sizeof(void*)*4);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_140);
x_148 = lean_ctor_get(x_135, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_135, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_135, 3);
lean_inc(x_151);
lean_dec_ref(x_135);
x_109 = x_132;
x_110 = x_133;
x_111 = x_134;
x_112 = x_148;
x_113 = x_149;
x_114 = x_150;
x_115 = x_151;
x_116 = x_136;
x_117 = x_137;
x_118 = x_138;
goto block_124;
}
else
{
if (lean_obj_tag(x_138) == 0)
{
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
x_125 = x_132;
x_126 = x_133;
x_127 = x_134;
x_128 = x_140;
goto block_131;
}
else
{
uint8_t x_152; 
lean_dec_ref(x_140);
x_152 = lean_ctor_get_uint8(x_138, sizeof(void*)*4);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_138, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_138, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_138, 3);
lean_inc(x_156);
lean_dec_ref(x_138);
x_109 = x_132;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_153;
x_116 = x_154;
x_117 = x_155;
x_118 = x_156;
goto block_124;
}
else
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_135);
if (x_157 == 0)
{
lean_object* x_158; 
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_152);
x_158 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_158, 0, x_135);
lean_ctor_set(x_158, 1, x_136);
lean_ctor_set(x_158, 2, x_137);
lean_ctor_set(x_158, 3, x_138);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_139);
x_125 = x_132;
x_126 = x_133;
x_127 = x_134;
x_128 = x_158;
goto block_131;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_135, 0);
x_160 = lean_ctor_get(x_135, 1);
x_161 = lean_ctor_get(x_135, 2);
x_162 = lean_ctor_get(x_135, 3);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_135);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_160);
lean_ctor_set(x_163, 2, x_161);
lean_ctor_set(x_163, 3, x_162);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_152);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_136);
lean_ctor_set(x_164, 2, x_137);
lean_ctor_set(x_164, 3, x_138);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_139);
x_125 = x_132;
x_126 = x_133;
x_127 = x_134;
x_128 = x_164;
goto block_131;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_balLeft___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_obj_tag(x_4) == 0)
{
goto block_204;
}
else
{
uint8_t x_205; 
x_205 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_4);
if (x_206 == 0)
{
uint8_t x_207; lean_object* x_208; 
x_207 = 1;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_207);
x_208 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_208, 0, x_1);
lean_ctor_set(x_208, 1, x_2);
lean_ctor_set(x_208, 2, x_3);
lean_ctor_set(x_208, 3, x_4);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_4, 0);
x_210 = lean_ctor_get(x_4, 1);
x_211 = lean_ctor_get(x_4, 2);
x_212 = lean_ctor_get(x_4, 3);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_4);
x_213 = 1;
x_214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_214, 0, x_209);
lean_ctor_set(x_214, 1, x_210);
lean_ctor_set(x_214, 2, x_211);
lean_ctor_set(x_214, 3, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*4, x_213);
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_2);
lean_ctor_set(x_215, 2, x_3);
lean_ctor_set(x_215, 3, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_205);
return x_215;
}
}
else
{
goto block_204;
}
}
block_7:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
block_23:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_11);
lean_ctor_set(x_20, 3, x_12);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_8);
x_21 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_8);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_19);
return x_22;
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_4);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_25);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_27);
return x_31;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_34);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_34);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_36);
x_24 = x_33;
x_25 = x_34;
x_26 = x_35;
x_27 = x_36;
x_28 = x_37;
x_29 = x_50;
goto block_32;
}
block_62:
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_53);
x_24 = x_52;
x_25 = x_53;
x_26 = x_54;
x_27 = x_55;
x_28 = x_56;
x_29 = x_61;
goto block_32;
}
block_204:
{
if (lean_obj_tag(x_1) == 0)
{
goto block_7;
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_64) == 0)
{
goto block_7;
}
else
{
uint8_t x_65; 
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*4);
if (x_65 == 0)
{
goto block_7;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc_ref(x_64);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
lean_dec_ref(x_1);
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 3);
lean_inc(x_72);
lean_dec_ref(x_64);
x_73 = l_Lean_RBNode_setRed___redArg(x_66);
if (lean_obj_tag(x_73) == 0)
{
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*4);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_73, 3);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_73, 3);
lean_dec(x_78);
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
lean_ctor_set(x_73, 0, x_76);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_73, 1);
x_81 = lean_ctor_get(x_73, 2);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_74);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_82;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
}
else
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_76, sizeof(void*)*4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 2);
lean_inc(x_85);
lean_dec_ref(x_73);
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_76, 3);
lean_inc(x_89);
lean_dec_ref(x_76);
x_33 = x_70;
x_34 = x_65;
x_35 = x_72;
x_36 = x_63;
x_37 = x_71;
x_38 = x_75;
x_39 = x_84;
x_40 = x_85;
x_41 = x_86;
x_42 = x_87;
x_43 = x_88;
x_44 = x_89;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
goto block_51;
}
else
{
lean_dec_ref(x_76);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_75, sizeof(void*)*4);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_73, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_73, 3);
lean_inc(x_93);
lean_dec_ref(x_73);
x_94 = lean_ctor_get(x_75, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_75, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_75, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_75, 3);
lean_inc(x_97);
lean_dec_ref(x_75);
x_33 = x_70;
x_34 = x_65;
x_35 = x_72;
x_36 = x_63;
x_37 = x_71;
x_38 = x_94;
x_39 = x_95;
x_40 = x_96;
x_41 = x_97;
x_42 = x_91;
x_43 = x_92;
x_44 = x_93;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
goto block_51;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_73, 3);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_75);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*4);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_73, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_73, 2);
lean_inc(x_101);
lean_dec_ref(x_73);
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 3);
lean_inc(x_105);
lean_dec_ref(x_98);
x_33 = x_70;
x_34 = x_65;
x_35 = x_72;
x_36 = x_63;
x_37 = x_71;
x_38 = x_75;
x_39 = x_100;
x_40 = x_101;
x_41 = x_102;
x_42 = x_103;
x_43 = x_104;
x_44 = x_105;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
goto block_51;
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_73);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_73, 3);
lean_dec(x_107);
x_108 = lean_ctor_get(x_73, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_75);
if (x_109 == 0)
{
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_99);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_75, 0);
x_111 = lean_ctor_get(x_75, 1);
x_112 = lean_ctor_get(x_75, 2);
x_113 = lean_ctor_get(x_75, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_75);
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_112);
lean_ctor_set(x_114, 3, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_99);
lean_ctor_set(x_73, 0, x_114);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_115 = lean_ctor_get(x_73, 1);
x_116 = lean_ctor_get(x_73, 2);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_73);
x_117 = lean_ctor_get(x_75, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_75, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_75, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_75, 3);
lean_inc(x_120);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_121 = x_75;
} else {
 lean_dec_ref(x_75);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 4, 1);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_99);
x_123 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
lean_ctor_set(x_123, 2, x_116);
lean_ctor_set(x_123, 3, x_98);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_74);
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_123;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
}
}
}
}
}
else
{
x_52 = x_70;
x_53 = x_65;
x_54 = x_72;
x_55 = x_63;
x_56 = x_71;
x_57 = x_73;
x_58 = x_67;
x_59 = x_68;
x_60 = x_69;
goto block_62;
}
}
}
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_1);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_1, 0);
x_126 = lean_ctor_get(x_1, 1);
x_127 = lean_ctor_get(x_1, 2);
x_128 = lean_ctor_get(x_1, 3);
x_129 = 0;
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_129);
if (lean_obj_tag(x_125) == 0)
{
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_1);
x_130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_129);
x_131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_2);
lean_ctor_set(x_131, 2, x_3);
lean_ctor_set(x_131, 3, x_4);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_63);
return x_131;
}
else
{
uint8_t x_132; 
x_132 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_1);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 3);
lean_inc(x_136);
lean_dec_ref(x_128);
x_8 = x_63;
x_9 = x_125;
x_10 = x_126;
x_11 = x_127;
x_12 = x_133;
x_13 = x_134;
x_14 = x_135;
x_15 = x_136;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
uint8_t x_137; 
lean_dec(x_127);
lean_dec(x_126);
x_137 = !lean_is_exclusive(x_128);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_128, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_128, 2);
lean_dec(x_139);
x_140 = lean_ctor_get(x_128, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_128, 0);
lean_dec(x_141);
lean_ctor_set(x_128, 3, x_4);
lean_ctor_set(x_128, 2, x_3);
lean_ctor_set(x_128, 1, x_2);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_63);
return x_128;
}
else
{
lean_object* x_142; 
lean_dec(x_128);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_2);
lean_ctor_set(x_142, 2, x_3);
lean_ctor_set(x_142, 3, x_4);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_63);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_125, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_1);
x_144 = lean_ctor_get(x_125, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_125, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_125, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_125, 3);
lean_inc(x_147);
lean_dec_ref(x_125);
x_8 = x_63;
x_9 = x_144;
x_10 = x_145;
x_11 = x_146;
x_12 = x_147;
x_13 = x_126;
x_14 = x_127;
x_15 = x_128;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_148; 
lean_dec(x_127);
lean_dec(x_126);
x_148 = !lean_is_exclusive(x_125);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_125, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_125, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_125, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_125, 0);
lean_dec(x_152);
lean_ctor_set(x_125, 3, x_4);
lean_ctor_set(x_125, 2, x_3);
lean_ctor_set(x_125, 1, x_2);
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_63);
return x_125;
}
else
{
lean_object* x_153; 
lean_dec(x_125);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_2);
lean_ctor_set(x_153, 2, x_3);
lean_ctor_set(x_153, 3, x_4);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_63);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_dec_ref(x_1);
x_154 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_128, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_128, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_128, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_128, 3);
lean_inc(x_158);
lean_dec_ref(x_128);
x_8 = x_63;
x_9 = x_125;
x_10 = x_126;
x_11 = x_127;
x_12 = x_155;
x_13 = x_156;
x_14 = x_157;
x_15 = x_158;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_125);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_154);
x_160 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_160, 0, x_125);
lean_ctor_set(x_160, 1, x_126);
lean_ctor_set(x_160, 2, x_127);
lean_ctor_set(x_160, 3, x_128);
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_129);
x_161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_2);
lean_ctor_set(x_161, 2, x_3);
lean_ctor_set(x_161, 3, x_4);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_63);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_125, 0);
x_163 = lean_ctor_get(x_125, 1);
x_164 = lean_ctor_get(x_125, 2);
x_165 = lean_ctor_get(x_125, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_125);
x_166 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_164);
lean_ctor_set(x_166, 3, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_154);
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_126);
lean_ctor_set(x_167, 2, x_127);
lean_ctor_set(x_167, 3, x_128);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_129);
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_3);
lean_ctor_set(x_168, 3, x_4);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_63);
return x_168;
}
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_1, 0);
x_170 = lean_ctor_get(x_1, 1);
x_171 = lean_ctor_get(x_1, 2);
x_172 = lean_ctor_get(x_1, 3);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_1);
x_173 = 0;
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
x_174 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_174, 0, x_169);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_171);
lean_ctor_set(x_174, 3, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_obj_tag(x_169) == 0)
{
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec_ref(x_174);
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_172);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_173);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_2);
lean_ctor_set(x_176, 2, x_3);
lean_ctor_set(x_176, 3, x_4);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_63);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = lean_ctor_get_uint8(x_172, sizeof(void*)*4);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec_ref(x_174);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 3);
lean_inc(x_181);
lean_dec_ref(x_172);
x_8 = x_63;
x_9 = x_169;
x_10 = x_170;
x_11 = x_171;
x_12 = x_178;
x_13 = x_179;
x_14 = x_180;
x_15 = x_181;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_171);
lean_dec(x_170);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 x_182 = x_172;
} else {
 lean_dec_ref(x_172);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 4, 1);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_2);
lean_ctor_set(x_183, 2, x_3);
lean_ctor_set(x_183, 3, x_4);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_63);
return x_183;
}
}
}
else
{
uint8_t x_184; 
x_184 = lean_ctor_get_uint8(x_169, sizeof(void*)*4);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec_ref(x_174);
x_185 = lean_ctor_get(x_169, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_169, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_169, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_169, 3);
lean_inc(x_188);
lean_dec_ref(x_169);
x_8 = x_63;
x_9 = x_185;
x_10 = x_186;
x_11 = x_187;
x_12 = x_188;
x_13 = x_170;
x_14 = x_171;
x_15 = x_172;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_171);
lean_dec(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 x_189 = x_169;
} else {
 lean_dec_ref(x_169);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 4, 1);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_174);
lean_ctor_set(x_190, 1, x_2);
lean_ctor_set(x_190, 2, x_3);
lean_ctor_set(x_190, 3, x_4);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_63);
return x_190;
}
else
{
uint8_t x_191; 
lean_dec_ref(x_174);
x_191 = lean_ctor_get_uint8(x_172, sizeof(void*)*4);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_172, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_172, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_172, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_172, 3);
lean_inc(x_195);
lean_dec_ref(x_172);
x_8 = x_63;
x_9 = x_169;
x_10 = x_170;
x_11 = x_171;
x_12 = x_192;
x_13 = x_193;
x_14 = x_194;
x_15 = x_195;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_169, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_169, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_169, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_169, 3);
lean_inc(x_199);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 x_200 = x_169;
} else {
 lean_dec_ref(x_169);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 4, 1);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_196);
lean_ctor_set(x_201, 1, x_197);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_191);
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_170);
lean_ctor_set(x_202, 2, x_171);
lean_ctor_set(x_202, 3, x_172);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_173);
x_203 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 2, x_3);
lean_ctor_set(x_203, 3, x_4);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_63);
return x_203;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_balRight___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object* x_1) {
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
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_RBNode_size___redArg(x_3);
x_6 = l_Lean_RBNode_size___redArg(x_4);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_size___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_box(x_4);
x_10 = lean_apply_5(x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_8 = x_1;
} else {
 lean_dec_ref(x_1);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
if (x_9 == 0)
{
uint8_t x_18; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
x_23 = l_Lean_RBNode_appendTrees___redArg(x_7, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_free_object(x_2);
x_14 = x_23;
goto block_17;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*4);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 2);
x_29 = lean_ctor_get(x_23, 3);
lean_ctor_set(x_23, 3, x_26);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_2, 0, x_29);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_24);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_2);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_24);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_5);
lean_ctor_set(x_35, 2, x_6);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_24);
lean_ctor_set(x_2, 0, x_34);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_24);
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_2);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_24);
return x_36;
}
}
else
{
lean_free_object(x_2);
x_14 = x_23;
goto block_17;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_2);
x_37 = l_Lean_RBNode_appendTrees___redArg(x_7, x_10);
if (lean_obj_tag(x_37) == 0)
{
x_14 = x_37;
goto block_17;
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 4, 1);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 2, x_6);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_38);
x_45 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_11);
lean_ctor_set(x_45, 2, x_12);
lean_ctor_set(x_45, 3, x_13);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_38);
x_46 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_38);
return x_46;
}
else
{
x_14 = x_37;
goto block_17;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
x_47 = l_Lean_RBNode_appendTrees___redArg(x_7, x_2);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
lean_ctor_set(x_48, 2, x_6);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_3);
return x_48;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
if (lean_is_scalar(x_8)) {
 x_15 = lean_alloc_ctor(1, 4, 1);
} else {
 x_15 = x_8;
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_9);
x_16 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_9);
return x_16;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_58 = x_2;
} else {
 lean_dec_ref(x_2);
 x_58 = lean_box(0);
}
if (x_53 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_58);
x_63 = l_Lean_RBNode_appendTrees___redArg(x_1, x_54);
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_53);
return x_64;
}
else
{
uint8_t x_65; 
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_1, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_1, 0);
lean_dec(x_69);
x_70 = l_Lean_RBNode_appendTrees___redArg(x_52, x_54);
if (lean_obj_tag(x_70) == 0)
{
lean_free_object(x_1);
x_59 = x_70;
goto block_62;
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_70, sizeof(void*)*4);
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec(x_58);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 1);
x_75 = lean_ctor_get(x_70, 2);
x_76 = lean_ctor_get(x_70, 3);
lean_ctor_set(x_70, 3, x_73);
lean_ctor_set(x_70, 2, x_51);
lean_ctor_set(x_70, 1, x_50);
lean_ctor_set(x_70, 0, x_49);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_53);
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_1);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_71);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
x_80 = lean_ctor_get(x_70, 2);
x_81 = lean_ctor_get(x_70, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_49);
lean_ctor_set(x_82, 1, x_50);
lean_ctor_set(x_82, 2, x_51);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_53);
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_81);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_1);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_71);
return x_83;
}
}
else
{
lean_free_object(x_1);
x_59 = x_70;
goto block_62;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_1);
x_84 = l_Lean_RBNode_appendTrees___redArg(x_52, x_54);
if (lean_obj_tag(x_84) == 0)
{
x_59 = x_84;
goto block_62;
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_84, sizeof(void*)*4);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_58);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 3);
lean_inc(x_89);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 x_90 = x_84;
} else {
 lean_dec_ref(x_84);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 4, 1);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_49);
lean_ctor_set(x_91, 1, x_50);
lean_ctor_set(x_91, 2, x_51);
lean_ctor_set(x_91, 3, x_86);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_53);
x_92 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_55);
lean_ctor_set(x_92, 2, x_56);
lean_ctor_set(x_92, 3, x_57);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_53);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_85);
return x_93;
}
else
{
x_59 = x_84;
goto block_62;
}
}
}
}
block_62:
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 4, 1);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_53);
x_61 = l_Lean_RBNode_balLeft___redArg(x_49, x_50, x_51, x_60);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_appendTrees___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_apply_1(x_3, x_2);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_5);
x_11 = lean_apply_2(x_4, x_1, lean_box(0));
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_dec_ref(x_2);
x_21 = lean_apply_8(x_5, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_apply_8(x_8, x_22, x_23, x_24, x_25, x_2, lean_box(0), lean_box(0), lean_box(0));
return x_26;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
x_27 = lean_apply_2(x_4, x_1, lean_box(0));
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_4);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 3);
lean_inc(x_32);
lean_dec_ref(x_2);
x_33 = lean_apply_7(x_7, x_1, x_29, x_30, x_31, x_32, lean_box(0), lean_box(0));
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 3);
lean_inc(x_41);
lean_dec_ref(x_2);
x_42 = lean_apply_8(x_6, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_2(x_3, x_1, lean_box(0));
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_4(x_2, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_2(x_3, x_1, lean_box(0));
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
uint8_t x_11; 
x_11 = l_Lean_RBNode_isBlack___redArg(x_5);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_RBNode_del___redArg(x_1, x_2, x_5);
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_12);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_3);
x_14 = l_Lean_RBNode_del___redArg(x_1, x_2, x_5);
x_15 = l_Lean_RBNode_balLeft___redArg(x_14, x_6, x_7, x_8);
return x_15;
}
}
case 1:
{
lean_object* x_16; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = l_Lean_RBNode_appendTrees___redArg(x_5, x_8);
return x_16;
}
default: 
{
uint8_t x_17; 
x_17 = l_Lean_RBNode_isBlack___redArg(x_8);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 0;
x_19 = l_Lean_RBNode_del___redArg(x_1, x_2, x_8);
lean_ctor_set(x_3, 3, x_19);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_18);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_3);
x_20 = l_Lean_RBNode_del___redArg(x_1, x_2, x_8);
x_21 = l_Lean_RBNode_balRight___redArg(x_5, x_6, x_7, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
lean_inc_ref(x_1);
lean_inc(x_23);
lean_inc(x_2);
x_26 = lean_apply_2(x_1, x_2, x_23);
x_27 = lean_unbox(x_26);
switch (x_27) {
case 0:
{
uint8_t x_28; 
x_28 = l_Lean_RBNode_isBlack___redArg(x_22);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = l_Lean_RBNode_del___redArg(x_1, x_2, x_22);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___redArg(x_1, x_2, x_22);
x_33 = l_Lean_RBNode_balLeft___redArg(x_32, x_23, x_24, x_25);
return x_33;
}
}
case 1:
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_2);
lean_dec_ref(x_1);
x_34 = l_Lean_RBNode_appendTrees___redArg(x_22, x_25);
return x_34;
}
default: 
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___redArg(x_25);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = 0;
x_37 = l_Lean_RBNode_del___redArg(x_1, x_2, x_25);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_RBNode_del___redArg(x_1, x_2, x_25);
x_40 = l_Lean_RBNode_balRight___redArg(x_22, x_23, x_24, x_39);
return x_40;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_del___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_del___redArg(x_1, x_2, x_3);
x_5 = l_Lean_RBNode_setBlack___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_erase___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
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
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_findCore___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
default: 
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_find___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_2 = x_8;
x_4 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_lowerBound___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_mapM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_mapM___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_dec_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
lean_inc(x_11);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_12);
x_16 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_10);
x_17 = lean_box(x_9);
x_18 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_11);
x_19 = lean_apply_2(x_7, lean_box(0), x_18);
lean_inc(x_8);
x_20 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_16);
lean_inc(x_8);
x_21 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_20, x_15);
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_14);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_mapM___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_RBNode_mapM___redArg___lam__3(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_9 = l_Lean_RBNode_map___redArg(x_1, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_2(x_1, x_6, x_7);
x_11 = l_Lean_RBNode_map___redArg(x_1, x_8);
lean_ctor_set(x_2, 3, x_11);
lean_ctor_set(x_2, 2, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_17 = l_Lean_RBNode_map___redArg(x_1, x_13);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_2(x_1, x_14, x_15);
x_19 = l_Lean_RBNode_map___redArg(x_1, x_16);
x_20 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_12);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_map___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBNode_toArray___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_toArray___redArg___closed__0;
x_3 = l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_toArray___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___Lean_RBNode_toArray_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_toArray___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_toArray(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkRBMap(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_empty(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instEmptyCollectionRBMap(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedRBMap(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_depth___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_depth___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_depth___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_depth(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_RBNode_isSingleton___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isSingleton___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_isSingleton___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBMap_isSingleton(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_fold___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBMap_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_revFold___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_revFold___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBMap_revFold(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RBNode_foldM___redArg(x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RBMap_foldM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_foldM___redArg(x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_box(0);
x_10 = l_Lean_RBNode_foldM___redArg(x_5, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBMap_forM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_1, x_8, x_2, x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(x_13, 0, x_9);
x_14 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_6, x_13, x_7, x_8);
x_15 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RBMap_forIn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_apply_2(x_1, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProd___lam__0), 4, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_2, x_9, x_3, x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProd___lam__2), 5, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_instForInProd(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_isEmpty___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_RBMap_isEmpty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBMap_toList___redArg___lam__0), 3, 0);
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_revFold___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_toList___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_toList(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_RBMap_toArray___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBMap_toArray___redArg___lam__0), 3, 0);
x_3 = l_Lean_RBMap_toArray___redArg___closed__0;
x_4 = l_Lean_RBNode_fold___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_toArray___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_toArray(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_min___redArg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_min___redArg(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_min___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_min(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_max___redArg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_max___redArg(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_max___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_max(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_RBMap_instRepr___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.rbmapOf ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_instRepr___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBMap_instRepr___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_RBMap_instRepr___redArg___lam__0___closed__1;
x_5 = l_Lean_RBMap_toList___redArg(x_2);
x_6 = l_List_repr___redArg(x_1, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_instReprTupleOfRepr___redArg(x_2);
x_4 = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_instRepr___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_instRepr___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_instRepr(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_insert___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_erase___redArg(x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc_ref(x_1);
x_8 = l_Lean_RBMap_ofList___redArg(x_1, x_5);
x_9 = l_Lean_RBNode_insert___redArg(x_1, x_8, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_ofList___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_findCore___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_find___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_find___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_find___redArg(x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_findD___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBMap_findD(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_lowerBound___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_lowerBound___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec_ref(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_find___redArg(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_6);
x_8 = 1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBMap_contains___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_RBMap_contains(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_RBNode_insert___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = l_List_foldl___redArg(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = l_List_foldl___redArg(x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_RBNode_insert___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBMap_fromArray___redArg___closed__1;
x_2 = l_Lean_RBMap_fromArray___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_fromArray___redArg___closed__5;
x_2 = l_Lean_RBMap_fromArray___redArg___closed__4;
x_3 = l_Lean_RBMap_fromArray___redArg___closed__3;
x_4 = l_Lean_RBMap_fromArray___redArg___closed__2;
x_5 = l_Lean_RBMap_fromArray___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_RBMap_fromArray___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBMap_fromArray___redArg___closed__6;
x_2 = l_Lean_RBMap_fromArray___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = l_Lean_RBMap_fromArray___redArg___closed__9;
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_1, x_10, x_11, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_3);
x_8 = l_Lean_RBMap_fromArray___redArg___closed__9;
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_7);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = 0;
x_13 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_8, x_11, x_3, x_12, x_13, x_5);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_RBNode_all___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_RBNode_all___redArg(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBMap_all___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_RBMap_all(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_RBNode_any___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_RBNode_any___redArg(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBMap_any___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_RBMap_any(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_size___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_size_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_size___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_size(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBMap_maxDepth___redArg___lam__0___boxed), 2, 0);
x_3 = l_Lean_RBNode_depth___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_maxDepth___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_maxDepth___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_maxDepth___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_maxDepth(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.RBMap", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.RBMap.min!", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("map is empty", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_min_x21___redArg___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(382u);
x_4 = l_Lean_RBMap_min_x21___redArg___closed__1;
x_5 = l_Lean_RBMap_min_x21___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_min___redArg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Lean_RBMap_min_x21___redArg___closed__3;
x_7 = l_panic___redArg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_min___redArg(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = l_Lean_RBMap_min_x21___redArg___closed__3;
x_10 = l_panic___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_min_x21___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBMap_min_x21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.RBMap.max!", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_min_x21___redArg___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(387u);
x_4 = l_Lean_RBMap_max_x21___redArg___closed__0;
x_5 = l_Lean_RBMap_min_x21___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_max___redArg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Lean_RBMap_max_x21___redArg___closed__1;
x_7 = l_panic___redArg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_max___redArg(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = l_Lean_RBMap_max_x21___redArg___closed__1;
x_10 = l_panic___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_max_x21___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBMap_max_x21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.RBMap.find!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not in the map", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_find_x21___redArg___closed__1;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(393u);
x_4 = l_Lean_RBMap_find_x21___redArg___closed__0;
x_5 = l_Lean_RBMap_min_x21___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_find___redArg(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBMap_find_x21___redArg___closed__2;
x_7 = l_panic___redArg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_find___redArg(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_RBMap_find_x21___redArg___closed__2;
x_9 = l_panic___redArg(x_4, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; lean_object* x_6; 
lean_dec_ref(x_1);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
switch (x_14) {
case 0:
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_9, x_3, x_4);
lean_ctor_set(x_2, 0, x_15);
return x_2;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
default: 
{
lean_object* x_16; 
x_16 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_12, x_3, x_4);
lean_ctor_set(x_2, 3, x_16);
return x_2;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc_ref(x_1);
lean_inc(x_18);
lean_inc(x_3);
x_21 = lean_apply_2(x_1, x_3, x_18);
x_22 = lean_unbox(x_21);
switch (x_22) {
case 0:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_17, x_3, x_4);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_7);
return x_24;
}
case 1:
{
lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_20, x_3, x_4);
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_18);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_7);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_32 = x_2;
} else {
 lean_dec_ref(x_2);
 x_32 = lean_box(0);
}
lean_inc_ref(x_1);
lean_inc(x_29);
lean_inc(x_3);
x_33 = lean_apply_2(x_1, x_3, x_29);
x_34 = lean_unbox(x_33);
switch (x_34) {
case 0:
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_28, x_3, x_4);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*4);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 3);
lean_inc(x_40);
if (x_36 == 0)
{
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_55; 
lean_dec(x_32);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_35, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_35, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_35, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_35, 0);
lean_dec(x_59);
lean_ctor_set(x_35, 0, x_40);
x_60 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_60, 0, x_35);
lean_ctor_set(x_60, 1, x_29);
lean_ctor_set(x_60, 2, x_30);
lean_ctor_set(x_60, 3, x_31);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_7);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_35);
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_40);
lean_ctor_set(x_61, 1, x_38);
lean_ctor_set(x_61, 2, x_39);
lean_ctor_set(x_61, 3, x_40);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_36);
x_62 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_29);
lean_ctor_set(x_62, 2, x_30);
lean_ctor_set(x_62, 3, x_31);
lean_ctor_set_uint8(x_62, sizeof(void*)*4, x_7);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_35);
x_64 = lean_ctor_get(x_40, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_40, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_40, 3);
lean_inc(x_67);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_64;
x_45 = x_65;
x_46 = x_66;
x_47 = x_67;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_68; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_40, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_40, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_40, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_40, 0);
lean_dec(x_72);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_7);
return x_40;
}
else
{
lean_object* x_73; 
lean_dec(x_40);
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_35);
lean_ctor_set(x_73, 1, x_29);
lean_ctor_set(x_73, 2, x_30);
lean_ctor_set(x_73, 3, x_31);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_7);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_35);
x_75 = lean_ctor_get(x_37, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_37, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_37, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_37, 3);
lean_inc(x_78);
lean_dec_ref(x_37);
x_41 = x_75;
x_42 = x_76;
x_43 = x_77;
x_44 = x_78;
x_45 = x_38;
x_46 = x_39;
x_47 = x_40;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_79; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_32);
x_79 = !lean_is_exclusive(x_37);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_37, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_37, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_37, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_37, 0);
lean_dec(x_83);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_84; 
lean_dec(x_37);
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_35);
lean_ctor_set(x_84, 1, x_29);
lean_ctor_set(x_84, 2, x_30);
lean_ctor_set(x_84, 3, x_31);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_7);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_35);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_35, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_35, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_35, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_35, 0);
lean_dec(x_89);
x_90 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_35);
x_91 = lean_ctor_get(x_40, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_40, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_40, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_40, 3);
lean_inc(x_94);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_91;
x_45 = x_92;
x_46 = x_93;
x_47 = x_94;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
uint8_t x_95; 
lean_dec(x_32);
x_95 = !lean_is_exclusive(x_37);
if (x_95 == 0)
{
lean_object* x_96; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_90);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_35);
lean_ctor_set(x_96, 1, x_29);
lean_ctor_set(x_96, 2, x_30);
lean_ctor_set(x_96, 3, x_31);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_37, 0);
x_98 = lean_ctor_get(x_37, 1);
x_99 = lean_ctor_get(x_37, 2);
x_100 = lean_ctor_get(x_37, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_37);
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_90);
lean_ctor_set(x_35, 0, x_101);
x_102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_102, 0, x_35);
lean_ctor_set(x_102, 1, x_29);
lean_ctor_set(x_102, 2, x_30);
lean_ctor_set(x_102, 3, x_31);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_7);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_35);
x_103 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_40, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_40, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_40, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_40, 3);
lean_inc(x_107);
lean_dec_ref(x_40);
x_41 = x_37;
x_42 = x_38;
x_43 = x_39;
x_44 = x_104;
x_45 = x_105;
x_46 = x_106;
x_47 = x_107;
x_48 = x_29;
x_49 = x_30;
x_50 = x_31;
goto block_54;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_32);
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_37, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_37, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_37, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_112 = x_37;
} else {
 lean_dec_ref(x_37);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 4, 1);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_103);
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_38);
lean_ctor_set(x_114, 2, x_39);
lean_ctor_set(x_114, 3, x_40);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_36);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_29);
lean_ctor_set(x_115, 2, x_30);
lean_ctor_set(x_115, 3, x_31);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_7);
return x_115;
}
}
}
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_35);
lean_ctor_set(x_116, 1, x_29);
lean_ctor_set(x_116, 2, x_30);
lean_ctor_set(x_116, 3, x_31);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_7);
return x_116;
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(1, 4, 1);
} else {
 x_51 = x_32;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_7);
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_7);
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_36);
return x_53;
}
}
case 1:
{
lean_object* x_117; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_1);
if (lean_is_scalar(x_32)) {
 x_117 = lean_alloc_ctor(1, 4, 1);
} else {
 x_117 = x_32;
}
lean_ctor_set(x_117, 0, x_28);
lean_ctor_set(x_117, 1, x_3);
lean_ctor_set(x_117, 2, x_4);
lean_ctor_set(x_117, 3, x_31);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
default: 
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_118 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_31, x_3, x_4);
x_119 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc(x_123);
if (x_119 == 0)
{
if (lean_obj_tag(x_120) == 0)
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_138; 
lean_dec(x_32);
x_138 = !lean_is_exclusive(x_118);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_118, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_118, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_118, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_118, 0);
lean_dec(x_142);
lean_ctor_set(x_118, 0, x_123);
x_143 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_143, 0, x_28);
lean_ctor_set(x_143, 1, x_29);
lean_ctor_set(x_143, 2, x_30);
lean_ctor_set(x_143, 3, x_118);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_7);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_118);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_121);
lean_ctor_set(x_144, 2, x_122);
lean_ctor_set(x_144, 3, x_123);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_119);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_28);
lean_ctor_set(x_145, 1, x_29);
lean_ctor_set(x_145, 2, x_30);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_7);
return x_145;
}
}
else
{
uint8_t x_146; 
x_146 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_118);
x_147 = lean_ctor_get(x_123, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_123, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_123, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_123, 3);
lean_inc(x_150);
lean_dec_ref(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_147;
x_131 = x_148;
x_132 = x_149;
x_133 = x_150;
goto block_137;
}
else
{
uint8_t x_151; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_32);
x_151 = !lean_is_exclusive(x_123);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_123, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_123, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_123, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_123, 0);
lean_dec(x_155);
lean_ctor_set(x_123, 3, x_118);
lean_ctor_set(x_123, 2, x_30);
lean_ctor_set(x_123, 1, x_29);
lean_ctor_set(x_123, 0, x_28);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_7);
return x_123;
}
else
{
lean_object* x_156; 
lean_dec(x_123);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_28);
lean_ctor_set(x_156, 1, x_29);
lean_ctor_set(x_156, 2, x_30);
lean_ctor_set(x_156, 3, x_118);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_7);
return x_156;
}
}
}
}
else
{
uint8_t x_157; 
x_157 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_118);
x_158 = lean_ctor_get(x_120, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_120, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_120, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_120, 3);
lean_inc(x_161);
lean_dec_ref(x_120);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_158;
x_128 = x_159;
x_129 = x_160;
x_130 = x_161;
x_131 = x_121;
x_132 = x_122;
x_133 = x_123;
goto block_137;
}
else
{
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_162; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_32);
x_162 = !lean_is_exclusive(x_120);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_120, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_120, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_120, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_120, 0);
lean_dec(x_166);
lean_ctor_set(x_120, 3, x_118);
lean_ctor_set(x_120, 2, x_30);
lean_ctor_set(x_120, 1, x_29);
lean_ctor_set(x_120, 0, x_28);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_167; 
lean_dec(x_120);
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_28);
lean_ctor_set(x_167, 1, x_29);
lean_ctor_set(x_167, 2, x_30);
lean_ctor_set(x_167, 3, x_118);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_7);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_118);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_118, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_118, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_118, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_118, 0);
lean_dec(x_172);
x_173 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_118);
x_174 = lean_ctor_get(x_123, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_123, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_123, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_123, 3);
lean_inc(x_177);
lean_dec_ref(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_174;
x_131 = x_175;
x_132 = x_176;
x_133 = x_177;
goto block_137;
}
else
{
uint8_t x_178; 
lean_dec(x_32);
x_178 = !lean_is_exclusive(x_120);
if (x_178 == 0)
{
lean_object* x_179; 
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_173);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_28);
lean_ctor_set(x_179, 1, x_29);
lean_ctor_set(x_179, 2, x_30);
lean_ctor_set(x_179, 3, x_118);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_7);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_120, 0);
x_181 = lean_ctor_get(x_120, 1);
x_182 = lean_ctor_get(x_120, 2);
x_183 = lean_ctor_get(x_120, 3);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_120);
x_184 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set(x_184, 1, x_181);
lean_ctor_set(x_184, 2, x_182);
lean_ctor_set(x_184, 3, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_173);
lean_ctor_set(x_118, 0, x_184);
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_28);
lean_ctor_set(x_185, 1, x_29);
lean_ctor_set(x_185, 2, x_30);
lean_ctor_set(x_185, 3, x_118);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_7);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_118);
x_186 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_123, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_123, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_123, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_123, 3);
lean_inc(x_190);
lean_dec_ref(x_123);
x_124 = x_28;
x_125 = x_29;
x_126 = x_30;
x_127 = x_120;
x_128 = x_121;
x_129 = x_122;
x_130 = x_187;
x_131 = x_188;
x_132 = x_189;
x_133 = x_190;
goto block_137;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_32);
x_191 = lean_ctor_get(x_120, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_120, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_120, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_120, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 x_195 = x_120;
} else {
 lean_dec_ref(x_120);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_186);
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_121);
lean_ctor_set(x_197, 2, x_122);
lean_ctor_set(x_197, 3, x_123);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_119);
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_28);
lean_ctor_set(x_198, 1, x_29);
lean_ctor_set(x_198, 2, x_30);
lean_ctor_set(x_198, 3, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_7);
return x_198;
}
}
}
}
}
}
else
{
lean_object* x_199; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_32);
x_199 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_199, 0, x_28);
lean_ctor_set(x_199, 1, x_29);
lean_ctor_set(x_199, 2, x_30);
lean_ctor_set(x_199, 3, x_118);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_7);
return x_199;
}
block_137:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
if (lean_is_scalar(x_32)) {
 x_134 = lean_alloc_ctor(1, 4, 1);
} else {
 x_134 = x_32;
}
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_125);
lean_ctor_set(x_134, 2, x_126);
lean_ctor_set(x_134, 3, x_127);
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_7);
x_135 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_7);
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_119);
return x_136;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___redArg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
switch (x_10) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
default: 
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
lean_dec_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(x_1, x_2, x_3, x_5);
lean_inc(x_6);
lean_inc(x_9);
lean_inc_ref(x_1);
x_14 = l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2___redArg(x_1, x_9, x_6);
if (lean_obj_tag(x_14) == 0)
{
x_10 = x_7;
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_2);
lean_inc(x_6);
x_16 = lean_apply_3(x_2, x_6, x_15, x_7);
x_10 = x_16;
goto block_13;
}
block_13:
{
lean_object* x_11; 
lean_inc_ref(x_1);
x_11 = l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(x_1, x_9, x_6, x_10);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___at___Lean_RBMap_mergeBy_spec__3___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
lean_dec_ref(x_5);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
lean_inc(x_7);
lean_inc(x_1);
lean_inc_ref(x_2);
x_11 = l_Lean_RBNode_find___at___Lean_RBMap_mergeBy_spec__2___redArg(x_2, x_1, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
x_4 = x_10;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_3);
lean_inc(x_7);
x_14 = lean_apply_3(x_3, x_7, x_8, x_13);
lean_inc_ref(x_2);
x_15 = l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_10, x_7, x_14);
x_4 = x_15;
x_5 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0___redArg(x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_fold___at___Lean_RBMap_intersectBy_spec__0___redArg(x_4, x_1, x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_RBMap_intersectBy___redArg(x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0___redArg(x_1, x_2, x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_apply_2(x_1, x_6, x_7);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_3 = x_9;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_13; 
lean_inc_ref(x_2);
x_13 = l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_9, x_6, x_7);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_filter_spec__0___redArg(x_2, x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_filter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0___redArg(x_1, x_2, x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_6);
x_10 = lean_apply_2(x_1, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_6);
x_3 = x_9;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc_ref(x_2);
x_13 = l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_9, x_6, x_12);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_fold___at___Lean_RBMap_filterMap_spec__0___redArg(x_2, x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBMap_filterMap___redArg(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rbmapOf_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc_ref(x_1);
x_8 = l_Lean_RBNode_insert___at___Lean_RBMap_mergeBy_spec__0___redArg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rbmapOf_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___at___Lean_rbmapOf_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at___Lean_rbmapOf_spec__0___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_rbmapOf___redArg(x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_RBNode_toArray___redArg___closed__0 = _init_l_Lean_RBNode_toArray___redArg___closed__0();
lean_mark_persistent(l_Lean_RBNode_toArray___redArg___closed__0);
l_Lean_RBMap_toArray___redArg___closed__0 = _init_l_Lean_RBMap_toArray___redArg___closed__0();
lean_mark_persistent(l_Lean_RBMap_toArray___redArg___closed__0);
l_Lean_RBMap_instRepr___redArg___lam__0___closed__0 = _init_l_Lean_RBMap_instRepr___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_RBMap_instRepr___redArg___lam__0___closed__0);
l_Lean_RBMap_instRepr___redArg___lam__0___closed__1 = _init_l_Lean_RBMap_instRepr___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1);
l_Lean_RBMap_fromArray___redArg___closed__0 = _init_l_Lean_RBMap_fromArray___redArg___closed__0();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__0);
l_Lean_RBMap_fromArray___redArg___closed__1 = _init_l_Lean_RBMap_fromArray___redArg___closed__1();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__1);
l_Lean_RBMap_fromArray___redArg___closed__2 = _init_l_Lean_RBMap_fromArray___redArg___closed__2();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__2);
l_Lean_RBMap_fromArray___redArg___closed__3 = _init_l_Lean_RBMap_fromArray___redArg___closed__3();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__3);
l_Lean_RBMap_fromArray___redArg___closed__4 = _init_l_Lean_RBMap_fromArray___redArg___closed__4();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__4);
l_Lean_RBMap_fromArray___redArg___closed__5 = _init_l_Lean_RBMap_fromArray___redArg___closed__5();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__5);
l_Lean_RBMap_fromArray___redArg___closed__6 = _init_l_Lean_RBMap_fromArray___redArg___closed__6();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__6);
l_Lean_RBMap_fromArray___redArg___closed__7 = _init_l_Lean_RBMap_fromArray___redArg___closed__7();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__7);
l_Lean_RBMap_fromArray___redArg___closed__8 = _init_l_Lean_RBMap_fromArray___redArg___closed__8();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__8);
l_Lean_RBMap_fromArray___redArg___closed__9 = _init_l_Lean_RBMap_fromArray___redArg___closed__9();
lean_mark_persistent(l_Lean_RBMap_fromArray___redArg___closed__9);
l_Lean_RBMap_min_x21___redArg___closed__0 = _init_l_Lean_RBMap_min_x21___redArg___closed__0();
lean_mark_persistent(l_Lean_RBMap_min_x21___redArg___closed__0);
l_Lean_RBMap_min_x21___redArg___closed__1 = _init_l_Lean_RBMap_min_x21___redArg___closed__1();
lean_mark_persistent(l_Lean_RBMap_min_x21___redArg___closed__1);
l_Lean_RBMap_min_x21___redArg___closed__2 = _init_l_Lean_RBMap_min_x21___redArg___closed__2();
lean_mark_persistent(l_Lean_RBMap_min_x21___redArg___closed__2);
l_Lean_RBMap_min_x21___redArg___closed__3 = _init_l_Lean_RBMap_min_x21___redArg___closed__3();
lean_mark_persistent(l_Lean_RBMap_min_x21___redArg___closed__3);
l_Lean_RBMap_max_x21___redArg___closed__0 = _init_l_Lean_RBMap_max_x21___redArg___closed__0();
lean_mark_persistent(l_Lean_RBMap_max_x21___redArg___closed__0);
l_Lean_RBMap_max_x21___redArg___closed__1 = _init_l_Lean_RBMap_max_x21___redArg___closed__1();
lean_mark_persistent(l_Lean_RBMap_max_x21___redArg___closed__1);
l_Lean_RBMap_find_x21___redArg___closed__0 = _init_l_Lean_RBMap_find_x21___redArg___closed__0();
lean_mark_persistent(l_Lean_RBMap_find_x21___redArg___closed__0);
l_Lean_RBMap_find_x21___redArg___closed__1 = _init_l_Lean_RBMap_find_x21___redArg___closed__1();
lean_mark_persistent(l_Lean_RBMap_find_x21___redArg___closed__1);
l_Lean_RBMap_find_x21___redArg___closed__2 = _init_l_Lean_RBMap_find_x21___redArg___closed__2();
lean_mark_persistent(l_Lean_RBMap_find_x21___redArg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
