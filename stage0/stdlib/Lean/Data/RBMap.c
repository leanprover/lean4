// Lean compiler output
// Module: Lean.Data.RBMap
// Imports: Init.Data.Ord Init.Data.Nat.Linear
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
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_rbmapOf___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at_Lean_RBMap_instRepr___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_max_x21___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_min_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___rarg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_any___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_find_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_RBNode_all___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at_Lean_RBMap_instRepr___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4;
static lean_object* l_Lean_RBColor_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_all(lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_toArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_fromList___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_RBMap_instRepr___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_maxDepth___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_toList___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__4;
lean_object* l_Nat_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_fromList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___rarg(lean_object*);
static lean_object* l_Lean_RBMap_max_x21___rarg___closed__2;
static lean_object* l_Lean_RBMap_max_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_instRepr___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_min_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1(lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_find_x21___rarg___closed__2;
static lean_object* l_Lean_RBMap_toArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__1;
static lean_object* l_Lean_RBMap_instRepr___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_toArray___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_RBMap_instRepr___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_min_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_max_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_find_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbmapOf___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_min_x21___spec__1(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___rarg___boxed(lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___rarg(lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___rarg(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_RBMap_min_x21___rarg___closed__3;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_RBMap_instRepr___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_RBMap_any___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3(lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBMap_size___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBMap_min_x21___rarg___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_instRepr___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_rbmapOf___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_min___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_RBColor_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBColor_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBColor_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBColor_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBColor_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBColor_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_RBColor_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_6 = l_Lean_RBNode_depth___rarg(x_1, x_4);
lean_inc(x_1);
x_7 = l_Lean_RBNode_depth___rarg(x_1, x_5);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_depth___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_min___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_max___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_fold___rarg(x_1, x_2, x_4);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_forM___rarg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_RBNode_forM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_RBNode_forM___rarg(x_1, x_2, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_forM___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBNode_forM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_forM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_forM___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_3(x_1, x_7, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_RBNode_foldM___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___rarg___lambda__2), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_RBNode_forIn_visit___rarg(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_2);
x_12 = lean_apply_3(x_2, x_3, x_4, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___rarg___lambda__1), 4, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_RBNode_forIn_visit___rarg(x_1, x_2, x_9, x_4);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___rarg___lambda__2), 7, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_11);
lean_closure_set(x_15, 4, x_12);
lean_closure_set(x_15, 5, x_13);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_RBNode_forIn_visit___rarg(x_1, x_4, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Lean_RBNode_revFold___rarg(x_1, x_2, x_7);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBNode_revFold___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_Lean_RBNode_all___rarg(x_1, x_4);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = 0;
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_all___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_1);
x_10 = l_Lean_RBNode_any___rarg(x_1, x_4);
if (x_10 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_any___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_singleton___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_isSingleton___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_isSingleton___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_9);
x_13 = 1;
x_14 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_7);
x_18 = 1;
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_4);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_9, sizeof(void*)*4);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 2);
x_30 = lean_ctor_get(x_9, 3);
x_31 = 1;
lean_ctor_set(x_9, 3, x_27);
lean_ctor_set(x_9, 2, x_23);
lean_ctor_set(x_9, 1, x_22);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_31);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_1);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_38 = 1;
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_22);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_38);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_1);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_1);
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_9, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_48 = x_9;
} else {
 lean_dec_ref(x_9);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 4, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_49);
x_51 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_2);
lean_ctor_set(x_51, 2, x_3);
lean_ctor_set(x_51, 3, x_4);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_49);
x_52 = 0;
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_9, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_9, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 0);
lean_dec(x_58);
x_59 = 1;
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_59);
return x_9;
}
else
{
uint8_t x_60; lean_object* x_61; 
lean_dec(x_9);
x_60 = 1;
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set(x_61, 2, x_3);
lean_ctor_set(x_61, 3, x_4);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get(x_1, 2);
x_66 = lean_ctor_get(x_1, 3);
x_67 = lean_ctor_get(x_1, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_8);
if (x_68 == 0)
{
uint8_t x_69; uint8_t x_70; lean_object* x_71; 
x_69 = 1;
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_69);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
x_70 = 0;
x_71 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_71, 0, x_8);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_65);
lean_ctor_set(x_71, 3, x_1);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_8, 0);
x_73 = lean_ctor_get(x_8, 1);
x_74 = lean_ctor_get(x_8, 2);
x_75 = lean_ctor_get(x_8, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_8);
x_76 = 1;
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_76);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_66);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_76);
x_78 = 0;
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_64);
lean_ctor_set(x_79, 2, x_65);
lean_ctor_set(x_79, 3, x_1);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_1, 1);
x_81 = lean_ctor_get(x_1, 2);
x_82 = lean_ctor_get(x_1, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_1);
x_83 = lean_ctor_get(x_8, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_8, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_8, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_8, 3);
lean_inc(x_86);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_87 = x_8;
} else {
 lean_dec_ref(x_8);
 x_87 = lean_box(0);
}
x_88 = 1;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 4, 1);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_85);
lean_ctor_set(x_89, 3, x_86);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_88);
x_90 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_2);
lean_ctor_set(x_90, 2, x_3);
lean_ctor_set(x_90, 3, x_4);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_88);
x_91 = 0;
x_92 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_80);
lean_ctor_set(x_92, 2, x_81);
lean_ctor_set(x_92, 3, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_1, 3);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_8);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_8, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_8, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_8, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_8, 0);
lean_dec(x_98);
x_99 = 1;
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_99);
return x_8;
}
else
{
uint8_t x_100; lean_object* x_101; 
lean_dec(x_8);
x_100 = 1;
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_2);
lean_ctor_set(x_101, 2, x_3);
lean_ctor_set(x_101, 3, x_4);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_93, sizeof(void*)*4);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_1);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_1, 1);
x_105 = lean_ctor_get(x_1, 2);
x_106 = lean_ctor_get(x_1, 3);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_93);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; 
x_109 = lean_ctor_get(x_93, 0);
x_110 = lean_ctor_get(x_93, 1);
x_111 = lean_ctor_get(x_93, 2);
x_112 = lean_ctor_get(x_93, 3);
x_113 = 1;
lean_inc(x_8);
lean_ctor_set(x_93, 3, x_109);
lean_ctor_set(x_93, 2, x_105);
lean_ctor_set(x_93, 1, x_104);
lean_ctor_set(x_93, 0, x_8);
x_114 = !lean_is_exclusive(x_8);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_8, 3);
lean_dec(x_115);
x_116 = lean_ctor_get(x_8, 2);
lean_dec(x_116);
x_117 = lean_ctor_get(x_8, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_8, 0);
lean_dec(x_118);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_113);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_112);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_113);
x_119 = 0;
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_119);
return x_1;
}
else
{
lean_object* x_120; uint8_t x_121; 
lean_dec(x_8);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_113);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_112);
lean_ctor_set(x_120, 1, x_2);
lean_ctor_set(x_120, 2, x_3);
lean_ctor_set(x_120, 3, x_4);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_113);
x_121 = 0;
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_121);
return x_1;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_122 = lean_ctor_get(x_93, 0);
x_123 = lean_ctor_get(x_93, 1);
x_124 = lean_ctor_get(x_93, 2);
x_125 = lean_ctor_get(x_93, 3);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_93);
x_126 = 1;
lean_inc(x_8);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_8);
lean_ctor_set(x_127, 1, x_104);
lean_ctor_set(x_127, 2, x_105);
lean_ctor_set(x_127, 3, x_122);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_128 = x_8;
} else {
 lean_dec_ref(x_8);
 x_128 = lean_box(0);
}
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_126);
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 2, x_3);
lean_ctor_set(x_129, 3, x_4);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_126);
x_130 = 0;
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set(x_1, 2, x_124);
lean_ctor_set(x_1, 1, x_123);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_131 = lean_ctor_get(x_1, 1);
x_132 = lean_ctor_get(x_1, 2);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_1);
x_133 = lean_ctor_get(x_93, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_93, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_93, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_93, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 x_137 = x_93;
} else {
 lean_dec_ref(x_93);
 x_137 = lean_box(0);
}
x_138 = 1;
lean_inc(x_8);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(1, 4, 1);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_8);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_132);
lean_ctor_set(x_139, 3, x_133);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_140 = x_8;
} else {
 lean_dec_ref(x_8);
 x_140 = lean_box(0);
}
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_138);
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_141, 1, x_2);
lean_ctor_set(x_141, 2, x_3);
lean_ctor_set(x_141, 3, x_4);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_138);
x_142 = 0;
x_143 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_134);
lean_ctor_set(x_143, 2, x_135);
lean_ctor_set(x_143, 3, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_142);
return x_143;
}
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_1);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_1, 3);
lean_dec(x_145);
x_146 = lean_ctor_get(x_1, 0);
lean_dec(x_146);
x_147 = !lean_is_exclusive(x_8);
if (x_147 == 0)
{
uint8_t x_148; lean_object* x_149; 
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_102);
x_148 = 1;
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_1);
lean_ctor_set(x_149, 1, x_2);
lean_ctor_set(x_149, 2, x_3);
lean_ctor_set(x_149, 3, x_4);
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_8, 0);
x_151 = lean_ctor_get(x_8, 1);
x_152 = lean_ctor_get(x_8, 2);
x_153 = lean_ctor_get(x_8, 3);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_8);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_151);
lean_ctor_set(x_154, 2, x_152);
lean_ctor_set(x_154, 3, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_102);
lean_ctor_set(x_1, 0, x_154);
x_155 = 1;
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_2);
lean_ctor_set(x_156, 2, x_3);
lean_ctor_set(x_156, 3, x_4);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_155);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_157 = lean_ctor_get(x_1, 1);
x_158 = lean_ctor_get(x_1, 2);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_1);
x_159 = lean_ctor_get(x_8, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_8, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_8, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_8, 3);
lean_inc(x_162);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_163 = x_8;
} else {
 lean_dec_ref(x_8);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_159);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_164, 2, x_161);
lean_ctor_set(x_164, 3, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_102);
x_165 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_157);
lean_ctor_set(x_165, 2, x_158);
lean_ctor_set(x_165, 3, x_93);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_7);
x_166 = 1;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_2);
lean_ctor_set(x_167, 2, x_3);
lean_ctor_set(x_167, 3, x_4);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
}
}
}
}
else
{
uint8_t x_168; lean_object* x_169; 
x_168 = 1;
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_2);
lean_ctor_set(x_169, 2, x_3);
lean_ctor_set(x_169, 3, x_4);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_168);
return x_169;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_balance1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_9);
x_13 = 1;
x_14 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_7);
x_18 = 1;
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_9, sizeof(void*)*4);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 2);
x_30 = lean_ctor_get(x_9, 3);
x_31 = 1;
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_31);
lean_ctor_set(x_4, 3, x_30);
lean_ctor_set(x_4, 2, x_29);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_27);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_31);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get(x_9, 2);
x_37 = lean_ctor_get(x_9, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_38 = 1;
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set(x_39, 3, x_8);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_38);
lean_ctor_set(x_4, 3, x_37);
lean_ctor_set(x_4, 2, x_36);
lean_ctor_set(x_4, 1, x_35);
lean_ctor_set(x_4, 0, x_34);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_22);
lean_ctor_set(x_41, 2, x_23);
lean_ctor_set(x_41, 3, x_4);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_4, 1);
x_43 = lean_ctor_get(x_4, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_9, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_48 = x_9;
} else {
 lean_dec_ref(x_9);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 4, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_3);
lean_ctor_set(x_50, 3, x_8);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_49);
x_51 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_49);
x_52 = 0;
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_43);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_9, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_9, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_9, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 0);
lean_dec(x_58);
x_59 = 1;
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_59);
return x_9;
}
else
{
uint8_t x_60; lean_object* x_61; 
lean_dec(x_9);
x_60 = 1;
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set(x_61, 2, x_3);
lean_ctor_set(x_61, 3, x_4);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_4);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_4, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_8);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_8, 0);
x_67 = lean_ctor_get(x_8, 1);
x_68 = lean_ctor_get(x_8, 2);
x_69 = lean_ctor_get(x_8, 3);
x_70 = 1;
lean_ctor_set(x_8, 3, x_66);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_70);
lean_ctor_set(x_4, 0, x_69);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_70);
x_71 = 0;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_8);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_4);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_8, 0);
x_74 = lean_ctor_get(x_8, 1);
x_75 = lean_ctor_get(x_8, 2);
x_76 = lean_ctor_get(x_8, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_8);
x_77 = 1;
x_78 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_3);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
lean_ctor_set(x_4, 0, x_76);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_77);
x_79 = 0;
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set(x_80, 3, x_4);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_4, 1);
x_82 = lean_ctor_get(x_4, 2);
x_83 = lean_ctor_get(x_4, 3);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_4);
x_84 = lean_ctor_get(x_8, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_8, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_8, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 3);
lean_inc(x_87);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_88 = x_8;
} else {
 lean_dec_ref(x_8);
 x_88 = lean_box(0);
}
x_89 = 1;
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 4, 1);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_2);
lean_ctor_set(x_90, 2, x_3);
lean_ctor_set(x_90, 3, x_84);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_89);
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_81);
lean_ctor_set(x_91, 2, x_82);
lean_ctor_set(x_91, 3, x_83);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_89);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_86);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
return x_93;
}
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_4, 3);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_8);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_8, 3);
lean_dec(x_96);
x_97 = lean_ctor_get(x_8, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_8, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_8, 0);
lean_dec(x_99);
x_100 = 1;
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_100);
return x_8;
}
else
{
uint8_t x_101; lean_object* x_102; 
lean_dec(x_8);
x_101 = 1;
x_102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_2);
lean_ctor_set(x_102, 2, x_3);
lean_ctor_set(x_102, 3, x_4);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_101);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = lean_ctor_get_uint8(x_94, sizeof(void*)*4);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_4);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_4, 3);
lean_dec(x_105);
x_106 = lean_ctor_get(x_4, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_94);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_94, 0);
x_109 = lean_ctor_get(x_94, 1);
x_110 = lean_ctor_get(x_94, 2);
x_111 = lean_ctor_get(x_94, 3);
x_112 = 1;
lean_inc(x_8);
lean_ctor_set(x_94, 3, x_8);
lean_ctor_set(x_94, 2, x_3);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 0, x_1);
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_8, 3);
lean_dec(x_114);
x_115 = lean_ctor_get(x_8, 2);
lean_dec(x_115);
x_116 = lean_ctor_get(x_8, 1);
lean_dec(x_116);
x_117 = lean_ctor_get(x_8, 0);
lean_dec(x_117);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_112);
lean_ctor_set(x_8, 3, x_111);
lean_ctor_set(x_8, 2, x_110);
lean_ctor_set(x_8, 1, x_109);
lean_ctor_set(x_8, 0, x_108);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_112);
x_118 = 0;
lean_ctor_set(x_4, 3, x_8);
lean_ctor_set(x_4, 0, x_94);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_118);
return x_4;
}
else
{
lean_object* x_119; uint8_t x_120; 
lean_dec(x_8);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_112);
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_109);
lean_ctor_set(x_119, 2, x_110);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_112);
x_120 = 0;
lean_ctor_set(x_4, 3, x_119);
lean_ctor_set(x_4, 0, x_94);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_120);
return x_4;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_121 = lean_ctor_get(x_94, 0);
x_122 = lean_ctor_get(x_94, 1);
x_123 = lean_ctor_get(x_94, 2);
x_124 = lean_ctor_get(x_94, 3);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_94);
x_125 = 1;
lean_inc(x_8);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_2);
lean_ctor_set(x_126, 2, x_3);
lean_ctor_set(x_126, 3, x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_127 = x_8;
} else {
 lean_dec_ref(x_8);
 x_127 = lean_box(0);
}
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 4, 1);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_122);
lean_ctor_set(x_128, 2, x_123);
lean_ctor_set(x_128, 3, x_124);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_125);
x_129 = 0;
lean_ctor_set(x_4, 3, x_128);
lean_ctor_set(x_4, 0, x_126);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_129);
return x_4;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_130 = lean_ctor_get(x_4, 1);
x_131 = lean_ctor_get(x_4, 2);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_4);
x_132 = lean_ctor_get(x_94, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_94, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_94, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_94, 3);
lean_inc(x_135);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 x_136 = x_94;
} else {
 lean_dec_ref(x_94);
 x_136 = lean_box(0);
}
x_137 = 1;
lean_inc(x_8);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(1, 4, 1);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_1);
lean_ctor_set(x_138, 1, x_2);
lean_ctor_set(x_138, 2, x_3);
lean_ctor_set(x_138, 3, x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_139 = x_8;
} else {
 lean_dec_ref(x_8);
 x_139 = lean_box(0);
}
lean_ctor_set_uint8(x_138, sizeof(void*)*4, x_137);
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 4, 1);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_132);
lean_ctor_set(x_140, 1, x_133);
lean_ctor_set(x_140, 2, x_134);
lean_ctor_set(x_140, 3, x_135);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_137);
x_141 = 0;
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_130);
lean_ctor_set(x_142, 2, x_131);
lean_ctor_set(x_142, 3, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_141);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_4, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_4, 0);
lean_dec(x_145);
x_146 = !lean_is_exclusive(x_8);
if (x_146 == 0)
{
uint8_t x_147; lean_object* x_148; 
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_103);
x_147 = 1;
x_148 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_2);
lean_ctor_set(x_148, 2, x_3);
lean_ctor_set(x_148, 3, x_4);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_147);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_8, 0);
x_150 = lean_ctor_get(x_8, 1);
x_151 = lean_ctor_get(x_8, 2);
x_152 = lean_ctor_get(x_8, 3);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_8);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_151);
lean_ctor_set(x_153, 3, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_103);
lean_ctor_set(x_4, 0, x_153);
x_154 = 1;
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_2);
lean_ctor_set(x_155, 2, x_3);
lean_ctor_set(x_155, 3, x_4);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_4, 1);
x_157 = lean_ctor_get(x_4, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_4);
x_158 = lean_ctor_get(x_8, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_8, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_8, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_8, 3);
lean_inc(x_161);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_162 = x_8;
} else {
 lean_dec_ref(x_8);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set(x_163, 1, x_159);
lean_ctor_set(x_163, 2, x_160);
lean_ctor_set(x_163, 3, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_103);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_157);
lean_ctor_set(x_164, 3, x_94);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
x_165 = 1;
x_166 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_2);
lean_ctor_set(x_166, 2, x_3);
lean_ctor_set(x_166, 3, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_165);
return x_166;
}
}
}
}
}
}
else
{
uint8_t x_167; lean_object* x_168; 
x_167 = 1;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_3);
lean_ctor_set(x_168, 3, x_4);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_balance2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_isRed___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_isRed___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_isBlack___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_isBlack___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_3);
x_14 = lean_apply_2(x_1, x_3, x_11);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
switch (x_15) {
case 0:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_RBNode_ins___rarg(x_1, x_10, x_3, x_4);
x_17 = 0;
lean_ctor_set(x_2, 0, x_16);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
case 1:
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_18 = 0;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
default: 
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_RBNode_ins___rarg(x_1, x_13, x_3, x_4);
x_20 = 0;
lean_ctor_set(x_2, 3, x_19);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_20);
return x_2;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_22);
lean_inc(x_3);
x_25 = lean_apply_2(x_1, x_3, x_22);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
switch (x_26) {
case 0:
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_ins___rarg(x_1, x_21, x_3, x_4);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
case 1:
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 3, x_24);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
default: 
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = l_Lean_RBNode_ins___rarg(x_1, x_24, x_3, x_4);
x_33 = 0;
x_34 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
lean_inc(x_37);
lean_inc(x_3);
x_40 = lean_apply_2(x_1, x_3, x_37);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
switch (x_41) {
case 0:
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_RBNode_ins___rarg(x_1, x_36, x_3, x_4);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_42, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_42, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_42, 0);
lean_dec(x_48);
lean_ctor_set(x_42, 0, x_45);
x_49 = 1;
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_49);
return x_2;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 1);
x_51 = lean_ctor_get(x_42, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_45);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_43);
x_53 = 1;
lean_ctor_set(x_2, 0, x_52);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_53);
return x_2;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_42, 1);
x_57 = lean_ctor_get(x_42, 2);
x_58 = lean_ctor_get(x_42, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_42, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_45);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_45, 0);
x_62 = lean_ctor_get(x_45, 1);
x_63 = lean_ctor_get(x_45, 2);
x_64 = lean_ctor_get(x_45, 3);
x_65 = 1;
lean_ctor_set(x_45, 3, x_61);
lean_ctor_set(x_45, 2, x_57);
lean_ctor_set(x_45, 1, x_56);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_65);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 0, x_64);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_2, 3, x_42);
lean_ctor_set(x_2, 2, x_63);
lean_ctor_set(x_2, 1, x_62);
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_66);
return x_2;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_45, 0);
x_68 = lean_ctor_get(x_45, 1);
x_69 = lean_ctor_get(x_45, 2);
x_70 = lean_ctor_get(x_45, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_45);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_44);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 0, x_70);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_2, 3, x_42);
lean_ctor_set(x_2, 2, x_69);
lean_ctor_set(x_2, 1, x_68);
lean_ctor_set(x_2, 0, x_72);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_73);
return x_2;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_42, 1);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_42);
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_45, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_80 = x_45;
} else {
 lean_dec_ref(x_45);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_44);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_37);
lean_ctor_set(x_83, 2, x_38);
lean_ctor_set(x_83, 3, x_39);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_2, 3, x_83);
lean_ctor_set(x_2, 2, x_78);
lean_ctor_set(x_2, 1, x_77);
lean_ctor_set(x_2, 0, x_82);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_84);
return x_2;
}
}
else
{
uint8_t x_85; 
lean_free_object(x_2);
x_85 = !lean_is_exclusive(x_45);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_45, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_45, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_45, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_45, 0);
lean_dec(x_89);
x_90 = 1;
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_90);
return x_45;
}
else
{
uint8_t x_91; lean_object* x_92; 
lean_dec(x_45);
x_91 = 1;
x_92 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_92, 0, x_42);
lean_ctor_set(x_92, 1, x_37);
lean_ctor_set(x_92, 2, x_38);
lean_ctor_set(x_92, 3, x_39);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
x_93 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_42);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_42, 1);
x_96 = lean_ctor_get(x_42, 2);
x_97 = lean_ctor_get(x_42, 3);
x_98 = lean_ctor_get(x_42, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
uint8_t x_100; uint8_t x_101; 
x_100 = 1;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_100);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 0, x_97);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_100);
x_101 = 0;
lean_ctor_set(x_2, 3, x_42);
lean_ctor_set(x_2, 2, x_96);
lean_ctor_set(x_2, 1, x_95);
lean_ctor_set(x_2, 0, x_44);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_101);
return x_2;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; 
x_102 = lean_ctor_get(x_44, 0);
x_103 = lean_ctor_get(x_44, 1);
x_104 = lean_ctor_get(x_44, 2);
x_105 = lean_ctor_get(x_44, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_44);
x_106 = 1;
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_105);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_42, 0, x_97);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_106);
x_108 = 0;
lean_ctor_set(x_2, 3, x_42);
lean_ctor_set(x_2, 2, x_96);
lean_ctor_set(x_2, 1, x_95);
lean_ctor_set(x_2, 0, x_107);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_108);
return x_2;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_109 = lean_ctor_get(x_42, 1);
x_110 = lean_ctor_get(x_42, 2);
x_111 = lean_ctor_get(x_42, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_42);
x_112 = lean_ctor_get(x_44, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_44, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_44, 3);
lean_inc(x_115);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_116 = x_44;
} else {
 lean_dec_ref(x_44);
 x_116 = lean_box(0);
}
x_117 = 1;
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 4, 1);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_113);
lean_ctor_set(x_118, 2, x_114);
lean_ctor_set(x_118, 3, x_115);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_117);
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_111);
lean_ctor_set(x_119, 1, x_37);
lean_ctor_set(x_119, 2, x_38);
lean_ctor_set(x_119, 3, x_39);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_117);
x_120 = 0;
lean_ctor_set(x_2, 3, x_119);
lean_ctor_set(x_2, 2, x_110);
lean_ctor_set(x_2, 1, x_109);
lean_ctor_set(x_2, 0, x_118);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_120);
return x_2;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_42, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_free_object(x_2);
x_122 = !lean_is_exclusive(x_44);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_44, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_44, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_44, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_44, 0);
lean_dec(x_126);
x_127 = 1;
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_127);
return x_44;
}
else
{
uint8_t x_128; lean_object* x_129; 
lean_dec(x_44);
x_128 = 1;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_42);
lean_ctor_set(x_129, 1, x_37);
lean_ctor_set(x_129, 2, x_38);
lean_ctor_set(x_129, 3, x_39);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_2);
x_131 = !lean_is_exclusive(x_42);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_42, 1);
x_133 = lean_ctor_get(x_42, 2);
x_134 = lean_ctor_get(x_42, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_42, 0);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_121);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; 
x_137 = lean_ctor_get(x_121, 0);
x_138 = lean_ctor_get(x_121, 1);
x_139 = lean_ctor_get(x_121, 2);
x_140 = lean_ctor_get(x_121, 3);
x_141 = 1;
lean_inc(x_44);
lean_ctor_set(x_121, 3, x_137);
lean_ctor_set(x_121, 2, x_133);
lean_ctor_set(x_121, 1, x_132);
lean_ctor_set(x_121, 0, x_44);
x_142 = !lean_is_exclusive(x_44);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_44, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_44, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_44, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_44, 0);
lean_dec(x_146);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_141);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 0, x_140);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_141);
x_147 = 0;
lean_ctor_set(x_42, 3, x_44);
lean_ctor_set(x_42, 2, x_139);
lean_ctor_set(x_42, 1, x_138);
lean_ctor_set(x_42, 0, x_121);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_147);
return x_42;
}
else
{
lean_object* x_148; uint8_t x_149; 
lean_dec(x_44);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_141);
x_148 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_37);
lean_ctor_set(x_148, 2, x_38);
lean_ctor_set(x_148, 3, x_39);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_141);
x_149 = 0;
lean_ctor_set(x_42, 3, x_148);
lean_ctor_set(x_42, 2, x_139);
lean_ctor_set(x_42, 1, x_138);
lean_ctor_set(x_42, 0, x_121);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_149);
return x_42;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_150 = lean_ctor_get(x_121, 0);
x_151 = lean_ctor_get(x_121, 1);
x_152 = lean_ctor_get(x_121, 2);
x_153 = lean_ctor_get(x_121, 3);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_121);
x_154 = 1;
lean_inc(x_44);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_44);
lean_ctor_set(x_155, 1, x_132);
lean_ctor_set(x_155, 2, x_133);
lean_ctor_set(x_155, 3, x_150);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_156 = x_44;
} else {
 lean_dec_ref(x_44);
 x_156 = lean_box(0);
}
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_154);
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 4, 1);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_37);
lean_ctor_set(x_157, 2, x_38);
lean_ctor_set(x_157, 3, x_39);
lean_ctor_set_uint8(x_157, sizeof(void*)*4, x_154);
x_158 = 0;
lean_ctor_set(x_42, 3, x_157);
lean_ctor_set(x_42, 2, x_152);
lean_ctor_set(x_42, 1, x_151);
lean_ctor_set(x_42, 0, x_155);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_158);
return x_42;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; 
x_159 = lean_ctor_get(x_42, 1);
x_160 = lean_ctor_get(x_42, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_42);
x_161 = lean_ctor_get(x_121, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_121, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_121, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_121, 3);
lean_inc(x_164);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_165 = x_121;
} else {
 lean_dec_ref(x_121);
 x_165 = lean_box(0);
}
x_166 = 1;
lean_inc(x_44);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(1, 4, 1);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_44);
lean_ctor_set(x_167, 1, x_159);
lean_ctor_set(x_167, 2, x_160);
lean_ctor_set(x_167, 3, x_161);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_168 = x_44;
} else {
 lean_dec_ref(x_44);
 x_168 = lean_box(0);
}
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 4, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_164);
lean_ctor_set(x_169, 1, x_37);
lean_ctor_set(x_169, 2, x_38);
lean_ctor_set(x_169, 3, x_39);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_166);
x_170 = 0;
x_171 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_162);
lean_ctor_set(x_171, 2, x_163);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
return x_171;
}
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_42);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_42, 3);
lean_dec(x_173);
x_174 = lean_ctor_get(x_42, 0);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_44);
if (x_175 == 0)
{
uint8_t x_176; 
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_130);
x_176 = 1;
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_176);
return x_2;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_44, 0);
x_178 = lean_ctor_get(x_44, 1);
x_179 = lean_ctor_get(x_44, 2);
x_180 = lean_ctor_get(x_44, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_44);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
lean_ctor_set(x_42, 0, x_181);
x_182 = 1;
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_182);
return x_2;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_42);
x_185 = lean_ctor_get(x_44, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_44, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_44, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_44, 3);
lean_inc(x_188);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_189 = x_44;
} else {
 lean_dec_ref(x_44);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 4, 1);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_185);
lean_ctor_set(x_190, 1, x_186);
lean_ctor_set(x_190, 2, x_187);
lean_ctor_set(x_190, 3, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_130);
x_191 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_183);
lean_ctor_set(x_191, 2, x_184);
lean_ctor_set(x_191, 3, x_121);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_43);
x_192 = 1;
lean_ctor_set(x_2, 0, x_191);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_192);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_193; 
x_193 = 1;
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_193);
return x_2;
}
}
case 1:
{
uint8_t x_194; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_194 = 1;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_194);
return x_2;
}
default: 
{
lean_object* x_195; uint8_t x_196; 
x_195 = l_Lean_RBNode_ins___rarg(x_1, x_39, x_3, x_4);
x_196 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_195, 3);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_195);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_195, 3);
lean_dec(x_200);
x_201 = lean_ctor_get(x_195, 0);
lean_dec(x_201);
lean_ctor_set(x_195, 0, x_198);
x_202 = 1;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_202);
return x_2;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_195, 1);
x_204 = lean_ctor_get(x_195, 2);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_195);
x_205 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_203);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_198);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_196);
x_206 = 1;
lean_ctor_set(x_2, 3, x_205);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_206);
return x_2;
}
}
else
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_198, sizeof(void*)*4);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_195);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_195, 1);
x_210 = lean_ctor_get(x_195, 2);
x_211 = lean_ctor_get(x_195, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_195, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_198);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_219; 
x_214 = lean_ctor_get(x_198, 0);
x_215 = lean_ctor_get(x_198, 1);
x_216 = lean_ctor_get(x_198, 2);
x_217 = lean_ctor_get(x_198, 3);
x_218 = 1;
lean_ctor_set(x_198, 3, x_197);
lean_ctor_set(x_198, 2, x_38);
lean_ctor_set(x_198, 1, x_37);
lean_ctor_set(x_198, 0, x_36);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_218);
lean_ctor_set(x_195, 3, x_217);
lean_ctor_set(x_195, 2, x_216);
lean_ctor_set(x_195, 1, x_215);
lean_ctor_set(x_195, 0, x_214);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_218);
x_219 = 0;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set(x_2, 2, x_210);
lean_ctor_set(x_2, 1, x_209);
lean_ctor_set(x_2, 0, x_198);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_219);
return x_2;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; uint8_t x_226; 
x_220 = lean_ctor_get(x_198, 0);
x_221 = lean_ctor_get(x_198, 1);
x_222 = lean_ctor_get(x_198, 2);
x_223 = lean_ctor_get(x_198, 3);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_198);
x_224 = 1;
x_225 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_225, 0, x_36);
lean_ctor_set(x_225, 1, x_37);
lean_ctor_set(x_225, 2, x_38);
lean_ctor_set(x_225, 3, x_197);
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_224);
lean_ctor_set(x_195, 3, x_223);
lean_ctor_set(x_195, 2, x_222);
lean_ctor_set(x_195, 1, x_221);
lean_ctor_set(x_195, 0, x_220);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_224);
x_226 = 0;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set(x_2, 2, x_210);
lean_ctor_set(x_2, 1, x_209);
lean_ctor_set(x_2, 0, x_225);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_226);
return x_2;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_227 = lean_ctor_get(x_195, 1);
x_228 = lean_ctor_get(x_195, 2);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_195);
x_229 = lean_ctor_get(x_198, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_198, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_198, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_198, 3);
lean_inc(x_232);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_233 = x_198;
} else {
 lean_dec_ref(x_198);
 x_233 = lean_box(0);
}
x_234 = 1;
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(1, 4, 1);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_36);
lean_ctor_set(x_235, 1, x_37);
lean_ctor_set(x_235, 2, x_38);
lean_ctor_set(x_235, 3, x_197);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
x_236 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_236, 0, x_229);
lean_ctor_set(x_236, 1, x_230);
lean_ctor_set(x_236, 2, x_231);
lean_ctor_set(x_236, 3, x_232);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_234);
x_237 = 0;
lean_ctor_set(x_2, 3, x_236);
lean_ctor_set(x_2, 2, x_228);
lean_ctor_set(x_2, 1, x_227);
lean_ctor_set(x_2, 0, x_235);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_237);
return x_2;
}
}
else
{
uint8_t x_238; 
lean_free_object(x_2);
x_238 = !lean_is_exclusive(x_198);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_239 = lean_ctor_get(x_198, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_198, 2);
lean_dec(x_240);
x_241 = lean_ctor_get(x_198, 1);
lean_dec(x_241);
x_242 = lean_ctor_get(x_198, 0);
lean_dec(x_242);
x_243 = 1;
lean_ctor_set(x_198, 3, x_195);
lean_ctor_set(x_198, 2, x_38);
lean_ctor_set(x_198, 1, x_37);
lean_ctor_set(x_198, 0, x_36);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_243);
return x_198;
}
else
{
uint8_t x_244; lean_object* x_245; 
lean_dec(x_198);
x_244 = 1;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_36);
lean_ctor_set(x_245, 1, x_37);
lean_ctor_set(x_245, 2, x_38);
lean_ctor_set(x_245, 3, x_195);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
return x_245;
}
}
}
}
else
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_197, sizeof(void*)*4);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_195);
if (x_247 == 0)
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_ctor_get(x_195, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_197);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_255; 
x_250 = lean_ctor_get(x_197, 0);
x_251 = lean_ctor_get(x_197, 1);
x_252 = lean_ctor_get(x_197, 2);
x_253 = lean_ctor_get(x_197, 3);
x_254 = 1;
lean_ctor_set(x_197, 3, x_250);
lean_ctor_set(x_197, 2, x_38);
lean_ctor_set(x_197, 1, x_37);
lean_ctor_set(x_197, 0, x_36);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_254);
lean_ctor_set(x_195, 0, x_253);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_254);
x_255 = 0;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set(x_2, 2, x_252);
lean_ctor_set(x_2, 1, x_251);
lean_ctor_set(x_2, 0, x_197);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_255);
return x_2;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; uint8_t x_262; 
x_256 = lean_ctor_get(x_197, 0);
x_257 = lean_ctor_get(x_197, 1);
x_258 = lean_ctor_get(x_197, 2);
x_259 = lean_ctor_get(x_197, 3);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_197);
x_260 = 1;
x_261 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_261, 0, x_36);
lean_ctor_set(x_261, 1, x_37);
lean_ctor_set(x_261, 2, x_38);
lean_ctor_set(x_261, 3, x_256);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_260);
lean_ctor_set(x_195, 0, x_259);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_260);
x_262 = 0;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set(x_2, 2, x_258);
lean_ctor_set(x_2, 1, x_257);
lean_ctor_set(x_2, 0, x_261);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_262);
return x_2;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_263 = lean_ctor_get(x_195, 1);
x_264 = lean_ctor_get(x_195, 2);
x_265 = lean_ctor_get(x_195, 3);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_195);
x_266 = lean_ctor_get(x_197, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_197, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_197, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_197, 3);
lean_inc(x_269);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 x_270 = x_197;
} else {
 lean_dec_ref(x_197);
 x_270 = lean_box(0);
}
x_271 = 1;
if (lean_is_scalar(x_270)) {
 x_272 = lean_alloc_ctor(1, 4, 1);
} else {
 x_272 = x_270;
}
lean_ctor_set(x_272, 0, x_36);
lean_ctor_set(x_272, 1, x_37);
lean_ctor_set(x_272, 2, x_38);
lean_ctor_set(x_272, 3, x_266);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_271);
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_269);
lean_ctor_set(x_273, 1, x_263);
lean_ctor_set(x_273, 2, x_264);
lean_ctor_set(x_273, 3, x_265);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_271);
x_274 = 0;
lean_ctor_set(x_2, 3, x_273);
lean_ctor_set(x_2, 2, x_268);
lean_ctor_set(x_2, 1, x_267);
lean_ctor_set(x_2, 0, x_272);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_274);
return x_2;
}
}
else
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_195, 3);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
uint8_t x_276; 
lean_free_object(x_2);
x_276 = !lean_is_exclusive(x_197);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_197, 3);
lean_dec(x_277);
x_278 = lean_ctor_get(x_197, 2);
lean_dec(x_278);
x_279 = lean_ctor_get(x_197, 1);
lean_dec(x_279);
x_280 = lean_ctor_get(x_197, 0);
lean_dec(x_280);
x_281 = 1;
lean_ctor_set(x_197, 3, x_195);
lean_ctor_set(x_197, 2, x_38);
lean_ctor_set(x_197, 1, x_37);
lean_ctor_set(x_197, 0, x_36);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_281);
return x_197;
}
else
{
uint8_t x_282; lean_object* x_283; 
lean_dec(x_197);
x_282 = 1;
x_283 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_283, 0, x_36);
lean_ctor_set(x_283, 1, x_37);
lean_ctor_set(x_283, 2, x_38);
lean_ctor_set(x_283, 3, x_195);
lean_ctor_set_uint8(x_283, sizeof(void*)*4, x_282);
return x_283;
}
}
else
{
uint8_t x_284; 
x_284 = lean_ctor_get_uint8(x_275, sizeof(void*)*4);
if (x_284 == 0)
{
uint8_t x_285; 
lean_free_object(x_2);
x_285 = !lean_is_exclusive(x_195);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = lean_ctor_get(x_195, 3);
lean_dec(x_286);
x_287 = lean_ctor_get(x_195, 0);
lean_dec(x_287);
x_288 = !lean_is_exclusive(x_275);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_294; 
x_289 = lean_ctor_get(x_275, 0);
x_290 = lean_ctor_get(x_275, 1);
x_291 = lean_ctor_get(x_275, 2);
x_292 = lean_ctor_get(x_275, 3);
x_293 = 1;
lean_inc(x_197);
lean_ctor_set(x_275, 3, x_197);
lean_ctor_set(x_275, 2, x_38);
lean_ctor_set(x_275, 1, x_37);
lean_ctor_set(x_275, 0, x_36);
x_294 = !lean_is_exclusive(x_197);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_295 = lean_ctor_get(x_197, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_197, 2);
lean_dec(x_296);
x_297 = lean_ctor_get(x_197, 1);
lean_dec(x_297);
x_298 = lean_ctor_get(x_197, 0);
lean_dec(x_298);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_293);
lean_ctor_set(x_197, 3, x_292);
lean_ctor_set(x_197, 2, x_291);
lean_ctor_set(x_197, 1, x_290);
lean_ctor_set(x_197, 0, x_289);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_293);
x_299 = 0;
lean_ctor_set(x_195, 3, x_197);
lean_ctor_set(x_195, 0, x_275);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_299);
return x_195;
}
else
{
lean_object* x_300; uint8_t x_301; 
lean_dec(x_197);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_293);
x_300 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_300, 0, x_289);
lean_ctor_set(x_300, 1, x_290);
lean_ctor_set(x_300, 2, x_291);
lean_ctor_set(x_300, 3, x_292);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_293);
x_301 = 0;
lean_ctor_set(x_195, 3, x_300);
lean_ctor_set(x_195, 0, x_275);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_301);
return x_195;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_302 = lean_ctor_get(x_275, 0);
x_303 = lean_ctor_get(x_275, 1);
x_304 = lean_ctor_get(x_275, 2);
x_305 = lean_ctor_get(x_275, 3);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_275);
x_306 = 1;
lean_inc(x_197);
x_307 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_307, 0, x_36);
lean_ctor_set(x_307, 1, x_37);
lean_ctor_set(x_307, 2, x_38);
lean_ctor_set(x_307, 3, x_197);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 x_308 = x_197;
} else {
 lean_dec_ref(x_197);
 x_308 = lean_box(0);
}
lean_ctor_set_uint8(x_307, sizeof(void*)*4, x_306);
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 4, 1);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_303);
lean_ctor_set(x_309, 2, x_304);
lean_ctor_set(x_309, 3, x_305);
lean_ctor_set_uint8(x_309, sizeof(void*)*4, x_306);
x_310 = 0;
lean_ctor_set(x_195, 3, x_309);
lean_ctor_set(x_195, 0, x_307);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_310);
return x_195;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; 
x_311 = lean_ctor_get(x_195, 1);
x_312 = lean_ctor_get(x_195, 2);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_195);
x_313 = lean_ctor_get(x_275, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_275, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_275, 2);
lean_inc(x_315);
x_316 = lean_ctor_get(x_275, 3);
lean_inc(x_316);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 lean_ctor_release(x_275, 2);
 lean_ctor_release(x_275, 3);
 x_317 = x_275;
} else {
 lean_dec_ref(x_275);
 x_317 = lean_box(0);
}
x_318 = 1;
lean_inc(x_197);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(1, 4, 1);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_36);
lean_ctor_set(x_319, 1, x_37);
lean_ctor_set(x_319, 2, x_38);
lean_ctor_set(x_319, 3, x_197);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 x_320 = x_197;
} else {
 lean_dec_ref(x_197);
 x_320 = lean_box(0);
}
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 4, 1);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_313);
lean_ctor_set(x_321, 1, x_314);
lean_ctor_set(x_321, 2, x_315);
lean_ctor_set(x_321, 3, x_316);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_318);
x_322 = 0;
x_323 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_311);
lean_ctor_set(x_323, 2, x_312);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_322);
return x_323;
}
}
else
{
uint8_t x_324; 
x_324 = !lean_is_exclusive(x_195);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_325 = lean_ctor_get(x_195, 3);
lean_dec(x_325);
x_326 = lean_ctor_get(x_195, 0);
lean_dec(x_326);
x_327 = !lean_is_exclusive(x_197);
if (x_327 == 0)
{
uint8_t x_328; 
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_284);
x_328 = 1;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_328);
return x_2;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_197, 0);
x_330 = lean_ctor_get(x_197, 1);
x_331 = lean_ctor_get(x_197, 2);
x_332 = lean_ctor_get(x_197, 3);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_197);
x_333 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_333, 0, x_329);
lean_ctor_set(x_333, 1, x_330);
lean_ctor_set(x_333, 2, x_331);
lean_ctor_set(x_333, 3, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_284);
lean_ctor_set(x_195, 0, x_333);
x_334 = 1;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_334);
return x_2;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_335 = lean_ctor_get(x_195, 1);
x_336 = lean_ctor_get(x_195, 2);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_195);
x_337 = lean_ctor_get(x_197, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_197, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_197, 2);
lean_inc(x_339);
x_340 = lean_ctor_get(x_197, 3);
lean_inc(x_340);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 lean_ctor_release(x_197, 3);
 x_341 = x_197;
} else {
 lean_dec_ref(x_197);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 4, 1);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_337);
lean_ctor_set(x_342, 1, x_338);
lean_ctor_set(x_342, 2, x_339);
lean_ctor_set(x_342, 3, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_284);
x_343 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_335);
lean_ctor_set(x_343, 2, x_336);
lean_ctor_set(x_343, 3, x_275);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_196);
x_344 = 1;
lean_ctor_set(x_2, 3, x_343);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_344);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_345; 
x_345 = 1;
lean_ctor_set(x_2, 3, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_345);
return x_2;
}
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_346 = lean_ctor_get(x_2, 0);
x_347 = lean_ctor_get(x_2, 1);
x_348 = lean_ctor_get(x_2, 2);
x_349 = lean_ctor_get(x_2, 3);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_347);
lean_inc(x_3);
x_350 = lean_apply_2(x_1, x_3, x_347);
x_351 = lean_unbox(x_350);
lean_dec(x_350);
switch (x_351) {
case 0:
{
lean_object* x_352; uint8_t x_353; 
x_352 = l_Lean_RBNode_ins___rarg(x_1, x_346, x_3, x_4);
x_353 = lean_ctor_get_uint8(x_352, sizeof(void*)*4);
if (x_353 == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_352, 3);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; 
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_352, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_358 = x_352;
} else {
 lean_dec_ref(x_352);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 4, 1);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_355);
lean_ctor_set(x_359, 1, x_356);
lean_ctor_set(x_359, 2, x_357);
lean_ctor_set(x_359, 3, x_355);
lean_ctor_set_uint8(x_359, sizeof(void*)*4, x_353);
x_360 = 1;
x_361 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_347);
lean_ctor_set(x_361, 2, x_348);
lean_ctor_set(x_361, 3, x_349);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_360);
return x_361;
}
else
{
uint8_t x_362; 
x_362 = lean_ctor_get_uint8(x_355, sizeof(void*)*4);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; 
x_363 = lean_ctor_get(x_352, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_352, 2);
lean_inc(x_364);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_365 = x_352;
} else {
 lean_dec_ref(x_352);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_355, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_355, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_355, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_355, 3);
lean_inc(x_369);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_370 = x_355;
} else {
 lean_dec_ref(x_355);
 x_370 = lean_box(0);
}
x_371 = 1;
if (lean_is_scalar(x_370)) {
 x_372 = lean_alloc_ctor(1, 4, 1);
} else {
 x_372 = x_370;
}
lean_ctor_set(x_372, 0, x_354);
lean_ctor_set(x_372, 1, x_363);
lean_ctor_set(x_372, 2, x_364);
lean_ctor_set(x_372, 3, x_366);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
if (lean_is_scalar(x_365)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_365;
}
lean_ctor_set(x_373, 0, x_369);
lean_ctor_set(x_373, 1, x_347);
lean_ctor_set(x_373, 2, x_348);
lean_ctor_set(x_373, 3, x_349);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_371);
x_374 = 0;
x_375 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_367);
lean_ctor_set(x_375, 2, x_368);
lean_ctor_set(x_375, 3, x_373);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_374);
return x_375;
}
else
{
lean_object* x_376; uint8_t x_377; lean_object* x_378; 
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_376 = x_355;
} else {
 lean_dec_ref(x_355);
 x_376 = lean_box(0);
}
x_377 = 1;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_352);
lean_ctor_set(x_378, 1, x_347);
lean_ctor_set(x_378, 2, x_348);
lean_ctor_set(x_378, 3, x_349);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
x_379 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; 
x_380 = lean_ctor_get(x_352, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_352, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_352, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_383 = x_352;
} else {
 lean_dec_ref(x_352);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_354, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_354, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_354, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_354, 3);
lean_inc(x_387);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_388 = x_354;
} else {
 lean_dec_ref(x_354);
 x_388 = lean_box(0);
}
x_389 = 1;
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_384);
lean_ctor_set(x_390, 1, x_385);
lean_ctor_set(x_390, 2, x_386);
lean_ctor_set(x_390, 3, x_387);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_389);
if (lean_is_scalar(x_383)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_383;
}
lean_ctor_set(x_391, 0, x_382);
lean_ctor_set(x_391, 1, x_347);
lean_ctor_set(x_391, 2, x_348);
lean_ctor_set(x_391, 3, x_349);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_389);
x_392 = 0;
x_393 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_380);
lean_ctor_set(x_393, 2, x_381);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
return x_393;
}
else
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_352, 3);
lean_inc(x_394);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; uint8_t x_396; lean_object* x_397; 
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_395 = x_354;
} else {
 lean_dec_ref(x_354);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_352);
lean_ctor_set(x_397, 1, x_347);
lean_ctor_set(x_397, 2, x_348);
lean_ctor_set(x_397, 3, x_349);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
return x_397;
}
else
{
uint8_t x_398; 
x_398 = lean_ctor_get_uint8(x_394, sizeof(void*)*4);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; 
x_399 = lean_ctor_get(x_352, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_352, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_401 = x_352;
} else {
 lean_dec_ref(x_352);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_394, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_394, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_394, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_394, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 lean_ctor_release(x_394, 3);
 x_406 = x_394;
} else {
 lean_dec_ref(x_394);
 x_406 = lean_box(0);
}
x_407 = 1;
lean_inc(x_354);
if (lean_is_scalar(x_406)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_406;
}
lean_ctor_set(x_408, 0, x_354);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_408, 2, x_400);
lean_ctor_set(x_408, 3, x_402);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_409 = x_354;
} else {
 lean_dec_ref(x_354);
 x_409 = lean_box(0);
}
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_405);
lean_ctor_set(x_410, 1, x_347);
lean_ctor_set(x_410, 2, x_348);
lean_ctor_set(x_410, 3, x_349);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_407);
x_411 = 0;
if (lean_is_scalar(x_401)) {
 x_412 = lean_alloc_ctor(1, 4, 1);
} else {
 x_412 = x_401;
}
lean_ctor_set(x_412, 0, x_408);
lean_ctor_set(x_412, 1, x_403);
lean_ctor_set(x_412, 2, x_404);
lean_ctor_set(x_412, 3, x_410);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_411);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_413 = lean_ctor_get(x_352, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_352, 2);
lean_inc(x_414);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_415 = x_352;
} else {
 lean_dec_ref(x_352);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_354, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_354, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_354, 2);
lean_inc(x_418);
x_419 = lean_ctor_get(x_354, 3);
lean_inc(x_419);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_420 = x_354;
} else {
 lean_dec_ref(x_354);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 4, 1);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_416);
lean_ctor_set(x_421, 1, x_417);
lean_ctor_set(x_421, 2, x_418);
lean_ctor_set(x_421, 3, x_419);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_398);
if (lean_is_scalar(x_415)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_415;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_413);
lean_ctor_set(x_422, 2, x_414);
lean_ctor_set(x_422, 3, x_394);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_353);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_347);
lean_ctor_set(x_424, 2, x_348);
lean_ctor_set(x_424, 3, x_349);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
}
}
}
}
else
{
uint8_t x_425; lean_object* x_426; 
x_425 = 1;
x_426 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_426, 0, x_352);
lean_ctor_set(x_426, 1, x_347);
lean_ctor_set(x_426, 2, x_348);
lean_ctor_set(x_426, 3, x_349);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
return x_426;
}
}
case 1:
{
uint8_t x_427; lean_object* x_428; 
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_1);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_346);
lean_ctor_set(x_428, 1, x_3);
lean_ctor_set(x_428, 2, x_4);
lean_ctor_set(x_428, 3, x_349);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
default: 
{
lean_object* x_429; uint8_t x_430; 
x_429 = l_Lean_RBNode_ins___rarg(x_1, x_349, x_3, x_4);
x_430 = lean_ctor_get_uint8(x_429, sizeof(void*)*4);
if (x_430 == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
x_432 = lean_ctor_get(x_429, 3);
lean_inc(x_432);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; lean_object* x_438; 
x_433 = lean_ctor_get(x_429, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_429, 2);
lean_inc(x_434);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_435 = x_429;
} else {
 lean_dec_ref(x_429);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_432);
lean_ctor_set(x_436, 1, x_433);
lean_ctor_set(x_436, 2, x_434);
lean_ctor_set(x_436, 3, x_432);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_430);
x_437 = 1;
x_438 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_438, 0, x_346);
lean_ctor_set(x_438, 1, x_347);
lean_ctor_set(x_438, 2, x_348);
lean_ctor_set(x_438, 3, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*4, x_437);
return x_438;
}
else
{
uint8_t x_439; 
x_439 = lean_ctor_get_uint8(x_432, sizeof(void*)*4);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_429, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_429, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_442 = x_429;
} else {
 lean_dec_ref(x_429);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_432, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_432, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_432, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_432, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_447 = x_432;
} else {
 lean_dec_ref(x_432);
 x_447 = lean_box(0);
}
x_448 = 1;
if (lean_is_scalar(x_447)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_447;
}
lean_ctor_set(x_449, 0, x_346);
lean_ctor_set(x_449, 1, x_347);
lean_ctor_set(x_449, 2, x_348);
lean_ctor_set(x_449, 3, x_431);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_443);
lean_ctor_set(x_450, 1, x_444);
lean_ctor_set(x_450, 2, x_445);
lean_ctor_set(x_450, 3, x_446);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_448);
x_451 = 0;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_440);
lean_ctor_set(x_452, 2, x_441);
lean_ctor_set(x_452, 3, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
else
{
lean_object* x_453; uint8_t x_454; lean_object* x_455; 
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_453 = x_432;
} else {
 lean_dec_ref(x_432);
 x_453 = lean_box(0);
}
x_454 = 1;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_346);
lean_ctor_set(x_455, 1, x_347);
lean_ctor_set(x_455, 2, x_348);
lean_ctor_set(x_455, 3, x_429);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
return x_455;
}
}
}
else
{
uint8_t x_456; 
x_456 = lean_ctor_get_uint8(x_431, sizeof(void*)*4);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; 
x_457 = lean_ctor_get(x_429, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_429, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_429, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_460 = x_429;
} else {
 lean_dec_ref(x_429);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_431, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_431, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_431, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_431, 3);
lean_inc(x_464);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_465 = x_431;
} else {
 lean_dec_ref(x_431);
 x_465 = lean_box(0);
}
x_466 = 1;
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_346);
lean_ctor_set(x_467, 1, x_347);
lean_ctor_set(x_467, 2, x_348);
lean_ctor_set(x_467, 3, x_461);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
if (lean_is_scalar(x_460)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_460;
}
lean_ctor_set(x_468, 0, x_464);
lean_ctor_set(x_468, 1, x_457);
lean_ctor_set(x_468, 2, x_458);
lean_ctor_set(x_468, 3, x_459);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_466);
x_469 = 0;
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_462);
lean_ctor_set(x_470, 2, x_463);
lean_ctor_set(x_470, 3, x_468);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
return x_470;
}
else
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_429, 3);
lean_inc(x_471);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; uint8_t x_473; lean_object* x_474; 
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_472 = x_431;
} else {
 lean_dec_ref(x_431);
 x_472 = lean_box(0);
}
x_473 = 1;
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_346);
lean_ctor_set(x_474, 1, x_347);
lean_ctor_set(x_474, 2, x_348);
lean_ctor_set(x_474, 3, x_429);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_473);
return x_474;
}
else
{
uint8_t x_475; 
x_475 = lean_ctor_get_uint8(x_471, sizeof(void*)*4);
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_476 = lean_ctor_get(x_429, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_429, 2);
lean_inc(x_477);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_478 = x_429;
} else {
 lean_dec_ref(x_429);
 x_478 = lean_box(0);
}
x_479 = lean_ctor_get(x_471, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_471, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_471, 2);
lean_inc(x_481);
x_482 = lean_ctor_get(x_471, 3);
lean_inc(x_482);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 lean_ctor_release(x_471, 3);
 x_483 = x_471;
} else {
 lean_dec_ref(x_471);
 x_483 = lean_box(0);
}
x_484 = 1;
lean_inc(x_431);
if (lean_is_scalar(x_483)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_483;
}
lean_ctor_set(x_485, 0, x_346);
lean_ctor_set(x_485, 1, x_347);
lean_ctor_set(x_485, 2, x_348);
lean_ctor_set(x_485, 3, x_431);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_486 = x_431;
} else {
 lean_dec_ref(x_431);
 x_486 = lean_box(0);
}
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_479);
lean_ctor_set(x_487, 1, x_480);
lean_ctor_set(x_487, 2, x_481);
lean_ctor_set(x_487, 3, x_482);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_484);
x_488 = 0;
if (lean_is_scalar(x_478)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_478;
}
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_476);
lean_ctor_set(x_489, 2, x_477);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; 
x_490 = lean_ctor_get(x_429, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_429, 2);
lean_inc(x_491);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_492 = x_429;
} else {
 lean_dec_ref(x_429);
 x_492 = lean_box(0);
}
x_493 = lean_ctor_get(x_431, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_431, 1);
lean_inc(x_494);
x_495 = lean_ctor_get(x_431, 2);
lean_inc(x_495);
x_496 = lean_ctor_get(x_431, 3);
lean_inc(x_496);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_497 = x_431;
} else {
 lean_dec_ref(x_431);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 4, 1);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_493);
lean_ctor_set(x_498, 1, x_494);
lean_ctor_set(x_498, 2, x_495);
lean_ctor_set(x_498, 3, x_496);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_475);
if (lean_is_scalar(x_492)) {
 x_499 = lean_alloc_ctor(1, 4, 1);
} else {
 x_499 = x_492;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_490);
lean_ctor_set(x_499, 2, x_491);
lean_ctor_set(x_499, 3, x_471);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_430);
x_500 = 1;
x_501 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_501, 0, x_346);
lean_ctor_set(x_501, 1, x_347);
lean_ctor_set(x_501, 2, x_348);
lean_ctor_set(x_501, 3, x_499);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
return x_501;
}
}
}
}
}
else
{
uint8_t x_502; lean_object* x_503; 
x_502 = 1;
x_503 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_503, 0, x_346);
lean_ctor_set(x_503, 1, x_347);
lean_ctor_set(x_503, 2, x_348);
lean_ctor_set(x_503, 3, x_429);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_502);
return x_503;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_ins___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_setBlack___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___rarg(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_insert___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_setRed___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_11);
x_14 = 0;
x_15 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_11);
x_20 = 0;
x_21 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = 1;
lean_ctor_set(x_8, 3, x_28);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_32);
x_33 = l_Lean_RBNode_setRed___rarg(x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; lean_object* x_35; 
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_4);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_34);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_33, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_33, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_33, 0);
lean_dec(x_41);
lean_ctor_set(x_33, 0, x_38);
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_42 = 0;
x_43 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_29);
lean_ctor_set(x_43, 2, x_30);
lean_ctor_set(x_43, 3, x_4);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_33, 1);
x_45 = lean_ctor_get(x_33, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_36);
lean_ctor_set(x_4, 3, x_46);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_47 = 0;
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_4);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_33, 1);
x_52 = lean_ctor_get(x_33, 2);
x_53 = lean_ctor_get(x_33, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_33, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
x_58 = lean_ctor_get(x_38, 2);
x_59 = lean_ctor_get(x_38, 3);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_32);
lean_ctor_set(x_33, 3, x_59);
lean_ctor_set(x_33, 2, x_58);
lean_ctor_set(x_33, 1, x_57);
lean_ctor_set(x_33, 0, x_56);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_60 = 0;
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_52);
lean_ctor_set(x_4, 1, x_51);
lean_ctor_set(x_4, 0, x_38);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_60);
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_29);
lean_ctor_set(x_61, 2, x_30);
lean_ctor_set(x_61, 3, x_4);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_38, 0);
x_63 = lean_ctor_get(x_38, 1);
x_64 = lean_ctor_get(x_38, 2);
x_65 = lean_ctor_get(x_38, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_38);
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_31);
lean_ctor_set(x_66, 1, x_23);
lean_ctor_set(x_66, 2, x_24);
lean_ctor_set(x_66, 3, x_37);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_32);
lean_ctor_set(x_33, 3, x_65);
lean_ctor_set(x_33, 2, x_64);
lean_ctor_set(x_33, 1, x_63);
lean_ctor_set(x_33, 0, x_62);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_67 = 0;
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_52);
lean_ctor_set(x_4, 1, x_51);
lean_ctor_set(x_4, 0, x_66);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_67);
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_8);
lean_ctor_set(x_68, 1, x_29);
lean_ctor_set(x_68, 2, x_30);
lean_ctor_set(x_68, 3, x_4);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_33, 1);
x_70 = lean_ctor_get(x_33, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_33);
x_71 = lean_ctor_get(x_38, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_38, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_38, 3);
lean_inc(x_74);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_75 = x_38;
} else {
 lean_dec_ref(x_38);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 4, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_23);
lean_ctor_set(x_76, 2, x_24);
lean_ctor_set(x_76, 3, x_37);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_32);
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_72);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_32);
x_78 = 0;
lean_ctor_set(x_4, 3, x_77);
lean_ctor_set(x_4, 2, x_70);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_76);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_78);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_8);
lean_ctor_set(x_79, 1, x_29);
lean_ctor_set(x_79, 2, x_30);
lean_ctor_set(x_79, 3, x_4);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_free_object(x_4);
x_80 = !lean_is_exclusive(x_38);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_38, 3);
lean_dec(x_81);
x_82 = lean_ctor_get(x_38, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_38, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_38, 0);
lean_dec(x_84);
lean_inc(x_33);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 0, x_31);
x_85 = !lean_is_exclusive(x_33);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_33, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_33, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_33, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_33, 0);
lean_dec(x_89);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_32);
x_90 = 0;
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_90);
return x_33;
}
else
{
uint8_t x_91; lean_object* x_92; 
lean_dec(x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_32);
x_91 = 0;
x_92 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_92, 0, x_8);
lean_ctor_set(x_92, 1, x_29);
lean_ctor_set(x_92, 2, x_30);
lean_ctor_set(x_92, 3, x_38);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
lean_dec(x_38);
lean_inc(x_33);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_31);
lean_ctor_set(x_93, 1, x_23);
lean_ctor_set(x_93, 2, x_24);
lean_ctor_set(x_93, 3, x_33);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_94 = x_33;
} else {
 lean_dec_ref(x_33);
 x_94 = lean_box(0);
}
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_32);
x_95 = 0;
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(1, 4, 1);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_8);
lean_ctor_set(x_96, 1, x_29);
lean_ctor_set(x_96, 2, x_30);
lean_ctor_set(x_96, 3, x_93);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
x_97 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_33);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_33, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_37);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_37, 0);
x_102 = lean_ctor_get(x_37, 1);
x_103 = lean_ctor_get(x_37, 2);
x_104 = lean_ctor_get(x_37, 3);
lean_ctor_set(x_37, 3, x_101);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_32);
lean_ctor_set(x_33, 0, x_104);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_105 = 0;
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_103);
lean_ctor_set(x_4, 1, x_102);
lean_ctor_set(x_4, 0, x_37);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_105);
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_8);
lean_ctor_set(x_106, 1, x_29);
lean_ctor_set(x_106, 2, x_30);
lean_ctor_set(x_106, 3, x_4);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_37, 0);
x_108 = lean_ctor_get(x_37, 1);
x_109 = lean_ctor_get(x_37, 2);
x_110 = lean_ctor_get(x_37, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_37);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_31);
lean_ctor_set(x_111, 1, x_23);
lean_ctor_set(x_111, 2, x_24);
lean_ctor_set(x_111, 3, x_107);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_32);
lean_ctor_set(x_33, 0, x_110);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
x_112 = 0;
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_109);
lean_ctor_set(x_4, 1, x_108);
lean_ctor_set(x_4, 0, x_111);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_112);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_8);
lean_ctor_set(x_113, 1, x_29);
lean_ctor_set(x_113, 2, x_30);
lean_ctor_set(x_113, 3, x_4);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_33, 1);
x_115 = lean_ctor_get(x_33, 2);
x_116 = lean_ctor_get(x_33, 3);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_33);
x_117 = lean_ctor_get(x_37, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_37, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_37, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_37, 3);
lean_inc(x_120);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_121 = x_37;
} else {
 lean_dec_ref(x_37);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 4, 1);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_31);
lean_ctor_set(x_122, 1, x_23);
lean_ctor_set(x_122, 2, x_24);
lean_ctor_set(x_122, 3, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_32);
x_123 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_114);
lean_ctor_set(x_123, 2, x_115);
lean_ctor_set(x_123, 3, x_116);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_32);
x_124 = 0;
lean_ctor_set(x_4, 3, x_123);
lean_ctor_set(x_4, 2, x_119);
lean_ctor_set(x_4, 1, x_118);
lean_ctor_set(x_4, 0, x_122);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_124);
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_8);
lean_ctor_set(x_125, 1, x_29);
lean_ctor_set(x_125, 2, x_30);
lean_ctor_set(x_125, 3, x_4);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_33, 3);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_free_object(x_4);
x_127 = !lean_is_exclusive(x_37);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_37, 3);
lean_dec(x_128);
x_129 = lean_ctor_get(x_37, 2);
lean_dec(x_129);
x_130 = lean_ctor_get(x_37, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_37, 0);
lean_dec(x_131);
lean_inc(x_33);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 0, x_31);
x_132 = !lean_is_exclusive(x_33);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_33, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_33, 2);
lean_dec(x_134);
x_135 = lean_ctor_get(x_33, 1);
lean_dec(x_135);
x_136 = lean_ctor_get(x_33, 0);
lean_dec(x_136);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_32);
x_137 = 0;
lean_ctor_set(x_33, 3, x_37);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_137);
return x_33;
}
else
{
uint8_t x_138; lean_object* x_139; 
lean_dec(x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_32);
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_8);
lean_ctor_set(x_139, 1, x_29);
lean_ctor_set(x_139, 2, x_30);
lean_ctor_set(x_139, 3, x_37);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_138);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
lean_dec(x_37);
lean_inc(x_33);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_31);
lean_ctor_set(x_140, 1, x_23);
lean_ctor_set(x_140, 2, x_24);
lean_ctor_set(x_140, 3, x_33);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_141 = x_33;
} else {
 lean_dec_ref(x_33);
 x_141 = lean_box(0);
}
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_32);
x_142 = 0;
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(1, 4, 1);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_8);
lean_ctor_set(x_143, 1, x_29);
lean_ctor_set(x_143, 2, x_30);
lean_ctor_set(x_143, 3, x_140);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_142);
return x_143;
}
}
else
{
uint8_t x_144; 
x_144 = lean_ctor_get_uint8(x_126, sizeof(void*)*4);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_33);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_33, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_33, 0);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_126);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_126, 0);
x_150 = lean_ctor_get(x_126, 1);
x_151 = lean_ctor_get(x_126, 2);
x_152 = lean_ctor_get(x_126, 3);
lean_inc(x_37);
lean_ctor_set(x_126, 3, x_37);
lean_ctor_set(x_126, 2, x_24);
lean_ctor_set(x_126, 1, x_23);
lean_ctor_set(x_126, 0, x_31);
x_153 = !lean_is_exclusive(x_37);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_154 = lean_ctor_get(x_37, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_37, 2);
lean_dec(x_155);
x_156 = lean_ctor_get(x_37, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_37, 0);
lean_dec(x_157);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_32);
lean_ctor_set(x_37, 3, x_152);
lean_ctor_set(x_37, 2, x_151);
lean_ctor_set(x_37, 1, x_150);
lean_ctor_set(x_37, 0, x_149);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_32);
x_158 = 0;
lean_ctor_set(x_33, 3, x_37);
lean_ctor_set(x_33, 0, x_126);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_158);
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_30);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_158);
return x_4;
}
else
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_37);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_32);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_149);
lean_ctor_set(x_159, 1, x_150);
lean_ctor_set(x_159, 2, x_151);
lean_ctor_set(x_159, 3, x_152);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_32);
x_160 = 0;
lean_ctor_set(x_33, 3, x_159);
lean_ctor_set(x_33, 0, x_126);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_160);
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_30);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_160);
return x_4;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_161 = lean_ctor_get(x_126, 0);
x_162 = lean_ctor_get(x_126, 1);
x_163 = lean_ctor_get(x_126, 2);
x_164 = lean_ctor_get(x_126, 3);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_126);
lean_inc(x_37);
x_165 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_165, 0, x_31);
lean_ctor_set(x_165, 1, x_23);
lean_ctor_set(x_165, 2, x_24);
lean_ctor_set(x_165, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_166 = x_37;
} else {
 lean_dec_ref(x_37);
 x_166 = lean_box(0);
}
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_32);
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 4, 1);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_164);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_32);
x_168 = 0;
lean_ctor_set(x_33, 3, x_167);
lean_ctor_set(x_33, 0, x_165);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_168);
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 2, x_30);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_168);
return x_4;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_169 = lean_ctor_get(x_33, 1);
x_170 = lean_ctor_get(x_33, 2);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_33);
x_171 = lean_ctor_get(x_126, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_126, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_126, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_126, 3);
lean_inc(x_174);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 x_175 = x_126;
} else {
 lean_dec_ref(x_126);
 x_175 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_31);
lean_ctor_set(x_176, 1, x_23);
lean_ctor_set(x_176, 2, x_24);
lean_ctor_set(x_176, 3, x_37);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_177 = x_37;
} else {
 lean_dec_ref(x_37);
 x_177 = lean_box(0);
}
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_32);
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_174);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_32);
x_179 = 0;
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_169);
lean_ctor_set(x_180, 2, x_170);
lean_ctor_set(x_180, 3, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
lean_ctor_set(x_4, 3, x_180);
lean_ctor_set(x_4, 2, x_30);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_179);
return x_4;
}
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_33);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_33, 3);
lean_dec(x_182);
x_183 = lean_ctor_get(x_33, 0);
lean_dec(x_183);
x_184 = !lean_is_exclusive(x_37);
if (x_184 == 0)
{
uint8_t x_185; lean_object* x_186; 
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_144);
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_185 = 0;
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_8);
lean_ctor_set(x_186, 1, x_29);
lean_ctor_set(x_186, 2, x_30);
lean_ctor_set(x_186, 3, x_4);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_37, 0);
x_188 = lean_ctor_get(x_37, 1);
x_189 = lean_ctor_get(x_37, 2);
x_190 = lean_ctor_get(x_37, 3);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_37);
x_191 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set(x_191, 2, x_189);
lean_ctor_set(x_191, 3, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_144);
lean_ctor_set(x_33, 0, x_191);
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_192 = 0;
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_8);
lean_ctor_set(x_193, 1, x_29);
lean_ctor_set(x_193, 2, x_30);
lean_ctor_set(x_193, 3, x_4);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_192);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; 
x_194 = lean_ctor_get(x_33, 1);
x_195 = lean_ctor_get(x_33, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_33);
x_196 = lean_ctor_get(x_37, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_37, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_37, 2);
lean_inc(x_198);
x_199 = lean_ctor_get(x_37, 3);
lean_inc(x_199);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_200 = x_37;
} else {
 lean_dec_ref(x_37);
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
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_144);
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_194);
lean_ctor_set(x_202, 2, x_195);
lean_ctor_set(x_202, 3, x_126);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_36);
lean_ctor_set(x_4, 3, x_202);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_203 = 0;
x_204 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_204, 0, x_8);
lean_ctor_set(x_204, 1, x_29);
lean_ctor_set(x_204, 2, x_30);
lean_ctor_set(x_204, 3, x_4);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_203);
return x_204;
}
}
}
}
}
}
else
{
uint8_t x_205; lean_object* x_206; 
lean_ctor_set(x_4, 3, x_33);
lean_ctor_set(x_4, 0, x_31);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_32);
x_205 = 0;
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_8);
lean_ctor_set(x_206, 1, x_29);
lean_ctor_set(x_206, 2, x_30);
lean_ctor_set(x_206, 3, x_4);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; 
x_207 = lean_ctor_get(x_8, 0);
x_208 = lean_ctor_get(x_8, 1);
x_209 = lean_ctor_get(x_8, 2);
x_210 = lean_ctor_get(x_8, 3);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_8);
x_211 = 1;
x_212 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_212, 0, x_1);
lean_ctor_set(x_212, 1, x_2);
lean_ctor_set(x_212, 2, x_3);
lean_ctor_set(x_212, 3, x_207);
lean_ctor_set_uint8(x_212, sizeof(void*)*4, x_211);
x_213 = l_Lean_RBNode_setRed___rarg(x_25);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; lean_object* x_215; 
lean_ctor_set(x_4, 3, x_213);
lean_ctor_set(x_4, 0, x_210);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_211);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_208);
lean_ctor_set(x_215, 2, x_209);
lean_ctor_set(x_215, 3, x_4);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
return x_215;
}
else
{
uint8_t x_216; 
x_216 = lean_ctor_get_uint8(x_213, sizeof(void*)*4);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_213, 0);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_213, 3);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_213, 2);
lean_inc(x_220);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_221 = x_213;
} else {
 lean_dec_ref(x_213);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 4, 1);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_219);
lean_ctor_set(x_222, 2, x_220);
lean_ctor_set(x_222, 3, x_218);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_216);
lean_ctor_set(x_4, 3, x_222);
lean_ctor_set(x_4, 0, x_210);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_211);
x_223 = 0;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_212);
lean_ctor_set(x_224, 1, x_208);
lean_ctor_set(x_224, 2, x_209);
lean_ctor_set(x_224, 3, x_4);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
return x_224;
}
else
{
uint8_t x_225; 
x_225 = lean_ctor_get_uint8(x_218, sizeof(void*)*4);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; 
x_226 = lean_ctor_get(x_213, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_213, 2);
lean_inc(x_227);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_228 = x_213;
} else {
 lean_dec_ref(x_213);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_218, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_218, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_218, 3);
lean_inc(x_232);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 x_233 = x_218;
} else {
 lean_dec_ref(x_218);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 4, 1);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_210);
lean_ctor_set(x_234, 1, x_23);
lean_ctor_set(x_234, 2, x_24);
lean_ctor_set(x_234, 3, x_217);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_211);
if (lean_is_scalar(x_228)) {
 x_235 = lean_alloc_ctor(1, 4, 1);
} else {
 x_235 = x_228;
}
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_230);
lean_ctor_set(x_235, 2, x_231);
lean_ctor_set(x_235, 3, x_232);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_211);
x_236 = 0;
lean_ctor_set(x_4, 3, x_235);
lean_ctor_set(x_4, 2, x_227);
lean_ctor_set(x_4, 1, x_226);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_236);
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_212);
lean_ctor_set(x_237, 1, x_208);
lean_ctor_set(x_237, 2, x_209);
lean_ctor_set(x_237, 3, x_4);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
lean_free_object(x_4);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 x_238 = x_218;
} else {
 lean_dec_ref(x_218);
 x_238 = lean_box(0);
}
lean_inc(x_213);
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 4, 1);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_210);
lean_ctor_set(x_239, 1, x_23);
lean_ctor_set(x_239, 2, x_24);
lean_ctor_set(x_239, 3, x_213);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_240 = x_213;
} else {
 lean_dec_ref(x_213);
 x_240 = lean_box(0);
}
lean_ctor_set_uint8(x_239, sizeof(void*)*4, x_211);
x_241 = 0;
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(1, 4, 1);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_212);
lean_ctor_set(x_242, 1, x_208);
lean_ctor_set(x_242, 2, x_209);
lean_ctor_set(x_242, 3, x_239);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
return x_242;
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_217, sizeof(void*)*4);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; 
x_244 = lean_ctor_get(x_213, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_213, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_213, 3);
lean_inc(x_246);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_247 = x_213;
} else {
 lean_dec_ref(x_213);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_217, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_217, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_217, 2);
lean_inc(x_250);
x_251 = lean_ctor_get(x_217, 3);
lean_inc(x_251);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_252 = x_217;
} else {
 lean_dec_ref(x_217);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 4, 1);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_210);
lean_ctor_set(x_253, 1, x_23);
lean_ctor_set(x_253, 2, x_24);
lean_ctor_set(x_253, 3, x_248);
lean_ctor_set_uint8(x_253, sizeof(void*)*4, x_211);
if (lean_is_scalar(x_247)) {
 x_254 = lean_alloc_ctor(1, 4, 1);
} else {
 x_254 = x_247;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_244);
lean_ctor_set(x_254, 2, x_245);
lean_ctor_set(x_254, 3, x_246);
lean_ctor_set_uint8(x_254, sizeof(void*)*4, x_211);
x_255 = 0;
lean_ctor_set(x_4, 3, x_254);
lean_ctor_set(x_4, 2, x_250);
lean_ctor_set(x_4, 1, x_249);
lean_ctor_set(x_4, 0, x_253);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_255);
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_212);
lean_ctor_set(x_256, 1, x_208);
lean_ctor_set(x_256, 2, x_209);
lean_ctor_set(x_256, 3, x_4);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
return x_256;
}
else
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_213, 3);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; 
lean_free_object(x_4);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_258 = x_217;
} else {
 lean_dec_ref(x_217);
 x_258 = lean_box(0);
}
lean_inc(x_213);
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_210);
lean_ctor_set(x_259, 1, x_23);
lean_ctor_set(x_259, 2, x_24);
lean_ctor_set(x_259, 3, x_213);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_260 = x_213;
} else {
 lean_dec_ref(x_213);
 x_260 = lean_box(0);
}
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_211);
x_261 = 0;
if (lean_is_scalar(x_260)) {
 x_262 = lean_alloc_ctor(1, 4, 1);
} else {
 x_262 = x_260;
}
lean_ctor_set(x_262, 0, x_212);
lean_ctor_set(x_262, 1, x_208);
lean_ctor_set(x_262, 2, x_209);
lean_ctor_set(x_262, 3, x_259);
lean_ctor_set_uint8(x_262, sizeof(void*)*4, x_261);
return x_262;
}
else
{
uint8_t x_263; 
x_263 = lean_ctor_get_uint8(x_257, sizeof(void*)*4);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_264 = lean_ctor_get(x_213, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_213, 2);
lean_inc(x_265);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_266 = x_213;
} else {
 lean_dec_ref(x_213);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_257, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_257, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_257, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_257, 3);
lean_inc(x_270);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 x_271 = x_257;
} else {
 lean_dec_ref(x_257);
 x_271 = lean_box(0);
}
lean_inc(x_217);
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 4, 1);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_210);
lean_ctor_set(x_272, 1, x_23);
lean_ctor_set(x_272, 2, x_24);
lean_ctor_set(x_272, 3, x_217);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_273 = x_217;
} else {
 lean_dec_ref(x_217);
 x_273 = lean_box(0);
}
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_211);
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 4, 1);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_268);
lean_ctor_set(x_274, 2, x_269);
lean_ctor_set(x_274, 3, x_270);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_211);
x_275 = 0;
if (lean_is_scalar(x_266)) {
 x_276 = lean_alloc_ctor(1, 4, 1);
} else {
 x_276 = x_266;
}
lean_ctor_set(x_276, 0, x_272);
lean_ctor_set(x_276, 1, x_264);
lean_ctor_set(x_276, 2, x_265);
lean_ctor_set(x_276, 3, x_274);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_275);
lean_ctor_set(x_4, 3, x_276);
lean_ctor_set(x_4, 2, x_209);
lean_ctor_set(x_4, 1, x_208);
lean_ctor_set(x_4, 0, x_212);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_275);
return x_4;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_277 = lean_ctor_get(x_213, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_213, 2);
lean_inc(x_278);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 x_279 = x_213;
} else {
 lean_dec_ref(x_213);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_217, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_217, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_217, 2);
lean_inc(x_282);
x_283 = lean_ctor_get(x_217, 3);
lean_inc(x_283);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_284 = x_217;
} else {
 lean_dec_ref(x_217);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_281);
lean_ctor_set(x_285, 2, x_282);
lean_ctor_set(x_285, 3, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_263);
if (lean_is_scalar(x_279)) {
 x_286 = lean_alloc_ctor(1, 4, 1);
} else {
 x_286 = x_279;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_277);
lean_ctor_set(x_286, 2, x_278);
lean_ctor_set(x_286, 3, x_257);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_216);
lean_ctor_set(x_4, 3, x_286);
lean_ctor_set(x_4, 0, x_210);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_211);
x_287 = 0;
x_288 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_288, 0, x_212);
lean_ctor_set(x_288, 1, x_208);
lean_ctor_set(x_288, 2, x_209);
lean_ctor_set(x_288, 3, x_4);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_287);
return x_288;
}
}
}
}
}
else
{
uint8_t x_289; lean_object* x_290; 
lean_ctor_set(x_4, 3, x_213);
lean_ctor_set(x_4, 0, x_210);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_211);
x_289 = 0;
x_290 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_290, 0, x_212);
lean_ctor_set(x_290, 1, x_208);
lean_ctor_set(x_290, 2, x_209);
lean_ctor_set(x_290, 3, x_4);
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_289);
return x_290;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; 
x_291 = lean_ctor_get(x_4, 1);
x_292 = lean_ctor_get(x_4, 2);
x_293 = lean_ctor_get(x_4, 3);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_4);
x_294 = lean_ctor_get(x_8, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_8, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_8, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_8, 3);
lean_inc(x_297);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_298 = x_8;
} else {
 lean_dec_ref(x_8);
 x_298 = lean_box(0);
}
x_299 = 1;
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_1);
lean_ctor_set(x_300, 1, x_2);
lean_ctor_set(x_300, 2, x_3);
lean_ctor_set(x_300, 3, x_294);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_299);
x_301 = l_Lean_RBNode_setRed___rarg(x_293);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_302 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_302, 0, x_297);
lean_ctor_set(x_302, 1, x_291);
lean_ctor_set(x_302, 2, x_292);
lean_ctor_set(x_302, 3, x_301);
lean_ctor_set_uint8(x_302, sizeof(void*)*4, x_299);
x_303 = 0;
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_295);
lean_ctor_set(x_304, 2, x_296);
lean_ctor_set(x_304, 3, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_303);
return x_304;
}
else
{
uint8_t x_305; 
x_305 = lean_ctor_get_uint8(x_301, sizeof(void*)*4);
if (x_305 == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_301, 0);
lean_inc(x_306);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_301, 3);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_308 = lean_ctor_get(x_301, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_301, 2);
lean_inc(x_309);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_310 = x_301;
} else {
 lean_dec_ref(x_301);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 4, 1);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_308);
lean_ctor_set(x_311, 2, x_309);
lean_ctor_set(x_311, 3, x_307);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_305);
x_312 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_312, 0, x_297);
lean_ctor_set(x_312, 1, x_291);
lean_ctor_set(x_312, 2, x_292);
lean_ctor_set(x_312, 3, x_311);
lean_ctor_set_uint8(x_312, sizeof(void*)*4, x_299);
x_313 = 0;
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_300);
lean_ctor_set(x_314, 1, x_295);
lean_ctor_set(x_314, 2, x_296);
lean_ctor_set(x_314, 3, x_312);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_313);
return x_314;
}
else
{
uint8_t x_315; 
x_315 = lean_ctor_get_uint8(x_307, sizeof(void*)*4);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; 
x_316 = lean_ctor_get(x_301, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_301, 2);
lean_inc(x_317);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_318 = x_301;
} else {
 lean_dec_ref(x_301);
 x_318 = lean_box(0);
}
x_319 = lean_ctor_get(x_307, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_307, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_307, 2);
lean_inc(x_321);
x_322 = lean_ctor_get(x_307, 3);
lean_inc(x_322);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 lean_ctor_release(x_307, 2);
 lean_ctor_release(x_307, 3);
 x_323 = x_307;
} else {
 lean_dec_ref(x_307);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 4, 1);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_297);
lean_ctor_set(x_324, 1, x_291);
lean_ctor_set(x_324, 2, x_292);
lean_ctor_set(x_324, 3, x_306);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_299);
if (lean_is_scalar(x_318)) {
 x_325 = lean_alloc_ctor(1, 4, 1);
} else {
 x_325 = x_318;
}
lean_ctor_set(x_325, 0, x_319);
lean_ctor_set(x_325, 1, x_320);
lean_ctor_set(x_325, 2, x_321);
lean_ctor_set(x_325, 3, x_322);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_299);
x_326 = 0;
x_327 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_316);
lean_ctor_set(x_327, 2, x_317);
lean_ctor_set(x_327, 3, x_325);
lean_ctor_set_uint8(x_327, sizeof(void*)*4, x_326);
x_328 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_328, 0, x_300);
lean_ctor_set(x_328, 1, x_295);
lean_ctor_set(x_328, 2, x_296);
lean_ctor_set(x_328, 3, x_327);
lean_ctor_set_uint8(x_328, sizeof(void*)*4, x_326);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; 
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 lean_ctor_release(x_307, 2);
 lean_ctor_release(x_307, 3);
 x_329 = x_307;
} else {
 lean_dec_ref(x_307);
 x_329 = lean_box(0);
}
lean_inc(x_301);
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 4, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_297);
lean_ctor_set(x_330, 1, x_291);
lean_ctor_set(x_330, 2, x_292);
lean_ctor_set(x_330, 3, x_301);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_331 = x_301;
} else {
 lean_dec_ref(x_301);
 x_331 = lean_box(0);
}
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_299);
x_332 = 0;
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_300);
lean_ctor_set(x_333, 1, x_295);
lean_ctor_set(x_333, 2, x_296);
lean_ctor_set(x_333, 3, x_330);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
return x_333;
}
}
}
else
{
uint8_t x_334; 
x_334 = lean_ctor_get_uint8(x_306, sizeof(void*)*4);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; 
x_335 = lean_ctor_get(x_301, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_301, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_301, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_338 = x_301;
} else {
 lean_dec_ref(x_301);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_306, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_306, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_306, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_306, 3);
lean_inc(x_342);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 x_343 = x_306;
} else {
 lean_dec_ref(x_306);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 4, 1);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_297);
lean_ctor_set(x_344, 1, x_291);
lean_ctor_set(x_344, 2, x_292);
lean_ctor_set(x_344, 3, x_339);
lean_ctor_set_uint8(x_344, sizeof(void*)*4, x_299);
if (lean_is_scalar(x_338)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_338;
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_335);
lean_ctor_set(x_345, 2, x_336);
lean_ctor_set(x_345, 3, x_337);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_299);
x_346 = 0;
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_340);
lean_ctor_set(x_347, 2, x_341);
lean_ctor_set(x_347, 3, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_300);
lean_ctor_set(x_348, 1, x_295);
lean_ctor_set(x_348, 2, x_296);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_346);
return x_348;
}
else
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_301, 3);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; 
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 x_350 = x_306;
} else {
 lean_dec_ref(x_306);
 x_350 = lean_box(0);
}
lean_inc(x_301);
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 4, 1);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_297);
lean_ctor_set(x_351, 1, x_291);
lean_ctor_set(x_351, 2, x_292);
lean_ctor_set(x_351, 3, x_301);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_352 = x_301;
} else {
 lean_dec_ref(x_301);
 x_352 = lean_box(0);
}
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_353 = 0;
if (lean_is_scalar(x_352)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_352;
}
lean_ctor_set(x_354, 0, x_300);
lean_ctor_set(x_354, 1, x_295);
lean_ctor_set(x_354, 2, x_296);
lean_ctor_set(x_354, 3, x_351);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_353);
return x_354;
}
else
{
uint8_t x_355; 
x_355 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; 
x_356 = lean_ctor_get(x_301, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_301, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_358 = x_301;
} else {
 lean_dec_ref(x_301);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_349, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_349, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_349, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_363 = x_349;
} else {
 lean_dec_ref(x_349);
 x_363 = lean_box(0);
}
lean_inc(x_306);
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 4, 1);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_297);
lean_ctor_set(x_364, 1, x_291);
lean_ctor_set(x_364, 2, x_292);
lean_ctor_set(x_364, 3, x_306);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 x_365 = x_306;
} else {
 lean_dec_ref(x_306);
 x_365 = lean_box(0);
}
lean_ctor_set_uint8(x_364, sizeof(void*)*4, x_299);
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 4, 1);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_359);
lean_ctor_set(x_366, 1, x_360);
lean_ctor_set(x_366, 2, x_361);
lean_ctor_set(x_366, 3, x_362);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_299);
x_367 = 0;
if (lean_is_scalar(x_358)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_358;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_356);
lean_ctor_set(x_368, 2, x_357);
lean_ctor_set(x_368, 3, x_366);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_367);
x_369 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_369, 0, x_300);
lean_ctor_set(x_369, 1, x_295);
lean_ctor_set(x_369, 2, x_296);
lean_ctor_set(x_369, 3, x_368);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_367);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; 
x_370 = lean_ctor_get(x_301, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_301, 2);
lean_inc(x_371);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 lean_ctor_release(x_301, 2);
 lean_ctor_release(x_301, 3);
 x_372 = x_301;
} else {
 lean_dec_ref(x_301);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_306, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_306, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_306, 2);
lean_inc(x_375);
x_376 = lean_ctor_get(x_306, 3);
lean_inc(x_376);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 x_377 = x_306;
} else {
 lean_dec_ref(x_306);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_355);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(1, 4, 1);
} else {
 x_379 = x_372;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_370);
lean_ctor_set(x_379, 2, x_371);
lean_ctor_set(x_379, 3, x_349);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_305);
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_297);
lean_ctor_set(x_380, 1, x_291);
lean_ctor_set(x_380, 2, x_292);
lean_ctor_set(x_380, 3, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_299);
x_381 = 0;
x_382 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_382, 0, x_300);
lean_ctor_set(x_382, 1, x_295);
lean_ctor_set(x_382, 2, x_296);
lean_ctor_set(x_382, 3, x_380);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_381);
return x_382;
}
}
}
}
}
else
{
lean_object* x_383; uint8_t x_384; lean_object* x_385; 
x_383 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_383, 0, x_297);
lean_ctor_set(x_383, 1, x_291);
lean_ctor_set(x_383, 2, x_292);
lean_ctor_set(x_383, 3, x_301);
lean_ctor_set_uint8(x_383, sizeof(void*)*4, x_299);
x_384 = 0;
x_385 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_385, 0, x_300);
lean_ctor_set(x_385, 1, x_295);
lean_ctor_set(x_385, 2, x_296);
lean_ctor_set(x_385, 3, x_383);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
return x_385;
}
}
}
}
}
}
else
{
uint8_t x_386; 
x_386 = !lean_is_exclusive(x_4);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_387 = lean_ctor_get(x_4, 0);
x_388 = lean_ctor_get(x_4, 1);
x_389 = lean_ctor_get(x_4, 2);
x_390 = lean_ctor_get(x_4, 3);
x_391 = 0;
lean_inc(x_390);
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_391);
if (lean_obj_tag(x_387) == 0)
{
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_392; uint8_t x_393; lean_object* x_394; 
lean_dec(x_4);
x_392 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_388);
lean_ctor_set(x_392, 2, x_389);
lean_ctor_set(x_392, 3, x_390);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
x_393 = 1;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_1);
lean_ctor_set(x_394, 1, x_2);
lean_ctor_set(x_394, 2, x_3);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
uint8_t x_395; 
x_395 = lean_ctor_get_uint8(x_390, sizeof(void*)*4);
if (x_395 == 0)
{
uint8_t x_396; 
lean_dec(x_4);
x_396 = !lean_is_exclusive(x_390);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; 
x_397 = lean_ctor_get(x_390, 0);
x_398 = lean_ctor_get(x_390, 1);
x_399 = lean_ctor_get(x_390, 2);
x_400 = lean_ctor_get(x_390, 3);
x_401 = 1;
lean_ctor_set(x_390, 3, x_387);
lean_ctor_set(x_390, 2, x_3);
lean_ctor_set(x_390, 1, x_2);
lean_ctor_set(x_390, 0, x_1);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_401);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_397);
lean_ctor_set(x_402, 1, x_398);
lean_ctor_set(x_402, 2, x_399);
lean_ctor_set(x_402, 3, x_400);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_401);
x_403 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_403, 0, x_390);
lean_ctor_set(x_403, 1, x_388);
lean_ctor_set(x_403, 2, x_389);
lean_ctor_set(x_403, 3, x_402);
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_391);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_404 = lean_ctor_get(x_390, 0);
x_405 = lean_ctor_get(x_390, 1);
x_406 = lean_ctor_get(x_390, 2);
x_407 = lean_ctor_get(x_390, 3);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_390);
x_408 = 1;
x_409 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_409, 0, x_1);
lean_ctor_set(x_409, 1, x_2);
lean_ctor_set(x_409, 2, x_3);
lean_ctor_set(x_409, 3, x_387);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_408);
x_410 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_410, 0, x_404);
lean_ctor_set(x_410, 1, x_405);
lean_ctor_set(x_410, 2, x_406);
lean_ctor_set(x_410, 3, x_407);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_408);
x_411 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_388);
lean_ctor_set(x_411, 2, x_389);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_391);
return x_411;
}
}
else
{
uint8_t x_412; 
lean_dec(x_389);
lean_dec(x_388);
x_412 = !lean_is_exclusive(x_390);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_413 = lean_ctor_get(x_390, 3);
lean_dec(x_413);
x_414 = lean_ctor_get(x_390, 2);
lean_dec(x_414);
x_415 = lean_ctor_get(x_390, 1);
lean_dec(x_415);
x_416 = lean_ctor_get(x_390, 0);
lean_dec(x_416);
x_417 = 1;
lean_ctor_set(x_390, 3, x_4);
lean_ctor_set(x_390, 2, x_3);
lean_ctor_set(x_390, 1, x_2);
lean_ctor_set(x_390, 0, x_1);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_417);
return x_390;
}
else
{
uint8_t x_418; lean_object* x_419; 
lean_dec(x_390);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_1);
lean_ctor_set(x_419, 1, x_2);
lean_ctor_set(x_419, 2, x_3);
lean_ctor_set(x_419, 3, x_4);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
else
{
uint8_t x_420; 
x_420 = lean_ctor_get_uint8(x_387, sizeof(void*)*4);
if (x_420 == 0)
{
uint8_t x_421; 
lean_dec(x_4);
x_421 = !lean_is_exclusive(x_387);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_387, 0);
x_423 = lean_ctor_get(x_387, 1);
x_424 = lean_ctor_get(x_387, 2);
x_425 = lean_ctor_get(x_387, 3);
x_426 = 1;
lean_ctor_set(x_387, 3, x_422);
lean_ctor_set(x_387, 2, x_3);
lean_ctor_set(x_387, 1, x_2);
lean_ctor_set(x_387, 0, x_1);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_426);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_388);
lean_ctor_set(x_427, 2, x_389);
lean_ctor_set(x_427, 3, x_390);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_426);
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_387);
lean_ctor_set(x_428, 1, x_423);
lean_ctor_set(x_428, 2, x_424);
lean_ctor_set(x_428, 3, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_391);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_429 = lean_ctor_get(x_387, 0);
x_430 = lean_ctor_get(x_387, 1);
x_431 = lean_ctor_get(x_387, 2);
x_432 = lean_ctor_get(x_387, 3);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_387);
x_433 = 1;
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_1);
lean_ctor_set(x_434, 1, x_2);
lean_ctor_set(x_434, 2, x_3);
lean_ctor_set(x_434, 3, x_429);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_433);
x_435 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_388);
lean_ctor_set(x_435, 2, x_389);
lean_ctor_set(x_435, 3, x_390);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_433);
x_436 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_430);
lean_ctor_set(x_436, 2, x_431);
lean_ctor_set(x_436, 3, x_435);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_391);
return x_436;
}
}
else
{
if (lean_obj_tag(x_390) == 0)
{
uint8_t x_437; 
lean_dec(x_389);
lean_dec(x_388);
x_437 = !lean_is_exclusive(x_387);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_438 = lean_ctor_get(x_387, 3);
lean_dec(x_438);
x_439 = lean_ctor_get(x_387, 2);
lean_dec(x_439);
x_440 = lean_ctor_get(x_387, 1);
lean_dec(x_440);
x_441 = lean_ctor_get(x_387, 0);
lean_dec(x_441);
x_442 = 1;
lean_ctor_set(x_387, 3, x_4);
lean_ctor_set(x_387, 2, x_3);
lean_ctor_set(x_387, 1, x_2);
lean_ctor_set(x_387, 0, x_1);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_442);
return x_387;
}
else
{
uint8_t x_443; lean_object* x_444; 
lean_dec(x_387);
x_443 = 1;
x_444 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_444, 0, x_1);
lean_ctor_set(x_444, 1, x_2);
lean_ctor_set(x_444, 2, x_3);
lean_ctor_set(x_444, 3, x_4);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
return x_444;
}
}
else
{
uint8_t x_445; 
lean_dec(x_4);
x_445 = lean_ctor_get_uint8(x_390, sizeof(void*)*4);
if (x_445 == 0)
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_390);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_452; 
x_447 = lean_ctor_get(x_390, 0);
x_448 = lean_ctor_get(x_390, 1);
x_449 = lean_ctor_get(x_390, 2);
x_450 = lean_ctor_get(x_390, 3);
x_451 = 1;
lean_inc(x_387);
lean_ctor_set(x_390, 3, x_387);
lean_ctor_set(x_390, 2, x_3);
lean_ctor_set(x_390, 1, x_2);
lean_ctor_set(x_390, 0, x_1);
x_452 = !lean_is_exclusive(x_387);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_453 = lean_ctor_get(x_387, 3);
lean_dec(x_453);
x_454 = lean_ctor_get(x_387, 2);
lean_dec(x_454);
x_455 = lean_ctor_get(x_387, 1);
lean_dec(x_455);
x_456 = lean_ctor_get(x_387, 0);
lean_dec(x_456);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_451);
lean_ctor_set(x_387, 3, x_450);
lean_ctor_set(x_387, 2, x_449);
lean_ctor_set(x_387, 1, x_448);
lean_ctor_set(x_387, 0, x_447);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_451);
x_457 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_457, 0, x_390);
lean_ctor_set(x_457, 1, x_388);
lean_ctor_set(x_457, 2, x_389);
lean_ctor_set(x_457, 3, x_387);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_391);
return x_457;
}
else
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_387);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_451);
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_447);
lean_ctor_set(x_458, 1, x_448);
lean_ctor_set(x_458, 2, x_449);
lean_ctor_set(x_458, 3, x_450);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_451);
x_459 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_459, 0, x_390);
lean_ctor_set(x_459, 1, x_388);
lean_ctor_set(x_459, 2, x_389);
lean_ctor_set(x_459, 3, x_458);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_391);
return x_459;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_460 = lean_ctor_get(x_390, 0);
x_461 = lean_ctor_get(x_390, 1);
x_462 = lean_ctor_get(x_390, 2);
x_463 = lean_ctor_get(x_390, 3);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_390);
x_464 = 1;
lean_inc(x_387);
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_1);
lean_ctor_set(x_465, 1, x_2);
lean_ctor_set(x_465, 2, x_3);
lean_ctor_set(x_465, 3, x_387);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 lean_ctor_release(x_387, 2);
 lean_ctor_release(x_387, 3);
 x_466 = x_387;
} else {
 lean_dec_ref(x_387);
 x_466 = lean_box(0);
}
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_460);
lean_ctor_set(x_467, 1, x_461);
lean_ctor_set(x_467, 2, x_462);
lean_ctor_set(x_467, 3, x_463);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_464);
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_388);
lean_ctor_set(x_468, 2, x_389);
lean_ctor_set(x_468, 3, x_467);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_391);
return x_468;
}
}
else
{
uint8_t x_469; 
x_469 = !lean_is_exclusive(x_387);
if (x_469 == 0)
{
lean_object* x_470; uint8_t x_471; lean_object* x_472; 
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_445);
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_387);
lean_ctor_set(x_470, 1, x_388);
lean_ctor_set(x_470, 2, x_389);
lean_ctor_set(x_470, 3, x_390);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_391);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_1);
lean_ctor_set(x_472, 1, x_2);
lean_ctor_set(x_472, 2, x_3);
lean_ctor_set(x_472, 3, x_470);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; 
x_473 = lean_ctor_get(x_387, 0);
x_474 = lean_ctor_get(x_387, 1);
x_475 = lean_ctor_get(x_387, 2);
x_476 = lean_ctor_get(x_387, 3);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_387);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_473);
lean_ctor_set(x_477, 1, x_474);
lean_ctor_set(x_477, 2, x_475);
lean_ctor_set(x_477, 3, x_476);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_445);
x_478 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_388);
lean_ctor_set(x_478, 2, x_389);
lean_ctor_set(x_478, 3, x_390);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_391);
x_479 = 1;
x_480 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_480, 0, x_1);
lean_ctor_set(x_480, 1, x_2);
lean_ctor_set(x_480, 2, x_3);
lean_ctor_set(x_480, 3, x_478);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
return x_480;
}
}
}
}
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_481 = lean_ctor_get(x_4, 0);
x_482 = lean_ctor_get(x_4, 1);
x_483 = lean_ctor_get(x_4, 2);
x_484 = lean_ctor_get(x_4, 3);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_4);
x_485 = 0;
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_482);
lean_ctor_set(x_486, 2, x_483);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
if (lean_obj_tag(x_481) == 0)
{
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_487; uint8_t x_488; lean_object* x_489; 
lean_dec(x_486);
x_487 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_482);
lean_ctor_set(x_487, 2, x_483);
lean_ctor_set(x_487, 3, x_484);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_485);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_1);
lean_ctor_set(x_489, 1, x_2);
lean_ctor_set(x_489, 2, x_3);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_484, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_486);
x_491 = lean_ctor_get(x_484, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_484, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_484, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_484, 3);
lean_inc(x_494);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 lean_ctor_release(x_484, 2);
 lean_ctor_release(x_484, 3);
 x_495 = x_484;
} else {
 lean_dec_ref(x_484);
 x_495 = lean_box(0);
}
x_496 = 1;
if (lean_is_scalar(x_495)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_495;
}
lean_ctor_set(x_497, 0, x_1);
lean_ctor_set(x_497, 1, x_2);
lean_ctor_set(x_497, 2, x_3);
lean_ctor_set(x_497, 3, x_481);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_491);
lean_ctor_set(x_498, 1, x_492);
lean_ctor_set(x_498, 2, x_493);
lean_ctor_set(x_498, 3, x_494);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_496);
x_499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_482);
lean_ctor_set(x_499, 2, x_483);
lean_ctor_set(x_499, 3, x_498);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_485);
return x_499;
}
else
{
lean_object* x_500; uint8_t x_501; lean_object* x_502; 
lean_dec(x_483);
lean_dec(x_482);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 lean_ctor_release(x_484, 2);
 lean_ctor_release(x_484, 3);
 x_500 = x_484;
} else {
 lean_dec_ref(x_484);
 x_500 = lean_box(0);
}
x_501 = 1;
if (lean_is_scalar(x_500)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_500;
}
lean_ctor_set(x_502, 0, x_1);
lean_ctor_set(x_502, 1, x_2);
lean_ctor_set(x_502, 2, x_3);
lean_ctor_set(x_502, 3, x_486);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_501);
return x_502;
}
}
}
else
{
uint8_t x_503; 
x_503 = lean_ctor_get_uint8(x_481, sizeof(void*)*4);
if (x_503 == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_486);
x_504 = lean_ctor_get(x_481, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_481, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_481, 2);
lean_inc(x_506);
x_507 = lean_ctor_get(x_481, 3);
lean_inc(x_507);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 lean_ctor_release(x_481, 2);
 lean_ctor_release(x_481, 3);
 x_508 = x_481;
} else {
 lean_dec_ref(x_481);
 x_508 = lean_box(0);
}
x_509 = 1;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_1);
lean_ctor_set(x_510, 1, x_2);
lean_ctor_set(x_510, 2, x_3);
lean_ctor_set(x_510, 3, x_504);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_511, 0, x_507);
lean_ctor_set(x_511, 1, x_482);
lean_ctor_set(x_511, 2, x_483);
lean_ctor_set(x_511, 3, x_484);
lean_ctor_set_uint8(x_511, sizeof(void*)*4, x_509);
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_505);
lean_ctor_set(x_512, 2, x_506);
lean_ctor_set(x_512, 3, x_511);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_485);
return x_512;
}
else
{
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_513; uint8_t x_514; lean_object* x_515; 
lean_dec(x_483);
lean_dec(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 lean_ctor_release(x_481, 2);
 lean_ctor_release(x_481, 3);
 x_513 = x_481;
} else {
 lean_dec_ref(x_481);
 x_513 = lean_box(0);
}
x_514 = 1;
if (lean_is_scalar(x_513)) {
 x_515 = lean_alloc_ctor(1, 4, 1);
} else {
 x_515 = x_513;
}
lean_ctor_set(x_515, 0, x_1);
lean_ctor_set(x_515, 1, x_2);
lean_ctor_set(x_515, 2, x_3);
lean_ctor_set(x_515, 3, x_486);
lean_ctor_set_uint8(x_515, sizeof(void*)*4, x_514);
return x_515;
}
else
{
uint8_t x_516; 
lean_dec(x_486);
x_516 = lean_ctor_get_uint8(x_484, sizeof(void*)*4);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_517 = lean_ctor_get(x_484, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_484, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_484, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_484, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 lean_ctor_release(x_484, 2);
 lean_ctor_release(x_484, 3);
 x_521 = x_484;
} else {
 lean_dec_ref(x_484);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_481);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_1);
lean_ctor_set(x_523, 1, x_2);
lean_ctor_set(x_523, 2, x_3);
lean_ctor_set(x_523, 3, x_481);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 lean_ctor_release(x_481, 2);
 lean_ctor_release(x_481, 3);
 x_524 = x_481;
} else {
 lean_dec_ref(x_481);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_482);
lean_ctor_set(x_526, 2, x_483);
lean_ctor_set(x_526, 3, x_525);
lean_ctor_set_uint8(x_526, sizeof(void*)*4, x_485);
return x_526;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; lean_object* x_535; 
x_527 = lean_ctor_get(x_481, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_481, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_481, 2);
lean_inc(x_529);
x_530 = lean_ctor_get(x_481, 3);
lean_inc(x_530);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 lean_ctor_release(x_481, 2);
 lean_ctor_release(x_481, 3);
 x_531 = x_481;
} else {
 lean_dec_ref(x_481);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 4, 1);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_527);
lean_ctor_set(x_532, 1, x_528);
lean_ctor_set(x_532, 2, x_529);
lean_ctor_set(x_532, 3, x_530);
lean_ctor_set_uint8(x_532, sizeof(void*)*4, x_516);
x_533 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_482);
lean_ctor_set(x_533, 2, x_483);
lean_ctor_set(x_533, 3, x_484);
lean_ctor_set_uint8(x_533, sizeof(void*)*4, x_485);
x_534 = 1;
x_535 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_535, 0, x_1);
lean_ctor_set(x_535, 1, x_2);
lean_ctor_set(x_535, 2, x_3);
lean_ctor_set(x_535, 3, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*4, x_534);
return x_535;
}
}
}
}
}
}
}
}
else
{
uint8_t x_536; 
x_536 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_536 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_537; 
x_537 = !lean_is_exclusive(x_1);
if (x_537 == 0)
{
uint8_t x_538; uint8_t x_539; lean_object* x_540; 
x_538 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_538);
x_539 = 0;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_1);
lean_ctor_set(x_540, 1, x_2);
lean_ctor_set(x_540, 2, x_3);
lean_ctor_set(x_540, 3, x_4);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; 
x_541 = lean_ctor_get(x_1, 0);
x_542 = lean_ctor_get(x_1, 1);
x_543 = lean_ctor_get(x_1, 2);
x_544 = lean_ctor_get(x_1, 3);
lean_inc(x_544);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_1);
x_545 = 1;
x_546 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_546, 0, x_541);
lean_ctor_set(x_546, 1, x_542);
lean_ctor_set(x_546, 2, x_543);
lean_ctor_set(x_546, 3, x_544);
lean_ctor_set_uint8(x_546, sizeof(void*)*4, x_545);
x_547 = 0;
x_548 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_2);
lean_ctor_set(x_548, 2, x_3);
lean_ctor_set(x_548, 3, x_4);
lean_ctor_set_uint8(x_548, sizeof(void*)*4, x_547);
return x_548;
}
}
else
{
uint8_t x_549; 
x_549 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_549 == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_4, 0);
lean_inc(x_550);
if (lean_obj_tag(x_550) == 0)
{
uint8_t x_551; 
x_551 = !lean_is_exclusive(x_1);
if (x_551 == 0)
{
uint8_t x_552; uint8_t x_553; lean_object* x_554; 
x_552 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_552);
x_553 = 0;
x_554 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_554, 0, x_1);
lean_ctor_set(x_554, 1, x_2);
lean_ctor_set(x_554, 2, x_3);
lean_ctor_set(x_554, 3, x_4);
lean_ctor_set_uint8(x_554, sizeof(void*)*4, x_553);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; 
x_555 = lean_ctor_get(x_1, 0);
x_556 = lean_ctor_get(x_1, 1);
x_557 = lean_ctor_get(x_1, 2);
x_558 = lean_ctor_get(x_1, 3);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_1);
x_559 = 1;
x_560 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_560, 0, x_555);
lean_ctor_set(x_560, 1, x_556);
lean_ctor_set(x_560, 2, x_557);
lean_ctor_set(x_560, 3, x_558);
lean_ctor_set_uint8(x_560, sizeof(void*)*4, x_559);
x_561 = 0;
x_562 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_2);
lean_ctor_set(x_562, 2, x_3);
lean_ctor_set(x_562, 3, x_4);
lean_ctor_set_uint8(x_562, sizeof(void*)*4, x_561);
return x_562;
}
}
else
{
uint8_t x_563; 
x_563 = lean_ctor_get_uint8(x_550, sizeof(void*)*4);
if (x_563 == 0)
{
uint8_t x_564; 
x_564 = !lean_is_exclusive(x_1);
if (x_564 == 0)
{
uint8_t x_565; 
x_565 = !lean_is_exclusive(x_4);
if (x_565 == 0)
{
lean_object* x_566; uint8_t x_567; uint8_t x_568; lean_object* x_569; 
x_566 = lean_ctor_get(x_4, 0);
lean_dec(x_566);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_563);
x_567 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_567);
x_568 = 0;
x_569 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_569, 0, x_1);
lean_ctor_set(x_569, 1, x_2);
lean_ctor_set(x_569, 2, x_3);
lean_ctor_set(x_569, 3, x_4);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_568);
return x_569;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; uint8_t x_575; lean_object* x_576; 
x_570 = lean_ctor_get(x_4, 1);
x_571 = lean_ctor_get(x_4, 2);
x_572 = lean_ctor_get(x_4, 3);
lean_inc(x_572);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_4);
x_573 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_573, 0, x_550);
lean_ctor_set(x_573, 1, x_570);
lean_ctor_set(x_573, 2, x_571);
lean_ctor_set(x_573, 3, x_572);
lean_ctor_set_uint8(x_573, sizeof(void*)*4, x_563);
x_574 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_574);
x_575 = 0;
x_576 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_576, 0, x_1);
lean_ctor_set(x_576, 1, x_2);
lean_ctor_set(x_576, 2, x_3);
lean_ctor_set(x_576, 3, x_573);
lean_ctor_set_uint8(x_576, sizeof(void*)*4, x_575);
return x_576;
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; lean_object* x_587; uint8_t x_588; lean_object* x_589; 
x_577 = lean_ctor_get(x_1, 0);
x_578 = lean_ctor_get(x_1, 1);
x_579 = lean_ctor_get(x_1, 2);
x_580 = lean_ctor_get(x_1, 3);
lean_inc(x_580);
lean_inc(x_579);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_1);
x_581 = lean_ctor_get(x_4, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_4, 2);
lean_inc(x_582);
x_583 = lean_ctor_get(x_4, 3);
lean_inc(x_583);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_584 = x_4;
} else {
 lean_dec_ref(x_4);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 4, 1);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_550);
lean_ctor_set(x_585, 1, x_581);
lean_ctor_set(x_585, 2, x_582);
lean_ctor_set(x_585, 3, x_583);
lean_ctor_set_uint8(x_585, sizeof(void*)*4, x_563);
x_586 = 1;
x_587 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_587, 0, x_577);
lean_ctor_set(x_587, 1, x_578);
lean_ctor_set(x_587, 2, x_579);
lean_ctor_set(x_587, 3, x_580);
lean_ctor_set_uint8(x_587, sizeof(void*)*4, x_586);
x_588 = 0;
x_589 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_2);
lean_ctor_set(x_589, 2, x_3);
lean_ctor_set(x_589, 3, x_585);
lean_ctor_set_uint8(x_589, sizeof(void*)*4, x_588);
return x_589;
}
}
else
{
uint8_t x_590; 
x_590 = !lean_is_exclusive(x_550);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_591 = lean_ctor_get(x_550, 3);
lean_dec(x_591);
x_592 = lean_ctor_get(x_550, 2);
lean_dec(x_592);
x_593 = lean_ctor_get(x_550, 1);
lean_dec(x_593);
x_594 = lean_ctor_get(x_550, 0);
lean_dec(x_594);
x_595 = !lean_is_exclusive(x_1);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; uint8_t x_601; 
x_596 = lean_ctor_get(x_1, 0);
x_597 = lean_ctor_get(x_1, 1);
x_598 = lean_ctor_get(x_1, 2);
x_599 = lean_ctor_get(x_1, 3);
x_600 = 1;
lean_ctor_set(x_550, 3, x_599);
lean_ctor_set(x_550, 2, x_598);
lean_ctor_set(x_550, 1, x_597);
lean_ctor_set(x_550, 0, x_596);
lean_ctor_set_uint8(x_550, sizeof(void*)*4, x_600);
x_601 = 0;
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_550);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_601);
return x_1;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; uint8_t x_607; lean_object* x_608; 
x_602 = lean_ctor_get(x_1, 0);
x_603 = lean_ctor_get(x_1, 1);
x_604 = lean_ctor_get(x_1, 2);
x_605 = lean_ctor_get(x_1, 3);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_1);
x_606 = 1;
lean_ctor_set(x_550, 3, x_605);
lean_ctor_set(x_550, 2, x_604);
lean_ctor_set(x_550, 1, x_603);
lean_ctor_set(x_550, 0, x_602);
lean_ctor_set_uint8(x_550, sizeof(void*)*4, x_606);
x_607 = 0;
x_608 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_608, 0, x_550);
lean_ctor_set(x_608, 1, x_2);
lean_ctor_set(x_608, 2, x_3);
lean_ctor_set(x_608, 3, x_4);
lean_ctor_set_uint8(x_608, sizeof(void*)*4, x_607);
return x_608;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; uint8_t x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; 
lean_dec(x_550);
x_609 = lean_ctor_get(x_1, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_1, 1);
lean_inc(x_610);
x_611 = lean_ctor_get(x_1, 2);
lean_inc(x_611);
x_612 = lean_ctor_get(x_1, 3);
lean_inc(x_612);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_613 = x_1;
} else {
 lean_dec_ref(x_1);
 x_613 = lean_box(0);
}
x_614 = 1;
x_615 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_615, 0, x_609);
lean_ctor_set(x_615, 1, x_610);
lean_ctor_set(x_615, 2, x_611);
lean_ctor_set(x_615, 3, x_612);
lean_ctor_set_uint8(x_615, sizeof(void*)*4, x_614);
x_616 = 0;
if (lean_is_scalar(x_613)) {
 x_617 = lean_alloc_ctor(1, 4, 1);
} else {
 x_617 = x_613;
}
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_2);
lean_ctor_set(x_617, 2, x_3);
lean_ctor_set(x_617, 3, x_4);
lean_ctor_set_uint8(x_617, sizeof(void*)*4, x_616);
return x_617;
}
}
}
}
else
{
uint8_t x_618; 
x_618 = !lean_is_exclusive(x_1);
if (x_618 == 0)
{
uint8_t x_619; uint8_t x_620; lean_object* x_621; 
x_619 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_619);
x_620 = 0;
x_621 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set(x_621, 1, x_2);
lean_ctor_set(x_621, 2, x_3);
lean_ctor_set(x_621, 3, x_4);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_620);
return x_621;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; lean_object* x_627; uint8_t x_628; lean_object* x_629; 
x_622 = lean_ctor_get(x_1, 0);
x_623 = lean_ctor_get(x_1, 1);
x_624 = lean_ctor_get(x_1, 2);
x_625 = lean_ctor_get(x_1, 3);
lean_inc(x_625);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_1);
x_626 = 1;
x_627 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_627, 0, x_622);
lean_ctor_set(x_627, 1, x_623);
lean_ctor_set(x_627, 2, x_624);
lean_ctor_set(x_627, 3, x_625);
lean_ctor_set_uint8(x_627, sizeof(void*)*4, x_626);
x_628 = 0;
x_629 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_2);
lean_ctor_set(x_629, 2, x_3);
lean_ctor_set(x_629, 3, x_4);
lean_ctor_set_uint8(x_629, sizeof(void*)*4, x_628);
return x_629;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_630; lean_object* x_631; 
x_630 = 0;
x_631 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_631, 0, x_1);
lean_ctor_set(x_631, 1, x_2);
lean_ctor_set(x_631, 2, x_3);
lean_ctor_set(x_631, 3, x_4);
lean_ctor_set_uint8(x_631, sizeof(void*)*4, x_630);
return x_631;
}
else
{
uint8_t x_632; 
x_632 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_632 == 0)
{
lean_object* x_633; 
x_633 = lean_ctor_get(x_4, 0);
lean_inc(x_633);
if (lean_obj_tag(x_633) == 0)
{
uint8_t x_634; lean_object* x_635; 
x_634 = 0;
x_635 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_635, 0, x_1);
lean_ctor_set(x_635, 1, x_2);
lean_ctor_set(x_635, 2, x_3);
lean_ctor_set(x_635, 3, x_4);
lean_ctor_set_uint8(x_635, sizeof(void*)*4, x_634);
return x_635;
}
else
{
uint8_t x_636; 
x_636 = lean_ctor_get_uint8(x_633, sizeof(void*)*4);
if (x_636 == 0)
{
uint8_t x_637; 
x_637 = !lean_is_exclusive(x_4);
if (x_637 == 0)
{
lean_object* x_638; uint8_t x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_4, 0);
lean_dec(x_638);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_636);
x_639 = 0;
x_640 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_640, 0, x_1);
lean_ctor_set(x_640, 1, x_2);
lean_ctor_set(x_640, 2, x_3);
lean_ctor_set(x_640, 3, x_4);
lean_ctor_set_uint8(x_640, sizeof(void*)*4, x_639);
return x_640;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; 
x_641 = lean_ctor_get(x_4, 1);
x_642 = lean_ctor_get(x_4, 2);
x_643 = lean_ctor_get(x_4, 3);
lean_inc(x_643);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_4);
x_644 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_644, 0, x_633);
lean_ctor_set(x_644, 1, x_641);
lean_ctor_set(x_644, 2, x_642);
lean_ctor_set(x_644, 3, x_643);
lean_ctor_set_uint8(x_644, sizeof(void*)*4, x_636);
x_645 = 0;
x_646 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_646, 0, x_1);
lean_ctor_set(x_646, 1, x_2);
lean_ctor_set(x_646, 2, x_3);
lean_ctor_set(x_646, 3, x_644);
lean_ctor_set_uint8(x_646, sizeof(void*)*4, x_645);
return x_646;
}
}
else
{
uint8_t x_647; 
x_647 = !lean_is_exclusive(x_1);
if (x_647 == 0)
{
uint8_t x_648; 
x_648 = !lean_is_exclusive(x_4);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
x_649 = lean_ctor_get(x_1, 0);
x_650 = lean_ctor_get(x_1, 1);
x_651 = lean_ctor_get(x_1, 2);
x_652 = lean_ctor_get(x_1, 3);
x_653 = lean_ctor_get(x_4, 1);
x_654 = lean_ctor_get(x_4, 2);
x_655 = lean_ctor_get(x_4, 3);
x_656 = lean_ctor_get(x_4, 0);
lean_dec(x_656);
x_657 = !lean_is_exclusive(x_633);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; lean_object* x_663; 
x_658 = lean_ctor_get(x_633, 0);
x_659 = lean_ctor_get(x_633, 1);
x_660 = lean_ctor_get(x_633, 2);
x_661 = lean_ctor_get(x_633, 3);
lean_ctor_set(x_633, 3, x_652);
lean_ctor_set(x_633, 2, x_651);
lean_ctor_set(x_633, 1, x_650);
lean_ctor_set(x_633, 0, x_649);
x_662 = 1;
lean_ctor_set(x_4, 3, x_658);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_662);
x_663 = l_Lean_RBNode_setRed___rarg(x_655);
if (lean_obj_tag(x_663) == 0)
{
uint8_t x_664; lean_object* x_665; 
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_664 = 0;
x_665 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_665, 0, x_4);
lean_ctor_set(x_665, 1, x_659);
lean_ctor_set(x_665, 2, x_660);
lean_ctor_set(x_665, 3, x_1);
lean_ctor_set_uint8(x_665, sizeof(void*)*4, x_664);
return x_665;
}
else
{
uint8_t x_666; 
x_666 = lean_ctor_get_uint8(x_663, sizeof(void*)*4);
if (x_666 == 0)
{
lean_object* x_667; 
x_667 = lean_ctor_get(x_663, 0);
lean_inc(x_667);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; 
x_668 = lean_ctor_get(x_663, 3);
lean_inc(x_668);
if (lean_obj_tag(x_668) == 0)
{
uint8_t x_669; 
x_669 = !lean_is_exclusive(x_663);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; uint8_t x_672; lean_object* x_673; 
x_670 = lean_ctor_get(x_663, 3);
lean_dec(x_670);
x_671 = lean_ctor_get(x_663, 0);
lean_dec(x_671);
lean_ctor_set(x_663, 0, x_668);
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_672 = 0;
x_673 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_673, 0, x_4);
lean_ctor_set(x_673, 1, x_659);
lean_ctor_set(x_673, 2, x_660);
lean_ctor_set(x_673, 3, x_1);
lean_ctor_set_uint8(x_673, sizeof(void*)*4, x_672);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; lean_object* x_678; 
x_674 = lean_ctor_get(x_663, 1);
x_675 = lean_ctor_get(x_663, 2);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_663);
x_676 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_676, 0, x_668);
lean_ctor_set(x_676, 1, x_674);
lean_ctor_set(x_676, 2, x_675);
lean_ctor_set(x_676, 3, x_668);
lean_ctor_set_uint8(x_676, sizeof(void*)*4, x_666);
lean_ctor_set(x_1, 3, x_676);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_677 = 0;
x_678 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_678, 0, x_4);
lean_ctor_set(x_678, 1, x_659);
lean_ctor_set(x_678, 2, x_660);
lean_ctor_set(x_678, 3, x_1);
lean_ctor_set_uint8(x_678, sizeof(void*)*4, x_677);
return x_678;
}
}
else
{
uint8_t x_679; 
x_679 = lean_ctor_get_uint8(x_668, sizeof(void*)*4);
if (x_679 == 0)
{
uint8_t x_680; 
x_680 = !lean_is_exclusive(x_663);
if (x_680 == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; 
x_681 = lean_ctor_get(x_663, 1);
x_682 = lean_ctor_get(x_663, 2);
x_683 = lean_ctor_get(x_663, 3);
lean_dec(x_683);
x_684 = lean_ctor_get(x_663, 0);
lean_dec(x_684);
x_685 = !lean_is_exclusive(x_668);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; lean_object* x_691; 
x_686 = lean_ctor_get(x_668, 0);
x_687 = lean_ctor_get(x_668, 1);
x_688 = lean_ctor_get(x_668, 2);
x_689 = lean_ctor_get(x_668, 3);
lean_ctor_set(x_668, 3, x_667);
lean_ctor_set(x_668, 2, x_654);
lean_ctor_set(x_668, 1, x_653);
lean_ctor_set(x_668, 0, x_661);
lean_ctor_set_uint8(x_668, sizeof(void*)*4, x_662);
lean_ctor_set(x_663, 3, x_689);
lean_ctor_set(x_663, 2, x_688);
lean_ctor_set(x_663, 1, x_687);
lean_ctor_set(x_663, 0, x_686);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_662);
x_690 = 0;
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_682);
lean_ctor_set(x_1, 1, x_681);
lean_ctor_set(x_1, 0, x_668);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_690);
x_691 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_691, 0, x_4);
lean_ctor_set(x_691, 1, x_659);
lean_ctor_set(x_691, 2, x_660);
lean_ctor_set(x_691, 3, x_1);
lean_ctor_set_uint8(x_691, sizeof(void*)*4, x_690);
return x_691;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; lean_object* x_698; 
x_692 = lean_ctor_get(x_668, 0);
x_693 = lean_ctor_get(x_668, 1);
x_694 = lean_ctor_get(x_668, 2);
x_695 = lean_ctor_get(x_668, 3);
lean_inc(x_695);
lean_inc(x_694);
lean_inc(x_693);
lean_inc(x_692);
lean_dec(x_668);
x_696 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_696, 0, x_661);
lean_ctor_set(x_696, 1, x_653);
lean_ctor_set(x_696, 2, x_654);
lean_ctor_set(x_696, 3, x_667);
lean_ctor_set_uint8(x_696, sizeof(void*)*4, x_662);
lean_ctor_set(x_663, 3, x_695);
lean_ctor_set(x_663, 2, x_694);
lean_ctor_set(x_663, 1, x_693);
lean_ctor_set(x_663, 0, x_692);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_662);
x_697 = 0;
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_682);
lean_ctor_set(x_1, 1, x_681);
lean_ctor_set(x_1, 0, x_696);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_697);
x_698 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_698, 0, x_4);
lean_ctor_set(x_698, 1, x_659);
lean_ctor_set(x_698, 2, x_660);
lean_ctor_set(x_698, 3, x_1);
lean_ctor_set_uint8(x_698, sizeof(void*)*4, x_697);
return x_698;
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; lean_object* x_709; 
x_699 = lean_ctor_get(x_663, 1);
x_700 = lean_ctor_get(x_663, 2);
lean_inc(x_700);
lean_inc(x_699);
lean_dec(x_663);
x_701 = lean_ctor_get(x_668, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_668, 1);
lean_inc(x_702);
x_703 = lean_ctor_get(x_668, 2);
lean_inc(x_703);
x_704 = lean_ctor_get(x_668, 3);
lean_inc(x_704);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 lean_ctor_release(x_668, 2);
 lean_ctor_release(x_668, 3);
 x_705 = x_668;
} else {
 lean_dec_ref(x_668);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 4, 1);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_661);
lean_ctor_set(x_706, 1, x_653);
lean_ctor_set(x_706, 2, x_654);
lean_ctor_set(x_706, 3, x_667);
lean_ctor_set_uint8(x_706, sizeof(void*)*4, x_662);
x_707 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_707, 0, x_701);
lean_ctor_set(x_707, 1, x_702);
lean_ctor_set(x_707, 2, x_703);
lean_ctor_set(x_707, 3, x_704);
lean_ctor_set_uint8(x_707, sizeof(void*)*4, x_662);
x_708 = 0;
lean_ctor_set(x_1, 3, x_707);
lean_ctor_set(x_1, 2, x_700);
lean_ctor_set(x_1, 1, x_699);
lean_ctor_set(x_1, 0, x_706);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_708);
x_709 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_709, 0, x_4);
lean_ctor_set(x_709, 1, x_659);
lean_ctor_set(x_709, 2, x_660);
lean_ctor_set(x_709, 3, x_1);
lean_ctor_set_uint8(x_709, sizeof(void*)*4, x_708);
return x_709;
}
}
else
{
uint8_t x_710; 
lean_free_object(x_1);
x_710 = !lean_is_exclusive(x_668);
if (x_710 == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; 
x_711 = lean_ctor_get(x_668, 3);
lean_dec(x_711);
x_712 = lean_ctor_get(x_668, 2);
lean_dec(x_712);
x_713 = lean_ctor_get(x_668, 1);
lean_dec(x_713);
x_714 = lean_ctor_get(x_668, 0);
lean_dec(x_714);
lean_inc(x_663);
lean_ctor_set(x_668, 3, x_663);
lean_ctor_set(x_668, 2, x_654);
lean_ctor_set(x_668, 1, x_653);
lean_ctor_set(x_668, 0, x_661);
x_715 = !lean_is_exclusive(x_663);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; 
x_716 = lean_ctor_get(x_663, 3);
lean_dec(x_716);
x_717 = lean_ctor_get(x_663, 2);
lean_dec(x_717);
x_718 = lean_ctor_get(x_663, 1);
lean_dec(x_718);
x_719 = lean_ctor_get(x_663, 0);
lean_dec(x_719);
lean_ctor_set_uint8(x_668, sizeof(void*)*4, x_662);
x_720 = 0;
lean_ctor_set(x_663, 2, x_660);
lean_ctor_set(x_663, 1, x_659);
lean_ctor_set(x_663, 0, x_4);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_720);
return x_663;
}
else
{
uint8_t x_721; lean_object* x_722; 
lean_dec(x_663);
lean_ctor_set_uint8(x_668, sizeof(void*)*4, x_662);
x_721 = 0;
x_722 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_722, 0, x_4);
lean_ctor_set(x_722, 1, x_659);
lean_ctor_set(x_722, 2, x_660);
lean_ctor_set(x_722, 3, x_668);
lean_ctor_set_uint8(x_722, sizeof(void*)*4, x_721);
return x_722;
}
}
else
{
lean_object* x_723; lean_object* x_724; uint8_t x_725; lean_object* x_726; 
lean_dec(x_668);
lean_inc(x_663);
x_723 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_723, 0, x_661);
lean_ctor_set(x_723, 1, x_653);
lean_ctor_set(x_723, 2, x_654);
lean_ctor_set(x_723, 3, x_663);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 lean_ctor_release(x_663, 2);
 lean_ctor_release(x_663, 3);
 x_724 = x_663;
} else {
 lean_dec_ref(x_663);
 x_724 = lean_box(0);
}
lean_ctor_set_uint8(x_723, sizeof(void*)*4, x_662);
x_725 = 0;
if (lean_is_scalar(x_724)) {
 x_726 = lean_alloc_ctor(1, 4, 1);
} else {
 x_726 = x_724;
}
lean_ctor_set(x_726, 0, x_4);
lean_ctor_set(x_726, 1, x_659);
lean_ctor_set(x_726, 2, x_660);
lean_ctor_set(x_726, 3, x_723);
lean_ctor_set_uint8(x_726, sizeof(void*)*4, x_725);
return x_726;
}
}
}
}
else
{
uint8_t x_727; 
x_727 = lean_ctor_get_uint8(x_667, sizeof(void*)*4);
if (x_727 == 0)
{
uint8_t x_728; 
x_728 = !lean_is_exclusive(x_663);
if (x_728 == 0)
{
lean_object* x_729; uint8_t x_730; 
x_729 = lean_ctor_get(x_663, 0);
lean_dec(x_729);
x_730 = !lean_is_exclusive(x_667);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; lean_object* x_736; 
x_731 = lean_ctor_get(x_667, 0);
x_732 = lean_ctor_get(x_667, 1);
x_733 = lean_ctor_get(x_667, 2);
x_734 = lean_ctor_get(x_667, 3);
lean_ctor_set(x_667, 3, x_731);
lean_ctor_set(x_667, 2, x_654);
lean_ctor_set(x_667, 1, x_653);
lean_ctor_set(x_667, 0, x_661);
lean_ctor_set_uint8(x_667, sizeof(void*)*4, x_662);
lean_ctor_set(x_663, 0, x_734);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_662);
x_735 = 0;
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_733);
lean_ctor_set(x_1, 1, x_732);
lean_ctor_set(x_1, 0, x_667);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_735);
x_736 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_736, 0, x_4);
lean_ctor_set(x_736, 1, x_659);
lean_ctor_set(x_736, 2, x_660);
lean_ctor_set(x_736, 3, x_1);
lean_ctor_set_uint8(x_736, sizeof(void*)*4, x_735);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; uint8_t x_742; lean_object* x_743; 
x_737 = lean_ctor_get(x_667, 0);
x_738 = lean_ctor_get(x_667, 1);
x_739 = lean_ctor_get(x_667, 2);
x_740 = lean_ctor_get(x_667, 3);
lean_inc(x_740);
lean_inc(x_739);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_667);
x_741 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_741, 0, x_661);
lean_ctor_set(x_741, 1, x_653);
lean_ctor_set(x_741, 2, x_654);
lean_ctor_set(x_741, 3, x_737);
lean_ctor_set_uint8(x_741, sizeof(void*)*4, x_662);
lean_ctor_set(x_663, 0, x_740);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_662);
x_742 = 0;
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_739);
lean_ctor_set(x_1, 1, x_738);
lean_ctor_set(x_1, 0, x_741);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_742);
x_743 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_743, 0, x_4);
lean_ctor_set(x_743, 1, x_659);
lean_ctor_set(x_743, 2, x_660);
lean_ctor_set(x_743, 3, x_1);
lean_ctor_set_uint8(x_743, sizeof(void*)*4, x_742);
return x_743;
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; uint8_t x_754; lean_object* x_755; 
x_744 = lean_ctor_get(x_663, 1);
x_745 = lean_ctor_get(x_663, 2);
x_746 = lean_ctor_get(x_663, 3);
lean_inc(x_746);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_663);
x_747 = lean_ctor_get(x_667, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_667, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_667, 2);
lean_inc(x_749);
x_750 = lean_ctor_get(x_667, 3);
lean_inc(x_750);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 lean_ctor_release(x_667, 2);
 lean_ctor_release(x_667, 3);
 x_751 = x_667;
} else {
 lean_dec_ref(x_667);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_751)) {
 x_752 = lean_alloc_ctor(1, 4, 1);
} else {
 x_752 = x_751;
}
lean_ctor_set(x_752, 0, x_661);
lean_ctor_set(x_752, 1, x_653);
lean_ctor_set(x_752, 2, x_654);
lean_ctor_set(x_752, 3, x_747);
lean_ctor_set_uint8(x_752, sizeof(void*)*4, x_662);
x_753 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_753, 0, x_750);
lean_ctor_set(x_753, 1, x_744);
lean_ctor_set(x_753, 2, x_745);
lean_ctor_set(x_753, 3, x_746);
lean_ctor_set_uint8(x_753, sizeof(void*)*4, x_662);
x_754 = 0;
lean_ctor_set(x_1, 3, x_753);
lean_ctor_set(x_1, 2, x_749);
lean_ctor_set(x_1, 1, x_748);
lean_ctor_set(x_1, 0, x_752);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_754);
x_755 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_755, 0, x_4);
lean_ctor_set(x_755, 1, x_659);
lean_ctor_set(x_755, 2, x_660);
lean_ctor_set(x_755, 3, x_1);
lean_ctor_set_uint8(x_755, sizeof(void*)*4, x_754);
return x_755;
}
}
else
{
lean_object* x_756; 
x_756 = lean_ctor_get(x_663, 3);
lean_inc(x_756);
if (lean_obj_tag(x_756) == 0)
{
uint8_t x_757; 
lean_free_object(x_1);
x_757 = !lean_is_exclusive(x_667);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; 
x_758 = lean_ctor_get(x_667, 3);
lean_dec(x_758);
x_759 = lean_ctor_get(x_667, 2);
lean_dec(x_759);
x_760 = lean_ctor_get(x_667, 1);
lean_dec(x_760);
x_761 = lean_ctor_get(x_667, 0);
lean_dec(x_761);
lean_inc(x_663);
lean_ctor_set(x_667, 3, x_663);
lean_ctor_set(x_667, 2, x_654);
lean_ctor_set(x_667, 1, x_653);
lean_ctor_set(x_667, 0, x_661);
x_762 = !lean_is_exclusive(x_663);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; 
x_763 = lean_ctor_get(x_663, 3);
lean_dec(x_763);
x_764 = lean_ctor_get(x_663, 2);
lean_dec(x_764);
x_765 = lean_ctor_get(x_663, 1);
lean_dec(x_765);
x_766 = lean_ctor_get(x_663, 0);
lean_dec(x_766);
lean_ctor_set_uint8(x_667, sizeof(void*)*4, x_662);
x_767 = 0;
lean_ctor_set(x_663, 3, x_667);
lean_ctor_set(x_663, 2, x_660);
lean_ctor_set(x_663, 1, x_659);
lean_ctor_set(x_663, 0, x_4);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_767);
return x_663;
}
else
{
uint8_t x_768; lean_object* x_769; 
lean_dec(x_663);
lean_ctor_set_uint8(x_667, sizeof(void*)*4, x_662);
x_768 = 0;
x_769 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_769, 0, x_4);
lean_ctor_set(x_769, 1, x_659);
lean_ctor_set(x_769, 2, x_660);
lean_ctor_set(x_769, 3, x_667);
lean_ctor_set_uint8(x_769, sizeof(void*)*4, x_768);
return x_769;
}
}
else
{
lean_object* x_770; lean_object* x_771; uint8_t x_772; lean_object* x_773; 
lean_dec(x_667);
lean_inc(x_663);
x_770 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_770, 0, x_661);
lean_ctor_set(x_770, 1, x_653);
lean_ctor_set(x_770, 2, x_654);
lean_ctor_set(x_770, 3, x_663);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 lean_ctor_release(x_663, 2);
 lean_ctor_release(x_663, 3);
 x_771 = x_663;
} else {
 lean_dec_ref(x_663);
 x_771 = lean_box(0);
}
lean_ctor_set_uint8(x_770, sizeof(void*)*4, x_662);
x_772 = 0;
if (lean_is_scalar(x_771)) {
 x_773 = lean_alloc_ctor(1, 4, 1);
} else {
 x_773 = x_771;
}
lean_ctor_set(x_773, 0, x_4);
lean_ctor_set(x_773, 1, x_659);
lean_ctor_set(x_773, 2, x_660);
lean_ctor_set(x_773, 3, x_770);
lean_ctor_set_uint8(x_773, sizeof(void*)*4, x_772);
return x_773;
}
}
else
{
uint8_t x_774; 
x_774 = lean_ctor_get_uint8(x_756, sizeof(void*)*4);
if (x_774 == 0)
{
uint8_t x_775; 
x_775 = !lean_is_exclusive(x_663);
if (x_775 == 0)
{
lean_object* x_776; lean_object* x_777; uint8_t x_778; 
x_776 = lean_ctor_get(x_663, 3);
lean_dec(x_776);
x_777 = lean_ctor_get(x_663, 0);
lean_dec(x_777);
x_778 = !lean_is_exclusive(x_756);
if (x_778 == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; uint8_t x_783; 
x_779 = lean_ctor_get(x_756, 0);
x_780 = lean_ctor_get(x_756, 1);
x_781 = lean_ctor_get(x_756, 2);
x_782 = lean_ctor_get(x_756, 3);
lean_inc(x_667);
lean_ctor_set(x_756, 3, x_667);
lean_ctor_set(x_756, 2, x_654);
lean_ctor_set(x_756, 1, x_653);
lean_ctor_set(x_756, 0, x_661);
x_783 = !lean_is_exclusive(x_667);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; 
x_784 = lean_ctor_get(x_667, 3);
lean_dec(x_784);
x_785 = lean_ctor_get(x_667, 2);
lean_dec(x_785);
x_786 = lean_ctor_get(x_667, 1);
lean_dec(x_786);
x_787 = lean_ctor_get(x_667, 0);
lean_dec(x_787);
lean_ctor_set_uint8(x_756, sizeof(void*)*4, x_662);
lean_ctor_set(x_667, 3, x_782);
lean_ctor_set(x_667, 2, x_781);
lean_ctor_set(x_667, 1, x_780);
lean_ctor_set(x_667, 0, x_779);
lean_ctor_set_uint8(x_667, sizeof(void*)*4, x_662);
x_788 = 0;
lean_ctor_set(x_663, 3, x_667);
lean_ctor_set(x_663, 0, x_756);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_788);
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_660);
lean_ctor_set(x_1, 1, x_659);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_788);
return x_1;
}
else
{
lean_object* x_789; uint8_t x_790; 
lean_dec(x_667);
lean_ctor_set_uint8(x_756, sizeof(void*)*4, x_662);
x_789 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_789, 0, x_779);
lean_ctor_set(x_789, 1, x_780);
lean_ctor_set(x_789, 2, x_781);
lean_ctor_set(x_789, 3, x_782);
lean_ctor_set_uint8(x_789, sizeof(void*)*4, x_662);
x_790 = 0;
lean_ctor_set(x_663, 3, x_789);
lean_ctor_set(x_663, 0, x_756);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_790);
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_660);
lean_ctor_set(x_1, 1, x_659);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_790);
return x_1;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; 
x_791 = lean_ctor_get(x_756, 0);
x_792 = lean_ctor_get(x_756, 1);
x_793 = lean_ctor_get(x_756, 2);
x_794 = lean_ctor_get(x_756, 3);
lean_inc(x_794);
lean_inc(x_793);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_756);
lean_inc(x_667);
x_795 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_795, 0, x_661);
lean_ctor_set(x_795, 1, x_653);
lean_ctor_set(x_795, 2, x_654);
lean_ctor_set(x_795, 3, x_667);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 lean_ctor_release(x_667, 2);
 lean_ctor_release(x_667, 3);
 x_796 = x_667;
} else {
 lean_dec_ref(x_667);
 x_796 = lean_box(0);
}
lean_ctor_set_uint8(x_795, sizeof(void*)*4, x_662);
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 4, 1);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_791);
lean_ctor_set(x_797, 1, x_792);
lean_ctor_set(x_797, 2, x_793);
lean_ctor_set(x_797, 3, x_794);
lean_ctor_set_uint8(x_797, sizeof(void*)*4, x_662);
x_798 = 0;
lean_ctor_set(x_663, 3, x_797);
lean_ctor_set(x_663, 0, x_795);
lean_ctor_set_uint8(x_663, sizeof(void*)*4, x_798);
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_660);
lean_ctor_set(x_1, 1, x_659);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_798);
return x_1;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; lean_object* x_810; 
x_799 = lean_ctor_get(x_663, 1);
x_800 = lean_ctor_get(x_663, 2);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_663);
x_801 = lean_ctor_get(x_756, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_756, 1);
lean_inc(x_802);
x_803 = lean_ctor_get(x_756, 2);
lean_inc(x_803);
x_804 = lean_ctor_get(x_756, 3);
lean_inc(x_804);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 lean_ctor_release(x_756, 2);
 lean_ctor_release(x_756, 3);
 x_805 = x_756;
} else {
 lean_dec_ref(x_756);
 x_805 = lean_box(0);
}
lean_inc(x_667);
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(1, 4, 1);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_661);
lean_ctor_set(x_806, 1, x_653);
lean_ctor_set(x_806, 2, x_654);
lean_ctor_set(x_806, 3, x_667);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 lean_ctor_release(x_667, 2);
 lean_ctor_release(x_667, 3);
 x_807 = x_667;
} else {
 lean_dec_ref(x_667);
 x_807 = lean_box(0);
}
lean_ctor_set_uint8(x_806, sizeof(void*)*4, x_662);
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 4, 1);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_801);
lean_ctor_set(x_808, 1, x_802);
lean_ctor_set(x_808, 2, x_803);
lean_ctor_set(x_808, 3, x_804);
lean_ctor_set_uint8(x_808, sizeof(void*)*4, x_662);
x_809 = 0;
x_810 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_810, 0, x_806);
lean_ctor_set(x_810, 1, x_799);
lean_ctor_set(x_810, 2, x_800);
lean_ctor_set(x_810, 3, x_808);
lean_ctor_set_uint8(x_810, sizeof(void*)*4, x_809);
lean_ctor_set(x_1, 3, x_810);
lean_ctor_set(x_1, 2, x_660);
lean_ctor_set(x_1, 1, x_659);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_809);
return x_1;
}
}
else
{
uint8_t x_811; 
x_811 = !lean_is_exclusive(x_663);
if (x_811 == 0)
{
lean_object* x_812; lean_object* x_813; uint8_t x_814; 
x_812 = lean_ctor_get(x_663, 3);
lean_dec(x_812);
x_813 = lean_ctor_get(x_663, 0);
lean_dec(x_813);
x_814 = !lean_is_exclusive(x_667);
if (x_814 == 0)
{
uint8_t x_815; lean_object* x_816; 
lean_ctor_set_uint8(x_667, sizeof(void*)*4, x_774);
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_815 = 0;
x_816 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_816, 0, x_4);
lean_ctor_set(x_816, 1, x_659);
lean_ctor_set(x_816, 2, x_660);
lean_ctor_set(x_816, 3, x_1);
lean_ctor_set_uint8(x_816, sizeof(void*)*4, x_815);
return x_816;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; lean_object* x_823; 
x_817 = lean_ctor_get(x_667, 0);
x_818 = lean_ctor_get(x_667, 1);
x_819 = lean_ctor_get(x_667, 2);
x_820 = lean_ctor_get(x_667, 3);
lean_inc(x_820);
lean_inc(x_819);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_667);
x_821 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_821, 0, x_817);
lean_ctor_set(x_821, 1, x_818);
lean_ctor_set(x_821, 2, x_819);
lean_ctor_set(x_821, 3, x_820);
lean_ctor_set_uint8(x_821, sizeof(void*)*4, x_774);
lean_ctor_set(x_663, 0, x_821);
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_822 = 0;
x_823 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_823, 0, x_4);
lean_ctor_set(x_823, 1, x_659);
lean_ctor_set(x_823, 2, x_660);
lean_ctor_set(x_823, 3, x_1);
lean_ctor_set_uint8(x_823, sizeof(void*)*4, x_822);
return x_823;
}
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; uint8_t x_833; lean_object* x_834; 
x_824 = lean_ctor_get(x_663, 1);
x_825 = lean_ctor_get(x_663, 2);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_663);
x_826 = lean_ctor_get(x_667, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_667, 1);
lean_inc(x_827);
x_828 = lean_ctor_get(x_667, 2);
lean_inc(x_828);
x_829 = lean_ctor_get(x_667, 3);
lean_inc(x_829);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 lean_ctor_release(x_667, 2);
 lean_ctor_release(x_667, 3);
 x_830 = x_667;
} else {
 lean_dec_ref(x_667);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 4, 1);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_826);
lean_ctor_set(x_831, 1, x_827);
lean_ctor_set(x_831, 2, x_828);
lean_ctor_set(x_831, 3, x_829);
lean_ctor_set_uint8(x_831, sizeof(void*)*4, x_774);
x_832 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_832, 0, x_831);
lean_ctor_set(x_832, 1, x_824);
lean_ctor_set(x_832, 2, x_825);
lean_ctor_set(x_832, 3, x_756);
lean_ctor_set_uint8(x_832, sizeof(void*)*4, x_666);
lean_ctor_set(x_1, 3, x_832);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_833 = 0;
x_834 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_834, 0, x_4);
lean_ctor_set(x_834, 1, x_659);
lean_ctor_set(x_834, 2, x_660);
lean_ctor_set(x_834, 3, x_1);
lean_ctor_set_uint8(x_834, sizeof(void*)*4, x_833);
return x_834;
}
}
}
}
}
}
else
{
uint8_t x_835; lean_object* x_836; 
lean_ctor_set(x_1, 3, x_663);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_661);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_662);
x_835 = 0;
x_836 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_836, 0, x_4);
lean_ctor_set(x_836, 1, x_659);
lean_ctor_set(x_836, 2, x_660);
lean_ctor_set(x_836, 3, x_1);
lean_ctor_set_uint8(x_836, sizeof(void*)*4, x_835);
return x_836;
}
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; lean_object* x_843; 
x_837 = lean_ctor_get(x_633, 0);
x_838 = lean_ctor_get(x_633, 1);
x_839 = lean_ctor_get(x_633, 2);
x_840 = lean_ctor_get(x_633, 3);
lean_inc(x_840);
lean_inc(x_839);
lean_inc(x_838);
lean_inc(x_837);
lean_dec(x_633);
x_841 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_841, 0, x_649);
lean_ctor_set(x_841, 1, x_650);
lean_ctor_set(x_841, 2, x_651);
lean_ctor_set(x_841, 3, x_652);
lean_ctor_set_uint8(x_841, sizeof(void*)*4, x_636);
x_842 = 1;
lean_ctor_set(x_4, 3, x_837);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_841);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_842);
x_843 = l_Lean_RBNode_setRed___rarg(x_655);
if (lean_obj_tag(x_843) == 0)
{
uint8_t x_844; lean_object* x_845; 
lean_ctor_set(x_1, 3, x_843);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_840);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_842);
x_844 = 0;
x_845 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_845, 0, x_4);
lean_ctor_set(x_845, 1, x_838);
lean_ctor_set(x_845, 2, x_839);
lean_ctor_set(x_845, 3, x_1);
lean_ctor_set_uint8(x_845, sizeof(void*)*4, x_844);
return x_845;
}
else
{
uint8_t x_846; 
x_846 = lean_ctor_get_uint8(x_843, sizeof(void*)*4);
if (x_846 == 0)
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_843, 0);
lean_inc(x_847);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; 
x_848 = lean_ctor_get(x_843, 3);
lean_inc(x_848);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; uint8_t x_853; lean_object* x_854; 
x_849 = lean_ctor_get(x_843, 1);
lean_inc(x_849);
x_850 = lean_ctor_get(x_843, 2);
lean_inc(x_850);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_851 = x_843;
} else {
 lean_dec_ref(x_843);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(1, 4, 1);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_848);
lean_ctor_set(x_852, 1, x_849);
lean_ctor_set(x_852, 2, x_850);
lean_ctor_set(x_852, 3, x_848);
lean_ctor_set_uint8(x_852, sizeof(void*)*4, x_846);
lean_ctor_set(x_1, 3, x_852);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_840);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_842);
x_853 = 0;
x_854 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_854, 0, x_4);
lean_ctor_set(x_854, 1, x_838);
lean_ctor_set(x_854, 2, x_839);
lean_ctor_set(x_854, 3, x_1);
lean_ctor_set_uint8(x_854, sizeof(void*)*4, x_853);
return x_854;
}
else
{
uint8_t x_855; 
x_855 = lean_ctor_get_uint8(x_848, sizeof(void*)*4);
if (x_855 == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; lean_object* x_867; 
x_856 = lean_ctor_get(x_843, 1);
lean_inc(x_856);
x_857 = lean_ctor_get(x_843, 2);
lean_inc(x_857);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_858 = x_843;
} else {
 lean_dec_ref(x_843);
 x_858 = lean_box(0);
}
x_859 = lean_ctor_get(x_848, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_848, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_848, 2);
lean_inc(x_861);
x_862 = lean_ctor_get(x_848, 3);
lean_inc(x_862);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 lean_ctor_release(x_848, 1);
 lean_ctor_release(x_848, 2);
 lean_ctor_release(x_848, 3);
 x_863 = x_848;
} else {
 lean_dec_ref(x_848);
 x_863 = lean_box(0);
}
if (lean_is_scalar(x_863)) {
 x_864 = lean_alloc_ctor(1, 4, 1);
} else {
 x_864 = x_863;
}
lean_ctor_set(x_864, 0, x_840);
lean_ctor_set(x_864, 1, x_653);
lean_ctor_set(x_864, 2, x_654);
lean_ctor_set(x_864, 3, x_847);
lean_ctor_set_uint8(x_864, sizeof(void*)*4, x_842);
if (lean_is_scalar(x_858)) {
 x_865 = lean_alloc_ctor(1, 4, 1);
} else {
 x_865 = x_858;
}
lean_ctor_set(x_865, 0, x_859);
lean_ctor_set(x_865, 1, x_860);
lean_ctor_set(x_865, 2, x_861);
lean_ctor_set(x_865, 3, x_862);
lean_ctor_set_uint8(x_865, sizeof(void*)*4, x_842);
x_866 = 0;
lean_ctor_set(x_1, 3, x_865);
lean_ctor_set(x_1, 2, x_857);
lean_ctor_set(x_1, 1, x_856);
lean_ctor_set(x_1, 0, x_864);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_866);
x_867 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_867, 0, x_4);
lean_ctor_set(x_867, 1, x_838);
lean_ctor_set(x_867, 2, x_839);
lean_ctor_set(x_867, 3, x_1);
lean_ctor_set_uint8(x_867, sizeof(void*)*4, x_866);
return x_867;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_871; lean_object* x_872; 
lean_free_object(x_1);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 lean_ctor_release(x_848, 1);
 lean_ctor_release(x_848, 2);
 lean_ctor_release(x_848, 3);
 x_868 = x_848;
} else {
 lean_dec_ref(x_848);
 x_868 = lean_box(0);
}
lean_inc(x_843);
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 4, 1);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_840);
lean_ctor_set(x_869, 1, x_653);
lean_ctor_set(x_869, 2, x_654);
lean_ctor_set(x_869, 3, x_843);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_870 = x_843;
} else {
 lean_dec_ref(x_843);
 x_870 = lean_box(0);
}
lean_ctor_set_uint8(x_869, sizeof(void*)*4, x_842);
x_871 = 0;
if (lean_is_scalar(x_870)) {
 x_872 = lean_alloc_ctor(1, 4, 1);
} else {
 x_872 = x_870;
}
lean_ctor_set(x_872, 0, x_4);
lean_ctor_set(x_872, 1, x_838);
lean_ctor_set(x_872, 2, x_839);
lean_ctor_set(x_872, 3, x_869);
lean_ctor_set_uint8(x_872, sizeof(void*)*4, x_871);
return x_872;
}
}
}
else
{
uint8_t x_873; 
x_873 = lean_ctor_get_uint8(x_847, sizeof(void*)*4);
if (x_873 == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; lean_object* x_886; 
x_874 = lean_ctor_get(x_843, 1);
lean_inc(x_874);
x_875 = lean_ctor_get(x_843, 2);
lean_inc(x_875);
x_876 = lean_ctor_get(x_843, 3);
lean_inc(x_876);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_877 = x_843;
} else {
 lean_dec_ref(x_843);
 x_877 = lean_box(0);
}
x_878 = lean_ctor_get(x_847, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_847, 1);
lean_inc(x_879);
x_880 = lean_ctor_get(x_847, 2);
lean_inc(x_880);
x_881 = lean_ctor_get(x_847, 3);
lean_inc(x_881);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 lean_ctor_release(x_847, 2);
 lean_ctor_release(x_847, 3);
 x_882 = x_847;
} else {
 lean_dec_ref(x_847);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 4, 1);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_840);
lean_ctor_set(x_883, 1, x_653);
lean_ctor_set(x_883, 2, x_654);
lean_ctor_set(x_883, 3, x_878);
lean_ctor_set_uint8(x_883, sizeof(void*)*4, x_842);
if (lean_is_scalar(x_877)) {
 x_884 = lean_alloc_ctor(1, 4, 1);
} else {
 x_884 = x_877;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_874);
lean_ctor_set(x_884, 2, x_875);
lean_ctor_set(x_884, 3, x_876);
lean_ctor_set_uint8(x_884, sizeof(void*)*4, x_842);
x_885 = 0;
lean_ctor_set(x_1, 3, x_884);
lean_ctor_set(x_1, 2, x_880);
lean_ctor_set(x_1, 1, x_879);
lean_ctor_set(x_1, 0, x_883);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_885);
x_886 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_886, 0, x_4);
lean_ctor_set(x_886, 1, x_838);
lean_ctor_set(x_886, 2, x_839);
lean_ctor_set(x_886, 3, x_1);
lean_ctor_set_uint8(x_886, sizeof(void*)*4, x_885);
return x_886;
}
else
{
lean_object* x_887; 
x_887 = lean_ctor_get(x_843, 3);
lean_inc(x_887);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; uint8_t x_891; lean_object* x_892; 
lean_free_object(x_1);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 lean_ctor_release(x_847, 2);
 lean_ctor_release(x_847, 3);
 x_888 = x_847;
} else {
 lean_dec_ref(x_847);
 x_888 = lean_box(0);
}
lean_inc(x_843);
if (lean_is_scalar(x_888)) {
 x_889 = lean_alloc_ctor(1, 4, 1);
} else {
 x_889 = x_888;
}
lean_ctor_set(x_889, 0, x_840);
lean_ctor_set(x_889, 1, x_653);
lean_ctor_set(x_889, 2, x_654);
lean_ctor_set(x_889, 3, x_843);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_890 = x_843;
} else {
 lean_dec_ref(x_843);
 x_890 = lean_box(0);
}
lean_ctor_set_uint8(x_889, sizeof(void*)*4, x_842);
x_891 = 0;
if (lean_is_scalar(x_890)) {
 x_892 = lean_alloc_ctor(1, 4, 1);
} else {
 x_892 = x_890;
}
lean_ctor_set(x_892, 0, x_4);
lean_ctor_set(x_892, 1, x_838);
lean_ctor_set(x_892, 2, x_839);
lean_ctor_set(x_892, 3, x_889);
lean_ctor_set_uint8(x_892, sizeof(void*)*4, x_891);
return x_892;
}
else
{
uint8_t x_893; 
x_893 = lean_ctor_get_uint8(x_887, sizeof(void*)*4);
if (x_893 == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; uint8_t x_905; lean_object* x_906; 
x_894 = lean_ctor_get(x_843, 1);
lean_inc(x_894);
x_895 = lean_ctor_get(x_843, 2);
lean_inc(x_895);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_896 = x_843;
} else {
 lean_dec_ref(x_843);
 x_896 = lean_box(0);
}
x_897 = lean_ctor_get(x_887, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_887, 1);
lean_inc(x_898);
x_899 = lean_ctor_get(x_887, 2);
lean_inc(x_899);
x_900 = lean_ctor_get(x_887, 3);
lean_inc(x_900);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 lean_ctor_release(x_887, 2);
 lean_ctor_release(x_887, 3);
 x_901 = x_887;
} else {
 lean_dec_ref(x_887);
 x_901 = lean_box(0);
}
lean_inc(x_847);
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 4, 1);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_840);
lean_ctor_set(x_902, 1, x_653);
lean_ctor_set(x_902, 2, x_654);
lean_ctor_set(x_902, 3, x_847);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 lean_ctor_release(x_847, 2);
 lean_ctor_release(x_847, 3);
 x_903 = x_847;
} else {
 lean_dec_ref(x_847);
 x_903 = lean_box(0);
}
lean_ctor_set_uint8(x_902, sizeof(void*)*4, x_842);
if (lean_is_scalar(x_903)) {
 x_904 = lean_alloc_ctor(1, 4, 1);
} else {
 x_904 = x_903;
}
lean_ctor_set(x_904, 0, x_897);
lean_ctor_set(x_904, 1, x_898);
lean_ctor_set(x_904, 2, x_899);
lean_ctor_set(x_904, 3, x_900);
lean_ctor_set_uint8(x_904, sizeof(void*)*4, x_842);
x_905 = 0;
if (lean_is_scalar(x_896)) {
 x_906 = lean_alloc_ctor(1, 4, 1);
} else {
 x_906 = x_896;
}
lean_ctor_set(x_906, 0, x_902);
lean_ctor_set(x_906, 1, x_894);
lean_ctor_set(x_906, 2, x_895);
lean_ctor_set(x_906, 3, x_904);
lean_ctor_set_uint8(x_906, sizeof(void*)*4, x_905);
lean_ctor_set(x_1, 3, x_906);
lean_ctor_set(x_1, 2, x_839);
lean_ctor_set(x_1, 1, x_838);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_905);
return x_1;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; uint8_t x_917; lean_object* x_918; 
x_907 = lean_ctor_get(x_843, 1);
lean_inc(x_907);
x_908 = lean_ctor_get(x_843, 2);
lean_inc(x_908);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 x_909 = x_843;
} else {
 lean_dec_ref(x_843);
 x_909 = lean_box(0);
}
x_910 = lean_ctor_get(x_847, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_847, 1);
lean_inc(x_911);
x_912 = lean_ctor_get(x_847, 2);
lean_inc(x_912);
x_913 = lean_ctor_get(x_847, 3);
lean_inc(x_913);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 lean_ctor_release(x_847, 2);
 lean_ctor_release(x_847, 3);
 x_914 = x_847;
} else {
 lean_dec_ref(x_847);
 x_914 = lean_box(0);
}
if (lean_is_scalar(x_914)) {
 x_915 = lean_alloc_ctor(1, 4, 1);
} else {
 x_915 = x_914;
}
lean_ctor_set(x_915, 0, x_910);
lean_ctor_set(x_915, 1, x_911);
lean_ctor_set(x_915, 2, x_912);
lean_ctor_set(x_915, 3, x_913);
lean_ctor_set_uint8(x_915, sizeof(void*)*4, x_893);
if (lean_is_scalar(x_909)) {
 x_916 = lean_alloc_ctor(1, 4, 1);
} else {
 x_916 = x_909;
}
lean_ctor_set(x_916, 0, x_915);
lean_ctor_set(x_916, 1, x_907);
lean_ctor_set(x_916, 2, x_908);
lean_ctor_set(x_916, 3, x_887);
lean_ctor_set_uint8(x_916, sizeof(void*)*4, x_846);
lean_ctor_set(x_1, 3, x_916);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_840);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_842);
x_917 = 0;
x_918 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_918, 0, x_4);
lean_ctor_set(x_918, 1, x_838);
lean_ctor_set(x_918, 2, x_839);
lean_ctor_set(x_918, 3, x_1);
lean_ctor_set_uint8(x_918, sizeof(void*)*4, x_917);
return x_918;
}
}
}
}
}
else
{
uint8_t x_919; lean_object* x_920; 
lean_ctor_set(x_1, 3, x_843);
lean_ctor_set(x_1, 2, x_654);
lean_ctor_set(x_1, 1, x_653);
lean_ctor_set(x_1, 0, x_840);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_842);
x_919 = 0;
x_920 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_920, 0, x_4);
lean_ctor_set(x_920, 1, x_838);
lean_ctor_set(x_920, 2, x_839);
lean_ctor_set(x_920, 3, x_1);
lean_ctor_set_uint8(x_920, sizeof(void*)*4, x_919);
return x_920;
}
}
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; lean_object* x_935; lean_object* x_936; 
x_921 = lean_ctor_get(x_1, 0);
x_922 = lean_ctor_get(x_1, 1);
x_923 = lean_ctor_get(x_1, 2);
x_924 = lean_ctor_get(x_1, 3);
x_925 = lean_ctor_get(x_4, 1);
x_926 = lean_ctor_get(x_4, 2);
x_927 = lean_ctor_get(x_4, 3);
lean_inc(x_927);
lean_inc(x_926);
lean_inc(x_925);
lean_dec(x_4);
x_928 = lean_ctor_get(x_633, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_633, 1);
lean_inc(x_929);
x_930 = lean_ctor_get(x_633, 2);
lean_inc(x_930);
x_931 = lean_ctor_get(x_633, 3);
lean_inc(x_931);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 lean_ctor_release(x_633, 2);
 lean_ctor_release(x_633, 3);
 x_932 = x_633;
} else {
 lean_dec_ref(x_633);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_932)) {
 x_933 = lean_alloc_ctor(1, 4, 1);
} else {
 x_933 = x_932;
}
lean_ctor_set(x_933, 0, x_921);
lean_ctor_set(x_933, 1, x_922);
lean_ctor_set(x_933, 2, x_923);
lean_ctor_set(x_933, 3, x_924);
lean_ctor_set_uint8(x_933, sizeof(void*)*4, x_636);
x_934 = 1;
x_935 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_2);
lean_ctor_set(x_935, 2, x_3);
lean_ctor_set(x_935, 3, x_928);
lean_ctor_set_uint8(x_935, sizeof(void*)*4, x_934);
x_936 = l_Lean_RBNode_setRed___rarg(x_927);
if (lean_obj_tag(x_936) == 0)
{
uint8_t x_937; lean_object* x_938; 
lean_ctor_set(x_1, 3, x_936);
lean_ctor_set(x_1, 2, x_926);
lean_ctor_set(x_1, 1, x_925);
lean_ctor_set(x_1, 0, x_931);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_934);
x_937 = 0;
x_938 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_929);
lean_ctor_set(x_938, 2, x_930);
lean_ctor_set(x_938, 3, x_1);
lean_ctor_set_uint8(x_938, sizeof(void*)*4, x_937);
return x_938;
}
else
{
uint8_t x_939; 
x_939 = lean_ctor_get_uint8(x_936, sizeof(void*)*4);
if (x_939 == 0)
{
lean_object* x_940; 
x_940 = lean_ctor_get(x_936, 0);
lean_inc(x_940);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; 
x_941 = lean_ctor_get(x_936, 3);
lean_inc(x_941);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; uint8_t x_946; lean_object* x_947; 
x_942 = lean_ctor_get(x_936, 1);
lean_inc(x_942);
x_943 = lean_ctor_get(x_936, 2);
lean_inc(x_943);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_944 = x_936;
} else {
 lean_dec_ref(x_936);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(1, 4, 1);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_941);
lean_ctor_set(x_945, 1, x_942);
lean_ctor_set(x_945, 2, x_943);
lean_ctor_set(x_945, 3, x_941);
lean_ctor_set_uint8(x_945, sizeof(void*)*4, x_939);
lean_ctor_set(x_1, 3, x_945);
lean_ctor_set(x_1, 2, x_926);
lean_ctor_set(x_1, 1, x_925);
lean_ctor_set(x_1, 0, x_931);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_934);
x_946 = 0;
x_947 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_947, 0, x_935);
lean_ctor_set(x_947, 1, x_929);
lean_ctor_set(x_947, 2, x_930);
lean_ctor_set(x_947, 3, x_1);
lean_ctor_set_uint8(x_947, sizeof(void*)*4, x_946);
return x_947;
}
else
{
uint8_t x_948; 
x_948 = lean_ctor_get_uint8(x_941, sizeof(void*)*4);
if (x_948 == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; uint8_t x_959; lean_object* x_960; 
x_949 = lean_ctor_get(x_936, 1);
lean_inc(x_949);
x_950 = lean_ctor_get(x_936, 2);
lean_inc(x_950);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_951 = x_936;
} else {
 lean_dec_ref(x_936);
 x_951 = lean_box(0);
}
x_952 = lean_ctor_get(x_941, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_941, 1);
lean_inc(x_953);
x_954 = lean_ctor_get(x_941, 2);
lean_inc(x_954);
x_955 = lean_ctor_get(x_941, 3);
lean_inc(x_955);
if (lean_is_exclusive(x_941)) {
 lean_ctor_release(x_941, 0);
 lean_ctor_release(x_941, 1);
 lean_ctor_release(x_941, 2);
 lean_ctor_release(x_941, 3);
 x_956 = x_941;
} else {
 lean_dec_ref(x_941);
 x_956 = lean_box(0);
}
if (lean_is_scalar(x_956)) {
 x_957 = lean_alloc_ctor(1, 4, 1);
} else {
 x_957 = x_956;
}
lean_ctor_set(x_957, 0, x_931);
lean_ctor_set(x_957, 1, x_925);
lean_ctor_set(x_957, 2, x_926);
lean_ctor_set(x_957, 3, x_940);
lean_ctor_set_uint8(x_957, sizeof(void*)*4, x_934);
if (lean_is_scalar(x_951)) {
 x_958 = lean_alloc_ctor(1, 4, 1);
} else {
 x_958 = x_951;
}
lean_ctor_set(x_958, 0, x_952);
lean_ctor_set(x_958, 1, x_953);
lean_ctor_set(x_958, 2, x_954);
lean_ctor_set(x_958, 3, x_955);
lean_ctor_set_uint8(x_958, sizeof(void*)*4, x_934);
x_959 = 0;
lean_ctor_set(x_1, 3, x_958);
lean_ctor_set(x_1, 2, x_950);
lean_ctor_set(x_1, 1, x_949);
lean_ctor_set(x_1, 0, x_957);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_959);
x_960 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_960, 0, x_935);
lean_ctor_set(x_960, 1, x_929);
lean_ctor_set(x_960, 2, x_930);
lean_ctor_set(x_960, 3, x_1);
lean_ctor_set_uint8(x_960, sizeof(void*)*4, x_959);
return x_960;
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; uint8_t x_964; lean_object* x_965; 
lean_free_object(x_1);
if (lean_is_exclusive(x_941)) {
 lean_ctor_release(x_941, 0);
 lean_ctor_release(x_941, 1);
 lean_ctor_release(x_941, 2);
 lean_ctor_release(x_941, 3);
 x_961 = x_941;
} else {
 lean_dec_ref(x_941);
 x_961 = lean_box(0);
}
lean_inc(x_936);
if (lean_is_scalar(x_961)) {
 x_962 = lean_alloc_ctor(1, 4, 1);
} else {
 x_962 = x_961;
}
lean_ctor_set(x_962, 0, x_931);
lean_ctor_set(x_962, 1, x_925);
lean_ctor_set(x_962, 2, x_926);
lean_ctor_set(x_962, 3, x_936);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_963 = x_936;
} else {
 lean_dec_ref(x_936);
 x_963 = lean_box(0);
}
lean_ctor_set_uint8(x_962, sizeof(void*)*4, x_934);
x_964 = 0;
if (lean_is_scalar(x_963)) {
 x_965 = lean_alloc_ctor(1, 4, 1);
} else {
 x_965 = x_963;
}
lean_ctor_set(x_965, 0, x_935);
lean_ctor_set(x_965, 1, x_929);
lean_ctor_set(x_965, 2, x_930);
lean_ctor_set(x_965, 3, x_962);
lean_ctor_set_uint8(x_965, sizeof(void*)*4, x_964);
return x_965;
}
}
}
else
{
uint8_t x_966; 
x_966 = lean_ctor_get_uint8(x_940, sizeof(void*)*4);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; uint8_t x_978; lean_object* x_979; 
x_967 = lean_ctor_get(x_936, 1);
lean_inc(x_967);
x_968 = lean_ctor_get(x_936, 2);
lean_inc(x_968);
x_969 = lean_ctor_get(x_936, 3);
lean_inc(x_969);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_970 = x_936;
} else {
 lean_dec_ref(x_936);
 x_970 = lean_box(0);
}
x_971 = lean_ctor_get(x_940, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_940, 1);
lean_inc(x_972);
x_973 = lean_ctor_get(x_940, 2);
lean_inc(x_973);
x_974 = lean_ctor_get(x_940, 3);
lean_inc(x_974);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 lean_ctor_release(x_940, 2);
 lean_ctor_release(x_940, 3);
 x_975 = x_940;
} else {
 lean_dec_ref(x_940);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(1, 4, 1);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_931);
lean_ctor_set(x_976, 1, x_925);
lean_ctor_set(x_976, 2, x_926);
lean_ctor_set(x_976, 3, x_971);
lean_ctor_set_uint8(x_976, sizeof(void*)*4, x_934);
if (lean_is_scalar(x_970)) {
 x_977 = lean_alloc_ctor(1, 4, 1);
} else {
 x_977 = x_970;
}
lean_ctor_set(x_977, 0, x_974);
lean_ctor_set(x_977, 1, x_967);
lean_ctor_set(x_977, 2, x_968);
lean_ctor_set(x_977, 3, x_969);
lean_ctor_set_uint8(x_977, sizeof(void*)*4, x_934);
x_978 = 0;
lean_ctor_set(x_1, 3, x_977);
lean_ctor_set(x_1, 2, x_973);
lean_ctor_set(x_1, 1, x_972);
lean_ctor_set(x_1, 0, x_976);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_978);
x_979 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_979, 0, x_935);
lean_ctor_set(x_979, 1, x_929);
lean_ctor_set(x_979, 2, x_930);
lean_ctor_set(x_979, 3, x_1);
lean_ctor_set_uint8(x_979, sizeof(void*)*4, x_978);
return x_979;
}
else
{
lean_object* x_980; 
x_980 = lean_ctor_get(x_936, 3);
lean_inc(x_980);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; uint8_t x_984; lean_object* x_985; 
lean_free_object(x_1);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 lean_ctor_release(x_940, 2);
 lean_ctor_release(x_940, 3);
 x_981 = x_940;
} else {
 lean_dec_ref(x_940);
 x_981 = lean_box(0);
}
lean_inc(x_936);
if (lean_is_scalar(x_981)) {
 x_982 = lean_alloc_ctor(1, 4, 1);
} else {
 x_982 = x_981;
}
lean_ctor_set(x_982, 0, x_931);
lean_ctor_set(x_982, 1, x_925);
lean_ctor_set(x_982, 2, x_926);
lean_ctor_set(x_982, 3, x_936);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_983 = x_936;
} else {
 lean_dec_ref(x_936);
 x_983 = lean_box(0);
}
lean_ctor_set_uint8(x_982, sizeof(void*)*4, x_934);
x_984 = 0;
if (lean_is_scalar(x_983)) {
 x_985 = lean_alloc_ctor(1, 4, 1);
} else {
 x_985 = x_983;
}
lean_ctor_set(x_985, 0, x_935);
lean_ctor_set(x_985, 1, x_929);
lean_ctor_set(x_985, 2, x_930);
lean_ctor_set(x_985, 3, x_982);
lean_ctor_set_uint8(x_985, sizeof(void*)*4, x_984);
return x_985;
}
else
{
uint8_t x_986; 
x_986 = lean_ctor_get_uint8(x_980, sizeof(void*)*4);
if (x_986 == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_998; lean_object* x_999; 
x_987 = lean_ctor_get(x_936, 1);
lean_inc(x_987);
x_988 = lean_ctor_get(x_936, 2);
lean_inc(x_988);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_989 = x_936;
} else {
 lean_dec_ref(x_936);
 x_989 = lean_box(0);
}
x_990 = lean_ctor_get(x_980, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_980, 1);
lean_inc(x_991);
x_992 = lean_ctor_get(x_980, 2);
lean_inc(x_992);
x_993 = lean_ctor_get(x_980, 3);
lean_inc(x_993);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 lean_ctor_release(x_980, 2);
 lean_ctor_release(x_980, 3);
 x_994 = x_980;
} else {
 lean_dec_ref(x_980);
 x_994 = lean_box(0);
}
lean_inc(x_940);
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(1, 4, 1);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_931);
lean_ctor_set(x_995, 1, x_925);
lean_ctor_set(x_995, 2, x_926);
lean_ctor_set(x_995, 3, x_940);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 lean_ctor_release(x_940, 2);
 lean_ctor_release(x_940, 3);
 x_996 = x_940;
} else {
 lean_dec_ref(x_940);
 x_996 = lean_box(0);
}
lean_ctor_set_uint8(x_995, sizeof(void*)*4, x_934);
if (lean_is_scalar(x_996)) {
 x_997 = lean_alloc_ctor(1, 4, 1);
} else {
 x_997 = x_996;
}
lean_ctor_set(x_997, 0, x_990);
lean_ctor_set(x_997, 1, x_991);
lean_ctor_set(x_997, 2, x_992);
lean_ctor_set(x_997, 3, x_993);
lean_ctor_set_uint8(x_997, sizeof(void*)*4, x_934);
x_998 = 0;
if (lean_is_scalar(x_989)) {
 x_999 = lean_alloc_ctor(1, 4, 1);
} else {
 x_999 = x_989;
}
lean_ctor_set(x_999, 0, x_995);
lean_ctor_set(x_999, 1, x_987);
lean_ctor_set(x_999, 2, x_988);
lean_ctor_set(x_999, 3, x_997);
lean_ctor_set_uint8(x_999, sizeof(void*)*4, x_998);
lean_ctor_set(x_1, 3, x_999);
lean_ctor_set(x_1, 2, x_930);
lean_ctor_set(x_1, 1, x_929);
lean_ctor_set(x_1, 0, x_935);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_998);
return x_1;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; lean_object* x_1011; 
x_1000 = lean_ctor_get(x_936, 1);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_936, 2);
lean_inc(x_1001);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 lean_ctor_release(x_936, 2);
 lean_ctor_release(x_936, 3);
 x_1002 = x_936;
} else {
 lean_dec_ref(x_936);
 x_1002 = lean_box(0);
}
x_1003 = lean_ctor_get(x_940, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_940, 1);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_940, 2);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_940, 3);
lean_inc(x_1006);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 lean_ctor_release(x_940, 2);
 lean_ctor_release(x_940, 3);
 x_1007 = x_940;
} else {
 lean_dec_ref(x_940);
 x_1007 = lean_box(0);
}
if (lean_is_scalar(x_1007)) {
 x_1008 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1008 = x_1007;
}
lean_ctor_set(x_1008, 0, x_1003);
lean_ctor_set(x_1008, 1, x_1004);
lean_ctor_set(x_1008, 2, x_1005);
lean_ctor_set(x_1008, 3, x_1006);
lean_ctor_set_uint8(x_1008, sizeof(void*)*4, x_986);
if (lean_is_scalar(x_1002)) {
 x_1009 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1009 = x_1002;
}
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1009, 1, x_1000);
lean_ctor_set(x_1009, 2, x_1001);
lean_ctor_set(x_1009, 3, x_980);
lean_ctor_set_uint8(x_1009, sizeof(void*)*4, x_939);
lean_ctor_set(x_1, 3, x_1009);
lean_ctor_set(x_1, 2, x_926);
lean_ctor_set(x_1, 1, x_925);
lean_ctor_set(x_1, 0, x_931);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_934);
x_1010 = 0;
x_1011 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1011, 0, x_935);
lean_ctor_set(x_1011, 1, x_929);
lean_ctor_set(x_1011, 2, x_930);
lean_ctor_set(x_1011, 3, x_1);
lean_ctor_set_uint8(x_1011, sizeof(void*)*4, x_1010);
return x_1011;
}
}
}
}
}
else
{
uint8_t x_1012; lean_object* x_1013; 
lean_ctor_set(x_1, 3, x_936);
lean_ctor_set(x_1, 2, x_926);
lean_ctor_set(x_1, 1, x_925);
lean_ctor_set(x_1, 0, x_931);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_934);
x_1012 = 0;
x_1013 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1013, 0, x_935);
lean_ctor_set(x_1013, 1, x_929);
lean_ctor_set(x_1013, 2, x_930);
lean_ctor_set(x_1013, 3, x_1);
lean_ctor_set_uint8(x_1013, sizeof(void*)*4, x_1012);
return x_1013;
}
}
}
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; uint8_t x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1014 = lean_ctor_get(x_1, 0);
x_1015 = lean_ctor_get(x_1, 1);
x_1016 = lean_ctor_get(x_1, 2);
x_1017 = lean_ctor_get(x_1, 3);
lean_inc(x_1017);
lean_inc(x_1016);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_1);
x_1018 = lean_ctor_get(x_4, 1);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_4, 2);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_4, 3);
lean_inc(x_1020);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1021 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1021 = lean_box(0);
}
x_1022 = lean_ctor_get(x_633, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_633, 1);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_633, 2);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_633, 3);
lean_inc(x_1025);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 lean_ctor_release(x_633, 2);
 lean_ctor_release(x_633, 3);
 x_1026 = x_633;
} else {
 lean_dec_ref(x_633);
 x_1026 = lean_box(0);
}
if (lean_is_scalar(x_1026)) {
 x_1027 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1027 = x_1026;
}
lean_ctor_set(x_1027, 0, x_1014);
lean_ctor_set(x_1027, 1, x_1015);
lean_ctor_set(x_1027, 2, x_1016);
lean_ctor_set(x_1027, 3, x_1017);
lean_ctor_set_uint8(x_1027, sizeof(void*)*4, x_636);
x_1028 = 1;
if (lean_is_scalar(x_1021)) {
 x_1029 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1029 = x_1021;
}
lean_ctor_set(x_1029, 0, x_1027);
lean_ctor_set(x_1029, 1, x_2);
lean_ctor_set(x_1029, 2, x_3);
lean_ctor_set(x_1029, 3, x_1022);
lean_ctor_set_uint8(x_1029, sizeof(void*)*4, x_1028);
x_1030 = l_Lean_RBNode_setRed___rarg(x_1020);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; uint8_t x_1032; lean_object* x_1033; 
x_1031 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1031, 0, x_1025);
lean_ctor_set(x_1031, 1, x_1018);
lean_ctor_set(x_1031, 2, x_1019);
lean_ctor_set(x_1031, 3, x_1030);
lean_ctor_set_uint8(x_1031, sizeof(void*)*4, x_1028);
x_1032 = 0;
x_1033 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1033, 0, x_1029);
lean_ctor_set(x_1033, 1, x_1023);
lean_ctor_set(x_1033, 2, x_1024);
lean_ctor_set(x_1033, 3, x_1031);
lean_ctor_set_uint8(x_1033, sizeof(void*)*4, x_1032);
return x_1033;
}
else
{
uint8_t x_1034; 
x_1034 = lean_ctor_get_uint8(x_1030, sizeof(void*)*4);
if (x_1034 == 0)
{
lean_object* x_1035; 
x_1035 = lean_ctor_get(x_1030, 0);
lean_inc(x_1035);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; 
x_1036 = lean_ctor_get(x_1030, 3);
lean_inc(x_1036);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; uint8_t x_1042; lean_object* x_1043; 
x_1037 = lean_ctor_get(x_1030, 1);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1030, 2);
lean_inc(x_1038);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1039 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1039 = lean_box(0);
}
if (lean_is_scalar(x_1039)) {
 x_1040 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1040 = x_1039;
}
lean_ctor_set(x_1040, 0, x_1036);
lean_ctor_set(x_1040, 1, x_1037);
lean_ctor_set(x_1040, 2, x_1038);
lean_ctor_set(x_1040, 3, x_1036);
lean_ctor_set_uint8(x_1040, sizeof(void*)*4, x_1034);
x_1041 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1041, 0, x_1025);
lean_ctor_set(x_1041, 1, x_1018);
lean_ctor_set(x_1041, 2, x_1019);
lean_ctor_set(x_1041, 3, x_1040);
lean_ctor_set_uint8(x_1041, sizeof(void*)*4, x_1028);
x_1042 = 0;
x_1043 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1043, 0, x_1029);
lean_ctor_set(x_1043, 1, x_1023);
lean_ctor_set(x_1043, 2, x_1024);
lean_ctor_set(x_1043, 3, x_1041);
lean_ctor_set_uint8(x_1043, sizeof(void*)*4, x_1042);
return x_1043;
}
else
{
uint8_t x_1044; 
x_1044 = lean_ctor_get_uint8(x_1036, sizeof(void*)*4);
if (x_1044 == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; uint8_t x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1045 = lean_ctor_get(x_1030, 1);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1030, 2);
lean_inc(x_1046);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1047 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1047 = lean_box(0);
}
x_1048 = lean_ctor_get(x_1036, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1036, 1);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1036, 2);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1036, 3);
lean_inc(x_1051);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 lean_ctor_release(x_1036, 2);
 lean_ctor_release(x_1036, 3);
 x_1052 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1052 = lean_box(0);
}
if (lean_is_scalar(x_1052)) {
 x_1053 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1053 = x_1052;
}
lean_ctor_set(x_1053, 0, x_1025);
lean_ctor_set(x_1053, 1, x_1018);
lean_ctor_set(x_1053, 2, x_1019);
lean_ctor_set(x_1053, 3, x_1035);
lean_ctor_set_uint8(x_1053, sizeof(void*)*4, x_1028);
if (lean_is_scalar(x_1047)) {
 x_1054 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1054 = x_1047;
}
lean_ctor_set(x_1054, 0, x_1048);
lean_ctor_set(x_1054, 1, x_1049);
lean_ctor_set(x_1054, 2, x_1050);
lean_ctor_set(x_1054, 3, x_1051);
lean_ctor_set_uint8(x_1054, sizeof(void*)*4, x_1028);
x_1055 = 0;
x_1056 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1056, 0, x_1053);
lean_ctor_set(x_1056, 1, x_1045);
lean_ctor_set(x_1056, 2, x_1046);
lean_ctor_set(x_1056, 3, x_1054);
lean_ctor_set_uint8(x_1056, sizeof(void*)*4, x_1055);
x_1057 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1057, 0, x_1029);
lean_ctor_set(x_1057, 1, x_1023);
lean_ctor_set(x_1057, 2, x_1024);
lean_ctor_set(x_1057, 3, x_1056);
lean_ctor_set_uint8(x_1057, sizeof(void*)*4, x_1055);
return x_1057;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; lean_object* x_1062; 
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 lean_ctor_release(x_1036, 2);
 lean_ctor_release(x_1036, 3);
 x_1058 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1058 = lean_box(0);
}
lean_inc(x_1030);
if (lean_is_scalar(x_1058)) {
 x_1059 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1059 = x_1058;
}
lean_ctor_set(x_1059, 0, x_1025);
lean_ctor_set(x_1059, 1, x_1018);
lean_ctor_set(x_1059, 2, x_1019);
lean_ctor_set(x_1059, 3, x_1030);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1060 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1060 = lean_box(0);
}
lean_ctor_set_uint8(x_1059, sizeof(void*)*4, x_1028);
x_1061 = 0;
if (lean_is_scalar(x_1060)) {
 x_1062 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1062 = x_1060;
}
lean_ctor_set(x_1062, 0, x_1029);
lean_ctor_set(x_1062, 1, x_1023);
lean_ctor_set(x_1062, 2, x_1024);
lean_ctor_set(x_1062, 3, x_1059);
lean_ctor_set_uint8(x_1062, sizeof(void*)*4, x_1061);
return x_1062;
}
}
}
else
{
uint8_t x_1063; 
x_1063 = lean_ctor_get_uint8(x_1035, sizeof(void*)*4);
if (x_1063 == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; uint8_t x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1064 = lean_ctor_get(x_1030, 1);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1030, 2);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1030, 3);
lean_inc(x_1066);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1067 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1067 = lean_box(0);
}
x_1068 = lean_ctor_get(x_1035, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1035, 1);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1035, 2);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1035, 3);
lean_inc(x_1071);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 lean_ctor_release(x_1035, 2);
 lean_ctor_release(x_1035, 3);
 x_1072 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1072 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1073 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1073 = x_1072;
}
lean_ctor_set(x_1073, 0, x_1025);
lean_ctor_set(x_1073, 1, x_1018);
lean_ctor_set(x_1073, 2, x_1019);
lean_ctor_set(x_1073, 3, x_1068);
lean_ctor_set_uint8(x_1073, sizeof(void*)*4, x_1028);
if (lean_is_scalar(x_1067)) {
 x_1074 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1074 = x_1067;
}
lean_ctor_set(x_1074, 0, x_1071);
lean_ctor_set(x_1074, 1, x_1064);
lean_ctor_set(x_1074, 2, x_1065);
lean_ctor_set(x_1074, 3, x_1066);
lean_ctor_set_uint8(x_1074, sizeof(void*)*4, x_1028);
x_1075 = 0;
x_1076 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1076, 0, x_1073);
lean_ctor_set(x_1076, 1, x_1069);
lean_ctor_set(x_1076, 2, x_1070);
lean_ctor_set(x_1076, 3, x_1074);
lean_ctor_set_uint8(x_1076, sizeof(void*)*4, x_1075);
x_1077 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1077, 0, x_1029);
lean_ctor_set(x_1077, 1, x_1023);
lean_ctor_set(x_1077, 2, x_1024);
lean_ctor_set(x_1077, 3, x_1076);
lean_ctor_set_uint8(x_1077, sizeof(void*)*4, x_1075);
return x_1077;
}
else
{
lean_object* x_1078; 
x_1078 = lean_ctor_get(x_1030, 3);
lean_inc(x_1078);
if (lean_obj_tag(x_1078) == 0)
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; lean_object* x_1083; 
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 lean_ctor_release(x_1035, 2);
 lean_ctor_release(x_1035, 3);
 x_1079 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1079 = lean_box(0);
}
lean_inc(x_1030);
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1025);
lean_ctor_set(x_1080, 1, x_1018);
lean_ctor_set(x_1080, 2, x_1019);
lean_ctor_set(x_1080, 3, x_1030);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1081 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1081 = lean_box(0);
}
lean_ctor_set_uint8(x_1080, sizeof(void*)*4, x_1028);
x_1082 = 0;
if (lean_is_scalar(x_1081)) {
 x_1083 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1083 = x_1081;
}
lean_ctor_set(x_1083, 0, x_1029);
lean_ctor_set(x_1083, 1, x_1023);
lean_ctor_set(x_1083, 2, x_1024);
lean_ctor_set(x_1083, 3, x_1080);
lean_ctor_set_uint8(x_1083, sizeof(void*)*4, x_1082);
return x_1083;
}
else
{
uint8_t x_1084; 
x_1084 = lean_ctor_get_uint8(x_1078, sizeof(void*)*4);
if (x_1084 == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1085 = lean_ctor_get(x_1030, 1);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1030, 2);
lean_inc(x_1086);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1087 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1087 = lean_box(0);
}
x_1088 = lean_ctor_get(x_1078, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1078, 1);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1078, 2);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1078, 3);
lean_inc(x_1091);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 lean_ctor_release(x_1078, 2);
 lean_ctor_release(x_1078, 3);
 x_1092 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1092 = lean_box(0);
}
lean_inc(x_1035);
if (lean_is_scalar(x_1092)) {
 x_1093 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1093 = x_1092;
}
lean_ctor_set(x_1093, 0, x_1025);
lean_ctor_set(x_1093, 1, x_1018);
lean_ctor_set(x_1093, 2, x_1019);
lean_ctor_set(x_1093, 3, x_1035);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 lean_ctor_release(x_1035, 2);
 lean_ctor_release(x_1035, 3);
 x_1094 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1094 = lean_box(0);
}
lean_ctor_set_uint8(x_1093, sizeof(void*)*4, x_1028);
if (lean_is_scalar(x_1094)) {
 x_1095 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1095 = x_1094;
}
lean_ctor_set(x_1095, 0, x_1088);
lean_ctor_set(x_1095, 1, x_1089);
lean_ctor_set(x_1095, 2, x_1090);
lean_ctor_set(x_1095, 3, x_1091);
lean_ctor_set_uint8(x_1095, sizeof(void*)*4, x_1028);
x_1096 = 0;
if (lean_is_scalar(x_1087)) {
 x_1097 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1097 = x_1087;
}
lean_ctor_set(x_1097, 0, x_1093);
lean_ctor_set(x_1097, 1, x_1085);
lean_ctor_set(x_1097, 2, x_1086);
lean_ctor_set(x_1097, 3, x_1095);
lean_ctor_set_uint8(x_1097, sizeof(void*)*4, x_1096);
x_1098 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1098, 0, x_1029);
lean_ctor_set(x_1098, 1, x_1023);
lean_ctor_set(x_1098, 2, x_1024);
lean_ctor_set(x_1098, 3, x_1097);
lean_ctor_set_uint8(x_1098, sizeof(void*)*4, x_1096);
return x_1098;
}
else
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; lean_object* x_1111; 
x_1099 = lean_ctor_get(x_1030, 1);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1030, 2);
lean_inc(x_1100);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 lean_ctor_release(x_1030, 1);
 lean_ctor_release(x_1030, 2);
 lean_ctor_release(x_1030, 3);
 x_1101 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1101 = lean_box(0);
}
x_1102 = lean_ctor_get(x_1035, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1035, 1);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1035, 2);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1035, 3);
lean_inc(x_1105);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 lean_ctor_release(x_1035, 2);
 lean_ctor_release(x_1035, 3);
 x_1106 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1106 = lean_box(0);
}
if (lean_is_scalar(x_1106)) {
 x_1107 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1107 = x_1106;
}
lean_ctor_set(x_1107, 0, x_1102);
lean_ctor_set(x_1107, 1, x_1103);
lean_ctor_set(x_1107, 2, x_1104);
lean_ctor_set(x_1107, 3, x_1105);
lean_ctor_set_uint8(x_1107, sizeof(void*)*4, x_1084);
if (lean_is_scalar(x_1101)) {
 x_1108 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1108 = x_1101;
}
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_1099);
lean_ctor_set(x_1108, 2, x_1100);
lean_ctor_set(x_1108, 3, x_1078);
lean_ctor_set_uint8(x_1108, sizeof(void*)*4, x_1034);
x_1109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1109, 0, x_1025);
lean_ctor_set(x_1109, 1, x_1018);
lean_ctor_set(x_1109, 2, x_1019);
lean_ctor_set(x_1109, 3, x_1108);
lean_ctor_set_uint8(x_1109, sizeof(void*)*4, x_1028);
x_1110 = 0;
x_1111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1111, 0, x_1029);
lean_ctor_set(x_1111, 1, x_1023);
lean_ctor_set(x_1111, 2, x_1024);
lean_ctor_set(x_1111, 3, x_1109);
lean_ctor_set_uint8(x_1111, sizeof(void*)*4, x_1110);
return x_1111;
}
}
}
}
}
else
{
lean_object* x_1112; uint8_t x_1113; lean_object* x_1114; 
x_1112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1112, 0, x_1025);
lean_ctor_set(x_1112, 1, x_1018);
lean_ctor_set(x_1112, 2, x_1019);
lean_ctor_set(x_1112, 3, x_1030);
lean_ctor_set_uint8(x_1112, sizeof(void*)*4, x_1028);
x_1113 = 0;
x_1114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1114, 0, x_1029);
lean_ctor_set(x_1114, 1, x_1023);
lean_ctor_set(x_1114, 2, x_1024);
lean_ctor_set(x_1114, 3, x_1112);
lean_ctor_set_uint8(x_1114, sizeof(void*)*4, x_1113);
return x_1114;
}
}
}
}
}
}
else
{
uint8_t x_1115; 
x_1115 = !lean_is_exclusive(x_1);
if (x_1115 == 0)
{
uint8_t x_1116; 
x_1116 = !lean_is_exclusive(x_4);
if (x_1116 == 0)
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; uint8_t x_1125; 
x_1117 = lean_ctor_get(x_1, 0);
x_1118 = lean_ctor_get(x_1, 1);
x_1119 = lean_ctor_get(x_1, 2);
x_1120 = lean_ctor_get(x_1, 3);
x_1121 = lean_ctor_get(x_4, 0);
x_1122 = lean_ctor_get(x_4, 1);
x_1123 = lean_ctor_get(x_4, 2);
x_1124 = lean_ctor_get(x_4, 3);
lean_ctor_set(x_4, 3, x_1120);
lean_ctor_set(x_4, 2, x_1119);
lean_ctor_set(x_4, 1, x_1118);
lean_ctor_set(x_4, 0, x_1117);
x_1125 = 0;
lean_inc(x_1124);
lean_inc(x_1123);
lean_inc(x_1122);
lean_inc(x_1121);
lean_ctor_set(x_1, 3, x_1124);
lean_ctor_set(x_1, 2, x_1123);
lean_ctor_set(x_1, 1, x_1122);
lean_ctor_set(x_1, 0, x_1121);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1125);
if (lean_obj_tag(x_1121) == 0)
{
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1126; uint8_t x_1127; lean_object* x_1128; 
lean_dec(x_1);
x_1126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1126, 0, x_1124);
lean_ctor_set(x_1126, 1, x_1122);
lean_ctor_set(x_1126, 2, x_1123);
lean_ctor_set(x_1126, 3, x_1124);
lean_ctor_set_uint8(x_1126, sizeof(void*)*4, x_1125);
x_1127 = 1;
x_1128 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1128, 0, x_4);
lean_ctor_set(x_1128, 1, x_2);
lean_ctor_set(x_1128, 2, x_3);
lean_ctor_set(x_1128, 3, x_1126);
lean_ctor_set_uint8(x_1128, sizeof(void*)*4, x_1127);
return x_1128;
}
else
{
uint8_t x_1129; 
x_1129 = lean_ctor_get_uint8(x_1124, sizeof(void*)*4);
if (x_1129 == 0)
{
uint8_t x_1130; 
lean_dec(x_1);
x_1130 = !lean_is_exclusive(x_1124);
if (x_1130 == 0)
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; uint8_t x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1131 = lean_ctor_get(x_1124, 0);
x_1132 = lean_ctor_get(x_1124, 1);
x_1133 = lean_ctor_get(x_1124, 2);
x_1134 = lean_ctor_get(x_1124, 3);
x_1135 = 1;
lean_ctor_set(x_1124, 3, x_1121);
lean_ctor_set(x_1124, 2, x_3);
lean_ctor_set(x_1124, 1, x_2);
lean_ctor_set(x_1124, 0, x_4);
lean_ctor_set_uint8(x_1124, sizeof(void*)*4, x_1135);
x_1136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1136, 0, x_1131);
lean_ctor_set(x_1136, 1, x_1132);
lean_ctor_set(x_1136, 2, x_1133);
lean_ctor_set(x_1136, 3, x_1134);
lean_ctor_set_uint8(x_1136, sizeof(void*)*4, x_1135);
x_1137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1137, 0, x_1124);
lean_ctor_set(x_1137, 1, x_1122);
lean_ctor_set(x_1137, 2, x_1123);
lean_ctor_set(x_1137, 3, x_1136);
lean_ctor_set_uint8(x_1137, sizeof(void*)*4, x_1125);
return x_1137;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; uint8_t x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1138 = lean_ctor_get(x_1124, 0);
x_1139 = lean_ctor_get(x_1124, 1);
x_1140 = lean_ctor_get(x_1124, 2);
x_1141 = lean_ctor_get(x_1124, 3);
lean_inc(x_1141);
lean_inc(x_1140);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1124);
x_1142 = 1;
x_1143 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1143, 0, x_4);
lean_ctor_set(x_1143, 1, x_2);
lean_ctor_set(x_1143, 2, x_3);
lean_ctor_set(x_1143, 3, x_1121);
lean_ctor_set_uint8(x_1143, sizeof(void*)*4, x_1142);
x_1144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1144, 0, x_1138);
lean_ctor_set(x_1144, 1, x_1139);
lean_ctor_set(x_1144, 2, x_1140);
lean_ctor_set(x_1144, 3, x_1141);
lean_ctor_set_uint8(x_1144, sizeof(void*)*4, x_1142);
x_1145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1145, 0, x_1143);
lean_ctor_set(x_1145, 1, x_1122);
lean_ctor_set(x_1145, 2, x_1123);
lean_ctor_set(x_1145, 3, x_1144);
lean_ctor_set_uint8(x_1145, sizeof(void*)*4, x_1125);
return x_1145;
}
}
else
{
uint8_t x_1146; 
lean_dec(x_1123);
lean_dec(x_1122);
x_1146 = !lean_is_exclusive(x_1124);
if (x_1146 == 0)
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; uint8_t x_1151; 
x_1147 = lean_ctor_get(x_1124, 3);
lean_dec(x_1147);
x_1148 = lean_ctor_get(x_1124, 2);
lean_dec(x_1148);
x_1149 = lean_ctor_get(x_1124, 1);
lean_dec(x_1149);
x_1150 = lean_ctor_get(x_1124, 0);
lean_dec(x_1150);
x_1151 = 1;
lean_ctor_set(x_1124, 3, x_1);
lean_ctor_set(x_1124, 2, x_3);
lean_ctor_set(x_1124, 1, x_2);
lean_ctor_set(x_1124, 0, x_4);
lean_ctor_set_uint8(x_1124, sizeof(void*)*4, x_1151);
return x_1124;
}
else
{
uint8_t x_1152; lean_object* x_1153; 
lean_dec(x_1124);
x_1152 = 1;
x_1153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1153, 0, x_4);
lean_ctor_set(x_1153, 1, x_2);
lean_ctor_set(x_1153, 2, x_3);
lean_ctor_set(x_1153, 3, x_1);
lean_ctor_set_uint8(x_1153, sizeof(void*)*4, x_1152);
return x_1153;
}
}
}
}
else
{
uint8_t x_1154; 
x_1154 = lean_ctor_get_uint8(x_1121, sizeof(void*)*4);
if (x_1154 == 0)
{
uint8_t x_1155; 
lean_dec(x_1);
x_1155 = !lean_is_exclusive(x_1121);
if (x_1155 == 0)
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; uint8_t x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1156 = lean_ctor_get(x_1121, 0);
x_1157 = lean_ctor_get(x_1121, 1);
x_1158 = lean_ctor_get(x_1121, 2);
x_1159 = lean_ctor_get(x_1121, 3);
x_1160 = 1;
lean_ctor_set(x_1121, 3, x_1156);
lean_ctor_set(x_1121, 2, x_3);
lean_ctor_set(x_1121, 1, x_2);
lean_ctor_set(x_1121, 0, x_4);
lean_ctor_set_uint8(x_1121, sizeof(void*)*4, x_1160);
x_1161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1161, 0, x_1159);
lean_ctor_set(x_1161, 1, x_1122);
lean_ctor_set(x_1161, 2, x_1123);
lean_ctor_set(x_1161, 3, x_1124);
lean_ctor_set_uint8(x_1161, sizeof(void*)*4, x_1160);
x_1162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1162, 0, x_1121);
lean_ctor_set(x_1162, 1, x_1157);
lean_ctor_set(x_1162, 2, x_1158);
lean_ctor_set(x_1162, 3, x_1161);
lean_ctor_set_uint8(x_1162, sizeof(void*)*4, x_1125);
return x_1162;
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; uint8_t x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1163 = lean_ctor_get(x_1121, 0);
x_1164 = lean_ctor_get(x_1121, 1);
x_1165 = lean_ctor_get(x_1121, 2);
x_1166 = lean_ctor_get(x_1121, 3);
lean_inc(x_1166);
lean_inc(x_1165);
lean_inc(x_1164);
lean_inc(x_1163);
lean_dec(x_1121);
x_1167 = 1;
x_1168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1168, 0, x_4);
lean_ctor_set(x_1168, 1, x_2);
lean_ctor_set(x_1168, 2, x_3);
lean_ctor_set(x_1168, 3, x_1163);
lean_ctor_set_uint8(x_1168, sizeof(void*)*4, x_1167);
x_1169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1169, 0, x_1166);
lean_ctor_set(x_1169, 1, x_1122);
lean_ctor_set(x_1169, 2, x_1123);
lean_ctor_set(x_1169, 3, x_1124);
lean_ctor_set_uint8(x_1169, sizeof(void*)*4, x_1167);
x_1170 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1170, 0, x_1168);
lean_ctor_set(x_1170, 1, x_1164);
lean_ctor_set(x_1170, 2, x_1165);
lean_ctor_set(x_1170, 3, x_1169);
lean_ctor_set_uint8(x_1170, sizeof(void*)*4, x_1125);
return x_1170;
}
}
else
{
if (lean_obj_tag(x_1124) == 0)
{
uint8_t x_1171; 
lean_dec(x_1123);
lean_dec(x_1122);
x_1171 = !lean_is_exclusive(x_1121);
if (x_1171 == 0)
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; uint8_t x_1176; 
x_1172 = lean_ctor_get(x_1121, 3);
lean_dec(x_1172);
x_1173 = lean_ctor_get(x_1121, 2);
lean_dec(x_1173);
x_1174 = lean_ctor_get(x_1121, 1);
lean_dec(x_1174);
x_1175 = lean_ctor_get(x_1121, 0);
lean_dec(x_1175);
x_1176 = 1;
lean_ctor_set(x_1121, 3, x_1);
lean_ctor_set(x_1121, 2, x_3);
lean_ctor_set(x_1121, 1, x_2);
lean_ctor_set(x_1121, 0, x_4);
lean_ctor_set_uint8(x_1121, sizeof(void*)*4, x_1176);
return x_1121;
}
else
{
uint8_t x_1177; lean_object* x_1178; 
lean_dec(x_1121);
x_1177 = 1;
x_1178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1178, 0, x_4);
lean_ctor_set(x_1178, 1, x_2);
lean_ctor_set(x_1178, 2, x_3);
lean_ctor_set(x_1178, 3, x_1);
lean_ctor_set_uint8(x_1178, sizeof(void*)*4, x_1177);
return x_1178;
}
}
else
{
uint8_t x_1179; 
lean_dec(x_1);
x_1179 = lean_ctor_get_uint8(x_1124, sizeof(void*)*4);
if (x_1179 == 0)
{
uint8_t x_1180; 
x_1180 = !lean_is_exclusive(x_1124);
if (x_1180 == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; uint8_t x_1185; uint8_t x_1186; 
x_1181 = lean_ctor_get(x_1124, 0);
x_1182 = lean_ctor_get(x_1124, 1);
x_1183 = lean_ctor_get(x_1124, 2);
x_1184 = lean_ctor_get(x_1124, 3);
x_1185 = 1;
lean_inc(x_1121);
lean_ctor_set(x_1124, 3, x_1121);
lean_ctor_set(x_1124, 2, x_3);
lean_ctor_set(x_1124, 1, x_2);
lean_ctor_set(x_1124, 0, x_4);
x_1186 = !lean_is_exclusive(x_1121);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1187 = lean_ctor_get(x_1121, 3);
lean_dec(x_1187);
x_1188 = lean_ctor_get(x_1121, 2);
lean_dec(x_1188);
x_1189 = lean_ctor_get(x_1121, 1);
lean_dec(x_1189);
x_1190 = lean_ctor_get(x_1121, 0);
lean_dec(x_1190);
lean_ctor_set_uint8(x_1124, sizeof(void*)*4, x_1185);
lean_ctor_set(x_1121, 3, x_1184);
lean_ctor_set(x_1121, 2, x_1183);
lean_ctor_set(x_1121, 1, x_1182);
lean_ctor_set(x_1121, 0, x_1181);
lean_ctor_set_uint8(x_1121, sizeof(void*)*4, x_1185);
x_1191 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1191, 0, x_1124);
lean_ctor_set(x_1191, 1, x_1122);
lean_ctor_set(x_1191, 2, x_1123);
lean_ctor_set(x_1191, 3, x_1121);
lean_ctor_set_uint8(x_1191, sizeof(void*)*4, x_1125);
return x_1191;
}
else
{
lean_object* x_1192; lean_object* x_1193; 
lean_dec(x_1121);
lean_ctor_set_uint8(x_1124, sizeof(void*)*4, x_1185);
x_1192 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1192, 0, x_1181);
lean_ctor_set(x_1192, 1, x_1182);
lean_ctor_set(x_1192, 2, x_1183);
lean_ctor_set(x_1192, 3, x_1184);
lean_ctor_set_uint8(x_1192, sizeof(void*)*4, x_1185);
x_1193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1193, 0, x_1124);
lean_ctor_set(x_1193, 1, x_1122);
lean_ctor_set(x_1193, 2, x_1123);
lean_ctor_set(x_1193, 3, x_1192);
lean_ctor_set_uint8(x_1193, sizeof(void*)*4, x_1125);
return x_1193;
}
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1194 = lean_ctor_get(x_1124, 0);
x_1195 = lean_ctor_get(x_1124, 1);
x_1196 = lean_ctor_get(x_1124, 2);
x_1197 = lean_ctor_get(x_1124, 3);
lean_inc(x_1197);
lean_inc(x_1196);
lean_inc(x_1195);
lean_inc(x_1194);
lean_dec(x_1124);
x_1198 = 1;
lean_inc(x_1121);
x_1199 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1199, 0, x_4);
lean_ctor_set(x_1199, 1, x_2);
lean_ctor_set(x_1199, 2, x_3);
lean_ctor_set(x_1199, 3, x_1121);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 lean_ctor_release(x_1121, 2);
 lean_ctor_release(x_1121, 3);
 x_1200 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1200 = lean_box(0);
}
lean_ctor_set_uint8(x_1199, sizeof(void*)*4, x_1198);
if (lean_is_scalar(x_1200)) {
 x_1201 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1201 = x_1200;
}
lean_ctor_set(x_1201, 0, x_1194);
lean_ctor_set(x_1201, 1, x_1195);
lean_ctor_set(x_1201, 2, x_1196);
lean_ctor_set(x_1201, 3, x_1197);
lean_ctor_set_uint8(x_1201, sizeof(void*)*4, x_1198);
x_1202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1202, 0, x_1199);
lean_ctor_set(x_1202, 1, x_1122);
lean_ctor_set(x_1202, 2, x_1123);
lean_ctor_set(x_1202, 3, x_1201);
lean_ctor_set_uint8(x_1202, sizeof(void*)*4, x_1125);
return x_1202;
}
}
else
{
uint8_t x_1203; 
x_1203 = !lean_is_exclusive(x_1121);
if (x_1203 == 0)
{
lean_object* x_1204; uint8_t x_1205; lean_object* x_1206; 
lean_ctor_set_uint8(x_1121, sizeof(void*)*4, x_1179);
x_1204 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1204, 0, x_1121);
lean_ctor_set(x_1204, 1, x_1122);
lean_ctor_set(x_1204, 2, x_1123);
lean_ctor_set(x_1204, 3, x_1124);
lean_ctor_set_uint8(x_1204, sizeof(void*)*4, x_1125);
x_1205 = 1;
x_1206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1206, 0, x_4);
lean_ctor_set(x_1206, 1, x_2);
lean_ctor_set(x_1206, 2, x_3);
lean_ctor_set(x_1206, 3, x_1204);
lean_ctor_set_uint8(x_1206, sizeof(void*)*4, x_1205);
return x_1206;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; uint8_t x_1213; lean_object* x_1214; 
x_1207 = lean_ctor_get(x_1121, 0);
x_1208 = lean_ctor_get(x_1121, 1);
x_1209 = lean_ctor_get(x_1121, 2);
x_1210 = lean_ctor_get(x_1121, 3);
lean_inc(x_1210);
lean_inc(x_1209);
lean_inc(x_1208);
lean_inc(x_1207);
lean_dec(x_1121);
x_1211 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1211, 0, x_1207);
lean_ctor_set(x_1211, 1, x_1208);
lean_ctor_set(x_1211, 2, x_1209);
lean_ctor_set(x_1211, 3, x_1210);
lean_ctor_set_uint8(x_1211, sizeof(void*)*4, x_1179);
x_1212 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1212, 0, x_1211);
lean_ctor_set(x_1212, 1, x_1122);
lean_ctor_set(x_1212, 2, x_1123);
lean_ctor_set(x_1212, 3, x_1124);
lean_ctor_set_uint8(x_1212, sizeof(void*)*4, x_1125);
x_1213 = 1;
x_1214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1214, 0, x_4);
lean_ctor_set(x_1214, 1, x_2);
lean_ctor_set(x_1214, 2, x_3);
lean_ctor_set(x_1214, 3, x_1212);
lean_ctor_set_uint8(x_1214, sizeof(void*)*4, x_1213);
return x_1214;
}
}
}
}
}
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; uint8_t x_1224; 
x_1215 = lean_ctor_get(x_1, 0);
x_1216 = lean_ctor_get(x_1, 1);
x_1217 = lean_ctor_get(x_1, 2);
x_1218 = lean_ctor_get(x_1, 3);
x_1219 = lean_ctor_get(x_4, 0);
x_1220 = lean_ctor_get(x_4, 1);
x_1221 = lean_ctor_get(x_4, 2);
x_1222 = lean_ctor_get(x_4, 3);
lean_inc(x_1222);
lean_inc(x_1221);
lean_inc(x_1220);
lean_inc(x_1219);
lean_dec(x_4);
x_1223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1223, 0, x_1215);
lean_ctor_set(x_1223, 1, x_1216);
lean_ctor_set(x_1223, 2, x_1217);
lean_ctor_set(x_1223, 3, x_1218);
lean_ctor_set_uint8(x_1223, sizeof(void*)*4, x_632);
x_1224 = 0;
lean_inc(x_1222);
lean_inc(x_1221);
lean_inc(x_1220);
lean_inc(x_1219);
lean_ctor_set(x_1, 3, x_1222);
lean_ctor_set(x_1, 2, x_1221);
lean_ctor_set(x_1, 1, x_1220);
lean_ctor_set(x_1, 0, x_1219);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1224);
if (lean_obj_tag(x_1219) == 0)
{
if (lean_obj_tag(x_1222) == 0)
{
lean_object* x_1225; uint8_t x_1226; lean_object* x_1227; 
lean_dec(x_1);
x_1225 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1225, 0, x_1222);
lean_ctor_set(x_1225, 1, x_1220);
lean_ctor_set(x_1225, 2, x_1221);
lean_ctor_set(x_1225, 3, x_1222);
lean_ctor_set_uint8(x_1225, sizeof(void*)*4, x_1224);
x_1226 = 1;
x_1227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1227, 0, x_1223);
lean_ctor_set(x_1227, 1, x_2);
lean_ctor_set(x_1227, 2, x_3);
lean_ctor_set(x_1227, 3, x_1225);
lean_ctor_set_uint8(x_1227, sizeof(void*)*4, x_1226);
return x_1227;
}
else
{
uint8_t x_1228; 
x_1228 = lean_ctor_get_uint8(x_1222, sizeof(void*)*4);
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
lean_dec(x_1);
x_1229 = lean_ctor_get(x_1222, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1222, 1);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1222, 2);
lean_inc(x_1231);
x_1232 = lean_ctor_get(x_1222, 3);
lean_inc(x_1232);
if (lean_is_exclusive(x_1222)) {
 lean_ctor_release(x_1222, 0);
 lean_ctor_release(x_1222, 1);
 lean_ctor_release(x_1222, 2);
 lean_ctor_release(x_1222, 3);
 x_1233 = x_1222;
} else {
 lean_dec_ref(x_1222);
 x_1233 = lean_box(0);
}
x_1234 = 1;
if (lean_is_scalar(x_1233)) {
 x_1235 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1235 = x_1233;
}
lean_ctor_set(x_1235, 0, x_1223);
lean_ctor_set(x_1235, 1, x_2);
lean_ctor_set(x_1235, 2, x_3);
lean_ctor_set(x_1235, 3, x_1219);
lean_ctor_set_uint8(x_1235, sizeof(void*)*4, x_1234);
x_1236 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1236, 0, x_1229);
lean_ctor_set(x_1236, 1, x_1230);
lean_ctor_set(x_1236, 2, x_1231);
lean_ctor_set(x_1236, 3, x_1232);
lean_ctor_set_uint8(x_1236, sizeof(void*)*4, x_1234);
x_1237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1237, 0, x_1235);
lean_ctor_set(x_1237, 1, x_1220);
lean_ctor_set(x_1237, 2, x_1221);
lean_ctor_set(x_1237, 3, x_1236);
lean_ctor_set_uint8(x_1237, sizeof(void*)*4, x_1224);
return x_1237;
}
else
{
lean_object* x_1238; uint8_t x_1239; lean_object* x_1240; 
lean_dec(x_1221);
lean_dec(x_1220);
if (lean_is_exclusive(x_1222)) {
 lean_ctor_release(x_1222, 0);
 lean_ctor_release(x_1222, 1);
 lean_ctor_release(x_1222, 2);
 lean_ctor_release(x_1222, 3);
 x_1238 = x_1222;
} else {
 lean_dec_ref(x_1222);
 x_1238 = lean_box(0);
}
x_1239 = 1;
if (lean_is_scalar(x_1238)) {
 x_1240 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1240 = x_1238;
}
lean_ctor_set(x_1240, 0, x_1223);
lean_ctor_set(x_1240, 1, x_2);
lean_ctor_set(x_1240, 2, x_3);
lean_ctor_set(x_1240, 3, x_1);
lean_ctor_set_uint8(x_1240, sizeof(void*)*4, x_1239);
return x_1240;
}
}
}
else
{
uint8_t x_1241; 
x_1241 = lean_ctor_get_uint8(x_1219, sizeof(void*)*4);
if (x_1241 == 0)
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; uint8_t x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_1);
x_1242 = lean_ctor_get(x_1219, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1219, 1);
lean_inc(x_1243);
x_1244 = lean_ctor_get(x_1219, 2);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1219, 3);
lean_inc(x_1245);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 lean_ctor_release(x_1219, 2);
 lean_ctor_release(x_1219, 3);
 x_1246 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1246 = lean_box(0);
}
x_1247 = 1;
if (lean_is_scalar(x_1246)) {
 x_1248 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1248 = x_1246;
}
lean_ctor_set(x_1248, 0, x_1223);
lean_ctor_set(x_1248, 1, x_2);
lean_ctor_set(x_1248, 2, x_3);
lean_ctor_set(x_1248, 3, x_1242);
lean_ctor_set_uint8(x_1248, sizeof(void*)*4, x_1247);
x_1249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1249, 0, x_1245);
lean_ctor_set(x_1249, 1, x_1220);
lean_ctor_set(x_1249, 2, x_1221);
lean_ctor_set(x_1249, 3, x_1222);
lean_ctor_set_uint8(x_1249, sizeof(void*)*4, x_1247);
x_1250 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1250, 0, x_1248);
lean_ctor_set(x_1250, 1, x_1243);
lean_ctor_set(x_1250, 2, x_1244);
lean_ctor_set(x_1250, 3, x_1249);
lean_ctor_set_uint8(x_1250, sizeof(void*)*4, x_1224);
return x_1250;
}
else
{
if (lean_obj_tag(x_1222) == 0)
{
lean_object* x_1251; uint8_t x_1252; lean_object* x_1253; 
lean_dec(x_1221);
lean_dec(x_1220);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 lean_ctor_release(x_1219, 2);
 lean_ctor_release(x_1219, 3);
 x_1251 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1251 = lean_box(0);
}
x_1252 = 1;
if (lean_is_scalar(x_1251)) {
 x_1253 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1253 = x_1251;
}
lean_ctor_set(x_1253, 0, x_1223);
lean_ctor_set(x_1253, 1, x_2);
lean_ctor_set(x_1253, 2, x_3);
lean_ctor_set(x_1253, 3, x_1);
lean_ctor_set_uint8(x_1253, sizeof(void*)*4, x_1252);
return x_1253;
}
else
{
uint8_t x_1254; 
lean_dec(x_1);
x_1254 = lean_ctor_get_uint8(x_1222, sizeof(void*)*4);
if (x_1254 == 0)
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1255 = lean_ctor_get(x_1222, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1222, 1);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_1222, 2);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1222, 3);
lean_inc(x_1258);
if (lean_is_exclusive(x_1222)) {
 lean_ctor_release(x_1222, 0);
 lean_ctor_release(x_1222, 1);
 lean_ctor_release(x_1222, 2);
 lean_ctor_release(x_1222, 3);
 x_1259 = x_1222;
} else {
 lean_dec_ref(x_1222);
 x_1259 = lean_box(0);
}
x_1260 = 1;
lean_inc(x_1219);
if (lean_is_scalar(x_1259)) {
 x_1261 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1261 = x_1259;
}
lean_ctor_set(x_1261, 0, x_1223);
lean_ctor_set(x_1261, 1, x_2);
lean_ctor_set(x_1261, 2, x_3);
lean_ctor_set(x_1261, 3, x_1219);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 lean_ctor_release(x_1219, 2);
 lean_ctor_release(x_1219, 3);
 x_1262 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1262 = lean_box(0);
}
lean_ctor_set_uint8(x_1261, sizeof(void*)*4, x_1260);
if (lean_is_scalar(x_1262)) {
 x_1263 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1263 = x_1262;
}
lean_ctor_set(x_1263, 0, x_1255);
lean_ctor_set(x_1263, 1, x_1256);
lean_ctor_set(x_1263, 2, x_1257);
lean_ctor_set(x_1263, 3, x_1258);
lean_ctor_set_uint8(x_1263, sizeof(void*)*4, x_1260);
x_1264 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1264, 0, x_1261);
lean_ctor_set(x_1264, 1, x_1220);
lean_ctor_set(x_1264, 2, x_1221);
lean_ctor_set(x_1264, 3, x_1263);
lean_ctor_set_uint8(x_1264, sizeof(void*)*4, x_1224);
return x_1264;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; uint8_t x_1272; lean_object* x_1273; 
x_1265 = lean_ctor_get(x_1219, 0);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1219, 1);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1219, 2);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_1219, 3);
lean_inc(x_1268);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 lean_ctor_release(x_1219, 2);
 lean_ctor_release(x_1219, 3);
 x_1269 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1269 = lean_box(0);
}
if (lean_is_scalar(x_1269)) {
 x_1270 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1270 = x_1269;
}
lean_ctor_set(x_1270, 0, x_1265);
lean_ctor_set(x_1270, 1, x_1266);
lean_ctor_set(x_1270, 2, x_1267);
lean_ctor_set(x_1270, 3, x_1268);
lean_ctor_set_uint8(x_1270, sizeof(void*)*4, x_1254);
x_1271 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1271, 0, x_1270);
lean_ctor_set(x_1271, 1, x_1220);
lean_ctor_set(x_1271, 2, x_1221);
lean_ctor_set(x_1271, 3, x_1222);
lean_ctor_set_uint8(x_1271, sizeof(void*)*4, x_1224);
x_1272 = 1;
x_1273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1273, 0, x_1223);
lean_ctor_set(x_1273, 1, x_2);
lean_ctor_set(x_1273, 2, x_3);
lean_ctor_set(x_1273, 3, x_1271);
lean_ctor_set_uint8(x_1273, sizeof(void*)*4, x_1272);
return x_1273;
}
}
}
}
}
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; lean_object* x_1285; 
x_1274 = lean_ctor_get(x_1, 0);
x_1275 = lean_ctor_get(x_1, 1);
x_1276 = lean_ctor_get(x_1, 2);
x_1277 = lean_ctor_get(x_1, 3);
lean_inc(x_1277);
lean_inc(x_1276);
lean_inc(x_1275);
lean_inc(x_1274);
lean_dec(x_1);
x_1278 = lean_ctor_get(x_4, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_4, 1);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_4, 2);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_4, 3);
lean_inc(x_1281);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1282 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1282 = lean_box(0);
}
if (lean_is_scalar(x_1282)) {
 x_1283 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1283 = x_1282;
}
lean_ctor_set(x_1283, 0, x_1274);
lean_ctor_set(x_1283, 1, x_1275);
lean_ctor_set(x_1283, 2, x_1276);
lean_ctor_set(x_1283, 3, x_1277);
lean_ctor_set_uint8(x_1283, sizeof(void*)*4, x_632);
x_1284 = 0;
lean_inc(x_1281);
lean_inc(x_1280);
lean_inc(x_1279);
lean_inc(x_1278);
x_1285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1285, 0, x_1278);
lean_ctor_set(x_1285, 1, x_1279);
lean_ctor_set(x_1285, 2, x_1280);
lean_ctor_set(x_1285, 3, x_1281);
lean_ctor_set_uint8(x_1285, sizeof(void*)*4, x_1284);
if (lean_obj_tag(x_1278) == 0)
{
if (lean_obj_tag(x_1281) == 0)
{
lean_object* x_1286; uint8_t x_1287; lean_object* x_1288; 
lean_dec(x_1285);
x_1286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1286, 0, x_1281);
lean_ctor_set(x_1286, 1, x_1279);
lean_ctor_set(x_1286, 2, x_1280);
lean_ctor_set(x_1286, 3, x_1281);
lean_ctor_set_uint8(x_1286, sizeof(void*)*4, x_1284);
x_1287 = 1;
x_1288 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1288, 0, x_1283);
lean_ctor_set(x_1288, 1, x_2);
lean_ctor_set(x_1288, 2, x_3);
lean_ctor_set(x_1288, 3, x_1286);
lean_ctor_set_uint8(x_1288, sizeof(void*)*4, x_1287);
return x_1288;
}
else
{
uint8_t x_1289; 
x_1289 = lean_ctor_get_uint8(x_1281, sizeof(void*)*4);
if (x_1289 == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; uint8_t x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
lean_dec(x_1285);
x_1290 = lean_ctor_get(x_1281, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1281, 1);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1281, 2);
lean_inc(x_1292);
x_1293 = lean_ctor_get(x_1281, 3);
lean_inc(x_1293);
if (lean_is_exclusive(x_1281)) {
 lean_ctor_release(x_1281, 0);
 lean_ctor_release(x_1281, 1);
 lean_ctor_release(x_1281, 2);
 lean_ctor_release(x_1281, 3);
 x_1294 = x_1281;
} else {
 lean_dec_ref(x_1281);
 x_1294 = lean_box(0);
}
x_1295 = 1;
if (lean_is_scalar(x_1294)) {
 x_1296 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1296 = x_1294;
}
lean_ctor_set(x_1296, 0, x_1283);
lean_ctor_set(x_1296, 1, x_2);
lean_ctor_set(x_1296, 2, x_3);
lean_ctor_set(x_1296, 3, x_1278);
lean_ctor_set_uint8(x_1296, sizeof(void*)*4, x_1295);
x_1297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1297, 0, x_1290);
lean_ctor_set(x_1297, 1, x_1291);
lean_ctor_set(x_1297, 2, x_1292);
lean_ctor_set(x_1297, 3, x_1293);
lean_ctor_set_uint8(x_1297, sizeof(void*)*4, x_1295);
x_1298 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1298, 0, x_1296);
lean_ctor_set(x_1298, 1, x_1279);
lean_ctor_set(x_1298, 2, x_1280);
lean_ctor_set(x_1298, 3, x_1297);
lean_ctor_set_uint8(x_1298, sizeof(void*)*4, x_1284);
return x_1298;
}
else
{
lean_object* x_1299; uint8_t x_1300; lean_object* x_1301; 
lean_dec(x_1280);
lean_dec(x_1279);
if (lean_is_exclusive(x_1281)) {
 lean_ctor_release(x_1281, 0);
 lean_ctor_release(x_1281, 1);
 lean_ctor_release(x_1281, 2);
 lean_ctor_release(x_1281, 3);
 x_1299 = x_1281;
} else {
 lean_dec_ref(x_1281);
 x_1299 = lean_box(0);
}
x_1300 = 1;
if (lean_is_scalar(x_1299)) {
 x_1301 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1301 = x_1299;
}
lean_ctor_set(x_1301, 0, x_1283);
lean_ctor_set(x_1301, 1, x_2);
lean_ctor_set(x_1301, 2, x_3);
lean_ctor_set(x_1301, 3, x_1285);
lean_ctor_set_uint8(x_1301, sizeof(void*)*4, x_1300);
return x_1301;
}
}
}
else
{
uint8_t x_1302; 
x_1302 = lean_ctor_get_uint8(x_1278, sizeof(void*)*4);
if (x_1302 == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_1285);
x_1303 = lean_ctor_get(x_1278, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1278, 1);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1278, 2);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1278, 3);
lean_inc(x_1306);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 lean_ctor_release(x_1278, 2);
 lean_ctor_release(x_1278, 3);
 x_1307 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1307 = lean_box(0);
}
x_1308 = 1;
if (lean_is_scalar(x_1307)) {
 x_1309 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1309 = x_1307;
}
lean_ctor_set(x_1309, 0, x_1283);
lean_ctor_set(x_1309, 1, x_2);
lean_ctor_set(x_1309, 2, x_3);
lean_ctor_set(x_1309, 3, x_1303);
lean_ctor_set_uint8(x_1309, sizeof(void*)*4, x_1308);
x_1310 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1310, 0, x_1306);
lean_ctor_set(x_1310, 1, x_1279);
lean_ctor_set(x_1310, 2, x_1280);
lean_ctor_set(x_1310, 3, x_1281);
lean_ctor_set_uint8(x_1310, sizeof(void*)*4, x_1308);
x_1311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1311, 0, x_1309);
lean_ctor_set(x_1311, 1, x_1304);
lean_ctor_set(x_1311, 2, x_1305);
lean_ctor_set(x_1311, 3, x_1310);
lean_ctor_set_uint8(x_1311, sizeof(void*)*4, x_1284);
return x_1311;
}
else
{
if (lean_obj_tag(x_1281) == 0)
{
lean_object* x_1312; uint8_t x_1313; lean_object* x_1314; 
lean_dec(x_1280);
lean_dec(x_1279);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 lean_ctor_release(x_1278, 2);
 lean_ctor_release(x_1278, 3);
 x_1312 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1312 = lean_box(0);
}
x_1313 = 1;
if (lean_is_scalar(x_1312)) {
 x_1314 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1314 = x_1312;
}
lean_ctor_set(x_1314, 0, x_1283);
lean_ctor_set(x_1314, 1, x_2);
lean_ctor_set(x_1314, 2, x_3);
lean_ctor_set(x_1314, 3, x_1285);
lean_ctor_set_uint8(x_1314, sizeof(void*)*4, x_1313);
return x_1314;
}
else
{
uint8_t x_1315; 
lean_dec(x_1285);
x_1315 = lean_ctor_get_uint8(x_1281, sizeof(void*)*4);
if (x_1315 == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; uint8_t x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; 
x_1316 = lean_ctor_get(x_1281, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1281, 1);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1281, 2);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1281, 3);
lean_inc(x_1319);
if (lean_is_exclusive(x_1281)) {
 lean_ctor_release(x_1281, 0);
 lean_ctor_release(x_1281, 1);
 lean_ctor_release(x_1281, 2);
 lean_ctor_release(x_1281, 3);
 x_1320 = x_1281;
} else {
 lean_dec_ref(x_1281);
 x_1320 = lean_box(0);
}
x_1321 = 1;
lean_inc(x_1278);
if (lean_is_scalar(x_1320)) {
 x_1322 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1322 = x_1320;
}
lean_ctor_set(x_1322, 0, x_1283);
lean_ctor_set(x_1322, 1, x_2);
lean_ctor_set(x_1322, 2, x_3);
lean_ctor_set(x_1322, 3, x_1278);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 lean_ctor_release(x_1278, 2);
 lean_ctor_release(x_1278, 3);
 x_1323 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1323 = lean_box(0);
}
lean_ctor_set_uint8(x_1322, sizeof(void*)*4, x_1321);
if (lean_is_scalar(x_1323)) {
 x_1324 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1324 = x_1323;
}
lean_ctor_set(x_1324, 0, x_1316);
lean_ctor_set(x_1324, 1, x_1317);
lean_ctor_set(x_1324, 2, x_1318);
lean_ctor_set(x_1324, 3, x_1319);
lean_ctor_set_uint8(x_1324, sizeof(void*)*4, x_1321);
x_1325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1325, 0, x_1322);
lean_ctor_set(x_1325, 1, x_1279);
lean_ctor_set(x_1325, 2, x_1280);
lean_ctor_set(x_1325, 3, x_1324);
lean_ctor_set_uint8(x_1325, sizeof(void*)*4, x_1284);
return x_1325;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; uint8_t x_1333; lean_object* x_1334; 
x_1326 = lean_ctor_get(x_1278, 0);
lean_inc(x_1326);
x_1327 = lean_ctor_get(x_1278, 1);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1278, 2);
lean_inc(x_1328);
x_1329 = lean_ctor_get(x_1278, 3);
lean_inc(x_1329);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 lean_ctor_release(x_1278, 2);
 lean_ctor_release(x_1278, 3);
 x_1330 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1330 = lean_box(0);
}
if (lean_is_scalar(x_1330)) {
 x_1331 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1331 = x_1330;
}
lean_ctor_set(x_1331, 0, x_1326);
lean_ctor_set(x_1331, 1, x_1327);
lean_ctor_set(x_1331, 2, x_1328);
lean_ctor_set(x_1331, 3, x_1329);
lean_ctor_set_uint8(x_1331, sizeof(void*)*4, x_1315);
x_1332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1332, 0, x_1331);
lean_ctor_set(x_1332, 1, x_1279);
lean_ctor_set(x_1332, 2, x_1280);
lean_ctor_set(x_1332, 3, x_1281);
lean_ctor_set_uint8(x_1332, sizeof(void*)*4, x_1284);
x_1333 = 1;
x_1334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1334, 0, x_1283);
lean_ctor_set(x_1334, 1, x_2);
lean_ctor_set(x_1334, 2, x_3);
lean_ctor_set(x_1334, 3, x_1332);
lean_ctor_set_uint8(x_1334, sizeof(void*)*4, x_1333);
return x_1334;
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
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_balLeft___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_1) == 0)
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
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set_uint8(x_10, sizeof(void*)*4, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_8, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = 0;
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_17);
return x_8;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_8);
x_18 = 0;
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_4);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_8, 2);
x_29 = lean_ctor_get(x_8, 3);
x_30 = l_Lean_RBNode_setRed___rarg(x_21);
x_31 = 1;
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_29);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_31);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_30, sizeof(void*)*4);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_30, 3);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_30, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
lean_ctor_set(x_30, 0, x_36);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_40 = 0;
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_41, 2, x_28);
lean_ctor_set(x_41, 3, x_8);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_30, 1);
x_43 = lean_ctor_get(x_30, 2);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_34);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_45 = 0;
x_46 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_27);
lean_ctor_set(x_46, 2, x_28);
lean_ctor_set(x_46, 3, x_8);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_30, 1);
x_50 = lean_ctor_get(x_30, 2);
x_51 = lean_ctor_get(x_30, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_30, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_36);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_36, 0);
x_55 = lean_ctor_get(x_36, 1);
x_56 = lean_ctor_get(x_36, 2);
x_57 = lean_ctor_get(x_36, 3);
lean_ctor_set(x_36, 3, x_54);
lean_ctor_set(x_36, 2, x_50);
lean_ctor_set(x_36, 1, x_49);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_31);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 0, x_57);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
x_58 = 0;
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_36);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_8);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_36, 0);
x_61 = lean_ctor_get(x_36, 1);
x_62 = lean_ctor_get(x_36, 2);
x_63 = lean_ctor_get(x_36, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_36);
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_35);
lean_ctor_set(x_64, 1, x_49);
lean_ctor_set(x_64, 2, x_50);
lean_ctor_set(x_64, 3, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_31);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 0, x_63);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
x_65 = 0;
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_27);
lean_ctor_set(x_66, 2, x_28);
lean_ctor_set(x_66, 3, x_8);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_30, 1);
x_68 = lean_ctor_get(x_30, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_30);
x_69 = lean_ctor_get(x_36, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_36, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_36, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_36, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 x_73 = x_36;
} else {
 lean_dec_ref(x_36);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 4, 1);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_35);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_68);
lean_ctor_set(x_74, 3, x_69);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_31);
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_22);
lean_ctor_set(x_75, 2, x_23);
lean_ctor_set(x_75, 3, x_26);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_31);
x_76 = 0;
lean_ctor_set(x_1, 3, x_75);
lean_ctor_set(x_1, 2, x_71);
lean_ctor_set(x_1, 1, x_70);
lean_ctor_set(x_1, 0, x_74);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_76);
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_27);
lean_ctor_set(x_77, 2, x_28);
lean_ctor_set(x_77, 3, x_8);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_1);
x_78 = !lean_is_exclusive(x_36);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_36, 3);
lean_dec(x_79);
x_80 = lean_ctor_get(x_36, 2);
lean_dec(x_80);
x_81 = lean_ctor_get(x_36, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_36, 0);
lean_dec(x_82);
lean_inc(x_30);
lean_ctor_set(x_36, 3, x_26);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 0, x_30);
x_83 = !lean_is_exclusive(x_30);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_30, 3);
lean_dec(x_84);
x_85 = lean_ctor_get(x_30, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_30, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_30, 0);
lean_dec(x_87);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_31);
x_88 = 0;
lean_ctor_set(x_30, 3, x_8);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 0, x_36);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_88);
return x_30;
}
else
{
uint8_t x_89; lean_object* x_90; 
lean_dec(x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_31);
x_89 = 0;
x_90 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_90, 0, x_36);
lean_ctor_set(x_90, 1, x_27);
lean_ctor_set(x_90, 2, x_28);
lean_ctor_set(x_90, 3, x_8);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
lean_dec(x_36);
lean_inc(x_30);
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_30);
lean_ctor_set(x_91, 1, x_22);
lean_ctor_set(x_91, 2, x_23);
lean_ctor_set(x_91, 3, x_26);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_92 = x_30;
} else {
 lean_dec_ref(x_30);
 x_92 = lean_box(0);
}
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_31);
x_93 = 0;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(1, 4, 1);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_27);
lean_ctor_set(x_94, 2, x_28);
lean_ctor_set(x_94, 3, x_8);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_35, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_30);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_30, 1);
x_98 = lean_ctor_get(x_30, 2);
x_99 = lean_ctor_get(x_30, 3);
x_100 = lean_ctor_get(x_30, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_35);
if (x_101 == 0)
{
uint8_t x_102; lean_object* x_103; 
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_31);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 0, x_99);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
x_102 = 0;
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_27);
lean_ctor_set(x_103, 2, x_28);
lean_ctor_set(x_103, 3, x_8);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_35, 0);
x_105 = lean_ctor_get(x_35, 1);
x_106 = lean_ctor_get(x_35, 2);
x_107 = lean_ctor_get(x_35, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_35);
x_108 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_108, 2, x_106);
lean_ctor_set(x_108, 3, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_31);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 0, x_99);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
x_109 = 0;
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_108);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_109);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_27);
lean_ctor_set(x_110, 2, x_28);
lean_ctor_set(x_110, 3, x_8);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_30, 1);
x_112 = lean_ctor_get(x_30, 2);
x_113 = lean_ctor_get(x_30, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_30);
x_114 = lean_ctor_get(x_35, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_35, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_35, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_35, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 x_118 = x_35;
} else {
 lean_dec_ref(x_35);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_116);
lean_ctor_set(x_119, 3, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_31);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_22);
lean_ctor_set(x_120, 2, x_23);
lean_ctor_set(x_120, 3, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_31);
x_121 = 0;
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_121);
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_27);
lean_ctor_set(x_122, 2, x_28);
lean_ctor_set(x_122, 3, x_8);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_121);
return x_122;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_30, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
lean_free_object(x_1);
x_124 = !lean_is_exclusive(x_35);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_35, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_35, 2);
lean_dec(x_126);
x_127 = lean_ctor_get(x_35, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_35, 0);
lean_dec(x_128);
lean_inc(x_30);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 0, x_30);
x_129 = !lean_is_exclusive(x_30);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_130 = lean_ctor_get(x_30, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_30, 2);
lean_dec(x_131);
x_132 = lean_ctor_get(x_30, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_30, 0);
lean_dec(x_133);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_31);
x_134 = 0;
lean_ctor_set(x_30, 3, x_8);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_134);
return x_30;
}
else
{
uint8_t x_135; lean_object* x_136; 
lean_dec(x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_31);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_35);
lean_ctor_set(x_136, 1, x_27);
lean_ctor_set(x_136, 2, x_28);
lean_ctor_set(x_136, 3, x_8);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
lean_dec(x_35);
lean_inc(x_30);
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_30);
lean_ctor_set(x_137, 1, x_22);
lean_ctor_set(x_137, 2, x_23);
lean_ctor_set(x_137, 3, x_26);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_138 = x_30;
} else {
 lean_dec_ref(x_30);
 x_138 = lean_box(0);
}
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_31);
x_139 = 0;
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(1, 4, 1);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_8);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_139);
return x_140;
}
}
else
{
uint8_t x_141; 
x_141 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_30);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_30, 1);
x_144 = lean_ctor_get(x_30, 2);
x_145 = lean_ctor_get(x_30, 3);
lean_dec(x_145);
x_146 = lean_ctor_get(x_30, 0);
lean_dec(x_146);
x_147 = !lean_is_exclusive(x_123);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_123, 0);
x_149 = lean_ctor_get(x_123, 1);
x_150 = lean_ctor_get(x_123, 2);
x_151 = lean_ctor_get(x_123, 3);
lean_inc(x_35);
lean_ctor_set(x_123, 3, x_148);
lean_ctor_set(x_123, 2, x_144);
lean_ctor_set(x_123, 1, x_143);
lean_ctor_set(x_123, 0, x_35);
x_152 = !lean_is_exclusive(x_35);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_35, 3);
lean_dec(x_153);
x_154 = lean_ctor_get(x_35, 2);
lean_dec(x_154);
x_155 = lean_ctor_get(x_35, 1);
lean_dec(x_155);
x_156 = lean_ctor_get(x_35, 0);
lean_dec(x_156);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_31);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 0, x_151);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_31);
x_157 = 0;
lean_ctor_set(x_30, 3, x_35);
lean_ctor_set(x_30, 2, x_150);
lean_ctor_set(x_30, 1, x_149);
lean_ctor_set(x_30, 0, x_123);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_157);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_157);
return x_1;
}
else
{
lean_object* x_158; uint8_t x_159; 
lean_dec(x_35);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_31);
x_158 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_22);
lean_ctor_set(x_158, 2, x_23);
lean_ctor_set(x_158, 3, x_26);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_31);
x_159 = 0;
lean_ctor_set(x_30, 3, x_158);
lean_ctor_set(x_30, 2, x_150);
lean_ctor_set(x_30, 1, x_149);
lean_ctor_set(x_30, 0, x_123);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_159);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_159);
return x_1;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_160 = lean_ctor_get(x_123, 0);
x_161 = lean_ctor_get(x_123, 1);
x_162 = lean_ctor_get(x_123, 2);
x_163 = lean_ctor_get(x_123, 3);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_123);
lean_inc(x_35);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_35);
lean_ctor_set(x_164, 1, x_143);
lean_ctor_set(x_164, 2, x_144);
lean_ctor_set(x_164, 3, x_160);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 x_165 = x_35;
} else {
 lean_dec_ref(x_35);
 x_165 = lean_box(0);
}
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_31);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_22);
lean_ctor_set(x_166, 2, x_23);
lean_ctor_set(x_166, 3, x_26);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_31);
x_167 = 0;
lean_ctor_set(x_30, 3, x_166);
lean_ctor_set(x_30, 2, x_162);
lean_ctor_set(x_30, 1, x_161);
lean_ctor_set(x_30, 0, x_164);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_167);
return x_1;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_168 = lean_ctor_get(x_30, 1);
x_169 = lean_ctor_get(x_30, 2);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_30);
x_170 = lean_ctor_get(x_123, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_123, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_123, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_123, 3);
lean_inc(x_173);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_174 = x_123;
} else {
 lean_dec_ref(x_123);
 x_174 = lean_box(0);
}
lean_inc(x_35);
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_35);
lean_ctor_set(x_175, 1, x_168);
lean_ctor_set(x_175, 2, x_169);
lean_ctor_set(x_175, 3, x_170);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 x_176 = x_35;
} else {
 lean_dec_ref(x_35);
 x_176 = lean_box(0);
}
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_31);
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 4, 1);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_22);
lean_ctor_set(x_177, 2, x_23);
lean_ctor_set(x_177, 3, x_26);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_31);
x_178 = 0;
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_171);
lean_ctor_set(x_179, 2, x_172);
lean_ctor_set(x_179, 3, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_178);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_179);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_30);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_30, 3);
lean_dec(x_181);
x_182 = lean_ctor_get(x_30, 0);
lean_dec(x_182);
x_183 = !lean_is_exclusive(x_35);
if (x_183 == 0)
{
uint8_t x_184; lean_object* x_185; 
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_141);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_184 = 0;
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_1);
lean_ctor_set(x_185, 1, x_27);
lean_ctor_set(x_185, 2, x_28);
lean_ctor_set(x_185, 3, x_8);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; 
x_186 = lean_ctor_get(x_35, 0);
x_187 = lean_ctor_get(x_35, 1);
x_188 = lean_ctor_get(x_35, 2);
x_189 = lean_ctor_get(x_35, 3);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_35);
x_190 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_190, 0, x_186);
lean_ctor_set(x_190, 1, x_187);
lean_ctor_set(x_190, 2, x_188);
lean_ctor_set(x_190, 3, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_141);
lean_ctor_set(x_30, 0, x_190);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_191 = 0;
x_192 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_192, 0, x_1);
lean_ctor_set(x_192, 1, x_27);
lean_ctor_set(x_192, 2, x_28);
lean_ctor_set(x_192, 3, x_8);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_191);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_30, 1);
x_194 = lean_ctor_get(x_30, 2);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_30);
x_195 = lean_ctor_get(x_35, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_35, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_35, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_35, 3);
lean_inc(x_198);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 x_199 = x_35;
} else {
 lean_dec_ref(x_35);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 4, 1);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_196);
lean_ctor_set(x_200, 2, x_197);
lean_ctor_set(x_200, 3, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_141);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_193);
lean_ctor_set(x_201, 2, x_194);
lean_ctor_set(x_201, 3, x_123);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_34);
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_202 = 0;
x_203 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_27);
lean_ctor_set(x_203, 2, x_28);
lean_ctor_set(x_203, 3, x_8);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_202);
return x_203;
}
}
}
}
}
}
else
{
uint8_t x_204; lean_object* x_205; 
lean_ctor_set(x_1, 3, x_26);
lean_ctor_set(x_1, 0, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
x_204 = 0;
x_205 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_205, 0, x_1);
lean_ctor_set(x_205, 1, x_27);
lean_ctor_set(x_205, 2, x_28);
lean_ctor_set(x_205, 3, x_8);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_8, 0);
x_207 = lean_ctor_get(x_8, 1);
x_208 = lean_ctor_get(x_8, 2);
x_209 = lean_ctor_get(x_8, 3);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_8);
x_210 = l_Lean_RBNode_setRed___rarg(x_21);
x_211 = 1;
x_212 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_2);
lean_ctor_set(x_212, 2, x_3);
lean_ctor_set(x_212, 3, x_4);
lean_ctor_set_uint8(x_212, sizeof(void*)*4, x_211);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_213; lean_object* x_214; 
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 0, x_210);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
x_213 = 0;
x_214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_214, 0, x_1);
lean_ctor_set(x_214, 1, x_207);
lean_ctor_set(x_214, 2, x_208);
lean_ctor_set(x_214, 3, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*4, x_213);
return x_214;
}
else
{
uint8_t x_215; 
x_215 = lean_ctor_get_uint8(x_210, sizeof(void*)*4);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_210, 0);
lean_inc(x_216);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_210, 3);
lean_inc(x_217);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_218 = lean_ctor_get(x_210, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_210, 2);
lean_inc(x_219);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_220 = x_210;
} else {
 lean_dec_ref(x_210);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 4, 1);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_217);
lean_ctor_set(x_221, 1, x_218);
lean_ctor_set(x_221, 2, x_219);
lean_ctor_set(x_221, 3, x_217);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_215);
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
x_222 = 0;
x_223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_223, 0, x_1);
lean_ctor_set(x_223, 1, x_207);
lean_ctor_set(x_223, 2, x_208);
lean_ctor_set(x_223, 3, x_212);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
return x_223;
}
else
{
uint8_t x_224; 
x_224 = lean_ctor_get_uint8(x_217, sizeof(void*)*4);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; 
x_225 = lean_ctor_get(x_210, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_210, 2);
lean_inc(x_226);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_227 = x_210;
} else {
 lean_dec_ref(x_210);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_217, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_217, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_217, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_217, 3);
lean_inc(x_231);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_232 = x_217;
} else {
 lean_dec_ref(x_217);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_216);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_228);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_211);
if (lean_is_scalar(x_227)) {
 x_234 = lean_alloc_ctor(1, 4, 1);
} else {
 x_234 = x_227;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_22);
lean_ctor_set(x_234, 2, x_23);
lean_ctor_set(x_234, 3, x_206);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_211);
x_235 = 0;
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_230);
lean_ctor_set(x_1, 1, x_229);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
x_236 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_236, 0, x_1);
lean_ctor_set(x_236, 1, x_207);
lean_ctor_set(x_236, 2, x_208);
lean_ctor_set(x_236, 3, x_212);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
lean_free_object(x_1);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 x_237 = x_217;
} else {
 lean_dec_ref(x_217);
 x_237 = lean_box(0);
}
lean_inc(x_210);
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 4, 1);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_210);
lean_ctor_set(x_238, 1, x_22);
lean_ctor_set(x_238, 2, x_23);
lean_ctor_set(x_238, 3, x_206);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_239 = x_210;
} else {
 lean_dec_ref(x_210);
 x_239 = lean_box(0);
}
lean_ctor_set_uint8(x_238, sizeof(void*)*4, x_211);
x_240 = 0;
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(1, 4, 1);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_207);
lean_ctor_set(x_241, 2, x_208);
lean_ctor_set(x_241, 3, x_212);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_216, sizeof(void*)*4);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; 
x_243 = lean_ctor_get(x_210, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_210, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_210, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_246 = x_210;
} else {
 lean_dec_ref(x_210);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_216, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_216, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_216, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_216, 3);
lean_inc(x_250);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_251 = x_216;
} else {
 lean_dec_ref(x_216);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 4, 1);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_247);
lean_ctor_set(x_252, 1, x_248);
lean_ctor_set(x_252, 2, x_249);
lean_ctor_set(x_252, 3, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*4, x_211);
if (lean_is_scalar(x_246)) {
 x_253 = lean_alloc_ctor(1, 4, 1);
} else {
 x_253 = x_246;
}
lean_ctor_set(x_253, 0, x_245);
lean_ctor_set(x_253, 1, x_22);
lean_ctor_set(x_253, 2, x_23);
lean_ctor_set(x_253, 3, x_206);
lean_ctor_set_uint8(x_253, sizeof(void*)*4, x_211);
x_254 = 0;
lean_ctor_set(x_1, 3, x_253);
lean_ctor_set(x_1, 2, x_244);
lean_ctor_set(x_1, 1, x_243);
lean_ctor_set(x_1, 0, x_252);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
x_255 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_255, 0, x_1);
lean_ctor_set(x_255, 1, x_207);
lean_ctor_set(x_255, 2, x_208);
lean_ctor_set(x_255, 3, x_212);
lean_ctor_set_uint8(x_255, sizeof(void*)*4, x_254);
return x_255;
}
else
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_210, 3);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; 
lean_free_object(x_1);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_257 = x_216;
} else {
 lean_dec_ref(x_216);
 x_257 = lean_box(0);
}
lean_inc(x_210);
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 4, 1);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_210);
lean_ctor_set(x_258, 1, x_22);
lean_ctor_set(x_258, 2, x_23);
lean_ctor_set(x_258, 3, x_206);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_259 = x_210;
} else {
 lean_dec_ref(x_210);
 x_259 = lean_box(0);
}
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_211);
x_260 = 0;
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(1, 4, 1);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_207);
lean_ctor_set(x_261, 2, x_208);
lean_ctor_set(x_261, 3, x_212);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_260);
return x_261;
}
else
{
uint8_t x_262; 
x_262 = lean_ctor_get_uint8(x_256, sizeof(void*)*4);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; 
x_263 = lean_ctor_get(x_210, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_210, 2);
lean_inc(x_264);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_265 = x_210;
} else {
 lean_dec_ref(x_210);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_256, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_256, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_256, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_256, 3);
lean_inc(x_269);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 lean_ctor_release(x_256, 3);
 x_270 = x_256;
} else {
 lean_dec_ref(x_256);
 x_270 = lean_box(0);
}
lean_inc(x_216);
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 4, 1);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_216);
lean_ctor_set(x_271, 1, x_263);
lean_ctor_set(x_271, 2, x_264);
lean_ctor_set(x_271, 3, x_266);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_272 = x_216;
} else {
 lean_dec_ref(x_216);
 x_272 = lean_box(0);
}
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_211);
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 4, 1);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_269);
lean_ctor_set(x_273, 1, x_22);
lean_ctor_set(x_273, 2, x_23);
lean_ctor_set(x_273, 3, x_206);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_211);
x_274 = 0;
if (lean_is_scalar(x_265)) {
 x_275 = lean_alloc_ctor(1, 4, 1);
} else {
 x_275 = x_265;
}
lean_ctor_set(x_275, 0, x_271);
lean_ctor_set(x_275, 1, x_267);
lean_ctor_set(x_275, 2, x_268);
lean_ctor_set(x_275, 3, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*4, x_274);
lean_ctor_set(x_1, 3, x_212);
lean_ctor_set(x_1, 2, x_208);
lean_ctor_set(x_1, 1, x_207);
lean_ctor_set(x_1, 0, x_275);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; 
x_276 = lean_ctor_get(x_210, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_210, 2);
lean_inc(x_277);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_278 = x_210;
} else {
 lean_dec_ref(x_210);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_216, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_216, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_216, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_216, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_283 = x_216;
} else {
 lean_dec_ref(x_216);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_279);
lean_ctor_set(x_284, 1, x_280);
lean_ctor_set(x_284, 2, x_281);
lean_ctor_set(x_284, 3, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_262);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_278;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_276);
lean_ctor_set(x_285, 2, x_277);
lean_ctor_set(x_285, 3, x_256);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_215);
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
x_286 = 0;
x_287 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_287, 0, x_1);
lean_ctor_set(x_287, 1, x_207);
lean_ctor_set(x_287, 2, x_208);
lean_ctor_set(x_287, 3, x_212);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_286);
return x_287;
}
}
}
}
}
else
{
uint8_t x_288; lean_object* x_289; 
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 0, x_210);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
x_288 = 0;
x_289 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_289, 0, x_1);
lean_ctor_set(x_289, 1, x_207);
lean_ctor_set(x_289, 2, x_208);
lean_ctor_set(x_289, 3, x_212);
lean_ctor_set_uint8(x_289, sizeof(void*)*4, x_288);
return x_289;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_290 = lean_ctor_get(x_1, 0);
x_291 = lean_ctor_get(x_1, 1);
x_292 = lean_ctor_get(x_1, 2);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_1);
x_293 = lean_ctor_get(x_8, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_8, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_8, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_8, 3);
lean_inc(x_296);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_297 = x_8;
} else {
 lean_dec_ref(x_8);
 x_297 = lean_box(0);
}
x_298 = l_Lean_RBNode_setRed___rarg(x_290);
x_299 = 1;
if (lean_is_scalar(x_297)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_297;
}
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_2);
lean_ctor_set(x_300, 2, x_3);
lean_ctor_set(x_300, 3, x_4);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_299);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; 
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_291);
lean_ctor_set(x_301, 2, x_292);
lean_ctor_set(x_301, 3, x_293);
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_299);
x_302 = 0;
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_294);
lean_ctor_set(x_303, 2, x_295);
lean_ctor_set(x_303, 3, x_300);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
return x_303;
}
else
{
uint8_t x_304; 
x_304 = lean_ctor_get_uint8(x_298, sizeof(void*)*4);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_298, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; 
x_306 = lean_ctor_get(x_298, 3);
lean_inc(x_306);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; 
x_307 = lean_ctor_get(x_298, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_298, 2);
lean_inc(x_308);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_309 = x_298;
} else {
 lean_dec_ref(x_298);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 4, 1);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_307);
lean_ctor_set(x_310, 2, x_308);
lean_ctor_set(x_310, 3, x_306);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_304);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_291);
lean_ctor_set(x_311, 2, x_292);
lean_ctor_set(x_311, 3, x_293);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_299);
x_312 = 0;
x_313 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_294);
lean_ctor_set(x_313, 2, x_295);
lean_ctor_set(x_313, 3, x_300);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_312);
return x_313;
}
else
{
uint8_t x_314; 
x_314 = lean_ctor_get_uint8(x_306, sizeof(void*)*4);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; 
x_315 = lean_ctor_get(x_298, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_298, 2);
lean_inc(x_316);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_317 = x_298;
} else {
 lean_dec_ref(x_298);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_306, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_306, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_306, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_306, 3);
lean_inc(x_321);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 x_322 = x_306;
} else {
 lean_dec_ref(x_306);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_305);
lean_ctor_set(x_323, 1, x_315);
lean_ctor_set(x_323, 2, x_316);
lean_ctor_set(x_323, 3, x_318);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_299);
if (lean_is_scalar(x_317)) {
 x_324 = lean_alloc_ctor(1, 4, 1);
} else {
 x_324 = x_317;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_291);
lean_ctor_set(x_324, 2, x_292);
lean_ctor_set(x_324, 3, x_293);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_299);
x_325 = 0;
x_326 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_319);
lean_ctor_set(x_326, 2, x_320);
lean_ctor_set(x_326, 3, x_324);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_325);
x_327 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_294);
lean_ctor_set(x_327, 2, x_295);
lean_ctor_set(x_327, 3, x_300);
lean_ctor_set_uint8(x_327, sizeof(void*)*4, x_325);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 x_328 = x_306;
} else {
 lean_dec_ref(x_306);
 x_328 = lean_box(0);
}
lean_inc(x_298);
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 4, 1);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_298);
lean_ctor_set(x_329, 1, x_291);
lean_ctor_set(x_329, 2, x_292);
lean_ctor_set(x_329, 3, x_293);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_330 = x_298;
} else {
 lean_dec_ref(x_298);
 x_330 = lean_box(0);
}
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_299);
x_331 = 0;
if (lean_is_scalar(x_330)) {
 x_332 = lean_alloc_ctor(1, 4, 1);
} else {
 x_332 = x_330;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_294);
lean_ctor_set(x_332, 2, x_295);
lean_ctor_set(x_332, 3, x_300);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
x_333 = lean_ctor_get_uint8(x_305, sizeof(void*)*4);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; 
x_334 = lean_ctor_get(x_298, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_298, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_298, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_337 = x_298;
} else {
 lean_dec_ref(x_298);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_305, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_305, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_305, 2);
lean_inc(x_340);
x_341 = lean_ctor_get(x_305, 3);
lean_inc(x_341);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 lean_ctor_release(x_305, 3);
 x_342 = x_305;
} else {
 lean_dec_ref(x_305);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(1, 4, 1);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
lean_ctor_set(x_343, 2, x_340);
lean_ctor_set(x_343, 3, x_341);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_299);
if (lean_is_scalar(x_337)) {
 x_344 = lean_alloc_ctor(1, 4, 1);
} else {
 x_344 = x_337;
}
lean_ctor_set(x_344, 0, x_336);
lean_ctor_set(x_344, 1, x_291);
lean_ctor_set(x_344, 2, x_292);
lean_ctor_set(x_344, 3, x_293);
lean_ctor_set_uint8(x_344, sizeof(void*)*4, x_299);
x_345 = 0;
x_346 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_334);
lean_ctor_set(x_346, 2, x_335);
lean_ctor_set(x_346, 3, x_344);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_345);
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_294);
lean_ctor_set(x_347, 2, x_295);
lean_ctor_set(x_347, 3, x_300);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_345);
return x_347;
}
else
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_298, 3);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; 
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 lean_ctor_release(x_305, 3);
 x_349 = x_305;
} else {
 lean_dec_ref(x_305);
 x_349 = lean_box(0);
}
lean_inc(x_298);
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 4, 1);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_298);
lean_ctor_set(x_350, 1, x_291);
lean_ctor_set(x_350, 2, x_292);
lean_ctor_set(x_350, 3, x_293);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_351 = x_298;
} else {
 lean_dec_ref(x_298);
 x_351 = lean_box(0);
}
lean_ctor_set_uint8(x_350, sizeof(void*)*4, x_299);
x_352 = 0;
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(1, 4, 1);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_294);
lean_ctor_set(x_353, 2, x_295);
lean_ctor_set(x_353, 3, x_300);
lean_ctor_set_uint8(x_353, sizeof(void*)*4, x_352);
return x_353;
}
else
{
uint8_t x_354; 
x_354 = lean_ctor_get_uint8(x_348, sizeof(void*)*4);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
x_355 = lean_ctor_get(x_298, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_298, 2);
lean_inc(x_356);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_357 = x_298;
} else {
 lean_dec_ref(x_298);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_348, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 2);
lean_inc(x_360);
x_361 = lean_ctor_get(x_348, 3);
lean_inc(x_361);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_362 = x_348;
} else {
 lean_dec_ref(x_348);
 x_362 = lean_box(0);
}
lean_inc(x_305);
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 4, 1);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_305);
lean_ctor_set(x_363, 1, x_355);
lean_ctor_set(x_363, 2, x_356);
lean_ctor_set(x_363, 3, x_358);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 lean_ctor_release(x_305, 3);
 x_364 = x_305;
} else {
 lean_dec_ref(x_305);
 x_364 = lean_box(0);
}
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_299);
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_361);
lean_ctor_set(x_365, 1, x_291);
lean_ctor_set(x_365, 2, x_292);
lean_ctor_set(x_365, 3, x_293);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_299);
x_366 = 0;
if (lean_is_scalar(x_357)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_357;
}
lean_ctor_set(x_367, 0, x_363);
lean_ctor_set(x_367, 1, x_359);
lean_ctor_set(x_367, 2, x_360);
lean_ctor_set(x_367, 3, x_365);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
x_368 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_294);
lean_ctor_set(x_368, 2, x_295);
lean_ctor_set(x_368, 3, x_300);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; 
x_369 = lean_ctor_get(x_298, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_298, 2);
lean_inc(x_370);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 x_371 = x_298;
} else {
 lean_dec_ref(x_298);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_305, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_305, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_305, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_305, 3);
lean_inc(x_375);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 lean_ctor_release(x_305, 3);
 x_376 = x_305;
} else {
 lean_dec_ref(x_305);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_372);
lean_ctor_set(x_377, 1, x_373);
lean_ctor_set(x_377, 2, x_374);
lean_ctor_set(x_377, 3, x_375);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_354);
if (lean_is_scalar(x_371)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_371;
}
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_369);
lean_ctor_set(x_378, 2, x_370);
lean_ctor_set(x_378, 3, x_348);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_304);
x_379 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_291);
lean_ctor_set(x_379, 2, x_292);
lean_ctor_set(x_379, 3, x_293);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_299);
x_380 = 0;
x_381 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_294);
lean_ctor_set(x_381, 2, x_295);
lean_ctor_set(x_381, 3, x_300);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_380);
return x_381;
}
}
}
}
}
else
{
lean_object* x_382; uint8_t x_383; lean_object* x_384; 
x_382 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_382, 0, x_298);
lean_ctor_set(x_382, 1, x_291);
lean_ctor_set(x_382, 2, x_292);
lean_ctor_set(x_382, 3, x_293);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_299);
x_383 = 0;
x_384 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_294);
lean_ctor_set(x_384, 2, x_295);
lean_ctor_set(x_384, 3, x_300);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
return x_384;
}
}
}
}
}
}
else
{
uint8_t x_385; 
x_385 = !lean_is_exclusive(x_1);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_386 = lean_ctor_get(x_1, 0);
x_387 = lean_ctor_get(x_1, 1);
x_388 = lean_ctor_get(x_1, 2);
x_389 = lean_ctor_get(x_1, 3);
x_390 = 0;
lean_inc(x_389);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_390);
if (lean_obj_tag(x_386) == 0)
{
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; 
lean_dec(x_1);
x_391 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_387);
lean_ctor_set(x_391, 2, x_388);
lean_ctor_set(x_391, 3, x_389);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
x_392 = 1;
x_393 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_2);
lean_ctor_set(x_393, 2, x_3);
lean_ctor_set(x_393, 3, x_4);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
return x_393;
}
else
{
uint8_t x_394; 
x_394 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_394 == 0)
{
uint8_t x_395; 
lean_dec(x_1);
x_395 = !lean_is_exclusive(x_389);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; 
x_396 = lean_ctor_get(x_389, 0);
x_397 = lean_ctor_get(x_389, 1);
x_398 = lean_ctor_get(x_389, 2);
x_399 = lean_ctor_get(x_389, 3);
x_400 = 1;
lean_ctor_set(x_389, 3, x_396);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_389, 1, x_387);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_400);
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_2);
lean_ctor_set(x_401, 2, x_3);
lean_ctor_set(x_401, 3, x_4);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_389);
lean_ctor_set(x_402, 1, x_397);
lean_ctor_set(x_402, 2, x_398);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_390);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_389, 0);
x_404 = lean_ctor_get(x_389, 1);
x_405 = lean_ctor_get(x_389, 2);
x_406 = lean_ctor_get(x_389, 3);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_389);
x_407 = 1;
x_408 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_408, 0, x_386);
lean_ctor_set(x_408, 1, x_387);
lean_ctor_set(x_408, 2, x_388);
lean_ctor_set(x_408, 3, x_403);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
x_409 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_2);
lean_ctor_set(x_409, 2, x_3);
lean_ctor_set(x_409, 3, x_4);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_407);
x_410 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set(x_410, 2, x_405);
lean_ctor_set(x_410, 3, x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_390);
return x_410;
}
}
else
{
uint8_t x_411; 
lean_dec(x_388);
lean_dec(x_387);
x_411 = !lean_is_exclusive(x_389);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
x_412 = lean_ctor_get(x_389, 3);
lean_dec(x_412);
x_413 = lean_ctor_get(x_389, 2);
lean_dec(x_413);
x_414 = lean_ctor_get(x_389, 1);
lean_dec(x_414);
x_415 = lean_ctor_get(x_389, 0);
lean_dec(x_415);
x_416 = 1;
lean_ctor_set(x_389, 3, x_4);
lean_ctor_set(x_389, 2, x_3);
lean_ctor_set(x_389, 1, x_2);
lean_ctor_set(x_389, 0, x_1);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_416);
return x_389;
}
else
{
uint8_t x_417; lean_object* x_418; 
lean_dec(x_389);
x_417 = 1;
x_418 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_418, 0, x_1);
lean_ctor_set(x_418, 1, x_2);
lean_ctor_set(x_418, 2, x_3);
lean_ctor_set(x_418, 3, x_4);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_417);
return x_418;
}
}
}
}
else
{
uint8_t x_419; 
x_419 = lean_ctor_get_uint8(x_386, sizeof(void*)*4);
if (x_419 == 0)
{
uint8_t x_420; 
lean_dec(x_1);
x_420 = !lean_is_exclusive(x_386);
if (x_420 == 0)
{
uint8_t x_421; lean_object* x_422; lean_object* x_423; 
x_421 = 1;
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_421);
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_389);
lean_ctor_set(x_422, 1, x_2);
lean_ctor_set(x_422, 2, x_3);
lean_ctor_set(x_422, 3, x_4);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_386);
lean_ctor_set(x_423, 1, x_387);
lean_ctor_set(x_423, 2, x_388);
lean_ctor_set(x_423, 3, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_390);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_424 = lean_ctor_get(x_386, 0);
x_425 = lean_ctor_get(x_386, 1);
x_426 = lean_ctor_get(x_386, 2);
x_427 = lean_ctor_get(x_386, 3);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_386);
x_428 = 1;
x_429 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_429, 0, x_424);
lean_ctor_set(x_429, 1, x_425);
lean_ctor_set(x_429, 2, x_426);
lean_ctor_set(x_429, 3, x_427);
lean_ctor_set_uint8(x_429, sizeof(void*)*4, x_428);
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_389);
lean_ctor_set(x_430, 1, x_2);
lean_ctor_set(x_430, 2, x_3);
lean_ctor_set(x_430, 3, x_4);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_428);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_387);
lean_ctor_set(x_431, 2, x_388);
lean_ctor_set(x_431, 3, x_430);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_390);
return x_431;
}
}
else
{
if (lean_obj_tag(x_389) == 0)
{
uint8_t x_432; 
lean_dec(x_388);
lean_dec(x_387);
x_432 = !lean_is_exclusive(x_386);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_433 = lean_ctor_get(x_386, 3);
lean_dec(x_433);
x_434 = lean_ctor_get(x_386, 2);
lean_dec(x_434);
x_435 = lean_ctor_get(x_386, 1);
lean_dec(x_435);
x_436 = lean_ctor_get(x_386, 0);
lean_dec(x_436);
x_437 = 1;
lean_ctor_set(x_386, 3, x_4);
lean_ctor_set(x_386, 2, x_3);
lean_ctor_set(x_386, 1, x_2);
lean_ctor_set(x_386, 0, x_1);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_437);
return x_386;
}
else
{
uint8_t x_438; lean_object* x_439; 
lean_dec(x_386);
x_438 = 1;
x_439 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_439, 0, x_1);
lean_ctor_set(x_439, 1, x_2);
lean_ctor_set(x_439, 2, x_3);
lean_ctor_set(x_439, 3, x_4);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
}
else
{
uint8_t x_440; 
lean_dec(x_1);
x_440 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_440 == 0)
{
uint8_t x_441; 
x_441 = !lean_is_exclusive(x_389);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; uint8_t x_447; 
x_442 = lean_ctor_get(x_389, 0);
x_443 = lean_ctor_get(x_389, 1);
x_444 = lean_ctor_get(x_389, 2);
x_445 = lean_ctor_get(x_389, 3);
x_446 = 1;
lean_inc(x_386);
lean_ctor_set(x_389, 3, x_442);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_389, 1, x_387);
lean_ctor_set(x_389, 0, x_386);
x_447 = !lean_is_exclusive(x_386);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = lean_ctor_get(x_386, 3);
lean_dec(x_448);
x_449 = lean_ctor_get(x_386, 2);
lean_dec(x_449);
x_450 = lean_ctor_get(x_386, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_386, 0);
lean_dec(x_451);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_446);
lean_ctor_set(x_386, 3, x_4);
lean_ctor_set(x_386, 2, x_3);
lean_ctor_set(x_386, 1, x_2);
lean_ctor_set(x_386, 0, x_445);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_446);
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_389);
lean_ctor_set(x_452, 1, x_443);
lean_ctor_set(x_452, 2, x_444);
lean_ctor_set(x_452, 3, x_386);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_390);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_386);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_446);
x_453 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_453, 0, x_445);
lean_ctor_set(x_453, 1, x_2);
lean_ctor_set(x_453, 2, x_3);
lean_ctor_set(x_453, 3, x_4);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_446);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_389);
lean_ctor_set(x_454, 1, x_443);
lean_ctor_set(x_454, 2, x_444);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_390);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_455 = lean_ctor_get(x_389, 0);
x_456 = lean_ctor_get(x_389, 1);
x_457 = lean_ctor_get(x_389, 2);
x_458 = lean_ctor_get(x_389, 3);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_389);
x_459 = 1;
lean_inc(x_386);
x_460 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_460, 0, x_386);
lean_ctor_set(x_460, 1, x_387);
lean_ctor_set(x_460, 2, x_388);
lean_ctor_set(x_460, 3, x_455);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 lean_ctor_release(x_386, 2);
 lean_ctor_release(x_386, 3);
 x_461 = x_386;
} else {
 lean_dec_ref(x_386);
 x_461 = lean_box(0);
}
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_459);
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_458);
lean_ctor_set(x_462, 1, x_2);
lean_ctor_set(x_462, 2, x_3);
lean_ctor_set(x_462, 3, x_4);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_459);
x_463 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_456);
lean_ctor_set(x_463, 2, x_457);
lean_ctor_set(x_463, 3, x_462);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_390);
return x_463;
}
}
else
{
uint8_t x_464; 
x_464 = !lean_is_exclusive(x_386);
if (x_464 == 0)
{
lean_object* x_465; uint8_t x_466; lean_object* x_467; 
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_440);
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_386);
lean_ctor_set(x_465, 1, x_387);
lean_ctor_set(x_465, 2, x_388);
lean_ctor_set(x_465, 3, x_389);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_390);
x_466 = 1;
x_467 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_2);
lean_ctor_set(x_467, 2, x_3);
lean_ctor_set(x_467, 3, x_4);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
return x_467;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; lean_object* x_475; 
x_468 = lean_ctor_get(x_386, 0);
x_469 = lean_ctor_get(x_386, 1);
x_470 = lean_ctor_get(x_386, 2);
x_471 = lean_ctor_get(x_386, 3);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_386);
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_468);
lean_ctor_set(x_472, 1, x_469);
lean_ctor_set(x_472, 2, x_470);
lean_ctor_set(x_472, 3, x_471);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_440);
x_473 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_387);
lean_ctor_set(x_473, 2, x_388);
lean_ctor_set(x_473, 3, x_389);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_390);
x_474 = 1;
x_475 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_2);
lean_ctor_set(x_475, 2, x_3);
lean_ctor_set(x_475, 3, x_4);
lean_ctor_set_uint8(x_475, sizeof(void*)*4, x_474);
return x_475;
}
}
}
}
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; 
x_476 = lean_ctor_get(x_1, 0);
x_477 = lean_ctor_get(x_1, 1);
x_478 = lean_ctor_get(x_1, 2);
x_479 = lean_ctor_get(x_1, 3);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_1);
x_480 = 0;
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
x_481 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_481, 0, x_476);
lean_ctor_set(x_481, 1, x_477);
lean_ctor_set(x_481, 2, x_478);
lean_ctor_set(x_481, 3, x_479);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_480);
if (lean_obj_tag(x_476) == 0)
{
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_482; uint8_t x_483; lean_object* x_484; 
lean_dec(x_481);
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_477);
lean_ctor_set(x_482, 2, x_478);
lean_ctor_set(x_482, 3, x_479);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_480);
x_483 = 1;
x_484 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_2);
lean_ctor_set(x_484, 2, x_3);
lean_ctor_set(x_484, 3, x_4);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
uint8_t x_485; 
x_485 = lean_ctor_get_uint8(x_479, sizeof(void*)*4);
if (x_485 == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_481);
x_486 = lean_ctor_get(x_479, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_479, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_479, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_479, 3);
lean_inc(x_489);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 lean_ctor_release(x_479, 2);
 lean_ctor_release(x_479, 3);
 x_490 = x_479;
} else {
 lean_dec_ref(x_479);
 x_490 = lean_box(0);
}
x_491 = 1;
if (lean_is_scalar(x_490)) {
 x_492 = lean_alloc_ctor(1, 4, 1);
} else {
 x_492 = x_490;
}
lean_ctor_set(x_492, 0, x_476);
lean_ctor_set(x_492, 1, x_477);
lean_ctor_set(x_492, 2, x_478);
lean_ctor_set(x_492, 3, x_486);
lean_ctor_set_uint8(x_492, sizeof(void*)*4, x_491);
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_489);
lean_ctor_set(x_493, 1, x_2);
lean_ctor_set(x_493, 2, x_3);
lean_ctor_set(x_493, 3, x_4);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_491);
x_494 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_487);
lean_ctor_set(x_494, 2, x_488);
lean_ctor_set(x_494, 3, x_493);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_480);
return x_494;
}
else
{
lean_object* x_495; uint8_t x_496; lean_object* x_497; 
lean_dec(x_478);
lean_dec(x_477);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 lean_ctor_release(x_479, 2);
 lean_ctor_release(x_479, 3);
 x_495 = x_479;
} else {
 lean_dec_ref(x_479);
 x_495 = lean_box(0);
}
x_496 = 1;
if (lean_is_scalar(x_495)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_495;
}
lean_ctor_set(x_497, 0, x_481);
lean_ctor_set(x_497, 1, x_2);
lean_ctor_set(x_497, 2, x_3);
lean_ctor_set(x_497, 3, x_4);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
return x_497;
}
}
}
else
{
uint8_t x_498; 
x_498 = lean_ctor_get_uint8(x_476, sizeof(void*)*4);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_481);
x_499 = lean_ctor_get(x_476, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_476, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_476, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_476, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_503 = x_476;
} else {
 lean_dec_ref(x_476);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
x_506 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_506, 0, x_479);
lean_ctor_set(x_506, 1, x_2);
lean_ctor_set(x_506, 2, x_3);
lean_ctor_set(x_506, 3, x_4);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_477);
lean_ctor_set(x_507, 2, x_478);
lean_ctor_set(x_507, 3, x_506);
lean_ctor_set_uint8(x_507, sizeof(void*)*4, x_480);
return x_507;
}
else
{
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_508; uint8_t x_509; lean_object* x_510; 
lean_dec(x_478);
lean_dec(x_477);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_508 = x_476;
} else {
 lean_dec_ref(x_476);
 x_508 = lean_box(0);
}
x_509 = 1;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_481);
lean_ctor_set(x_510, 1, x_2);
lean_ctor_set(x_510, 2, x_3);
lean_ctor_set(x_510, 3, x_4);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
return x_510;
}
else
{
uint8_t x_511; 
lean_dec(x_481);
x_511 = lean_ctor_get_uint8(x_479, sizeof(void*)*4);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_512 = lean_ctor_get(x_479, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_479, 1);
lean_inc(x_513);
x_514 = lean_ctor_get(x_479, 2);
lean_inc(x_514);
x_515 = lean_ctor_get(x_479, 3);
lean_inc(x_515);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 lean_ctor_release(x_479, 2);
 lean_ctor_release(x_479, 3);
 x_516 = x_479;
} else {
 lean_dec_ref(x_479);
 x_516 = lean_box(0);
}
x_517 = 1;
lean_inc(x_476);
if (lean_is_scalar(x_516)) {
 x_518 = lean_alloc_ctor(1, 4, 1);
} else {
 x_518 = x_516;
}
lean_ctor_set(x_518, 0, x_476);
lean_ctor_set(x_518, 1, x_477);
lean_ctor_set(x_518, 2, x_478);
lean_ctor_set(x_518, 3, x_512);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_519 = x_476;
} else {
 lean_dec_ref(x_476);
 x_519 = lean_box(0);
}
lean_ctor_set_uint8(x_518, sizeof(void*)*4, x_517);
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 4, 1);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_515);
lean_ctor_set(x_520, 1, x_2);
lean_ctor_set(x_520, 2, x_3);
lean_ctor_set(x_520, 3, x_4);
lean_ctor_set_uint8(x_520, sizeof(void*)*4, x_517);
x_521 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_513);
lean_ctor_set(x_521, 2, x_514);
lean_ctor_set(x_521, 3, x_520);
lean_ctor_set_uint8(x_521, sizeof(void*)*4, x_480);
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; 
x_522 = lean_ctor_get(x_476, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_476, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_476, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_476, 3);
lean_inc(x_525);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_526 = x_476;
} else {
 lean_dec_ref(x_476);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_522);
lean_ctor_set(x_527, 1, x_523);
lean_ctor_set(x_527, 2, x_524);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_511);
x_528 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_477);
lean_ctor_set(x_528, 2, x_478);
lean_ctor_set(x_528, 3, x_479);
lean_ctor_set_uint8(x_528, sizeof(void*)*4, x_480);
x_529 = 1;
x_530 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_2);
lean_ctor_set(x_530, 2, x_3);
lean_ctor_set(x_530, 3, x_4);
lean_ctor_set_uint8(x_530, sizeof(void*)*4, x_529);
return x_530;
}
}
}
}
}
}
}
}
else
{
uint8_t x_531; 
x_531 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_531 == 0)
{
uint8_t x_532; 
x_532 = !lean_is_exclusive(x_4);
if (x_532 == 0)
{
uint8_t x_533; uint8_t x_534; lean_object* x_535; 
x_533 = 1;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_533);
x_534 = 0;
x_535 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_535, 0, x_1);
lean_ctor_set(x_535, 1, x_2);
lean_ctor_set(x_535, 2, x_3);
lean_ctor_set(x_535, 3, x_4);
lean_ctor_set_uint8(x_535, sizeof(void*)*4, x_534);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; 
x_536 = lean_ctor_get(x_4, 0);
x_537 = lean_ctor_get(x_4, 1);
x_538 = lean_ctor_get(x_4, 2);
x_539 = lean_ctor_get(x_4, 3);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_4);
x_540 = 1;
x_541 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_541, 0, x_536);
lean_ctor_set(x_541, 1, x_537);
lean_ctor_set(x_541, 2, x_538);
lean_ctor_set(x_541, 3, x_539);
lean_ctor_set_uint8(x_541, sizeof(void*)*4, x_540);
x_542 = 0;
x_543 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_543, 0, x_1);
lean_ctor_set(x_543, 1, x_2);
lean_ctor_set(x_543, 2, x_3);
lean_ctor_set(x_543, 3, x_541);
lean_ctor_set_uint8(x_543, sizeof(void*)*4, x_542);
return x_543;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_544; lean_object* x_545; 
x_544 = 0;
x_545 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_545, 0, x_1);
lean_ctor_set(x_545, 1, x_2);
lean_ctor_set(x_545, 2, x_3);
lean_ctor_set(x_545, 3, x_4);
lean_ctor_set_uint8(x_545, sizeof(void*)*4, x_544);
return x_545;
}
else
{
uint8_t x_546; 
x_546 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_546 == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_1, 3);
lean_inc(x_547);
if (lean_obj_tag(x_547) == 0)
{
uint8_t x_548; lean_object* x_549; 
x_548 = 0;
x_549 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_549, 0, x_1);
lean_ctor_set(x_549, 1, x_2);
lean_ctor_set(x_549, 2, x_3);
lean_ctor_set(x_549, 3, x_4);
lean_ctor_set_uint8(x_549, sizeof(void*)*4, x_548);
return x_549;
}
else
{
uint8_t x_550; 
x_550 = lean_ctor_get_uint8(x_547, sizeof(void*)*4);
if (x_550 == 0)
{
uint8_t x_551; 
x_551 = !lean_is_exclusive(x_547);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_552 = lean_ctor_get(x_547, 3);
lean_dec(x_552);
x_553 = lean_ctor_get(x_547, 2);
lean_dec(x_553);
x_554 = lean_ctor_get(x_547, 1);
lean_dec(x_554);
x_555 = lean_ctor_get(x_547, 0);
lean_dec(x_555);
x_556 = 0;
lean_ctor_set(x_547, 3, x_4);
lean_ctor_set(x_547, 2, x_3);
lean_ctor_set(x_547, 1, x_2);
lean_ctor_set(x_547, 0, x_1);
lean_ctor_set_uint8(x_547, sizeof(void*)*4, x_556);
return x_547;
}
else
{
uint8_t x_557; lean_object* x_558; 
lean_dec(x_547);
x_557 = 0;
x_558 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_558, 0, x_1);
lean_ctor_set(x_558, 1, x_2);
lean_ctor_set(x_558, 2, x_3);
lean_ctor_set(x_558, 3, x_4);
lean_ctor_set_uint8(x_558, sizeof(void*)*4, x_557);
return x_558;
}
}
else
{
uint8_t x_559; 
x_559 = !lean_is_exclusive(x_1);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; 
x_560 = lean_ctor_get(x_1, 0);
x_561 = lean_ctor_get(x_1, 1);
x_562 = lean_ctor_get(x_1, 2);
x_563 = lean_ctor_get(x_1, 3);
lean_dec(x_563);
x_564 = !lean_is_exclusive(x_547);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; uint8_t x_571; 
x_565 = lean_ctor_get(x_547, 0);
x_566 = lean_ctor_get(x_547, 1);
x_567 = lean_ctor_get(x_547, 2);
x_568 = lean_ctor_get(x_547, 3);
x_569 = l_Lean_RBNode_setRed___rarg(x_560);
x_570 = 1;
lean_inc(x_4);
lean_ctor_set(x_547, 3, x_4);
lean_ctor_set(x_547, 2, x_3);
lean_ctor_set(x_547, 1, x_2);
lean_ctor_set(x_547, 0, x_568);
x_571 = !lean_is_exclusive(x_4);
if (x_571 == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_572 = lean_ctor_get(x_4, 3);
lean_dec(x_572);
x_573 = lean_ctor_get(x_4, 2);
lean_dec(x_573);
x_574 = lean_ctor_get(x_4, 1);
lean_dec(x_574);
x_575 = lean_ctor_get(x_4, 0);
lean_dec(x_575);
lean_ctor_set_uint8(x_547, sizeof(void*)*4, x_570);
if (lean_obj_tag(x_569) == 0)
{
uint8_t x_576; 
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_576 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_576);
return x_4;
}
else
{
uint8_t x_577; 
x_577 = lean_ctor_get_uint8(x_569, sizeof(void*)*4);
if (x_577 == 0)
{
lean_object* x_578; 
x_578 = lean_ctor_get(x_569, 0);
lean_inc(x_578);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; 
x_579 = lean_ctor_get(x_569, 3);
lean_inc(x_579);
if (lean_obj_tag(x_579) == 0)
{
uint8_t x_580; 
x_580 = !lean_is_exclusive(x_569);
if (x_580 == 0)
{
lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_581 = lean_ctor_get(x_569, 3);
lean_dec(x_581);
x_582 = lean_ctor_get(x_569, 0);
lean_dec(x_582);
lean_ctor_set(x_569, 0, x_579);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_583 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_583);
return x_4;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_584 = lean_ctor_get(x_569, 1);
x_585 = lean_ctor_get(x_569, 2);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_569);
x_586 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_586, 0, x_579);
lean_ctor_set(x_586, 1, x_584);
lean_ctor_set(x_586, 2, x_585);
lean_ctor_set(x_586, 3, x_579);
lean_ctor_set_uint8(x_586, sizeof(void*)*4, x_577);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_586);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_587 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_587);
return x_4;
}
}
else
{
uint8_t x_588; 
x_588 = lean_ctor_get_uint8(x_579, sizeof(void*)*4);
if (x_588 == 0)
{
uint8_t x_589; 
x_589 = !lean_is_exclusive(x_569);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
x_590 = lean_ctor_get(x_569, 1);
x_591 = lean_ctor_get(x_569, 2);
x_592 = lean_ctor_get(x_569, 3);
lean_dec(x_592);
x_593 = lean_ctor_get(x_569, 0);
lean_dec(x_593);
x_594 = !lean_is_exclusive(x_579);
if (x_594 == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; 
x_595 = lean_ctor_get(x_579, 0);
x_596 = lean_ctor_get(x_579, 1);
x_597 = lean_ctor_get(x_579, 2);
x_598 = lean_ctor_get(x_579, 3);
lean_ctor_set(x_579, 3, x_595);
lean_ctor_set(x_579, 2, x_591);
lean_ctor_set(x_579, 1, x_590);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set_uint8(x_579, sizeof(void*)*4, x_570);
lean_ctor_set(x_569, 3, x_565);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 0, x_598);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_570);
x_599 = 0;
lean_ctor_set(x_1, 3, x_569);
lean_ctor_set(x_1, 2, x_597);
lean_ctor_set(x_1, 1, x_596);
lean_ctor_set(x_1, 0, x_579);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_599);
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_599);
return x_4;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
x_600 = lean_ctor_get(x_579, 0);
x_601 = lean_ctor_get(x_579, 1);
x_602 = lean_ctor_get(x_579, 2);
x_603 = lean_ctor_get(x_579, 3);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_579);
x_604 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_604, 0, x_578);
lean_ctor_set(x_604, 1, x_590);
lean_ctor_set(x_604, 2, x_591);
lean_ctor_set(x_604, 3, x_600);
lean_ctor_set_uint8(x_604, sizeof(void*)*4, x_570);
lean_ctor_set(x_569, 3, x_565);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 0, x_603);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_570);
x_605 = 0;
lean_ctor_set(x_1, 3, x_569);
lean_ctor_set(x_1, 2, x_602);
lean_ctor_set(x_1, 1, x_601);
lean_ctor_set(x_1, 0, x_604);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_605);
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_605);
return x_4;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_606 = lean_ctor_get(x_569, 1);
x_607 = lean_ctor_get(x_569, 2);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_569);
x_608 = lean_ctor_get(x_579, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_579, 1);
lean_inc(x_609);
x_610 = lean_ctor_get(x_579, 2);
lean_inc(x_610);
x_611 = lean_ctor_get(x_579, 3);
lean_inc(x_611);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 lean_ctor_release(x_579, 2);
 lean_ctor_release(x_579, 3);
 x_612 = x_579;
} else {
 lean_dec_ref(x_579);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 4, 1);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_578);
lean_ctor_set(x_613, 1, x_606);
lean_ctor_set(x_613, 2, x_607);
lean_ctor_set(x_613, 3, x_608);
lean_ctor_set_uint8(x_613, sizeof(void*)*4, x_570);
x_614 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_614, 0, x_611);
lean_ctor_set(x_614, 1, x_561);
lean_ctor_set(x_614, 2, x_562);
lean_ctor_set(x_614, 3, x_565);
lean_ctor_set_uint8(x_614, sizeof(void*)*4, x_570);
x_615 = 0;
lean_ctor_set(x_1, 3, x_614);
lean_ctor_set(x_1, 2, x_610);
lean_ctor_set(x_1, 1, x_609);
lean_ctor_set(x_1, 0, x_613);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_615);
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_615);
return x_4;
}
}
else
{
uint8_t x_616; 
lean_free_object(x_4);
lean_free_object(x_1);
x_616 = !lean_is_exclusive(x_579);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; 
x_617 = lean_ctor_get(x_579, 3);
lean_dec(x_617);
x_618 = lean_ctor_get(x_579, 2);
lean_dec(x_618);
x_619 = lean_ctor_get(x_579, 1);
lean_dec(x_619);
x_620 = lean_ctor_get(x_579, 0);
lean_dec(x_620);
lean_inc(x_569);
lean_ctor_set(x_579, 3, x_565);
lean_ctor_set(x_579, 2, x_562);
lean_ctor_set(x_579, 1, x_561);
lean_ctor_set(x_579, 0, x_569);
x_621 = !lean_is_exclusive(x_569);
if (x_621 == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_622 = lean_ctor_get(x_569, 3);
lean_dec(x_622);
x_623 = lean_ctor_get(x_569, 2);
lean_dec(x_623);
x_624 = lean_ctor_get(x_569, 1);
lean_dec(x_624);
x_625 = lean_ctor_get(x_569, 0);
lean_dec(x_625);
lean_ctor_set_uint8(x_579, sizeof(void*)*4, x_570);
x_626 = 0;
lean_ctor_set(x_569, 3, x_547);
lean_ctor_set(x_569, 2, x_567);
lean_ctor_set(x_569, 1, x_566);
lean_ctor_set(x_569, 0, x_579);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_626);
return x_569;
}
else
{
uint8_t x_627; lean_object* x_628; 
lean_dec(x_569);
lean_ctor_set_uint8(x_579, sizeof(void*)*4, x_570);
x_627 = 0;
x_628 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_628, 0, x_579);
lean_ctor_set(x_628, 1, x_566);
lean_ctor_set(x_628, 2, x_567);
lean_ctor_set(x_628, 3, x_547);
lean_ctor_set_uint8(x_628, sizeof(void*)*4, x_627);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; 
lean_dec(x_579);
lean_inc(x_569);
x_629 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_629, 0, x_569);
lean_ctor_set(x_629, 1, x_561);
lean_ctor_set(x_629, 2, x_562);
lean_ctor_set(x_629, 3, x_565);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_630 = x_569;
} else {
 lean_dec_ref(x_569);
 x_630 = lean_box(0);
}
lean_ctor_set_uint8(x_629, sizeof(void*)*4, x_570);
x_631 = 0;
if (lean_is_scalar(x_630)) {
 x_632 = lean_alloc_ctor(1, 4, 1);
} else {
 x_632 = x_630;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_566);
lean_ctor_set(x_632, 2, x_567);
lean_ctor_set(x_632, 3, x_547);
lean_ctor_set_uint8(x_632, sizeof(void*)*4, x_631);
return x_632;
}
}
}
}
else
{
uint8_t x_633; 
x_633 = lean_ctor_get_uint8(x_578, sizeof(void*)*4);
if (x_633 == 0)
{
uint8_t x_634; 
x_634 = !lean_is_exclusive(x_569);
if (x_634 == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; 
x_635 = lean_ctor_get(x_569, 1);
x_636 = lean_ctor_get(x_569, 2);
x_637 = lean_ctor_get(x_569, 3);
x_638 = lean_ctor_get(x_569, 0);
lean_dec(x_638);
x_639 = !lean_is_exclusive(x_578);
if (x_639 == 0)
{
uint8_t x_640; 
lean_ctor_set_uint8(x_578, sizeof(void*)*4, x_570);
lean_ctor_set(x_569, 3, x_565);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 0, x_637);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_570);
x_640 = 0;
lean_ctor_set(x_1, 3, x_569);
lean_ctor_set(x_1, 2, x_636);
lean_ctor_set(x_1, 1, x_635);
lean_ctor_set(x_1, 0, x_578);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_640);
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_640);
return x_4;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_641 = lean_ctor_get(x_578, 0);
x_642 = lean_ctor_get(x_578, 1);
x_643 = lean_ctor_get(x_578, 2);
x_644 = lean_ctor_get(x_578, 3);
lean_inc(x_644);
lean_inc(x_643);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_578);
x_645 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_645, 0, x_641);
lean_ctor_set(x_645, 1, x_642);
lean_ctor_set(x_645, 2, x_643);
lean_ctor_set(x_645, 3, x_644);
lean_ctor_set_uint8(x_645, sizeof(void*)*4, x_570);
lean_ctor_set(x_569, 3, x_565);
lean_ctor_set(x_569, 2, x_562);
lean_ctor_set(x_569, 1, x_561);
lean_ctor_set(x_569, 0, x_637);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_570);
x_646 = 0;
lean_ctor_set(x_1, 3, x_569);
lean_ctor_set(x_1, 2, x_636);
lean_ctor_set(x_1, 1, x_635);
lean_ctor_set(x_1, 0, x_645);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_646);
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_646);
return x_4;
}
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; 
x_647 = lean_ctor_get(x_569, 1);
x_648 = lean_ctor_get(x_569, 2);
x_649 = lean_ctor_get(x_569, 3);
lean_inc(x_649);
lean_inc(x_648);
lean_inc(x_647);
lean_dec(x_569);
x_650 = lean_ctor_get(x_578, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_578, 1);
lean_inc(x_651);
x_652 = lean_ctor_get(x_578, 2);
lean_inc(x_652);
x_653 = lean_ctor_get(x_578, 3);
lean_inc(x_653);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 lean_ctor_release(x_578, 2);
 lean_ctor_release(x_578, 3);
 x_654 = x_578;
} else {
 lean_dec_ref(x_578);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 4, 1);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_650);
lean_ctor_set(x_655, 1, x_651);
lean_ctor_set(x_655, 2, x_652);
lean_ctor_set(x_655, 3, x_653);
lean_ctor_set_uint8(x_655, sizeof(void*)*4, x_570);
x_656 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_656, 0, x_649);
lean_ctor_set(x_656, 1, x_561);
lean_ctor_set(x_656, 2, x_562);
lean_ctor_set(x_656, 3, x_565);
lean_ctor_set_uint8(x_656, sizeof(void*)*4, x_570);
x_657 = 0;
lean_ctor_set(x_1, 3, x_656);
lean_ctor_set(x_1, 2, x_648);
lean_ctor_set(x_1, 1, x_647);
lean_ctor_set(x_1, 0, x_655);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_657);
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_657);
return x_4;
}
}
else
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_569, 3);
lean_inc(x_658);
if (lean_obj_tag(x_658) == 0)
{
uint8_t x_659; 
lean_free_object(x_4);
lean_free_object(x_1);
x_659 = !lean_is_exclusive(x_578);
if (x_659 == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; 
x_660 = lean_ctor_get(x_578, 3);
lean_dec(x_660);
x_661 = lean_ctor_get(x_578, 2);
lean_dec(x_661);
x_662 = lean_ctor_get(x_578, 1);
lean_dec(x_662);
x_663 = lean_ctor_get(x_578, 0);
lean_dec(x_663);
lean_inc(x_569);
lean_ctor_set(x_578, 3, x_565);
lean_ctor_set(x_578, 2, x_562);
lean_ctor_set(x_578, 1, x_561);
lean_ctor_set(x_578, 0, x_569);
x_664 = !lean_is_exclusive(x_569);
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
x_665 = lean_ctor_get(x_569, 3);
lean_dec(x_665);
x_666 = lean_ctor_get(x_569, 2);
lean_dec(x_666);
x_667 = lean_ctor_get(x_569, 1);
lean_dec(x_667);
x_668 = lean_ctor_get(x_569, 0);
lean_dec(x_668);
lean_ctor_set_uint8(x_578, sizeof(void*)*4, x_570);
x_669 = 0;
lean_ctor_set(x_569, 3, x_547);
lean_ctor_set(x_569, 2, x_567);
lean_ctor_set(x_569, 1, x_566);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_669);
return x_569;
}
else
{
uint8_t x_670; lean_object* x_671; 
lean_dec(x_569);
lean_ctor_set_uint8(x_578, sizeof(void*)*4, x_570);
x_670 = 0;
x_671 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_671, 0, x_578);
lean_ctor_set(x_671, 1, x_566);
lean_ctor_set(x_671, 2, x_567);
lean_ctor_set(x_671, 3, x_547);
lean_ctor_set_uint8(x_671, sizeof(void*)*4, x_670);
return x_671;
}
}
else
{
lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; 
lean_dec(x_578);
lean_inc(x_569);
x_672 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_672, 0, x_569);
lean_ctor_set(x_672, 1, x_561);
lean_ctor_set(x_672, 2, x_562);
lean_ctor_set(x_672, 3, x_565);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_673 = x_569;
} else {
 lean_dec_ref(x_569);
 x_673 = lean_box(0);
}
lean_ctor_set_uint8(x_672, sizeof(void*)*4, x_570);
x_674 = 0;
if (lean_is_scalar(x_673)) {
 x_675 = lean_alloc_ctor(1, 4, 1);
} else {
 x_675 = x_673;
}
lean_ctor_set(x_675, 0, x_672);
lean_ctor_set(x_675, 1, x_566);
lean_ctor_set(x_675, 2, x_567);
lean_ctor_set(x_675, 3, x_547);
lean_ctor_set_uint8(x_675, sizeof(void*)*4, x_674);
return x_675;
}
}
else
{
uint8_t x_676; 
x_676 = lean_ctor_get_uint8(x_658, sizeof(void*)*4);
if (x_676 == 0)
{
uint8_t x_677; 
lean_free_object(x_4);
x_677 = !lean_is_exclusive(x_569);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
x_678 = lean_ctor_get(x_569, 1);
x_679 = lean_ctor_get(x_569, 2);
x_680 = lean_ctor_get(x_569, 3);
lean_dec(x_680);
x_681 = lean_ctor_get(x_569, 0);
lean_dec(x_681);
x_682 = !lean_is_exclusive(x_658);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
x_683 = lean_ctor_get(x_658, 0);
x_684 = lean_ctor_get(x_658, 1);
x_685 = lean_ctor_get(x_658, 2);
x_686 = lean_ctor_get(x_658, 3);
lean_inc(x_578);
lean_ctor_set(x_658, 3, x_683);
lean_ctor_set(x_658, 2, x_679);
lean_ctor_set(x_658, 1, x_678);
lean_ctor_set(x_658, 0, x_578);
x_687 = !lean_is_exclusive(x_578);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
x_688 = lean_ctor_get(x_578, 3);
lean_dec(x_688);
x_689 = lean_ctor_get(x_578, 2);
lean_dec(x_689);
x_690 = lean_ctor_get(x_578, 1);
lean_dec(x_690);
x_691 = lean_ctor_get(x_578, 0);
lean_dec(x_691);
lean_ctor_set_uint8(x_658, sizeof(void*)*4, x_570);
lean_ctor_set(x_578, 3, x_565);
lean_ctor_set(x_578, 2, x_562);
lean_ctor_set(x_578, 1, x_561);
lean_ctor_set(x_578, 0, x_686);
lean_ctor_set_uint8(x_578, sizeof(void*)*4, x_570);
x_692 = 0;
lean_ctor_set(x_569, 3, x_578);
lean_ctor_set(x_569, 2, x_685);
lean_ctor_set(x_569, 1, x_684);
lean_ctor_set(x_569, 0, x_658);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_692);
lean_ctor_set(x_1, 2, x_567);
lean_ctor_set(x_1, 1, x_566);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_692);
return x_1;
}
else
{
lean_object* x_693; uint8_t x_694; 
lean_dec(x_578);
lean_ctor_set_uint8(x_658, sizeof(void*)*4, x_570);
x_693 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_693, 0, x_686);
lean_ctor_set(x_693, 1, x_561);
lean_ctor_set(x_693, 2, x_562);
lean_ctor_set(x_693, 3, x_565);
lean_ctor_set_uint8(x_693, sizeof(void*)*4, x_570);
x_694 = 0;
lean_ctor_set(x_569, 3, x_693);
lean_ctor_set(x_569, 2, x_685);
lean_ctor_set(x_569, 1, x_684);
lean_ctor_set(x_569, 0, x_658);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_694);
lean_ctor_set(x_1, 2, x_567);
lean_ctor_set(x_1, 1, x_566);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_694);
return x_1;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_695 = lean_ctor_get(x_658, 0);
x_696 = lean_ctor_get(x_658, 1);
x_697 = lean_ctor_get(x_658, 2);
x_698 = lean_ctor_get(x_658, 3);
lean_inc(x_698);
lean_inc(x_697);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_658);
lean_inc(x_578);
x_699 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_699, 0, x_578);
lean_ctor_set(x_699, 1, x_678);
lean_ctor_set(x_699, 2, x_679);
lean_ctor_set(x_699, 3, x_695);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 lean_ctor_release(x_578, 2);
 lean_ctor_release(x_578, 3);
 x_700 = x_578;
} else {
 lean_dec_ref(x_578);
 x_700 = lean_box(0);
}
lean_ctor_set_uint8(x_699, sizeof(void*)*4, x_570);
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 4, 1);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_561);
lean_ctor_set(x_701, 2, x_562);
lean_ctor_set(x_701, 3, x_565);
lean_ctor_set_uint8(x_701, sizeof(void*)*4, x_570);
x_702 = 0;
lean_ctor_set(x_569, 3, x_701);
lean_ctor_set(x_569, 2, x_697);
lean_ctor_set(x_569, 1, x_696);
lean_ctor_set(x_569, 0, x_699);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_702);
lean_ctor_set(x_1, 2, x_567);
lean_ctor_set(x_1, 1, x_566);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_702);
return x_1;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; 
x_703 = lean_ctor_get(x_569, 1);
x_704 = lean_ctor_get(x_569, 2);
lean_inc(x_704);
lean_inc(x_703);
lean_dec(x_569);
x_705 = lean_ctor_get(x_658, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_658, 1);
lean_inc(x_706);
x_707 = lean_ctor_get(x_658, 2);
lean_inc(x_707);
x_708 = lean_ctor_get(x_658, 3);
lean_inc(x_708);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 lean_ctor_release(x_658, 2);
 lean_ctor_release(x_658, 3);
 x_709 = x_658;
} else {
 lean_dec_ref(x_658);
 x_709 = lean_box(0);
}
lean_inc(x_578);
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(1, 4, 1);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_578);
lean_ctor_set(x_710, 1, x_703);
lean_ctor_set(x_710, 2, x_704);
lean_ctor_set(x_710, 3, x_705);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 lean_ctor_release(x_578, 2);
 lean_ctor_release(x_578, 3);
 x_711 = x_578;
} else {
 lean_dec_ref(x_578);
 x_711 = lean_box(0);
}
lean_ctor_set_uint8(x_710, sizeof(void*)*4, x_570);
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 4, 1);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_708);
lean_ctor_set(x_712, 1, x_561);
lean_ctor_set(x_712, 2, x_562);
lean_ctor_set(x_712, 3, x_565);
lean_ctor_set_uint8(x_712, sizeof(void*)*4, x_570);
x_713 = 0;
x_714 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_714, 0, x_710);
lean_ctor_set(x_714, 1, x_706);
lean_ctor_set(x_714, 2, x_707);
lean_ctor_set(x_714, 3, x_712);
lean_ctor_set_uint8(x_714, sizeof(void*)*4, x_713);
lean_ctor_set(x_1, 2, x_567);
lean_ctor_set(x_1, 1, x_566);
lean_ctor_set(x_1, 0, x_714);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_713);
return x_1;
}
}
else
{
uint8_t x_715; 
x_715 = !lean_is_exclusive(x_569);
if (x_715 == 0)
{
lean_object* x_716; lean_object* x_717; uint8_t x_718; 
x_716 = lean_ctor_get(x_569, 3);
lean_dec(x_716);
x_717 = lean_ctor_get(x_569, 0);
lean_dec(x_717);
x_718 = !lean_is_exclusive(x_578);
if (x_718 == 0)
{
uint8_t x_719; 
lean_ctor_set_uint8(x_578, sizeof(void*)*4, x_676);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_719 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_719);
return x_4;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; 
x_720 = lean_ctor_get(x_578, 0);
x_721 = lean_ctor_get(x_578, 1);
x_722 = lean_ctor_get(x_578, 2);
x_723 = lean_ctor_get(x_578, 3);
lean_inc(x_723);
lean_inc(x_722);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_578);
x_724 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_724, 0, x_720);
lean_ctor_set(x_724, 1, x_721);
lean_ctor_set(x_724, 2, x_722);
lean_ctor_set(x_724, 3, x_723);
lean_ctor_set_uint8(x_724, sizeof(void*)*4, x_676);
lean_ctor_set(x_569, 0, x_724);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_725 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_725);
return x_4;
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; 
x_726 = lean_ctor_get(x_569, 1);
x_727 = lean_ctor_get(x_569, 2);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_569);
x_728 = lean_ctor_get(x_578, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_578, 1);
lean_inc(x_729);
x_730 = lean_ctor_get(x_578, 2);
lean_inc(x_730);
x_731 = lean_ctor_get(x_578, 3);
lean_inc(x_731);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 lean_ctor_release(x_578, 2);
 lean_ctor_release(x_578, 3);
 x_732 = x_578;
} else {
 lean_dec_ref(x_578);
 x_732 = lean_box(0);
}
if (lean_is_scalar(x_732)) {
 x_733 = lean_alloc_ctor(1, 4, 1);
} else {
 x_733 = x_732;
}
lean_ctor_set(x_733, 0, x_728);
lean_ctor_set(x_733, 1, x_729);
lean_ctor_set(x_733, 2, x_730);
lean_ctor_set(x_733, 3, x_731);
lean_ctor_set_uint8(x_733, sizeof(void*)*4, x_676);
x_734 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_726);
lean_ctor_set(x_734, 2, x_727);
lean_ctor_set(x_734, 3, x_658);
lean_ctor_set_uint8(x_734, sizeof(void*)*4, x_577);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_734);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_735 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_735);
return x_4;
}
}
}
}
}
}
else
{
uint8_t x_736; 
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_736 = 0;
lean_ctor_set(x_4, 3, x_547);
lean_ctor_set(x_4, 2, x_567);
lean_ctor_set(x_4, 1, x_566);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_736);
return x_4;
}
}
}
else
{
lean_dec(x_4);
lean_ctor_set_uint8(x_547, sizeof(void*)*4, x_570);
if (lean_obj_tag(x_569) == 0)
{
uint8_t x_737; lean_object* x_738; 
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_737 = 0;
x_738 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_738, 0, x_1);
lean_ctor_set(x_738, 1, x_566);
lean_ctor_set(x_738, 2, x_567);
lean_ctor_set(x_738, 3, x_547);
lean_ctor_set_uint8(x_738, sizeof(void*)*4, x_737);
return x_738;
}
else
{
uint8_t x_739; 
x_739 = lean_ctor_get_uint8(x_569, sizeof(void*)*4);
if (x_739 == 0)
{
lean_object* x_740; 
x_740 = lean_ctor_get(x_569, 0);
lean_inc(x_740);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; 
x_741 = lean_ctor_get(x_569, 3);
lean_inc(x_741);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; lean_object* x_747; 
x_742 = lean_ctor_get(x_569, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_569, 2);
lean_inc(x_743);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_744 = x_569;
} else {
 lean_dec_ref(x_569);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 4, 1);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_741);
lean_ctor_set(x_745, 1, x_742);
lean_ctor_set(x_745, 2, x_743);
lean_ctor_set(x_745, 3, x_741);
lean_ctor_set_uint8(x_745, sizeof(void*)*4, x_739);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_745);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_746 = 0;
x_747 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_747, 0, x_1);
lean_ctor_set(x_747, 1, x_566);
lean_ctor_set(x_747, 2, x_567);
lean_ctor_set(x_747, 3, x_547);
lean_ctor_set_uint8(x_747, sizeof(void*)*4, x_746);
return x_747;
}
else
{
uint8_t x_748; 
x_748 = lean_ctor_get_uint8(x_741, sizeof(void*)*4);
if (x_748 == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; lean_object* x_760; 
x_749 = lean_ctor_get(x_569, 1);
lean_inc(x_749);
x_750 = lean_ctor_get(x_569, 2);
lean_inc(x_750);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_751 = x_569;
} else {
 lean_dec_ref(x_569);
 x_751 = lean_box(0);
}
x_752 = lean_ctor_get(x_741, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_741, 1);
lean_inc(x_753);
x_754 = lean_ctor_get(x_741, 2);
lean_inc(x_754);
x_755 = lean_ctor_get(x_741, 3);
lean_inc(x_755);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 lean_ctor_release(x_741, 2);
 lean_ctor_release(x_741, 3);
 x_756 = x_741;
} else {
 lean_dec_ref(x_741);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 4, 1);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_740);
lean_ctor_set(x_757, 1, x_749);
lean_ctor_set(x_757, 2, x_750);
lean_ctor_set(x_757, 3, x_752);
lean_ctor_set_uint8(x_757, sizeof(void*)*4, x_570);
if (lean_is_scalar(x_751)) {
 x_758 = lean_alloc_ctor(1, 4, 1);
} else {
 x_758 = x_751;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_561);
lean_ctor_set(x_758, 2, x_562);
lean_ctor_set(x_758, 3, x_565);
lean_ctor_set_uint8(x_758, sizeof(void*)*4, x_570);
x_759 = 0;
lean_ctor_set(x_1, 3, x_758);
lean_ctor_set(x_1, 2, x_754);
lean_ctor_set(x_1, 1, x_753);
lean_ctor_set(x_1, 0, x_757);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_759);
x_760 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_760, 0, x_1);
lean_ctor_set(x_760, 1, x_566);
lean_ctor_set(x_760, 2, x_567);
lean_ctor_set(x_760, 3, x_547);
lean_ctor_set_uint8(x_760, sizeof(void*)*4, x_759);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; lean_object* x_765; 
lean_free_object(x_1);
if (lean_is_exclusive(x_741)) {
 lean_ctor_release(x_741, 0);
 lean_ctor_release(x_741, 1);
 lean_ctor_release(x_741, 2);
 lean_ctor_release(x_741, 3);
 x_761 = x_741;
} else {
 lean_dec_ref(x_741);
 x_761 = lean_box(0);
}
lean_inc(x_569);
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 4, 1);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_569);
lean_ctor_set(x_762, 1, x_561);
lean_ctor_set(x_762, 2, x_562);
lean_ctor_set(x_762, 3, x_565);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_763 = x_569;
} else {
 lean_dec_ref(x_569);
 x_763 = lean_box(0);
}
lean_ctor_set_uint8(x_762, sizeof(void*)*4, x_570);
x_764 = 0;
if (lean_is_scalar(x_763)) {
 x_765 = lean_alloc_ctor(1, 4, 1);
} else {
 x_765 = x_763;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_566);
lean_ctor_set(x_765, 2, x_567);
lean_ctor_set(x_765, 3, x_547);
lean_ctor_set_uint8(x_765, sizeof(void*)*4, x_764);
return x_765;
}
}
}
else
{
uint8_t x_766; 
x_766 = lean_ctor_get_uint8(x_740, sizeof(void*)*4);
if (x_766 == 0)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; uint8_t x_778; lean_object* x_779; 
x_767 = lean_ctor_get(x_569, 1);
lean_inc(x_767);
x_768 = lean_ctor_get(x_569, 2);
lean_inc(x_768);
x_769 = lean_ctor_get(x_569, 3);
lean_inc(x_769);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_770 = x_569;
} else {
 lean_dec_ref(x_569);
 x_770 = lean_box(0);
}
x_771 = lean_ctor_get(x_740, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_740, 1);
lean_inc(x_772);
x_773 = lean_ctor_get(x_740, 2);
lean_inc(x_773);
x_774 = lean_ctor_get(x_740, 3);
lean_inc(x_774);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 lean_ctor_release(x_740, 2);
 lean_ctor_release(x_740, 3);
 x_775 = x_740;
} else {
 lean_dec_ref(x_740);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 4, 1);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_771);
lean_ctor_set(x_776, 1, x_772);
lean_ctor_set(x_776, 2, x_773);
lean_ctor_set(x_776, 3, x_774);
lean_ctor_set_uint8(x_776, sizeof(void*)*4, x_570);
if (lean_is_scalar(x_770)) {
 x_777 = lean_alloc_ctor(1, 4, 1);
} else {
 x_777 = x_770;
}
lean_ctor_set(x_777, 0, x_769);
lean_ctor_set(x_777, 1, x_561);
lean_ctor_set(x_777, 2, x_562);
lean_ctor_set(x_777, 3, x_565);
lean_ctor_set_uint8(x_777, sizeof(void*)*4, x_570);
x_778 = 0;
lean_ctor_set(x_1, 3, x_777);
lean_ctor_set(x_1, 2, x_768);
lean_ctor_set(x_1, 1, x_767);
lean_ctor_set(x_1, 0, x_776);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_778);
x_779 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_779, 0, x_1);
lean_ctor_set(x_779, 1, x_566);
lean_ctor_set(x_779, 2, x_567);
lean_ctor_set(x_779, 3, x_547);
lean_ctor_set_uint8(x_779, sizeof(void*)*4, x_778);
return x_779;
}
else
{
lean_object* x_780; 
x_780 = lean_ctor_get(x_569, 3);
lean_inc(x_780);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; lean_object* x_785; 
lean_free_object(x_1);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 lean_ctor_release(x_740, 2);
 lean_ctor_release(x_740, 3);
 x_781 = x_740;
} else {
 lean_dec_ref(x_740);
 x_781 = lean_box(0);
}
lean_inc(x_569);
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 4, 1);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_569);
lean_ctor_set(x_782, 1, x_561);
lean_ctor_set(x_782, 2, x_562);
lean_ctor_set(x_782, 3, x_565);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_783 = x_569;
} else {
 lean_dec_ref(x_569);
 x_783 = lean_box(0);
}
lean_ctor_set_uint8(x_782, sizeof(void*)*4, x_570);
x_784 = 0;
if (lean_is_scalar(x_783)) {
 x_785 = lean_alloc_ctor(1, 4, 1);
} else {
 x_785 = x_783;
}
lean_ctor_set(x_785, 0, x_782);
lean_ctor_set(x_785, 1, x_566);
lean_ctor_set(x_785, 2, x_567);
lean_ctor_set(x_785, 3, x_547);
lean_ctor_set_uint8(x_785, sizeof(void*)*4, x_784);
return x_785;
}
else
{
uint8_t x_786; 
x_786 = lean_ctor_get_uint8(x_780, sizeof(void*)*4);
if (x_786 == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; lean_object* x_799; 
x_787 = lean_ctor_get(x_569, 1);
lean_inc(x_787);
x_788 = lean_ctor_get(x_569, 2);
lean_inc(x_788);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_789 = x_569;
} else {
 lean_dec_ref(x_569);
 x_789 = lean_box(0);
}
x_790 = lean_ctor_get(x_780, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_780, 1);
lean_inc(x_791);
x_792 = lean_ctor_get(x_780, 2);
lean_inc(x_792);
x_793 = lean_ctor_get(x_780, 3);
lean_inc(x_793);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 lean_ctor_release(x_780, 2);
 lean_ctor_release(x_780, 3);
 x_794 = x_780;
} else {
 lean_dec_ref(x_780);
 x_794 = lean_box(0);
}
lean_inc(x_740);
if (lean_is_scalar(x_794)) {
 x_795 = lean_alloc_ctor(1, 4, 1);
} else {
 x_795 = x_794;
}
lean_ctor_set(x_795, 0, x_740);
lean_ctor_set(x_795, 1, x_787);
lean_ctor_set(x_795, 2, x_788);
lean_ctor_set(x_795, 3, x_790);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 lean_ctor_release(x_740, 2);
 lean_ctor_release(x_740, 3);
 x_796 = x_740;
} else {
 lean_dec_ref(x_740);
 x_796 = lean_box(0);
}
lean_ctor_set_uint8(x_795, sizeof(void*)*4, x_570);
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 4, 1);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_793);
lean_ctor_set(x_797, 1, x_561);
lean_ctor_set(x_797, 2, x_562);
lean_ctor_set(x_797, 3, x_565);
lean_ctor_set_uint8(x_797, sizeof(void*)*4, x_570);
x_798 = 0;
if (lean_is_scalar(x_789)) {
 x_799 = lean_alloc_ctor(1, 4, 1);
} else {
 x_799 = x_789;
}
lean_ctor_set(x_799, 0, x_795);
lean_ctor_set(x_799, 1, x_791);
lean_ctor_set(x_799, 2, x_792);
lean_ctor_set(x_799, 3, x_797);
lean_ctor_set_uint8(x_799, sizeof(void*)*4, x_798);
lean_ctor_set(x_1, 2, x_567);
lean_ctor_set(x_1, 1, x_566);
lean_ctor_set(x_1, 0, x_799);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_798);
return x_1;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; uint8_t x_810; lean_object* x_811; 
x_800 = lean_ctor_get(x_569, 1);
lean_inc(x_800);
x_801 = lean_ctor_get(x_569, 2);
lean_inc(x_801);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 lean_ctor_release(x_569, 2);
 lean_ctor_release(x_569, 3);
 x_802 = x_569;
} else {
 lean_dec_ref(x_569);
 x_802 = lean_box(0);
}
x_803 = lean_ctor_get(x_740, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_740, 1);
lean_inc(x_804);
x_805 = lean_ctor_get(x_740, 2);
lean_inc(x_805);
x_806 = lean_ctor_get(x_740, 3);
lean_inc(x_806);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 lean_ctor_release(x_740, 2);
 lean_ctor_release(x_740, 3);
 x_807 = x_740;
} else {
 lean_dec_ref(x_740);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 4, 1);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_803);
lean_ctor_set(x_808, 1, x_804);
lean_ctor_set(x_808, 2, x_805);
lean_ctor_set(x_808, 3, x_806);
lean_ctor_set_uint8(x_808, sizeof(void*)*4, x_786);
if (lean_is_scalar(x_802)) {
 x_809 = lean_alloc_ctor(1, 4, 1);
} else {
 x_809 = x_802;
}
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_800);
lean_ctor_set(x_809, 2, x_801);
lean_ctor_set(x_809, 3, x_780);
lean_ctor_set_uint8(x_809, sizeof(void*)*4, x_739);
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_809);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_810 = 0;
x_811 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_811, 0, x_1);
lean_ctor_set(x_811, 1, x_566);
lean_ctor_set(x_811, 2, x_567);
lean_ctor_set(x_811, 3, x_547);
lean_ctor_set_uint8(x_811, sizeof(void*)*4, x_810);
return x_811;
}
}
}
}
}
else
{
uint8_t x_812; lean_object* x_813; 
lean_ctor_set(x_1, 3, x_565);
lean_ctor_set(x_1, 0, x_569);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_570);
x_812 = 0;
x_813 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_813, 0, x_1);
lean_ctor_set(x_813, 1, x_566);
lean_ctor_set(x_813, 2, x_567);
lean_ctor_set(x_813, 3, x_547);
lean_ctor_set_uint8(x_813, sizeof(void*)*4, x_812);
return x_813;
}
}
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint8_t x_819; lean_object* x_820; lean_object* x_821; 
x_814 = lean_ctor_get(x_547, 0);
x_815 = lean_ctor_get(x_547, 1);
x_816 = lean_ctor_get(x_547, 2);
x_817 = lean_ctor_get(x_547, 3);
lean_inc(x_817);
lean_inc(x_816);
lean_inc(x_815);
lean_inc(x_814);
lean_dec(x_547);
x_818 = l_Lean_RBNode_setRed___rarg(x_560);
x_819 = 1;
lean_inc(x_4);
x_820 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_820, 0, x_817);
lean_ctor_set(x_820, 1, x_2);
lean_ctor_set(x_820, 2, x_3);
lean_ctor_set(x_820, 3, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_821 = x_4;
} else {
 lean_dec_ref(x_4);
 x_821 = lean_box(0);
}
lean_ctor_set_uint8(x_820, sizeof(void*)*4, x_819);
if (lean_obj_tag(x_818) == 0)
{
uint8_t x_822; lean_object* x_823; 
lean_ctor_set(x_1, 3, x_814);
lean_ctor_set(x_1, 0, x_818);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_819);
x_822 = 0;
if (lean_is_scalar(x_821)) {
 x_823 = lean_alloc_ctor(1, 4, 1);
} else {
 x_823 = x_821;
}
lean_ctor_set(x_823, 0, x_1);
lean_ctor_set(x_823, 1, x_815);
lean_ctor_set(x_823, 2, x_816);
lean_ctor_set(x_823, 3, x_820);
lean_ctor_set_uint8(x_823, sizeof(void*)*4, x_822);
return x_823;
}
else
{
uint8_t x_824; 
x_824 = lean_ctor_get_uint8(x_818, sizeof(void*)*4);
if (x_824 == 0)
{
lean_object* x_825; 
x_825 = lean_ctor_get(x_818, 0);
lean_inc(x_825);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; 
x_826 = lean_ctor_get(x_818, 3);
lean_inc(x_826);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; lean_object* x_832; 
x_827 = lean_ctor_get(x_818, 1);
lean_inc(x_827);
x_828 = lean_ctor_get(x_818, 2);
lean_inc(x_828);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_829 = x_818;
} else {
 lean_dec_ref(x_818);
 x_829 = lean_box(0);
}
if (lean_is_scalar(x_829)) {
 x_830 = lean_alloc_ctor(1, 4, 1);
} else {
 x_830 = x_829;
}
lean_ctor_set(x_830, 0, x_826);
lean_ctor_set(x_830, 1, x_827);
lean_ctor_set(x_830, 2, x_828);
lean_ctor_set(x_830, 3, x_826);
lean_ctor_set_uint8(x_830, sizeof(void*)*4, x_824);
lean_ctor_set(x_1, 3, x_814);
lean_ctor_set(x_1, 0, x_830);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_819);
x_831 = 0;
if (lean_is_scalar(x_821)) {
 x_832 = lean_alloc_ctor(1, 4, 1);
} else {
 x_832 = x_821;
}
lean_ctor_set(x_832, 0, x_1);
lean_ctor_set(x_832, 1, x_815);
lean_ctor_set(x_832, 2, x_816);
lean_ctor_set(x_832, 3, x_820);
lean_ctor_set_uint8(x_832, sizeof(void*)*4, x_831);
return x_832;
}
else
{
uint8_t x_833; 
x_833 = lean_ctor_get_uint8(x_826, sizeof(void*)*4);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; 
x_834 = lean_ctor_get(x_818, 1);
lean_inc(x_834);
x_835 = lean_ctor_get(x_818, 2);
lean_inc(x_835);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_836 = x_818;
} else {
 lean_dec_ref(x_818);
 x_836 = lean_box(0);
}
x_837 = lean_ctor_get(x_826, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_826, 1);
lean_inc(x_838);
x_839 = lean_ctor_get(x_826, 2);
lean_inc(x_839);
x_840 = lean_ctor_get(x_826, 3);
lean_inc(x_840);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 lean_ctor_release(x_826, 2);
 lean_ctor_release(x_826, 3);
 x_841 = x_826;
} else {
 lean_dec_ref(x_826);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 4, 1);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_825);
lean_ctor_set(x_842, 1, x_834);
lean_ctor_set(x_842, 2, x_835);
lean_ctor_set(x_842, 3, x_837);
lean_ctor_set_uint8(x_842, sizeof(void*)*4, x_819);
if (lean_is_scalar(x_836)) {
 x_843 = lean_alloc_ctor(1, 4, 1);
} else {
 x_843 = x_836;
}
lean_ctor_set(x_843, 0, x_840);
lean_ctor_set(x_843, 1, x_561);
lean_ctor_set(x_843, 2, x_562);
lean_ctor_set(x_843, 3, x_814);
lean_ctor_set_uint8(x_843, sizeof(void*)*4, x_819);
x_844 = 0;
lean_ctor_set(x_1, 3, x_843);
lean_ctor_set(x_1, 2, x_839);
lean_ctor_set(x_1, 1, x_838);
lean_ctor_set(x_1, 0, x_842);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_844);
if (lean_is_scalar(x_821)) {
 x_845 = lean_alloc_ctor(1, 4, 1);
} else {
 x_845 = x_821;
}
lean_ctor_set(x_845, 0, x_1);
lean_ctor_set(x_845, 1, x_815);
lean_ctor_set(x_845, 2, x_816);
lean_ctor_set(x_845, 3, x_820);
lean_ctor_set_uint8(x_845, sizeof(void*)*4, x_844);
return x_845;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; uint8_t x_849; lean_object* x_850; 
lean_dec(x_821);
lean_free_object(x_1);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 lean_ctor_release(x_826, 2);
 lean_ctor_release(x_826, 3);
 x_846 = x_826;
} else {
 lean_dec_ref(x_826);
 x_846 = lean_box(0);
}
lean_inc(x_818);
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 4, 1);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_818);
lean_ctor_set(x_847, 1, x_561);
lean_ctor_set(x_847, 2, x_562);
lean_ctor_set(x_847, 3, x_814);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_848 = x_818;
} else {
 lean_dec_ref(x_818);
 x_848 = lean_box(0);
}
lean_ctor_set_uint8(x_847, sizeof(void*)*4, x_819);
x_849 = 0;
if (lean_is_scalar(x_848)) {
 x_850 = lean_alloc_ctor(1, 4, 1);
} else {
 x_850 = x_848;
}
lean_ctor_set(x_850, 0, x_847);
lean_ctor_set(x_850, 1, x_815);
lean_ctor_set(x_850, 2, x_816);
lean_ctor_set(x_850, 3, x_820);
lean_ctor_set_uint8(x_850, sizeof(void*)*4, x_849);
return x_850;
}
}
}
else
{
uint8_t x_851; 
x_851 = lean_ctor_get_uint8(x_825, sizeof(void*)*4);
if (x_851 == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; lean_object* x_864; 
x_852 = lean_ctor_get(x_818, 1);
lean_inc(x_852);
x_853 = lean_ctor_get(x_818, 2);
lean_inc(x_853);
x_854 = lean_ctor_get(x_818, 3);
lean_inc(x_854);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_855 = x_818;
} else {
 lean_dec_ref(x_818);
 x_855 = lean_box(0);
}
x_856 = lean_ctor_get(x_825, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_825, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_825, 2);
lean_inc(x_858);
x_859 = lean_ctor_get(x_825, 3);
lean_inc(x_859);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 lean_ctor_release(x_825, 2);
 lean_ctor_release(x_825, 3);
 x_860 = x_825;
} else {
 lean_dec_ref(x_825);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 4, 1);
} else {
 x_861 = x_860;
}
lean_ctor_set(x_861, 0, x_856);
lean_ctor_set(x_861, 1, x_857);
lean_ctor_set(x_861, 2, x_858);
lean_ctor_set(x_861, 3, x_859);
lean_ctor_set_uint8(x_861, sizeof(void*)*4, x_819);
if (lean_is_scalar(x_855)) {
 x_862 = lean_alloc_ctor(1, 4, 1);
} else {
 x_862 = x_855;
}
lean_ctor_set(x_862, 0, x_854);
lean_ctor_set(x_862, 1, x_561);
lean_ctor_set(x_862, 2, x_562);
lean_ctor_set(x_862, 3, x_814);
lean_ctor_set_uint8(x_862, sizeof(void*)*4, x_819);
x_863 = 0;
lean_ctor_set(x_1, 3, x_862);
lean_ctor_set(x_1, 2, x_853);
lean_ctor_set(x_1, 1, x_852);
lean_ctor_set(x_1, 0, x_861);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_863);
if (lean_is_scalar(x_821)) {
 x_864 = lean_alloc_ctor(1, 4, 1);
} else {
 x_864 = x_821;
}
lean_ctor_set(x_864, 0, x_1);
lean_ctor_set(x_864, 1, x_815);
lean_ctor_set(x_864, 2, x_816);
lean_ctor_set(x_864, 3, x_820);
lean_ctor_set_uint8(x_864, sizeof(void*)*4, x_863);
return x_864;
}
else
{
lean_object* x_865; 
x_865 = lean_ctor_get(x_818, 3);
lean_inc(x_865);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; lean_object* x_870; 
lean_dec(x_821);
lean_free_object(x_1);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 lean_ctor_release(x_825, 2);
 lean_ctor_release(x_825, 3);
 x_866 = x_825;
} else {
 lean_dec_ref(x_825);
 x_866 = lean_box(0);
}
lean_inc(x_818);
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(1, 4, 1);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_818);
lean_ctor_set(x_867, 1, x_561);
lean_ctor_set(x_867, 2, x_562);
lean_ctor_set(x_867, 3, x_814);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_868 = x_818;
} else {
 lean_dec_ref(x_818);
 x_868 = lean_box(0);
}
lean_ctor_set_uint8(x_867, sizeof(void*)*4, x_819);
x_869 = 0;
if (lean_is_scalar(x_868)) {
 x_870 = lean_alloc_ctor(1, 4, 1);
} else {
 x_870 = x_868;
}
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_815);
lean_ctor_set(x_870, 2, x_816);
lean_ctor_set(x_870, 3, x_820);
lean_ctor_set_uint8(x_870, sizeof(void*)*4, x_869);
return x_870;
}
else
{
uint8_t x_871; 
x_871 = lean_ctor_get_uint8(x_865, sizeof(void*)*4);
if (x_871 == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_883; lean_object* x_884; 
lean_dec(x_821);
x_872 = lean_ctor_get(x_818, 1);
lean_inc(x_872);
x_873 = lean_ctor_get(x_818, 2);
lean_inc(x_873);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_874 = x_818;
} else {
 lean_dec_ref(x_818);
 x_874 = lean_box(0);
}
x_875 = lean_ctor_get(x_865, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_865, 1);
lean_inc(x_876);
x_877 = lean_ctor_get(x_865, 2);
lean_inc(x_877);
x_878 = lean_ctor_get(x_865, 3);
lean_inc(x_878);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 lean_ctor_release(x_865, 2);
 lean_ctor_release(x_865, 3);
 x_879 = x_865;
} else {
 lean_dec_ref(x_865);
 x_879 = lean_box(0);
}
lean_inc(x_825);
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 4, 1);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_825);
lean_ctor_set(x_880, 1, x_872);
lean_ctor_set(x_880, 2, x_873);
lean_ctor_set(x_880, 3, x_875);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 lean_ctor_release(x_825, 2);
 lean_ctor_release(x_825, 3);
 x_881 = x_825;
} else {
 lean_dec_ref(x_825);
 x_881 = lean_box(0);
}
lean_ctor_set_uint8(x_880, sizeof(void*)*4, x_819);
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(1, 4, 1);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_878);
lean_ctor_set(x_882, 1, x_561);
lean_ctor_set(x_882, 2, x_562);
lean_ctor_set(x_882, 3, x_814);
lean_ctor_set_uint8(x_882, sizeof(void*)*4, x_819);
x_883 = 0;
if (lean_is_scalar(x_874)) {
 x_884 = lean_alloc_ctor(1, 4, 1);
} else {
 x_884 = x_874;
}
lean_ctor_set(x_884, 0, x_880);
lean_ctor_set(x_884, 1, x_876);
lean_ctor_set(x_884, 2, x_877);
lean_ctor_set(x_884, 3, x_882);
lean_ctor_set_uint8(x_884, sizeof(void*)*4, x_883);
lean_ctor_set(x_1, 3, x_820);
lean_ctor_set(x_1, 2, x_816);
lean_ctor_set(x_1, 1, x_815);
lean_ctor_set(x_1, 0, x_884);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_883);
return x_1;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; uint8_t x_895; lean_object* x_896; 
x_885 = lean_ctor_get(x_818, 1);
lean_inc(x_885);
x_886 = lean_ctor_get(x_818, 2);
lean_inc(x_886);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 lean_ctor_release(x_818, 2);
 lean_ctor_release(x_818, 3);
 x_887 = x_818;
} else {
 lean_dec_ref(x_818);
 x_887 = lean_box(0);
}
x_888 = lean_ctor_get(x_825, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_825, 1);
lean_inc(x_889);
x_890 = lean_ctor_get(x_825, 2);
lean_inc(x_890);
x_891 = lean_ctor_get(x_825, 3);
lean_inc(x_891);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 lean_ctor_release(x_825, 2);
 lean_ctor_release(x_825, 3);
 x_892 = x_825;
} else {
 lean_dec_ref(x_825);
 x_892 = lean_box(0);
}
if (lean_is_scalar(x_892)) {
 x_893 = lean_alloc_ctor(1, 4, 1);
} else {
 x_893 = x_892;
}
lean_ctor_set(x_893, 0, x_888);
lean_ctor_set(x_893, 1, x_889);
lean_ctor_set(x_893, 2, x_890);
lean_ctor_set(x_893, 3, x_891);
lean_ctor_set_uint8(x_893, sizeof(void*)*4, x_871);
if (lean_is_scalar(x_887)) {
 x_894 = lean_alloc_ctor(1, 4, 1);
} else {
 x_894 = x_887;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_885);
lean_ctor_set(x_894, 2, x_886);
lean_ctor_set(x_894, 3, x_865);
lean_ctor_set_uint8(x_894, sizeof(void*)*4, x_824);
lean_ctor_set(x_1, 3, x_814);
lean_ctor_set(x_1, 0, x_894);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_819);
x_895 = 0;
if (lean_is_scalar(x_821)) {
 x_896 = lean_alloc_ctor(1, 4, 1);
} else {
 x_896 = x_821;
}
lean_ctor_set(x_896, 0, x_1);
lean_ctor_set(x_896, 1, x_815);
lean_ctor_set(x_896, 2, x_816);
lean_ctor_set(x_896, 3, x_820);
lean_ctor_set_uint8(x_896, sizeof(void*)*4, x_895);
return x_896;
}
}
}
}
}
else
{
uint8_t x_897; lean_object* x_898; 
lean_ctor_set(x_1, 3, x_814);
lean_ctor_set(x_1, 0, x_818);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_819);
x_897 = 0;
if (lean_is_scalar(x_821)) {
 x_898 = lean_alloc_ctor(1, 4, 1);
} else {
 x_898 = x_821;
}
lean_ctor_set(x_898, 0, x_1);
lean_ctor_set(x_898, 1, x_815);
lean_ctor_set(x_898, 2, x_816);
lean_ctor_set(x_898, 3, x_820);
lean_ctor_set_uint8(x_898, sizeof(void*)*4, x_897);
return x_898;
}
}
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; uint8_t x_908; lean_object* x_909; lean_object* x_910; 
x_899 = lean_ctor_get(x_1, 0);
x_900 = lean_ctor_get(x_1, 1);
x_901 = lean_ctor_get(x_1, 2);
lean_inc(x_901);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_1);
x_902 = lean_ctor_get(x_547, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_547, 1);
lean_inc(x_903);
x_904 = lean_ctor_get(x_547, 2);
lean_inc(x_904);
x_905 = lean_ctor_get(x_547, 3);
lean_inc(x_905);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 lean_ctor_release(x_547, 2);
 lean_ctor_release(x_547, 3);
 x_906 = x_547;
} else {
 lean_dec_ref(x_547);
 x_906 = lean_box(0);
}
x_907 = l_Lean_RBNode_setRed___rarg(x_899);
x_908 = 1;
lean_inc(x_4);
if (lean_is_scalar(x_906)) {
 x_909 = lean_alloc_ctor(1, 4, 1);
} else {
 x_909 = x_906;
}
lean_ctor_set(x_909, 0, x_905);
lean_ctor_set(x_909, 1, x_2);
lean_ctor_set(x_909, 2, x_3);
lean_ctor_set(x_909, 3, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_910 = x_4;
} else {
 lean_dec_ref(x_4);
 x_910 = lean_box(0);
}
lean_ctor_set_uint8(x_909, sizeof(void*)*4, x_908);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_911; uint8_t x_912; lean_object* x_913; 
x_911 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_911, 0, x_907);
lean_ctor_set(x_911, 1, x_900);
lean_ctor_set(x_911, 2, x_901);
lean_ctor_set(x_911, 3, x_902);
lean_ctor_set_uint8(x_911, sizeof(void*)*4, x_908);
x_912 = 0;
if (lean_is_scalar(x_910)) {
 x_913 = lean_alloc_ctor(1, 4, 1);
} else {
 x_913 = x_910;
}
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_903);
lean_ctor_set(x_913, 2, x_904);
lean_ctor_set(x_913, 3, x_909);
lean_ctor_set_uint8(x_913, sizeof(void*)*4, x_912);
return x_913;
}
else
{
uint8_t x_914; 
x_914 = lean_ctor_get_uint8(x_907, sizeof(void*)*4);
if (x_914 == 0)
{
lean_object* x_915; 
x_915 = lean_ctor_get(x_907, 0);
lean_inc(x_915);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; 
x_916 = lean_ctor_get(x_907, 3);
lean_inc(x_916);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; uint8_t x_922; lean_object* x_923; 
x_917 = lean_ctor_get(x_907, 1);
lean_inc(x_917);
x_918 = lean_ctor_get(x_907, 2);
lean_inc(x_918);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_919 = x_907;
} else {
 lean_dec_ref(x_907);
 x_919 = lean_box(0);
}
if (lean_is_scalar(x_919)) {
 x_920 = lean_alloc_ctor(1, 4, 1);
} else {
 x_920 = x_919;
}
lean_ctor_set(x_920, 0, x_916);
lean_ctor_set(x_920, 1, x_917);
lean_ctor_set(x_920, 2, x_918);
lean_ctor_set(x_920, 3, x_916);
lean_ctor_set_uint8(x_920, sizeof(void*)*4, x_914);
x_921 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_900);
lean_ctor_set(x_921, 2, x_901);
lean_ctor_set(x_921, 3, x_902);
lean_ctor_set_uint8(x_921, sizeof(void*)*4, x_908);
x_922 = 0;
if (lean_is_scalar(x_910)) {
 x_923 = lean_alloc_ctor(1, 4, 1);
} else {
 x_923 = x_910;
}
lean_ctor_set(x_923, 0, x_921);
lean_ctor_set(x_923, 1, x_903);
lean_ctor_set(x_923, 2, x_904);
lean_ctor_set(x_923, 3, x_909);
lean_ctor_set_uint8(x_923, sizeof(void*)*4, x_922);
return x_923;
}
else
{
uint8_t x_924; 
x_924 = lean_ctor_get_uint8(x_916, sizeof(void*)*4);
if (x_924 == 0)
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; uint8_t x_935; lean_object* x_936; lean_object* x_937; 
x_925 = lean_ctor_get(x_907, 1);
lean_inc(x_925);
x_926 = lean_ctor_get(x_907, 2);
lean_inc(x_926);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_927 = x_907;
} else {
 lean_dec_ref(x_907);
 x_927 = lean_box(0);
}
x_928 = lean_ctor_get(x_916, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_916, 1);
lean_inc(x_929);
x_930 = lean_ctor_get(x_916, 2);
lean_inc(x_930);
x_931 = lean_ctor_get(x_916, 3);
lean_inc(x_931);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 lean_ctor_release(x_916, 2);
 lean_ctor_release(x_916, 3);
 x_932 = x_916;
} else {
 lean_dec_ref(x_916);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_932)) {
 x_933 = lean_alloc_ctor(1, 4, 1);
} else {
 x_933 = x_932;
}
lean_ctor_set(x_933, 0, x_915);
lean_ctor_set(x_933, 1, x_925);
lean_ctor_set(x_933, 2, x_926);
lean_ctor_set(x_933, 3, x_928);
lean_ctor_set_uint8(x_933, sizeof(void*)*4, x_908);
if (lean_is_scalar(x_927)) {
 x_934 = lean_alloc_ctor(1, 4, 1);
} else {
 x_934 = x_927;
}
lean_ctor_set(x_934, 0, x_931);
lean_ctor_set(x_934, 1, x_900);
lean_ctor_set(x_934, 2, x_901);
lean_ctor_set(x_934, 3, x_902);
lean_ctor_set_uint8(x_934, sizeof(void*)*4, x_908);
x_935 = 0;
x_936 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_936, 0, x_933);
lean_ctor_set(x_936, 1, x_929);
lean_ctor_set(x_936, 2, x_930);
lean_ctor_set(x_936, 3, x_934);
lean_ctor_set_uint8(x_936, sizeof(void*)*4, x_935);
if (lean_is_scalar(x_910)) {
 x_937 = lean_alloc_ctor(1, 4, 1);
} else {
 x_937 = x_910;
}
lean_ctor_set(x_937, 0, x_936);
lean_ctor_set(x_937, 1, x_903);
lean_ctor_set(x_937, 2, x_904);
lean_ctor_set(x_937, 3, x_909);
lean_ctor_set_uint8(x_937, sizeof(void*)*4, x_935);
return x_937;
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; uint8_t x_941; lean_object* x_942; 
lean_dec(x_910);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 lean_ctor_release(x_916, 2);
 lean_ctor_release(x_916, 3);
 x_938 = x_916;
} else {
 lean_dec_ref(x_916);
 x_938 = lean_box(0);
}
lean_inc(x_907);
if (lean_is_scalar(x_938)) {
 x_939 = lean_alloc_ctor(1, 4, 1);
} else {
 x_939 = x_938;
}
lean_ctor_set(x_939, 0, x_907);
lean_ctor_set(x_939, 1, x_900);
lean_ctor_set(x_939, 2, x_901);
lean_ctor_set(x_939, 3, x_902);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_940 = x_907;
} else {
 lean_dec_ref(x_907);
 x_940 = lean_box(0);
}
lean_ctor_set_uint8(x_939, sizeof(void*)*4, x_908);
x_941 = 0;
if (lean_is_scalar(x_940)) {
 x_942 = lean_alloc_ctor(1, 4, 1);
} else {
 x_942 = x_940;
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_903);
lean_ctor_set(x_942, 2, x_904);
lean_ctor_set(x_942, 3, x_909);
lean_ctor_set_uint8(x_942, sizeof(void*)*4, x_941);
return x_942;
}
}
}
else
{
uint8_t x_943; 
x_943 = lean_ctor_get_uint8(x_915, sizeof(void*)*4);
if (x_943 == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; uint8_t x_955; lean_object* x_956; lean_object* x_957; 
x_944 = lean_ctor_get(x_907, 1);
lean_inc(x_944);
x_945 = lean_ctor_get(x_907, 2);
lean_inc(x_945);
x_946 = lean_ctor_get(x_907, 3);
lean_inc(x_946);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_947 = x_907;
} else {
 lean_dec_ref(x_907);
 x_947 = lean_box(0);
}
x_948 = lean_ctor_get(x_915, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_915, 1);
lean_inc(x_949);
x_950 = lean_ctor_get(x_915, 2);
lean_inc(x_950);
x_951 = lean_ctor_get(x_915, 3);
lean_inc(x_951);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 lean_ctor_release(x_915, 2);
 lean_ctor_release(x_915, 3);
 x_952 = x_915;
} else {
 lean_dec_ref(x_915);
 x_952 = lean_box(0);
}
if (lean_is_scalar(x_952)) {
 x_953 = lean_alloc_ctor(1, 4, 1);
} else {
 x_953 = x_952;
}
lean_ctor_set(x_953, 0, x_948);
lean_ctor_set(x_953, 1, x_949);
lean_ctor_set(x_953, 2, x_950);
lean_ctor_set(x_953, 3, x_951);
lean_ctor_set_uint8(x_953, sizeof(void*)*4, x_908);
if (lean_is_scalar(x_947)) {
 x_954 = lean_alloc_ctor(1, 4, 1);
} else {
 x_954 = x_947;
}
lean_ctor_set(x_954, 0, x_946);
lean_ctor_set(x_954, 1, x_900);
lean_ctor_set(x_954, 2, x_901);
lean_ctor_set(x_954, 3, x_902);
lean_ctor_set_uint8(x_954, sizeof(void*)*4, x_908);
x_955 = 0;
x_956 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_956, 0, x_953);
lean_ctor_set(x_956, 1, x_944);
lean_ctor_set(x_956, 2, x_945);
lean_ctor_set(x_956, 3, x_954);
lean_ctor_set_uint8(x_956, sizeof(void*)*4, x_955);
if (lean_is_scalar(x_910)) {
 x_957 = lean_alloc_ctor(1, 4, 1);
} else {
 x_957 = x_910;
}
lean_ctor_set(x_957, 0, x_956);
lean_ctor_set(x_957, 1, x_903);
lean_ctor_set(x_957, 2, x_904);
lean_ctor_set(x_957, 3, x_909);
lean_ctor_set_uint8(x_957, sizeof(void*)*4, x_955);
return x_957;
}
else
{
lean_object* x_958; 
x_958 = lean_ctor_get(x_907, 3);
lean_inc(x_958);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; lean_object* x_963; 
lean_dec(x_910);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 lean_ctor_release(x_915, 2);
 lean_ctor_release(x_915, 3);
 x_959 = x_915;
} else {
 lean_dec_ref(x_915);
 x_959 = lean_box(0);
}
lean_inc(x_907);
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(1, 4, 1);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_907);
lean_ctor_set(x_960, 1, x_900);
lean_ctor_set(x_960, 2, x_901);
lean_ctor_set(x_960, 3, x_902);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_961 = x_907;
} else {
 lean_dec_ref(x_907);
 x_961 = lean_box(0);
}
lean_ctor_set_uint8(x_960, sizeof(void*)*4, x_908);
x_962 = 0;
if (lean_is_scalar(x_961)) {
 x_963 = lean_alloc_ctor(1, 4, 1);
} else {
 x_963 = x_961;
}
lean_ctor_set(x_963, 0, x_960);
lean_ctor_set(x_963, 1, x_903);
lean_ctor_set(x_963, 2, x_904);
lean_ctor_set(x_963, 3, x_909);
lean_ctor_set_uint8(x_963, sizeof(void*)*4, x_962);
return x_963;
}
else
{
uint8_t x_964; 
x_964 = lean_ctor_get_uint8(x_958, sizeof(void*)*4);
if (x_964 == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; uint8_t x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_910);
x_965 = lean_ctor_get(x_907, 1);
lean_inc(x_965);
x_966 = lean_ctor_get(x_907, 2);
lean_inc(x_966);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_967 = x_907;
} else {
 lean_dec_ref(x_907);
 x_967 = lean_box(0);
}
x_968 = lean_ctor_get(x_958, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_958, 1);
lean_inc(x_969);
x_970 = lean_ctor_get(x_958, 2);
lean_inc(x_970);
x_971 = lean_ctor_get(x_958, 3);
lean_inc(x_971);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 lean_ctor_release(x_958, 2);
 lean_ctor_release(x_958, 3);
 x_972 = x_958;
} else {
 lean_dec_ref(x_958);
 x_972 = lean_box(0);
}
lean_inc(x_915);
if (lean_is_scalar(x_972)) {
 x_973 = lean_alloc_ctor(1, 4, 1);
} else {
 x_973 = x_972;
}
lean_ctor_set(x_973, 0, x_915);
lean_ctor_set(x_973, 1, x_965);
lean_ctor_set(x_973, 2, x_966);
lean_ctor_set(x_973, 3, x_968);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 lean_ctor_release(x_915, 2);
 lean_ctor_release(x_915, 3);
 x_974 = x_915;
} else {
 lean_dec_ref(x_915);
 x_974 = lean_box(0);
}
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_908);
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 4, 1);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_971);
lean_ctor_set(x_975, 1, x_900);
lean_ctor_set(x_975, 2, x_901);
lean_ctor_set(x_975, 3, x_902);
lean_ctor_set_uint8(x_975, sizeof(void*)*4, x_908);
x_976 = 0;
if (lean_is_scalar(x_967)) {
 x_977 = lean_alloc_ctor(1, 4, 1);
} else {
 x_977 = x_967;
}
lean_ctor_set(x_977, 0, x_973);
lean_ctor_set(x_977, 1, x_969);
lean_ctor_set(x_977, 2, x_970);
lean_ctor_set(x_977, 3, x_975);
lean_ctor_set_uint8(x_977, sizeof(void*)*4, x_976);
x_978 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_903);
lean_ctor_set(x_978, 2, x_904);
lean_ctor_set(x_978, 3, x_909);
lean_ctor_set_uint8(x_978, sizeof(void*)*4, x_976);
return x_978;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; uint8_t x_990; lean_object* x_991; 
x_979 = lean_ctor_get(x_907, 1);
lean_inc(x_979);
x_980 = lean_ctor_get(x_907, 2);
lean_inc(x_980);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 lean_ctor_release(x_907, 2);
 lean_ctor_release(x_907, 3);
 x_981 = x_907;
} else {
 lean_dec_ref(x_907);
 x_981 = lean_box(0);
}
x_982 = lean_ctor_get(x_915, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_915, 1);
lean_inc(x_983);
x_984 = lean_ctor_get(x_915, 2);
lean_inc(x_984);
x_985 = lean_ctor_get(x_915, 3);
lean_inc(x_985);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 lean_ctor_release(x_915, 2);
 lean_ctor_release(x_915, 3);
 x_986 = x_915;
} else {
 lean_dec_ref(x_915);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(1, 4, 1);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_982);
lean_ctor_set(x_987, 1, x_983);
lean_ctor_set(x_987, 2, x_984);
lean_ctor_set(x_987, 3, x_985);
lean_ctor_set_uint8(x_987, sizeof(void*)*4, x_964);
if (lean_is_scalar(x_981)) {
 x_988 = lean_alloc_ctor(1, 4, 1);
} else {
 x_988 = x_981;
}
lean_ctor_set(x_988, 0, x_987);
lean_ctor_set(x_988, 1, x_979);
lean_ctor_set(x_988, 2, x_980);
lean_ctor_set(x_988, 3, x_958);
lean_ctor_set_uint8(x_988, sizeof(void*)*4, x_914);
x_989 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_989, 0, x_988);
lean_ctor_set(x_989, 1, x_900);
lean_ctor_set(x_989, 2, x_901);
lean_ctor_set(x_989, 3, x_902);
lean_ctor_set_uint8(x_989, sizeof(void*)*4, x_908);
x_990 = 0;
if (lean_is_scalar(x_910)) {
 x_991 = lean_alloc_ctor(1, 4, 1);
} else {
 x_991 = x_910;
}
lean_ctor_set(x_991, 0, x_989);
lean_ctor_set(x_991, 1, x_903);
lean_ctor_set(x_991, 2, x_904);
lean_ctor_set(x_991, 3, x_909);
lean_ctor_set_uint8(x_991, sizeof(void*)*4, x_990);
return x_991;
}
}
}
}
}
else
{
lean_object* x_992; uint8_t x_993; lean_object* x_994; 
x_992 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_992, 0, x_907);
lean_ctor_set(x_992, 1, x_900);
lean_ctor_set(x_992, 2, x_901);
lean_ctor_set(x_992, 3, x_902);
lean_ctor_set_uint8(x_992, sizeof(void*)*4, x_908);
x_993 = 0;
if (lean_is_scalar(x_910)) {
 x_994 = lean_alloc_ctor(1, 4, 1);
} else {
 x_994 = x_910;
}
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_903);
lean_ctor_set(x_994, 2, x_904);
lean_ctor_set(x_994, 3, x_909);
lean_ctor_set_uint8(x_994, sizeof(void*)*4, x_993);
return x_994;
}
}
}
}
}
}
else
{
uint8_t x_995; 
x_995 = !lean_is_exclusive(x_1);
if (x_995 == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; 
x_996 = lean_ctor_get(x_1, 0);
x_997 = lean_ctor_get(x_1, 1);
x_998 = lean_ctor_get(x_1, 2);
x_999 = lean_ctor_get(x_1, 3);
x_1000 = 0;
lean_inc(x_999);
lean_inc(x_998);
lean_inc(x_997);
lean_inc(x_996);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1000);
if (lean_obj_tag(x_996) == 0)
{
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1001; uint8_t x_1002; lean_object* x_1003; 
lean_dec(x_1);
x_1001 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set(x_1001, 1, x_997);
lean_ctor_set(x_1001, 2, x_998);
lean_ctor_set(x_1001, 3, x_999);
lean_ctor_set_uint8(x_1001, sizeof(void*)*4, x_1000);
x_1002 = 1;
x_1003 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1003, 0, x_1001);
lean_ctor_set(x_1003, 1, x_2);
lean_ctor_set(x_1003, 2, x_3);
lean_ctor_set(x_1003, 3, x_4);
lean_ctor_set_uint8(x_1003, sizeof(void*)*4, x_1002);
return x_1003;
}
else
{
uint8_t x_1004; 
x_1004 = lean_ctor_get_uint8(x_999, sizeof(void*)*4);
if (x_1004 == 0)
{
uint8_t x_1005; 
lean_dec(x_1);
x_1005 = !lean_is_exclusive(x_999);
if (x_1005 == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1006 = lean_ctor_get(x_999, 0);
x_1007 = lean_ctor_get(x_999, 1);
x_1008 = lean_ctor_get(x_999, 2);
x_1009 = lean_ctor_get(x_999, 3);
x_1010 = 1;
lean_ctor_set(x_999, 3, x_1006);
lean_ctor_set(x_999, 2, x_998);
lean_ctor_set(x_999, 1, x_997);
lean_ctor_set(x_999, 0, x_996);
lean_ctor_set_uint8(x_999, sizeof(void*)*4, x_1010);
x_1011 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_2);
lean_ctor_set(x_1011, 2, x_3);
lean_ctor_set(x_1011, 3, x_4);
lean_ctor_set_uint8(x_1011, sizeof(void*)*4, x_1010);
x_1012 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1012, 0, x_999);
lean_ctor_set(x_1012, 1, x_1007);
lean_ctor_set(x_1012, 2, x_1008);
lean_ctor_set(x_1012, 3, x_1011);
lean_ctor_set_uint8(x_1012, sizeof(void*)*4, x_1000);
return x_1012;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; uint8_t x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1013 = lean_ctor_get(x_999, 0);
x_1014 = lean_ctor_get(x_999, 1);
x_1015 = lean_ctor_get(x_999, 2);
x_1016 = lean_ctor_get(x_999, 3);
lean_inc(x_1016);
lean_inc(x_1015);
lean_inc(x_1014);
lean_inc(x_1013);
lean_dec(x_999);
x_1017 = 1;
x_1018 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1018, 0, x_996);
lean_ctor_set(x_1018, 1, x_997);
lean_ctor_set(x_1018, 2, x_998);
lean_ctor_set(x_1018, 3, x_1013);
lean_ctor_set_uint8(x_1018, sizeof(void*)*4, x_1017);
x_1019 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1019, 0, x_1016);
lean_ctor_set(x_1019, 1, x_2);
lean_ctor_set(x_1019, 2, x_3);
lean_ctor_set(x_1019, 3, x_4);
lean_ctor_set_uint8(x_1019, sizeof(void*)*4, x_1017);
x_1020 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1014);
lean_ctor_set(x_1020, 2, x_1015);
lean_ctor_set(x_1020, 3, x_1019);
lean_ctor_set_uint8(x_1020, sizeof(void*)*4, x_1000);
return x_1020;
}
}
else
{
uint8_t x_1021; 
lean_dec(x_998);
lean_dec(x_997);
x_1021 = !lean_is_exclusive(x_999);
if (x_1021 == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; 
x_1022 = lean_ctor_get(x_999, 3);
lean_dec(x_1022);
x_1023 = lean_ctor_get(x_999, 2);
lean_dec(x_1023);
x_1024 = lean_ctor_get(x_999, 1);
lean_dec(x_1024);
x_1025 = lean_ctor_get(x_999, 0);
lean_dec(x_1025);
x_1026 = 1;
lean_ctor_set(x_999, 3, x_4);
lean_ctor_set(x_999, 2, x_3);
lean_ctor_set(x_999, 1, x_2);
lean_ctor_set(x_999, 0, x_1);
lean_ctor_set_uint8(x_999, sizeof(void*)*4, x_1026);
return x_999;
}
else
{
uint8_t x_1027; lean_object* x_1028; 
lean_dec(x_999);
x_1027 = 1;
x_1028 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1028, 0, x_1);
lean_ctor_set(x_1028, 1, x_2);
lean_ctor_set(x_1028, 2, x_3);
lean_ctor_set(x_1028, 3, x_4);
lean_ctor_set_uint8(x_1028, sizeof(void*)*4, x_1027);
return x_1028;
}
}
}
}
else
{
uint8_t x_1029; 
x_1029 = lean_ctor_get_uint8(x_996, sizeof(void*)*4);
if (x_1029 == 0)
{
uint8_t x_1030; 
lean_dec(x_1);
x_1030 = !lean_is_exclusive(x_996);
if (x_1030 == 0)
{
uint8_t x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1031 = 1;
lean_ctor_set_uint8(x_996, sizeof(void*)*4, x_1031);
x_1032 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1032, 0, x_999);
lean_ctor_set(x_1032, 1, x_2);
lean_ctor_set(x_1032, 2, x_3);
lean_ctor_set(x_1032, 3, x_4);
lean_ctor_set_uint8(x_1032, sizeof(void*)*4, x_1031);
x_1033 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1033, 0, x_996);
lean_ctor_set(x_1033, 1, x_997);
lean_ctor_set(x_1033, 2, x_998);
lean_ctor_set(x_1033, 3, x_1032);
lean_ctor_set_uint8(x_1033, sizeof(void*)*4, x_1000);
return x_1033;
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; uint8_t x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1034 = lean_ctor_get(x_996, 0);
x_1035 = lean_ctor_get(x_996, 1);
x_1036 = lean_ctor_get(x_996, 2);
x_1037 = lean_ctor_get(x_996, 3);
lean_inc(x_1037);
lean_inc(x_1036);
lean_inc(x_1035);
lean_inc(x_1034);
lean_dec(x_996);
x_1038 = 1;
x_1039 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1039, 0, x_1034);
lean_ctor_set(x_1039, 1, x_1035);
lean_ctor_set(x_1039, 2, x_1036);
lean_ctor_set(x_1039, 3, x_1037);
lean_ctor_set_uint8(x_1039, sizeof(void*)*4, x_1038);
x_1040 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1040, 0, x_999);
lean_ctor_set(x_1040, 1, x_2);
lean_ctor_set(x_1040, 2, x_3);
lean_ctor_set(x_1040, 3, x_4);
lean_ctor_set_uint8(x_1040, sizeof(void*)*4, x_1038);
x_1041 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1041, 0, x_1039);
lean_ctor_set(x_1041, 1, x_997);
lean_ctor_set(x_1041, 2, x_998);
lean_ctor_set(x_1041, 3, x_1040);
lean_ctor_set_uint8(x_1041, sizeof(void*)*4, x_1000);
return x_1041;
}
}
else
{
if (lean_obj_tag(x_999) == 0)
{
uint8_t x_1042; 
lean_dec(x_998);
lean_dec(x_997);
x_1042 = !lean_is_exclusive(x_996);
if (x_1042 == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
x_1043 = lean_ctor_get(x_996, 3);
lean_dec(x_1043);
x_1044 = lean_ctor_get(x_996, 2);
lean_dec(x_1044);
x_1045 = lean_ctor_get(x_996, 1);
lean_dec(x_1045);
x_1046 = lean_ctor_get(x_996, 0);
lean_dec(x_1046);
x_1047 = 1;
lean_ctor_set(x_996, 3, x_4);
lean_ctor_set(x_996, 2, x_3);
lean_ctor_set(x_996, 1, x_2);
lean_ctor_set(x_996, 0, x_1);
lean_ctor_set_uint8(x_996, sizeof(void*)*4, x_1047);
return x_996;
}
else
{
uint8_t x_1048; lean_object* x_1049; 
lean_dec(x_996);
x_1048 = 1;
x_1049 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1049, 0, x_1);
lean_ctor_set(x_1049, 1, x_2);
lean_ctor_set(x_1049, 2, x_3);
lean_ctor_set(x_1049, 3, x_4);
lean_ctor_set_uint8(x_1049, sizeof(void*)*4, x_1048);
return x_1049;
}
}
else
{
uint8_t x_1050; 
lean_dec(x_1);
x_1050 = lean_ctor_get_uint8(x_999, sizeof(void*)*4);
if (x_1050 == 0)
{
uint8_t x_1051; 
x_1051 = !lean_is_exclusive(x_999);
if (x_1051 == 0)
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; uint8_t x_1056; uint8_t x_1057; 
x_1052 = lean_ctor_get(x_999, 0);
x_1053 = lean_ctor_get(x_999, 1);
x_1054 = lean_ctor_get(x_999, 2);
x_1055 = lean_ctor_get(x_999, 3);
x_1056 = 1;
lean_inc(x_996);
lean_ctor_set(x_999, 3, x_1052);
lean_ctor_set(x_999, 2, x_998);
lean_ctor_set(x_999, 1, x_997);
lean_ctor_set(x_999, 0, x_996);
x_1057 = !lean_is_exclusive(x_996);
if (x_1057 == 0)
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; uint8_t x_1062; 
x_1058 = lean_ctor_get(x_996, 3);
lean_dec(x_1058);
x_1059 = lean_ctor_get(x_996, 2);
lean_dec(x_1059);
x_1060 = lean_ctor_get(x_996, 1);
lean_dec(x_1060);
x_1061 = lean_ctor_get(x_996, 0);
lean_dec(x_1061);
lean_ctor_set_uint8(x_999, sizeof(void*)*4, x_1056);
lean_inc(x_4);
lean_ctor_set(x_996, 3, x_4);
lean_ctor_set(x_996, 2, x_3);
lean_ctor_set(x_996, 1, x_2);
lean_ctor_set(x_996, 0, x_1055);
x_1062 = !lean_is_exclusive(x_4);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1063 = lean_ctor_get(x_4, 3);
lean_dec(x_1063);
x_1064 = lean_ctor_get(x_4, 2);
lean_dec(x_1064);
x_1065 = lean_ctor_get(x_4, 1);
lean_dec(x_1065);
x_1066 = lean_ctor_get(x_4, 0);
lean_dec(x_1066);
lean_ctor_set_uint8(x_996, sizeof(void*)*4, x_1056);
lean_ctor_set(x_4, 3, x_996);
lean_ctor_set(x_4, 2, x_1054);
lean_ctor_set(x_4, 1, x_1053);
lean_ctor_set(x_4, 0, x_999);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1000);
return x_4;
}
else
{
lean_object* x_1067; 
lean_dec(x_4);
lean_ctor_set_uint8(x_996, sizeof(void*)*4, x_1056);
x_1067 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1067, 0, x_999);
lean_ctor_set(x_1067, 1, x_1053);
lean_ctor_set(x_1067, 2, x_1054);
lean_ctor_set(x_1067, 3, x_996);
lean_ctor_set_uint8(x_1067, sizeof(void*)*4, x_1000);
return x_1067;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_996);
lean_ctor_set_uint8(x_999, sizeof(void*)*4, x_1056);
lean_inc(x_4);
x_1068 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1068, 0, x_1055);
lean_ctor_set(x_1068, 1, x_2);
lean_ctor_set(x_1068, 2, x_3);
lean_ctor_set(x_1068, 3, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1069 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1069 = lean_box(0);
}
lean_ctor_set_uint8(x_1068, sizeof(void*)*4, x_1056);
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_999);
lean_ctor_set(x_1070, 1, x_1053);
lean_ctor_set(x_1070, 2, x_1054);
lean_ctor_set(x_1070, 3, x_1068);
lean_ctor_set_uint8(x_1070, sizeof(void*)*4, x_1000);
return x_1070;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; uint8_t x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1071 = lean_ctor_get(x_999, 0);
x_1072 = lean_ctor_get(x_999, 1);
x_1073 = lean_ctor_get(x_999, 2);
x_1074 = lean_ctor_get(x_999, 3);
lean_inc(x_1074);
lean_inc(x_1073);
lean_inc(x_1072);
lean_inc(x_1071);
lean_dec(x_999);
x_1075 = 1;
lean_inc(x_996);
x_1076 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1076, 0, x_996);
lean_ctor_set(x_1076, 1, x_997);
lean_ctor_set(x_1076, 2, x_998);
lean_ctor_set(x_1076, 3, x_1071);
if (lean_is_exclusive(x_996)) {
 lean_ctor_release(x_996, 0);
 lean_ctor_release(x_996, 1);
 lean_ctor_release(x_996, 2);
 lean_ctor_release(x_996, 3);
 x_1077 = x_996;
} else {
 lean_dec_ref(x_996);
 x_1077 = lean_box(0);
}
lean_ctor_set_uint8(x_1076, sizeof(void*)*4, x_1075);
lean_inc(x_4);
if (lean_is_scalar(x_1077)) {
 x_1078 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1078 = x_1077;
}
lean_ctor_set(x_1078, 0, x_1074);
lean_ctor_set(x_1078, 1, x_2);
lean_ctor_set(x_1078, 2, x_3);
lean_ctor_set(x_1078, 3, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1079 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1079 = lean_box(0);
}
lean_ctor_set_uint8(x_1078, sizeof(void*)*4, x_1075);
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1076);
lean_ctor_set(x_1080, 1, x_1072);
lean_ctor_set(x_1080, 2, x_1073);
lean_ctor_set(x_1080, 3, x_1078);
lean_ctor_set_uint8(x_1080, sizeof(void*)*4, x_1000);
return x_1080;
}
}
else
{
uint8_t x_1081; 
x_1081 = !lean_is_exclusive(x_996);
if (x_1081 == 0)
{
lean_object* x_1082; uint8_t x_1083; lean_object* x_1084; 
lean_ctor_set_uint8(x_996, sizeof(void*)*4, x_1050);
x_1082 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1082, 0, x_996);
lean_ctor_set(x_1082, 1, x_997);
lean_ctor_set(x_1082, 2, x_998);
lean_ctor_set(x_1082, 3, x_999);
lean_ctor_set_uint8(x_1082, sizeof(void*)*4, x_1000);
x_1083 = 1;
x_1084 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1084, 0, x_1082);
lean_ctor_set(x_1084, 1, x_2);
lean_ctor_set(x_1084, 2, x_3);
lean_ctor_set(x_1084, 3, x_4);
lean_ctor_set_uint8(x_1084, sizeof(void*)*4, x_1083);
return x_1084;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; lean_object* x_1092; 
x_1085 = lean_ctor_get(x_996, 0);
x_1086 = lean_ctor_get(x_996, 1);
x_1087 = lean_ctor_get(x_996, 2);
x_1088 = lean_ctor_get(x_996, 3);
lean_inc(x_1088);
lean_inc(x_1087);
lean_inc(x_1086);
lean_inc(x_1085);
lean_dec(x_996);
x_1089 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1089, 0, x_1085);
lean_ctor_set(x_1089, 1, x_1086);
lean_ctor_set(x_1089, 2, x_1087);
lean_ctor_set(x_1089, 3, x_1088);
lean_ctor_set_uint8(x_1089, sizeof(void*)*4, x_1050);
x_1090 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1090, 0, x_1089);
lean_ctor_set(x_1090, 1, x_997);
lean_ctor_set(x_1090, 2, x_998);
lean_ctor_set(x_1090, 3, x_999);
lean_ctor_set_uint8(x_1090, sizeof(void*)*4, x_1000);
x_1091 = 1;
x_1092 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_2);
lean_ctor_set(x_1092, 2, x_3);
lean_ctor_set(x_1092, 3, x_4);
lean_ctor_set_uint8(x_1092, sizeof(void*)*4, x_1091);
return x_1092;
}
}
}
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; lean_object* x_1098; 
x_1093 = lean_ctor_get(x_1, 0);
x_1094 = lean_ctor_get(x_1, 1);
x_1095 = lean_ctor_get(x_1, 2);
x_1096 = lean_ctor_get(x_1, 3);
lean_inc(x_1096);
lean_inc(x_1095);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_1);
x_1097 = 0;
lean_inc(x_1096);
lean_inc(x_1095);
lean_inc(x_1094);
lean_inc(x_1093);
x_1098 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1098, 0, x_1093);
lean_ctor_set(x_1098, 1, x_1094);
lean_ctor_set(x_1098, 2, x_1095);
lean_ctor_set(x_1098, 3, x_1096);
lean_ctor_set_uint8(x_1098, sizeof(void*)*4, x_1097);
if (lean_obj_tag(x_1093) == 0)
{
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1099; uint8_t x_1100; lean_object* x_1101; 
lean_dec(x_1098);
x_1099 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1099, 0, x_1096);
lean_ctor_set(x_1099, 1, x_1094);
lean_ctor_set(x_1099, 2, x_1095);
lean_ctor_set(x_1099, 3, x_1096);
lean_ctor_set_uint8(x_1099, sizeof(void*)*4, x_1097);
x_1100 = 1;
x_1101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1101, 0, x_1099);
lean_ctor_set(x_1101, 1, x_2);
lean_ctor_set(x_1101, 2, x_3);
lean_ctor_set(x_1101, 3, x_4);
lean_ctor_set_uint8(x_1101, sizeof(void*)*4, x_1100);
return x_1101;
}
else
{
uint8_t x_1102; 
x_1102 = lean_ctor_get_uint8(x_1096, sizeof(void*)*4);
if (x_1102 == 0)
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; uint8_t x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_1098);
x_1103 = lean_ctor_get(x_1096, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1096, 1);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1096, 2);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1096, 3);
lean_inc(x_1106);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 lean_ctor_release(x_1096, 2);
 lean_ctor_release(x_1096, 3);
 x_1107 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1107 = lean_box(0);
}
x_1108 = 1;
if (lean_is_scalar(x_1107)) {
 x_1109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1109 = x_1107;
}
lean_ctor_set(x_1109, 0, x_1093);
lean_ctor_set(x_1109, 1, x_1094);
lean_ctor_set(x_1109, 2, x_1095);
lean_ctor_set(x_1109, 3, x_1103);
lean_ctor_set_uint8(x_1109, sizeof(void*)*4, x_1108);
x_1110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1110, 0, x_1106);
lean_ctor_set(x_1110, 1, x_2);
lean_ctor_set(x_1110, 2, x_3);
lean_ctor_set(x_1110, 3, x_4);
lean_ctor_set_uint8(x_1110, sizeof(void*)*4, x_1108);
x_1111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1104);
lean_ctor_set(x_1111, 2, x_1105);
lean_ctor_set(x_1111, 3, x_1110);
lean_ctor_set_uint8(x_1111, sizeof(void*)*4, x_1097);
return x_1111;
}
else
{
lean_object* x_1112; uint8_t x_1113; lean_object* x_1114; 
lean_dec(x_1095);
lean_dec(x_1094);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 lean_ctor_release(x_1096, 2);
 lean_ctor_release(x_1096, 3);
 x_1112 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1112 = lean_box(0);
}
x_1113 = 1;
if (lean_is_scalar(x_1112)) {
 x_1114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1114 = x_1112;
}
lean_ctor_set(x_1114, 0, x_1098);
lean_ctor_set(x_1114, 1, x_2);
lean_ctor_set(x_1114, 2, x_3);
lean_ctor_set(x_1114, 3, x_4);
lean_ctor_set_uint8(x_1114, sizeof(void*)*4, x_1113);
return x_1114;
}
}
}
else
{
uint8_t x_1115; 
x_1115 = lean_ctor_get_uint8(x_1093, sizeof(void*)*4);
if (x_1115 == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; uint8_t x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_1098);
x_1116 = lean_ctor_get(x_1093, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1093, 1);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1093, 2);
lean_inc(x_1118);
x_1119 = lean_ctor_get(x_1093, 3);
lean_inc(x_1119);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 lean_ctor_release(x_1093, 2);
 lean_ctor_release(x_1093, 3);
 x_1120 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1120 = lean_box(0);
}
x_1121 = 1;
if (lean_is_scalar(x_1120)) {
 x_1122 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1122 = x_1120;
}
lean_ctor_set(x_1122, 0, x_1116);
lean_ctor_set(x_1122, 1, x_1117);
lean_ctor_set(x_1122, 2, x_1118);
lean_ctor_set(x_1122, 3, x_1119);
lean_ctor_set_uint8(x_1122, sizeof(void*)*4, x_1121);
x_1123 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1123, 0, x_1096);
lean_ctor_set(x_1123, 1, x_2);
lean_ctor_set(x_1123, 2, x_3);
lean_ctor_set(x_1123, 3, x_4);
lean_ctor_set_uint8(x_1123, sizeof(void*)*4, x_1121);
x_1124 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1124, 0, x_1122);
lean_ctor_set(x_1124, 1, x_1094);
lean_ctor_set(x_1124, 2, x_1095);
lean_ctor_set(x_1124, 3, x_1123);
lean_ctor_set_uint8(x_1124, sizeof(void*)*4, x_1097);
return x_1124;
}
else
{
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1125; uint8_t x_1126; lean_object* x_1127; 
lean_dec(x_1095);
lean_dec(x_1094);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 lean_ctor_release(x_1093, 2);
 lean_ctor_release(x_1093, 3);
 x_1125 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1125 = lean_box(0);
}
x_1126 = 1;
if (lean_is_scalar(x_1125)) {
 x_1127 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1127 = x_1125;
}
lean_ctor_set(x_1127, 0, x_1098);
lean_ctor_set(x_1127, 1, x_2);
lean_ctor_set(x_1127, 2, x_3);
lean_ctor_set(x_1127, 3, x_4);
lean_ctor_set_uint8(x_1127, sizeof(void*)*4, x_1126);
return x_1127;
}
else
{
uint8_t x_1128; 
lean_dec(x_1098);
x_1128 = lean_ctor_get_uint8(x_1096, sizeof(void*)*4);
if (x_1128 == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1129 = lean_ctor_get(x_1096, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1096, 1);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1096, 2);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1096, 3);
lean_inc(x_1132);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 lean_ctor_release(x_1096, 2);
 lean_ctor_release(x_1096, 3);
 x_1133 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1133 = lean_box(0);
}
x_1134 = 1;
lean_inc(x_1093);
if (lean_is_scalar(x_1133)) {
 x_1135 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1135 = x_1133;
}
lean_ctor_set(x_1135, 0, x_1093);
lean_ctor_set(x_1135, 1, x_1094);
lean_ctor_set(x_1135, 2, x_1095);
lean_ctor_set(x_1135, 3, x_1129);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 lean_ctor_release(x_1093, 2);
 lean_ctor_release(x_1093, 3);
 x_1136 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1136 = lean_box(0);
}
lean_ctor_set_uint8(x_1135, sizeof(void*)*4, x_1134);
lean_inc(x_4);
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1137 = x_1136;
}
lean_ctor_set(x_1137, 0, x_1132);
lean_ctor_set(x_1137, 1, x_2);
lean_ctor_set(x_1137, 2, x_3);
lean_ctor_set(x_1137, 3, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1138 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1138 = lean_box(0);
}
lean_ctor_set_uint8(x_1137, sizeof(void*)*4, x_1134);
if (lean_is_scalar(x_1138)) {
 x_1139 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1139 = x_1138;
}
lean_ctor_set(x_1139, 0, x_1135);
lean_ctor_set(x_1139, 1, x_1130);
lean_ctor_set(x_1139, 2, x_1131);
lean_ctor_set(x_1139, 3, x_1137);
lean_ctor_set_uint8(x_1139, sizeof(void*)*4, x_1097);
return x_1139;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; uint8_t x_1147; lean_object* x_1148; 
x_1140 = lean_ctor_get(x_1093, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1093, 1);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1093, 2);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1093, 3);
lean_inc(x_1143);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 lean_ctor_release(x_1093, 2);
 lean_ctor_release(x_1093, 3);
 x_1144 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1144 = lean_box(0);
}
if (lean_is_scalar(x_1144)) {
 x_1145 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1145 = x_1144;
}
lean_ctor_set(x_1145, 0, x_1140);
lean_ctor_set(x_1145, 1, x_1141);
lean_ctor_set(x_1145, 2, x_1142);
lean_ctor_set(x_1145, 3, x_1143);
lean_ctor_set_uint8(x_1145, sizeof(void*)*4, x_1128);
x_1146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1146, 0, x_1145);
lean_ctor_set(x_1146, 1, x_1094);
lean_ctor_set(x_1146, 2, x_1095);
lean_ctor_set(x_1146, 3, x_1096);
lean_ctor_set_uint8(x_1146, sizeof(void*)*4, x_1097);
x_1147 = 1;
x_1148 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_2);
lean_ctor_set(x_1148, 2, x_3);
lean_ctor_set(x_1148, 3, x_4);
lean_ctor_set_uint8(x_1148, sizeof(void*)*4, x_1147);
return x_1148;
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
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_balRight___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___rarg(lean_object* x_1) {
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
x_5 = l_Lean_RBNode_size___rarg(x_3);
x_6 = l_Lean_RBNode_size___rarg(x_4);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_size___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_1);
x_9 = lean_box(x_4);
x_10 = lean_apply_5(x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_RBNode_appendTrees___rarg(x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = 0;
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_13);
return x_1;
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 2);
x_19 = lean_ctor_get(x_12, 3);
x_20 = 0;
lean_ctor_set(x_12, 3, x_16);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_20);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_20);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_18);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
x_23 = lean_ctor_get(x_12, 2);
x_24 = lean_ctor_get(x_12, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_8);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
lean_ctor_set(x_2, 0, x_24);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_25);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_25);
return x_1;
}
}
else
{
uint8_t x_27; 
x_27 = 0;
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_27);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_27);
return x_1;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_2, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_36 = l_Lean_RBNode_appendTrees___rarg(x_31, x_32);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; lean_object* x_38; 
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_37);
return x_1;
}
else
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_36, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 3);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
x_45 = 0;
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(1, 4, 1);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_29);
lean_ctor_set(x_46, 2, x_30);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_45);
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_34);
lean_ctor_set(x_47, 3, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_45);
lean_ctor_set(x_1, 3, x_47);
lean_ctor_set(x_1, 2, x_42);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_35);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_48);
lean_ctor_set(x_1, 3, x_49);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
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
x_59 = l_Lean_RBNode_appendTrees___rarg(x_53, x_54);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_60 = 0;
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(1, 4, 1);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_60);
x_62 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*4, x_60);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_59, sizeof(void*)*4);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 3);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
x_69 = 0;
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 4, 1);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_50);
lean_ctor_set(x_70, 1, x_51);
lean_ctor_set(x_70, 2, x_52);
lean_ctor_set(x_70, 3, x_64);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_69);
if (lean_is_scalar(x_58)) {
 x_71 = lean_alloc_ctor(1, 4, 1);
} else {
 x_71 = x_58;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_55);
lean_ctor_set(x_71, 2, x_56);
lean_ctor_set(x_71, 3, x_57);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_69);
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_65);
lean_ctor_set(x_72, 2, x_66);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_69);
return x_72;
}
else
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_73 = 0;
if (lean_is_scalar(x_58)) {
 x_74 = lean_alloc_ctor(1, 4, 1);
} else {
 x_74 = x_58;
}
lean_ctor_set(x_74, 0, x_59);
lean_ctor_set(x_74, 1, x_55);
lean_ctor_set(x_74, 2, x_56);
lean_ctor_set(x_74, 3, x_57);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_73);
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_51);
lean_ctor_set(x_75, 2, x_52);
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_73);
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 3);
lean_inc(x_79);
lean_dec(x_1);
lean_inc(x_2);
x_80 = l_Lean_RBNode_appendTrees___rarg(x_79, x_2);
x_81 = !lean_is_exclusive(x_2);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_2, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_2, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_2, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_2, 0);
lean_dec(x_85);
x_86 = 0;
lean_ctor_set(x_2, 3, x_80);
lean_ctor_set(x_2, 2, x_78);
lean_ctor_set(x_2, 1, x_77);
lean_ctor_set(x_2, 0, x_76);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_86);
return x_2;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_2);
x_87 = 0;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_77);
lean_ctor_set(x_88, 2, x_78);
lean_ctor_set(x_88, 3, x_80);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
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
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_2, 0);
x_92 = l_Lean_RBNode_appendTrees___rarg(x_1, x_91);
x_93 = 0;
lean_ctor_set(x_2, 0, x_92);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_93);
return x_2;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_2, 0);
x_95 = lean_ctor_get(x_2, 1);
x_96 = lean_ctor_get(x_2, 2);
x_97 = lean_ctor_get(x_2, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_2);
x_98 = l_Lean_RBNode_appendTrees___rarg(x_1, x_94);
x_99 = 0;
x_100 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_96);
lean_ctor_set(x_100, 3, x_97);
lean_ctor_set_uint8(x_100, sizeof(void*)*4, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_1);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_2);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_1, 0);
x_104 = lean_ctor_get(x_1, 1);
x_105 = lean_ctor_get(x_1, 2);
x_106 = lean_ctor_get(x_1, 3);
x_107 = lean_ctor_get(x_2, 0);
x_108 = l_Lean_RBNode_appendTrees___rarg(x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; lean_object* x_110; 
lean_free_object(x_1);
x_109 = 1;
lean_ctor_set(x_2, 0, x_108);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_109);
x_110 = l_Lean_RBNode_balLeft___rarg(x_103, x_104, x_105, x_2);
return x_110;
}
else
{
uint8_t x_111; 
x_111 = lean_ctor_get_uint8(x_108, sizeof(void*)*4);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
x_115 = lean_ctor_get(x_108, 2);
x_116 = lean_ctor_get(x_108, 3);
x_117 = 1;
lean_ctor_set(x_108, 3, x_113);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_117);
lean_ctor_set(x_2, 0, x_116);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_117);
x_118 = 0;
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_108);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_118);
return x_1;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_108, 0);
x_120 = lean_ctor_get(x_108, 1);
x_121 = lean_ctor_get(x_108, 2);
x_122 = lean_ctor_get(x_108, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_123 = 1;
x_124 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_124, 0, x_103);
lean_ctor_set(x_124, 1, x_104);
lean_ctor_set(x_124, 2, x_105);
lean_ctor_set(x_124, 3, x_119);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_123);
lean_ctor_set(x_2, 0, x_122);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_123);
x_125 = 0;
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_125);
return x_1;
}
}
else
{
uint8_t x_126; lean_object* x_127; 
lean_free_object(x_1);
x_126 = 1;
lean_ctor_set(x_2, 0, x_108);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_126);
x_127 = l_Lean_RBNode_balLeft___rarg(x_103, x_104, x_105, x_2);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_128 = lean_ctor_get(x_1, 0);
x_129 = lean_ctor_get(x_1, 1);
x_130 = lean_ctor_get(x_1, 2);
x_131 = lean_ctor_get(x_1, 3);
x_132 = lean_ctor_get(x_2, 0);
x_133 = lean_ctor_get(x_2, 1);
x_134 = lean_ctor_get(x_2, 2);
x_135 = lean_ctor_get(x_2, 3);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_2);
x_136 = l_Lean_RBNode_appendTrees___rarg(x_131, x_132);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_1);
x_137 = 1;
x_138 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_133);
lean_ctor_set(x_138, 2, x_134);
lean_ctor_set(x_138, 3, x_135);
lean_ctor_set_uint8(x_138, sizeof(void*)*4, x_137);
x_139 = l_Lean_RBNode_balLeft___rarg(x_128, x_129, x_130, x_138);
return x_139;
}
else
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_136, sizeof(void*)*4);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_136, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_136, 3);
lean_inc(x_144);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 x_145 = x_136;
} else {
 lean_dec_ref(x_136);
 x_145 = lean_box(0);
}
x_146 = 1;
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(1, 4, 1);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_129);
lean_ctor_set(x_147, 2, x_130);
lean_ctor_set(x_147, 3, x_141);
lean_ctor_set_uint8(x_147, sizeof(void*)*4, x_146);
x_148 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_133);
lean_ctor_set(x_148, 2, x_134);
lean_ctor_set(x_148, 3, x_135);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_146);
x_149 = 0;
lean_ctor_set(x_1, 3, x_148);
lean_ctor_set(x_1, 2, x_143);
lean_ctor_set(x_1, 1, x_142);
lean_ctor_set(x_1, 0, x_147);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_149);
return x_1;
}
else
{
uint8_t x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_1);
x_150 = 1;
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_136);
lean_ctor_set(x_151, 1, x_133);
lean_ctor_set(x_151, 2, x_134);
lean_ctor_set(x_151, 3, x_135);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
x_152 = l_Lean_RBNode_balLeft___rarg(x_128, x_129, x_130, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_153 = lean_ctor_get(x_1, 0);
x_154 = lean_ctor_get(x_1, 1);
x_155 = lean_ctor_get(x_1, 2);
x_156 = lean_ctor_get(x_1, 3);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_1);
x_157 = lean_ctor_get(x_2, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_2, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_2, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_2, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_161 = x_2;
} else {
 lean_dec_ref(x_2);
 x_161 = lean_box(0);
}
x_162 = l_Lean_RBNode_appendTrees___rarg(x_156, x_157);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; lean_object* x_164; lean_object* x_165; 
x_163 = 1;
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_163);
x_165 = l_Lean_RBNode_balLeft___rarg(x_153, x_154, x_155, x_164);
return x_165;
}
else
{
uint8_t x_166; 
x_166 = lean_ctor_get_uint8(x_162, sizeof(void*)*4);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 3);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
x_172 = 1;
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_153);
lean_ctor_set(x_173, 1, x_154);
lean_ctor_set(x_173, 2, x_155);
lean_ctor_set(x_173, 3, x_167);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
if (lean_is_scalar(x_161)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_161;
}
lean_ctor_set(x_174, 0, x_170);
lean_ctor_set(x_174, 1, x_158);
lean_ctor_set(x_174, 2, x_159);
lean_ctor_set(x_174, 3, x_160);
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_172);
x_175 = 0;
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_168);
lean_ctor_set(x_176, 2, x_169);
lean_ctor_set(x_176, 3, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_175);
return x_176;
}
else
{
uint8_t x_177; lean_object* x_178; lean_object* x_179; 
x_177 = 1;
if (lean_is_scalar(x_161)) {
 x_178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_178 = x_161;
}
lean_ctor_set(x_178, 0, x_162);
lean_ctor_set(x_178, 1, x_158);
lean_ctor_set(x_178, 2, x_159);
lean_ctor_set(x_178, 3, x_160);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
x_179 = l_Lean_RBNode_balLeft___rarg(x_153, x_154, x_155, x_178);
return x_179;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_appendTrees___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_2);
x_10 = lean_apply_2(x_1, x_2, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
uint8_t x_12; 
x_12 = l_Lean_RBNode_isBlack___rarg(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_RBNode_del___rarg(x_1, x_2, x_6);
x_14 = 0;
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_3);
x_15 = l_Lean_RBNode_del___rarg(x_1, x_2, x_6);
x_16 = l_Lean_RBNode_balLeft___rarg(x_15, x_7, x_8, x_9);
return x_16;
}
}
case 1:
{
lean_object* x_17; 
lean_free_object(x_3);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_RBNode_appendTrees___rarg(x_6, x_9);
return x_17;
}
default: 
{
uint8_t x_18; 
x_18 = l_Lean_RBNode_isBlack___rarg(x_9);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_RBNode_del___rarg(x_1, x_2, x_9);
x_20 = 0;
lean_ctor_set(x_3, 3, x_19);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_20);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_3);
x_21 = l_Lean_RBNode_del___rarg(x_1, x_2, x_9);
x_22 = l_Lean_RBNode_balRight___rarg(x_6, x_7, x_8, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_24);
lean_inc(x_2);
x_27 = lean_apply_2(x_1, x_2, x_24);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
switch (x_28) {
case 0:
{
uint8_t x_29; 
x_29 = l_Lean_RBNode_isBlack___rarg(x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Lean_RBNode_del___rarg(x_1, x_2, x_23);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_RBNode_del___rarg(x_1, x_2, x_23);
x_34 = l_Lean_RBNode_balLeft___rarg(x_33, x_24, x_25, x_26);
return x_34;
}
}
case 1:
{
lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_RBNode_appendTrees___rarg(x_23, x_26);
return x_35;
}
default: 
{
uint8_t x_36; 
x_36 = l_Lean_RBNode_isBlack___rarg(x_26);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = l_Lean_RBNode_del___rarg(x_1, x_2, x_26);
x_38 = 0;
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_RBNode_del___rarg(x_1, x_2, x_26);
x_41 = l_Lean_RBNode_balRight___rarg(x_23, x_24, x_25, x_40);
return x_41;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_del___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_RBNode_del___rarg(x_1, x_2, x_3);
x_5 = l_Lean_RBNode_setBlack___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_erase___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_findCore___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_dec(x_9);
lean_dec(x_8);
x_2 = lean_box(0);
x_3 = x_6;
goto _start;
}
case 1:
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
default: 
{
lean_dec(x_8);
lean_dec(x_6);
x_2 = lean_box(0);
x_3 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_find___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_lowerBound___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_mapM___rarg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_box(x_7);
lean_inc(x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_9);
x_16 = lean_apply_2(x_13, lean_box(0), x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_8);
lean_inc(x_12);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_16, x_17);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___rarg___lambda__3___boxed), 4, 3);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_10);
lean_inc(x_12);
x_20 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_11);
x_22 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_RBNode_mapM___rarg___lambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_mapM___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_mapM___rarg___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___rarg(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_RBNode_map___rarg(x_1, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_10 = lean_apply_2(x_1, x_6, x_7);
x_11 = l_Lean_RBNode_map___rarg(x_1, x_8);
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
x_17 = l_Lean_RBNode_map___rarg(x_1, x_13);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_2(x_1, x_14, x_15);
x_19 = l_Lean_RBNode_map___rarg(x_1, x_16);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBNode_map___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg(x_1, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_toArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_toArray___rarg___closed__1;
x_3 = l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_toArray___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_RBNode_toArray___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_toArray___rarg(x_1);
lean_dec(x_1);
return x_2;
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_depth___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_depth___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_depth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_RBNode_isSingleton___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_isSingleton___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_isSingleton___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_isSingleton(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBMap_fold___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_fold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_revFold___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBMap_revFold___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_revFold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_RBMap_foldM___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_foldM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBMap_forM___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_foldM___at_Lean_RBMap_forM___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_forM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
lean_inc(x_4);
x_13 = lean_apply_2(x_4, x_12, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_5);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg(x_1, x_2, x_9, x_4);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg___lambda__2), 7, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_10);
lean_closure_set(x_15, 2, x_11);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_12);
lean_closure_set(x_15, 5, x_13);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_RBMap_forIn___spec__1___rarg(x_1, x_4, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_forIn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
lean_inc(x_4);
x_13 = lean_apply_2(x_4, x_12, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_5);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg(x_1, x_2, x_9, x_4);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg___lambda__2), 7, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_10);
lean_closure_set(x_15, 2, x_11);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_12);
lean_closure_set(x_15, 5, x_13);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_RBMap_instForInProd___spec__1___rarg(x_1, x_4, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProd___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProd___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_instForInProd(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_isEmpty___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_isEmpty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_RBMap_toList___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBMap_toList___rarg___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_RBMap_toList___rarg___closed__1;
x_4 = l_Lean_RBNode_revFold___rarg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_toList___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_toList(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_RBMap_toArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_RBMap_toArray___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_RBMap_toArray___rarg___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_RBMap_toArray___rarg___closed__2;
x_3 = l_Lean_RBMap_toArray___rarg___closed__1;
x_4 = l_Lean_RBNode_fold___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_toArray___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_toArray(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_min___rarg(x_1);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_min___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_min(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_max___rarg(x_1);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_max___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_max(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_apply_2(x_1, x_6, x_8);
x_10 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
x_11 = lean_apply_2(x_2, x_7, x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = l_List_reverse___rarg(x_12);
x_14 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3;
x_15 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_13, x_14);
x_16 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = 0;
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_apply_2(x_1, x_24, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_apply_2(x_2, x_25, x_26);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_reverse___rarg(x_31);
x_33 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3;
x_34 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_32, x_33);
x_35 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6;
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = 0;
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_repr___at_Lean_RBMap_instRepr___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_repr___at_Lean_RBMap_instRepr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_repr___at_Lean_RBMap_instRepr___spec__2___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_instRepr___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_4);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(x_1, x_2, x_7, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_4 = x_11;
x_5 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
lean_inc(x_3);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(x_1, x_2, x_13, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_4 = x_18;
x_5 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_instRepr___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_RBMap_instRepr___spec__5___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_RBMap_instRepr___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(x_1, x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(x_1, x_2, x_10, x_11);
x_13 = l_List_foldl___at_Lean_RBMap_instRepr___spec__5___rarg(x_1, x_2, x_4, x_12, x_6);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_RBMap_instRepr___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at_Lean_RBMap_instRepr___spec__4___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3;
lean_inc(x_3);
x_7 = l_Std_Format_joinSep___at_Lean_RBMap_instRepr___spec__4___rarg(x_1, x_2, x_3, x_6);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6;
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_11);
x_12 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = 0;
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_3);
x_18 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
x_20 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = 0;
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_RBMap_instRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.rbmapOf ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_instRepr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBMap_instRepr___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_RBMap_toList___rarg(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg(x_1, x_2, x_5, x_6);
x_8 = l_Lean_RBMap_instRepr___rarg___closed__2;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Repr_addAppParen(x_9, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_instRepr___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_instRepr(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_insert___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_erase___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_Lean_RBMap_ofList___rarg(x_1, x_5);
x_9 = l_Lean_RBNode_insert___rarg(x_1, x_8, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_ofList___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_findCore_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_find_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_2, x_3);
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
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_findD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_findD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_lowerBound___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_lowerBound___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_contains___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBMap_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_fromList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_Lean_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_RBMap_fromList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_RBMap_fromList___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at_Lean_RBMap_fromList___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
lean_inc(x_1);
x_12 = l_Lean_RBNode_insert___rarg(x_1, x_5, x_8, x_9);
x_3 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg(x_2, x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_RBMap_fromArray___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_fromArray___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_RBNode_all___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_all___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBMap_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_all(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_RBNode_any___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_any___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBMap_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_any(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_size___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_RBMap_size___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_RBMap_maxDepth___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_max___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_maxDepth___rarg___closed__1;
x_3 = l_Lean_RBNode_depth___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_maxDepth___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_maxDepth___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_maxDepth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_min_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_panic_fn(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_min_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panic___at_Lean_RBMap_min_x21___spec__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.RBMap", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.RBMap.min!", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("map is empty", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_min_x21___rarg___closed__1;
x_2 = l_Lean_RBMap_min_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(378u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_RBMap_min_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_min___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_RBMap_min_x21___rarg___closed__4;
x_6 = l_panic___at_Lean_RBMap_min_x21___spec__1___rarg(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_min_x21___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_min_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_min_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_max_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_panic_fn(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_RBMap_max_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_panic___at_Lean_RBMap_max_x21___spec__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.RBMap.max!", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_min_x21___rarg___closed__1;
x_2 = l_Lean_RBMap_max_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(383u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_RBMap_min_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_max___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_RBMap_max_x21___rarg___closed__2;
x_6 = l_panic___at_Lean_RBMap_max_x21___spec__1___rarg(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_RBMap_max_x21___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_max_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_max_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.RBMap.find!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not in the map", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_RBMap_min_x21___rarg___closed__1;
x_2 = l_Lean_RBMap_find_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(389u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_RBMap_find_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBMap_find_x21___rarg___closed__3;
x_7 = l_panic___rarg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_find_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_1, x_2, x_3, x_5);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_RBNode_insert___rarg(x_1, x_9, x_6, x_7);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_2);
lean_inc(x_6);
x_14 = lean_apply_3(x_2, x_6, x_13, x_7);
lean_inc(x_1);
x_15 = l_Lean_RBNode_insert___rarg(x_1, x_9, x_6, x_14);
x_3 = x_15;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_mergeBy___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6, x_8);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_1);
x_13 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_5, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_6 = x_12;
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_9);
x_16 = lean_apply_3(x_4, x_9, x_10, x_15);
lean_inc(x_1);
x_17 = l_Lean_RBNode_insert___rarg(x_1, x_12, x_9, x_16);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_6 = x_17;
x_7 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_RBNode_fold___at_Lean_RBMap_intersectBy___spec__1___rarg(x_1, lean_box(0), lean_box(0), x_4, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_intersectBy___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1___rarg(x_1, x_2, x_3, x_5);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_apply_2(x_2, x_6, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
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
lean_inc(x_1);
x_13 = l_Lean_RBNode_insert___rarg(x_1, x_9, x_6, x_7);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_fold___at_Lean_RBMap_filter___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_filter___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
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
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1___rarg(x_1, lean_box(0), x_3, x_4, x_6);
lean_inc(x_3);
lean_inc(x_7);
x_11 = lean_apply_2(x_3, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_7);
x_2 = lean_box(0);
x_4 = x_10;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = l_Lean_RBNode_insert___rarg(x_1, x_10, x_7, x_13);
x_2 = lean_box(0);
x_4 = x_14;
x_5 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_fold___at_Lean_RBMap_filterMap___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_RBMap_filterMap___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_rbmapOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_Lean_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_rbmapOf___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_rbmapOf___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at_Lean_rbmapOf___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_rbmapOf___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_RBColor_noConfusion___rarg___closed__1 = _init_l_Lean_RBColor_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_RBColor_noConfusion___rarg___closed__1);
l_Lean_RBNode_toArray___rarg___closed__1 = _init_l_Lean_RBNode_toArray___rarg___closed__1();
lean_mark_persistent(l_Lean_RBNode_toArray___rarg___closed__1);
l_Lean_RBMap_toList___rarg___closed__1 = _init_l_Lean_RBMap_toList___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_toList___rarg___closed__1);
l_Lean_RBMap_toArray___rarg___closed__1 = _init_l_Lean_RBMap_toArray___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_toArray___rarg___closed__1);
l_Lean_RBMap_toArray___rarg___closed__2 = _init_l_Lean_RBMap_toArray___rarg___closed__2();
lean_mark_persistent(l_Lean_RBMap_toArray___rarg___closed__2);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__1 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__1();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__1);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__2 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__2();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__2);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__3);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__4);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__5 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__5();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__5);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__6);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__7);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__8 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__8();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__8);
l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9 = _init_l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9();
lean_mark_persistent(l_Prod_repr___at_Lean_RBMap_instRepr___spec__3___rarg___closed__9);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__1 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__1();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__1);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__2 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__2();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__2);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__3);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__4 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__4();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__4);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__5);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__6);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__7 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__7();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__7);
l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8 = _init_l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8();
lean_mark_persistent(l_List_repr___at_Lean_RBMap_instRepr___spec__1___rarg___closed__8);
l_Lean_RBMap_instRepr___rarg___closed__1 = _init_l_Lean_RBMap_instRepr___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_instRepr___rarg___closed__1);
l_Lean_RBMap_instRepr___rarg___closed__2 = _init_l_Lean_RBMap_instRepr___rarg___closed__2();
lean_mark_persistent(l_Lean_RBMap_instRepr___rarg___closed__2);
l_Lean_RBMap_maxDepth___rarg___closed__1 = _init_l_Lean_RBMap_maxDepth___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_maxDepth___rarg___closed__1);
l_Lean_RBMap_min_x21___rarg___closed__1 = _init_l_Lean_RBMap_min_x21___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_min_x21___rarg___closed__1);
l_Lean_RBMap_min_x21___rarg___closed__2 = _init_l_Lean_RBMap_min_x21___rarg___closed__2();
lean_mark_persistent(l_Lean_RBMap_min_x21___rarg___closed__2);
l_Lean_RBMap_min_x21___rarg___closed__3 = _init_l_Lean_RBMap_min_x21___rarg___closed__3();
lean_mark_persistent(l_Lean_RBMap_min_x21___rarg___closed__3);
l_Lean_RBMap_min_x21___rarg___closed__4 = _init_l_Lean_RBMap_min_x21___rarg___closed__4();
lean_mark_persistent(l_Lean_RBMap_min_x21___rarg___closed__4);
l_Lean_RBMap_max_x21___rarg___closed__1 = _init_l_Lean_RBMap_max_x21___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_max_x21___rarg___closed__1);
l_Lean_RBMap_max_x21___rarg___closed__2 = _init_l_Lean_RBMap_max_x21___rarg___closed__2();
lean_mark_persistent(l_Lean_RBMap_max_x21___rarg___closed__2);
l_Lean_RBMap_find_x21___rarg___closed__1 = _init_l_Lean_RBMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_Lean_RBMap_find_x21___rarg___closed__1);
l_Lean_RBMap_find_x21___rarg___closed__2 = _init_l_Lean_RBMap_find_x21___rarg___closed__2();
lean_mark_persistent(l_Lean_RBMap_find_x21___rarg___closed__2);
l_Lean_RBMap_find_x21___rarg___closed__3 = _init_l_Lean_RBMap_find_x21___rarg___closed__3();
lean_mark_persistent(l_Lean_RBMap_find_x21___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
