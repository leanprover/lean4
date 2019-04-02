// Lean compiler output
// Module: init.data.rbmap.basic
// Imports: init.data.ordering.basic init.coe init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_RBNode_depth___rarg(obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_contains___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_min___boxed(obj*, obj*);
obj* l_RBNode_max___main___boxed(obj*, obj*);
obj* l_RBNode_balance1(obj*, obj*);
obj* l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1(obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_RBNode_find(obj*, obj*);
obj* l_RBNode_depth___main___rarg___boxed(obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___boxed(obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__5___rarg(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_insert___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_contains(obj*, obj*, obj*);
obj* l_RBNode_findCore(obj*, obj*, obj*);
obj* l_RBMap_find___main___at_RBMap_contains___spec__1(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_contains___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBMap_fromList___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound(obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(obj*, obj*);
obj* l_RBNode_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_find___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___boxed(obj*, obj*, obj*);
obj* l_RBMap_any___main(obj*, obj*, obj*);
obj* l_RBMap_contains___boxed(obj*, obj*, obj*);
obj* l_RBMap_any___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_setBlack(obj*, obj*);
obj* l_RBNode_isRed___boxed(obj*, obj*);
obj* l_RBNode_ins___main(obj*, obj*, obj*);
obj* l_RBNode_balance2___main___boxed(obj*, obj*);
obj* l_RBMap_ofList(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_rbmapOf___spec__5___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at_rbmapOf___spec__3___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_toList___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_min(obj*, obj*, obj*);
obj* l_RBMap_toList___rarg(obj*);
obj* l_RBMap_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_isRed___rarg___boxed(obj*);
obj* l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBNode_all___rarg(obj*, obj*);
obj* l_RBNode_balance2(obj*, obj*);
obj* l_RBMap_findCore___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_ofList___main___spec__2(obj*, obj*, obj*);
obj* l_RBMap_all___main(obj*, obj*, obj*);
obj* l_RBMap_min___main___rarg(obj*);
obj* l_RBMap_min___rarg(obj*);
obj* l_RBMap_fromList___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___rarg(obj*, obj*, obj*);
uint8 l_RBNode_any___main___rarg(obj*, obj*);
obj* l_RBMap_findCore(obj*, obj*, obj*);
obj* l_RBNode_isRed___main___rarg___boxed(obj*);
obj* l_RBNode_lowerBound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmapOf___rarg(obj*, obj*, obj*);
obj* l_RBNode_any___main(obj*, obj*);
obj* l_RBNode_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_revFold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_findCore___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__3(obj*, obj*, obj*);
obj* l_rbmapOf(obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_toList___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBMap_mfold(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___boxed(obj*, obj*, obj*);
obj* l_RBMap_mfor(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main(obj*, obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBMap_lowerBound___main(obj*, obj*, obj*);
obj* l_RBMap_mfold___main(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_all___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_any(obj*, obj*);
obj* l_RBMap_depth(obj*, obj*, obj*);
obj* l_RBNode_max(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_isRed(obj*, obj*);
obj* l_RBMap_toList___main(obj*, obj*, obj*);
uint8 l_RBMap_any___main___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBNode_insert___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___rarg(obj*);
obj* l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBMap_findCore___main___rarg(obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(obj*, obj*, uint8, obj*);
obj* l_RBMap_fold___main(obj*, obj*, obj*, obj*);
obj* l_RBMap_fold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_depth___boxed(obj*, obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_fromList___spec__2___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___boxed(obj*, obj*);
obj* l_RBMap_lowerBound(obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main___boxed(obj*, obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__6(obj*, obj*, obj*);
obj* l_RBMap_isEmpty(obj*, obj*, obj*);
obj* l_RBNode_setBlack___boxed(obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_RBNode_insert___spec__2___boxed(obj*, obj*, obj*);
obj* l_RBMap_mfor___rarg(obj*, obj*, obj*);
obj* l_mkRBMap___boxed(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_insert___main___spec__1(obj*, obj*, obj*);
obj* l_RBMap_toList___main___rarg(obj*);
obj* l_RBMap_ofList___main___rarg(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1(obj*, obj*, obj*);
obj* l_RBNode_balance2___main(obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_contains___spec__2(obj*, obj*);
obj* l_RBNode_all___main___rarg___boxed(obj*, obj*);
obj* l_RBMap_revFold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBMap_ofList___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__3(obj*, obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__3;
obj* l_RBNode_singleton(obj*, obj*);
obj* l_RBMap_ofList___rarg(obj*, obj*);
obj* l_RBNode_find___main___boxed(obj*, obj*);
obj* l_RBMap_fold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_rbmapOf___spec__5(obj*, obj*, obj*);
obj* l_RBNode_findCore___boxed(obj*, obj*, obj*);
obj* l_RBMap_find___main___at_RBMap_contains___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_balance2___rarg(obj*, obj*);
obj* l_RBNode_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_lowerBound___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___boxed(obj*, obj*);
obj* l_RBNode_insert___at_RBMap_fromList___spec__2___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBMap_revFold___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___rarg(obj*, obj*, obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_findCore___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert(obj*, obj*, obj*);
uint8 l_RBNode_isRed___rarg(obj*);
obj* l_RBMap_HasRepr(obj*, obj*, obj*);
obj* l_RBMap_min___boxed(obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l_RBMap_fromList___at_rbmapOf___spec__1(obj*, obj*, obj*);
obj* l_RBMap_fold___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_ofList___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__5(obj*, obj*, obj*);
obj* l_RBMap_ofList___boxed(obj*, obj*, obj*);
obj* l_RBMap_min___main(obj*, obj*, obj*);
obj* l_RBMap_mfor___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_ofList___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_HasRepr___rarg___closed__1;
obj* l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_max(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_all___boxed(obj*, obj*);
obj* l_RBNode_find___main(obj*, obj*);
obj* l_RBMap_insert___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_max___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_RBMap_HasEmptyc___boxed(obj*, obj*, obj*);
obj* l_RBNode_isRed___main___boxed(obj*, obj*);
obj* l_RBMap_HasRepr___rarg(obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___boxed(obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_RBMap_find(obj*, obj*, obj*);
obj* l_RBMap_max___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_isRed___main(obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBMap_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_rbmapOf___spec__4___boxed(obj*, obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__6___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__3___boxed(obj*, obj*, obj*);
obj* l_RBMap_depth___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__4(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__2___boxed(obj*, obj*, obj*);
uint8 l_RBNode_all___main___rarg(obj*, obj*);
uint8 l_RBNode_any___rarg(obj*, obj*);
obj* l_RBMap_toList(obj*, obj*, obj*);
obj* l_RBMap_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___boxed(obj*, obj*);
obj* l_RBNode_insert___at_RBMap_fromList___spec__2(obj*, obj*, obj*);
obj* l_RBNode_all(obj*, obj*);
obj* l_RBNode_mfold___main(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_insert___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBMap_findCore___main(obj*, obj*, obj*);
obj* l_RBMap_any___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_any___main___rarg___boxed(obj*, obj*);
obj* l_RBMap_max___main(obj*, obj*, obj*);
obj* l_RBNode_all___main(obj*, obj*);
obj* l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBMap_isEmpty___main___rarg(obj*);
obj* l_RBNode_max___rarg(obj*);
obj* l_RBMap_all___main___boxed(obj*, obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1(obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1(obj*, obj*);
obj* l_RBNode_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_balance2___boxed(obj*, obj*);
obj* l_RBNode_all___rarg___boxed(obj*, obj*);
obj* l_rbmapOf___boxed(obj*, obj*);
obj* l_RBNode_depth___main(obj*, obj*);
obj* l_RBNode_mfold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main(obj*, obj*, obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main(obj*, obj*, obj*);
obj* l_RBMap_lowerBound___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBNode_insert___spec__2(obj*, obj*, obj*);
obj* l_RBNode_min(obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__5___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___main(obj*, obj*);
obj* l_RBMap_mfold___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_any___main___boxed(obj*, obj*);
obj* l_RBMap_fold(obj*, obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_balance1___main(obj*, obj*);
obj* l_RBNode_any___boxed(obj*, obj*);
obj* l_RBNode_setBlack___main(obj*, obj*);
obj* l_RBMap_find___boxed(obj*, obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__1;
obj* l_RBMap_any___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_fromList___boxed(obj*, obj*);
uint8 l_RBMap_all___rarg(obj*, obj*);
obj* l_RBMap_any___rarg___boxed(obj*, obj*);
obj* l_RBMap_find___main___boxed(obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(obj*, obj*);
obj* l_RBMap_insert(obj*, obj*, obj*);
obj* l_RBMap_revFold(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBMap_fromList___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_revFold___main(obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1(obj*, obj*);
obj* l_RBMap_lowerBound___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___boxed(obj*, obj*, obj*);
uint8 l_RBMap_all___main___rarg(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_balance1___boxed(obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_contains___spec__2___boxed(obj*, obj*);
obj* l_RBNode_depth___main___boxed(obj*, obj*);
obj* l_RBMap_insert___main___at_rbmapOf___spec__2___boxed(obj*, obj*, obj*);
obj* l_RBMap_revFold___main(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1___boxed(obj*, obj*);
obj* l_RBMap_all___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_fromList(obj*, obj*);
obj* l_RBNode_any___rarg___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_RBNode_insert___spec__1(obj*, obj*, obj*);
obj* l_RBNode_max___main(obj*, obj*);
obj* l_RBNode_setBlack___rarg(obj*);
obj* l_RBMap_lowerBound___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___boxed(obj*, obj*, obj*);
obj* l_RBMap_HasEmptyc(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBMap_ofList___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___main___boxed(obj*, obj*);
obj* l_RBMap_insert___main___at_rbmapOf___spec__2(obj*, obj*, obj*);
obj* l_RBNode_depth___boxed(obj*, obj*);
obj* l_RBMap_find___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_balance1___main___rarg(obj*, obj*);
obj* l_RBMap_isEmpty___rarg___boxed(obj*);
obj* l_rbmapOf___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_revFold___main___rarg(obj*, obj*, obj*);
obj* l_mkRBMap(obj*, obj*, obj*);
obj* l_RBNode_balance1___main___boxed(obj*, obj*);
obj* l_RBMap_fromList___at_rbmapOf___spec__1___rarg(obj*, obj*);
obj* l_RBMap_all(obj*, obj*, obj*, obj*);
obj* l_RBMap_ofList___main(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_rbmapOf___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_rbmapOf___spec__4(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBMap_ofList___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_RBNode_lowerBound___boxed(obj*, obj*, obj*);
obj* l_RBMap_fromList___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_all___rarg___boxed(obj*, obj*);
obj* l_RBNode_fold___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBMap_fromList___spec__1(obj*, obj*, obj*);
obj* l_RBNode_fold(obj*, obj*, obj*);
obj* l_RBNode_depth(obj*, obj*);
obj* l_RBMap_min___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_all___main___boxed(obj*, obj*);
obj* l_RBNode_mfold(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_rbmapOf___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__4(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main___rarg___boxed(obj*);
obj* l_RBNode_balance1___rarg(obj*, obj*);
obj* l_RBMap_find___main(obj*, obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__2;
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBMap_any___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__4___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBMap_ofList___main___spec__1(obj*, obj*, obj*);
obj* l_RBMap_any(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_RBMap_contains___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_RBMap_HasRepr___boxed(obj*, obj*, obj*);
obj* l_RBNode_findCore___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___at_rbmapOf___spec__3(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__2(obj*, obj*, obj*);
obj* l_RBMap_max___rarg(obj*);
obj* l_RBMap_max___main___rarg(obj*);
uint8 l_RBMap_isEmpty___rarg(obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(obj*, obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__6___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__3(obj*, obj*, obj*);
obj* l_RBMap_fromList___at_rbmapOf___spec__1___boxed(obj*, obj*, obj*);
uint8 l_RBMap_contains___rarg(obj*, obj*, obj*);
obj* l_RBNode_revFold___boxed(obj*, obj*, obj*);
obj* l_RBMap_mfold___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_RBMap_max___boxed(obj*, obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::mk_nat_obj(0ul);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_0);
x_7 = l_RBNode_depth___main___rarg(x_0, x_4);
lean::inc(x_0);
x_9 = l_RBNode_depth___main___rarg(x_0, x_5);
x_10 = lean::apply_2(x_0, x_7, x_9);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_10, x_11);
lean::dec(x_10);
return x_12;
}
}
}
obj* l_RBNode_depth___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_depth___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_depth___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_depth___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_depth___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_depth___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_min___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_RBNode_min___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_min___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_min___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_min___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_min___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_min___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_max___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 3);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_RBNode_max___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_max___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_max___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_max___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_max___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_max___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_RBNode_fold___main___rarg(x_0, x_4, x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_6, x_8, x_14);
x_1 = x_10;
x_2 = x_16;
goto _start;
}
}
}
obj* l_RBNode_fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_fold___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_mfold___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_8 = lean::apply_3(x_0, x_1, x_2, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg), 4, 3);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_0);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_RBNode_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_25; obj* x_27; obj* x_28; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_2, 3);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_mfold___main___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_21);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg___lambda__1), 7, 6);
lean::closure_set(x_27, 0, x_1);
lean::closure_set(x_27, 1, x_14);
lean::closure_set(x_27, 2, x_16);
lean::closure_set(x_27, 3, x_0);
lean::closure_set(x_27, 4, x_18);
lean::closure_set(x_27, 5, x_21);
x_28 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* l_RBNode_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg), 4, 0);
return x_4;
}
}
obj* l_RBNode_mfold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___rarg), 4, 0);
return x_4;
}
}
obj* l_RBNode_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_revFold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_RBNode_revFold___main___rarg(x_0, x_10, x_2);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_6, x_8, x_14);
x_1 = x_4;
x_2 = x_16;
goto _start;
}
}
}
obj* l_RBNode_revFold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_revFold___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_revFold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_revFold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_revFold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_0);
x_3 = 1;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; uint8 x_15; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_8);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_19; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_4);
x_19 = 0;
return x_19;
}
else
{
uint8 x_21; 
lean::inc(x_0);
x_21 = l_RBNode_all___main___rarg(x_0, x_4);
if (x_21 == 0)
{
uint8 x_24; 
lean::dec(x_10);
lean::dec(x_0);
x_24 = 0;
return x_24;
}
else
{
x_1 = x_10;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_all___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_all___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_all___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_all___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_all___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_all___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_all___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_0);
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; uint8 x_15; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_8);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_17; 
lean::inc(x_0);
x_17 = l_RBNode_any___main___rarg(x_0, x_4);
if (x_17 == 0)
{
x_1 = x_10;
goto _start;
}
else
{
uint8 x_21; 
lean::dec(x_10);
lean::dec(x_0);
x_21 = 1;
return x_21;
}
}
else
{
uint8 x_25; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_4);
x_25 = 1;
return x_25;
}
}
}
}
obj* l_RBNode_any___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_any___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_any___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_any___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_any___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_any___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_any___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_any___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_any___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_any(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_singleton___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_1);
lean::cnstr_set(x_4, 3, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
}
obj* l_RBNode_singleton(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_singleton___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_singleton___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_singleton(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance1___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 1);
x_10 = lean::cnstr_get(x_0, 2);
x_12 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_14 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_1, 1);
x_17 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_19 = x_1;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_1);
 x_19 = lean::box(0);
}
x_20 = 0;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_6);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_20);
x_22 = x_21;
x_23 = 1;
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_8);
lean::cnstr_set(x_24, 2, x_10);
lean::cnstr_set(x_24, 3, x_12);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_23);
x_25 = x_24;
return x_25;
}
else
{
uint8 x_26; 
x_26 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*4);
if (x_26 == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_27 = lean::cnstr_get(x_0, 1);
x_29 = lean::cnstr_get(x_0, 2);
x_31 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_33 = x_0;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_0);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_1, 1);
x_36 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_38 = x_1;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_1);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_6, 0);
x_41 = lean::cnstr_get(x_6, 1);
x_43 = lean::cnstr_get(x_6, 2);
x_45 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_47 = x_6;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_6);
 x_47 = lean::box(0);
}
x_48 = 1;
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_34);
lean::cnstr_set(x_49, 2, x_36);
lean::cnstr_set(x_49, 3, x_39);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_48);
x_50 = x_49;
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_45);
lean::cnstr_set(x_51, 1, x_27);
lean::cnstr_set(x_51, 2, x_29);
lean::cnstr_set(x_51, 3, x_31);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_48);
x_52 = x_51;
if (lean::is_scalar(x_33)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_33;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_41);
lean::cnstr_set(x_53, 2, x_43);
lean::cnstr_set(x_53, 3, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_26);
x_54 = x_53;
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_55 = lean::cnstr_get(x_0, 1);
x_57 = lean::cnstr_get(x_0, 2);
x_59 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_61 = x_0;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_0);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_66 = x_1;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_1);
 x_66 = lean::box(0);
}
x_67 = 0;
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_4);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_64);
lean::cnstr_set(x_68, 3, x_6);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_67);
x_69 = x_68;
if (lean::is_scalar(x_61)) {
 x_70 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_70 = x_61;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_55);
lean::cnstr_set(x_70, 2, x_57);
lean::cnstr_set(x_70, 3, x_59);
lean::cnstr_set_scalar(x_70, sizeof(void*)*4, x_26);
x_71 = x_70;
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*4);
if (x_72 == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_73 = lean::cnstr_get(x_0, 1);
x_75 = lean::cnstr_get(x_0, 2);
x_77 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_79 = x_0;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_0);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_1, 1);
x_82 = lean::cnstr_get(x_1, 2);
x_84 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_86 = x_1;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_1);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_4, 0);
x_89 = lean::cnstr_get(x_4, 1);
x_91 = lean::cnstr_get(x_4, 2);
x_93 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 x_95 = x_4;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_4);
 x_95 = lean::box(0);
}
x_96 = 1;
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_87);
lean::cnstr_set(x_97, 1, x_89);
lean::cnstr_set(x_97, 2, x_91);
lean::cnstr_set(x_97, 3, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_96);
x_98 = x_97;
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_99 = x_86;
}
lean::cnstr_set(x_99, 0, x_84);
lean::cnstr_set(x_99, 1, x_73);
lean::cnstr_set(x_99, 2, x_75);
lean::cnstr_set(x_99, 3, x_77);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_96);
x_100 = x_99;
if (lean::is_scalar(x_79)) {
 x_101 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_101 = x_79;
}
lean::cnstr_set(x_101, 0, x_98);
lean::cnstr_set(x_101, 1, x_80);
lean::cnstr_set(x_101, 2, x_82);
lean::cnstr_set(x_101, 3, x_100);
lean::cnstr_set_scalar(x_101, sizeof(void*)*4, x_72);
x_102 = x_101;
return x_102;
}
else
{
obj* x_103; 
x_103 = lean::cnstr_get(x_1, 3);
lean::inc(x_103);
if (lean::obj_tag(x_103) == 0)
{
obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_114; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_105 = lean::cnstr_get(x_0, 1);
x_107 = lean::cnstr_get(x_0, 2);
x_109 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_111 = x_0;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::inc(x_109);
 lean::dec(x_0);
 x_111 = lean::box(0);
}
x_112 = lean::cnstr_get(x_1, 1);
x_114 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_116 = x_1;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_1);
 x_116 = lean::box(0);
}
x_117 = 0;
if (lean::is_scalar(x_116)) {
 x_118 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_118 = x_116;
}
lean::cnstr_set(x_118, 0, x_4);
lean::cnstr_set(x_118, 1, x_112);
lean::cnstr_set(x_118, 2, x_114);
lean::cnstr_set(x_118, 3, x_103);
lean::cnstr_set_scalar(x_118, sizeof(void*)*4, x_117);
x_119 = x_118;
if (lean::is_scalar(x_111)) {
 x_120 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_120 = x_111;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_105);
lean::cnstr_set(x_120, 2, x_107);
lean::cnstr_set(x_120, 3, x_109);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_72);
x_121 = x_120;
return x_121;
}
else
{
uint8 x_122; 
x_122 = lean::cnstr_get_scalar<uint8>(x_103, sizeof(void*)*4);
if (x_122 == 0)
{
obj* x_123; obj* x_125; obj* x_127; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_123 = lean::cnstr_get(x_0, 1);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_0, 2);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_0, 3);
lean::inc(x_127);
lean::dec(x_0);
x_130 = lean::cnstr_get(x_1, 1);
x_132 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_134 = x_1;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::dec(x_1);
 x_134 = lean::box(0);
}
x_135 = lean::cnstr_get(x_103, 0);
x_137 = lean::cnstr_get(x_103, 1);
x_139 = lean::cnstr_get(x_103, 2);
x_141 = lean::cnstr_get(x_103, 3);
if (lean::is_exclusive(x_103)) {
 x_143 = x_103;
} else {
 lean::inc(x_135);
 lean::inc(x_137);
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_103);
 x_143 = lean::box(0);
}
lean::inc(x_4);
if (lean::is_scalar(x_143)) {
 x_145 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_145 = x_143;
}
lean::cnstr_set(x_145, 0, x_4);
lean::cnstr_set(x_145, 1, x_130);
lean::cnstr_set(x_145, 2, x_132);
lean::cnstr_set(x_145, 3, x_135);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_146 = x_4;
} else {
 lean::dec(x_4);
 x_146 = lean::box(0);
}
lean::cnstr_set_scalar(x_145, sizeof(void*)*4, x_72);
x_147 = x_145;
if (lean::is_scalar(x_146)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_146;
}
lean::cnstr_set(x_148, 0, x_141);
lean::cnstr_set(x_148, 1, x_123);
lean::cnstr_set(x_148, 2, x_125);
lean::cnstr_set(x_148, 3, x_127);
lean::cnstr_set_scalar(x_148, sizeof(void*)*4, x_72);
x_149 = x_148;
if (lean::is_scalar(x_134)) {
 x_150 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_150 = x_134;
}
lean::cnstr_set(x_150, 0, x_147);
lean::cnstr_set(x_150, 1, x_137);
lean::cnstr_set(x_150, 2, x_139);
lean::cnstr_set(x_150, 3, x_149);
lean::cnstr_set_scalar(x_150, sizeof(void*)*4, x_122);
x_151 = x_150;
return x_151;
}
else
{
obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_152 = lean::cnstr_get(x_0, 1);
x_154 = lean::cnstr_get(x_0, 2);
x_156 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_158 = x_0;
} else {
 lean::inc(x_152);
 lean::inc(x_154);
 lean::inc(x_156);
 lean::dec(x_0);
 x_158 = lean::box(0);
}
x_159 = lean::cnstr_get(x_1, 1);
x_161 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_163 = x_1;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_1);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_4, 0);
x_166 = lean::cnstr_get(x_4, 1);
x_168 = lean::cnstr_get(x_4, 2);
x_170 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 x_172 = x_4;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_4);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_122);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_103);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_158)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_158;
}
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_152);
lean::cnstr_set(x_178, 2, x_154);
lean::cnstr_set(x_178, 3, x_156);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_122);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
obj* l_RBNode_balance1___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance1___main___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_balance1___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance1___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance1___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_balance1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance1___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_balance1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance2___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
x_12 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_14 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_1, 1);
x_17 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_19 = x_1;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_1);
 x_19 = lean::box(0);
}
x_20 = 0;
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_6);
lean::cnstr_set_scalar(x_21, sizeof(void*)*4, x_20);
x_22 = x_21;
x_23 = 1;
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_10);
lean::cnstr_set(x_24, 2, x_12);
lean::cnstr_set(x_24, 3, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*4, x_23);
x_25 = x_24;
return x_25;
}
else
{
uint8 x_26; 
x_26 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*4);
if (x_26 == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_27 = lean::cnstr_get(x_0, 0);
x_29 = lean::cnstr_get(x_0, 1);
x_31 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_33 = x_0;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_0);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_1, 1);
x_36 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_38 = x_1;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_1);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_6, 0);
x_41 = lean::cnstr_get(x_6, 1);
x_43 = lean::cnstr_get(x_6, 2);
x_45 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_47 = x_6;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_6);
 x_47 = lean::box(0);
}
x_48 = 1;
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_27);
lean::cnstr_set(x_49, 1, x_29);
lean::cnstr_set(x_49, 2, x_31);
lean::cnstr_set(x_49, 3, x_4);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_48);
x_50 = x_49;
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_39);
lean::cnstr_set(x_51, 1, x_41);
lean::cnstr_set(x_51, 2, x_43);
lean::cnstr_set(x_51, 3, x_45);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_48);
x_52 = x_51;
if (lean::is_scalar(x_33)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_33;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_34);
lean::cnstr_set(x_53, 2, x_36);
lean::cnstr_set(x_53, 3, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*4, x_26);
x_54 = x_53;
return x_54;
}
else
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_55 = lean::cnstr_get(x_0, 0);
x_57 = lean::cnstr_get(x_0, 1);
x_59 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_61 = x_0;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_0);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_66 = x_1;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_1);
 x_66 = lean::box(0);
}
x_67 = 0;
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_4);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_64);
lean::cnstr_set(x_68, 3, x_6);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_67);
x_69 = x_68;
if (lean::is_scalar(x_61)) {
 x_70 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_70 = x_61;
}
lean::cnstr_set(x_70, 0, x_55);
lean::cnstr_set(x_70, 1, x_57);
lean::cnstr_set(x_70, 2, x_59);
lean::cnstr_set(x_70, 3, x_69);
lean::cnstr_set_scalar(x_70, sizeof(void*)*4, x_26);
x_71 = x_70;
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*4);
if (x_72 == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_73 = lean::cnstr_get(x_0, 0);
x_75 = lean::cnstr_get(x_0, 1);
x_77 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_79 = x_0;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_0);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_1, 1);
x_82 = lean::cnstr_get(x_1, 2);
x_84 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_86 = x_1;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_1);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_4, 0);
x_89 = lean::cnstr_get(x_4, 1);
x_91 = lean::cnstr_get(x_4, 2);
x_93 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 x_95 = x_4;
} else {
 lean::inc(x_87);
 lean::inc(x_89);
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_4);
 x_95 = lean::box(0);
}
x_96 = 1;
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_73);
lean::cnstr_set(x_97, 1, x_75);
lean::cnstr_set(x_97, 2, x_77);
lean::cnstr_set(x_97, 3, x_87);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_96);
x_98 = x_97;
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_99 = x_86;
}
lean::cnstr_set(x_99, 0, x_93);
lean::cnstr_set(x_99, 1, x_80);
lean::cnstr_set(x_99, 2, x_82);
lean::cnstr_set(x_99, 3, x_84);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_96);
x_100 = x_99;
if (lean::is_scalar(x_79)) {
 x_101 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_101 = x_79;
}
lean::cnstr_set(x_101, 0, x_98);
lean::cnstr_set(x_101, 1, x_89);
lean::cnstr_set(x_101, 2, x_91);
lean::cnstr_set(x_101, 3, x_100);
lean::cnstr_set_scalar(x_101, sizeof(void*)*4, x_72);
x_102 = x_101;
return x_102;
}
else
{
obj* x_103; 
x_103 = lean::cnstr_get(x_1, 3);
lean::inc(x_103);
if (lean::obj_tag(x_103) == 0)
{
obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_114; obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_105 = lean::cnstr_get(x_0, 0);
x_107 = lean::cnstr_get(x_0, 1);
x_109 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_111 = x_0;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::inc(x_109);
 lean::dec(x_0);
 x_111 = lean::box(0);
}
x_112 = lean::cnstr_get(x_1, 1);
x_114 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_116 = x_1;
} else {
 lean::inc(x_112);
 lean::inc(x_114);
 lean::dec(x_1);
 x_116 = lean::box(0);
}
x_117 = 0;
if (lean::is_scalar(x_116)) {
 x_118 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_118 = x_116;
}
lean::cnstr_set(x_118, 0, x_4);
lean::cnstr_set(x_118, 1, x_112);
lean::cnstr_set(x_118, 2, x_114);
lean::cnstr_set(x_118, 3, x_103);
lean::cnstr_set_scalar(x_118, sizeof(void*)*4, x_117);
x_119 = x_118;
if (lean::is_scalar(x_111)) {
 x_120 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_120 = x_111;
}
lean::cnstr_set(x_120, 0, x_105);
lean::cnstr_set(x_120, 1, x_107);
lean::cnstr_set(x_120, 2, x_109);
lean::cnstr_set(x_120, 3, x_119);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_72);
x_121 = x_120;
return x_121;
}
else
{
uint8 x_122; 
x_122 = lean::cnstr_get_scalar<uint8>(x_103, sizeof(void*)*4);
if (x_122 == 0)
{
obj* x_123; obj* x_125; obj* x_127; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_123 = lean::cnstr_get(x_0, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_0, 1);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_0, 2);
lean::inc(x_127);
lean::dec(x_0);
x_130 = lean::cnstr_get(x_1, 1);
x_132 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_134 = x_1;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::dec(x_1);
 x_134 = lean::box(0);
}
x_135 = lean::cnstr_get(x_103, 0);
x_137 = lean::cnstr_get(x_103, 1);
x_139 = lean::cnstr_get(x_103, 2);
x_141 = lean::cnstr_get(x_103, 3);
if (lean::is_exclusive(x_103)) {
 x_143 = x_103;
} else {
 lean::inc(x_135);
 lean::inc(x_137);
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_103);
 x_143 = lean::box(0);
}
lean::inc(x_4);
if (lean::is_scalar(x_143)) {
 x_145 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_145 = x_143;
}
lean::cnstr_set(x_145, 0, x_123);
lean::cnstr_set(x_145, 1, x_125);
lean::cnstr_set(x_145, 2, x_127);
lean::cnstr_set(x_145, 3, x_4);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_146 = x_4;
} else {
 lean::dec(x_4);
 x_146 = lean::box(0);
}
lean::cnstr_set_scalar(x_145, sizeof(void*)*4, x_72);
x_147 = x_145;
if (lean::is_scalar(x_146)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_146;
}
lean::cnstr_set(x_148, 0, x_135);
lean::cnstr_set(x_148, 1, x_137);
lean::cnstr_set(x_148, 2, x_139);
lean::cnstr_set(x_148, 3, x_141);
lean::cnstr_set_scalar(x_148, sizeof(void*)*4, x_72);
x_149 = x_148;
if (lean::is_scalar(x_134)) {
 x_150 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_150 = x_134;
}
lean::cnstr_set(x_150, 0, x_147);
lean::cnstr_set(x_150, 1, x_130);
lean::cnstr_set(x_150, 2, x_132);
lean::cnstr_set(x_150, 3, x_149);
lean::cnstr_set_scalar(x_150, sizeof(void*)*4, x_122);
x_151 = x_150;
return x_151;
}
else
{
obj* x_152; obj* x_154; obj* x_156; obj* x_158; obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_152 = lean::cnstr_get(x_0, 0);
x_154 = lean::cnstr_get(x_0, 1);
x_156 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_158 = x_0;
} else {
 lean::inc(x_152);
 lean::inc(x_154);
 lean::inc(x_156);
 lean::dec(x_0);
 x_158 = lean::box(0);
}
x_159 = lean::cnstr_get(x_1, 1);
x_161 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 3);
 x_163 = x_1;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_1);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_4, 0);
x_166 = lean::cnstr_get(x_4, 1);
x_168 = lean::cnstr_get(x_4, 2);
x_170 = lean::cnstr_get(x_4, 3);
if (lean::is_exclusive(x_4)) {
 x_172 = x_4;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_4);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_122);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_103);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_158)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_158;
}
lean::cnstr_set(x_178, 0, x_152);
lean::cnstr_set(x_178, 1, x_154);
lean::cnstr_set(x_178, 2, x_156);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_122);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
obj* l_RBNode_balance2___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance2___main___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_balance2___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance2___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance2___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_balance2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance2___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_balance2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_isRed___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
}
}
obj* l_RBNode_isRed___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isRed___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBNode_isRed___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBNode_isRed___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_isRed___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_isRed___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_isRed___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_RBNode_isRed___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_isRed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isRed___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBNode_isRed___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBNode_isRed___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_isRed___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_isRed(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_ins(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_setBlack___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_9 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_0);
 x_9 = lean::box(0);
}
x_10 = 1;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_5);
lean::cnstr_set(x_11, 3, x_7);
lean::cnstr_set_scalar(x_11, sizeof(void*)*4, x_10);
x_12 = x_11;
return x_12;
}
}
}
obj* l_RBNode_setBlack___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setBlack___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_setBlack___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_setBlack___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_setBlack___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_setBlack___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_setBlack(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setBlack___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_setBlack___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_setBlack(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBNode_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBNode_insert___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBNode_insert___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBNode_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBNode_insert___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBNode_insert___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBNode_insert___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBNode_insert___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_findCore___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
lean::dec(x_8);
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_findCore___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_findCore___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_findCore___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_findCore(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_findCore___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = lean::box(0);
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_RBNode_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_RBNode_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_lowerBound___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_3);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_8);
lean::cnstr_set(x_32, 1, x_10);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_1 = x_12;
x_3 = x_33;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_lowerBound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___main___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_lowerBound___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_lowerBound___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_lowerBound___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_lowerBound___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_lowerBound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_lowerBound___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_lowerBound(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_mkRBMap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_mkRBMap___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mkRBMap(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_HasEmptyc(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_RBMap_HasEmptyc___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_HasEmptyc(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBMap_depth(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_depth___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_depth___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_depth(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_fold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_fold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_fold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_revFold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_revFold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_revFold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_revFold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_revFold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_revFold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_revFold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_revFold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_revFold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_revFold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfold___main___rarg), 4, 0);
return x_5;
}
}
obj* l_RBMap_mfold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_mfold___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBMap_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfold___rarg), 4, 0);
return x_5;
}
}
obj* l_RBMap_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_mfold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
x_18 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg), 4, 3);
lean::closure_set(x_19, 0, x_0);
lean::closure_set(x_19, 1, x_1);
lean::closure_set(x_19, 2, x_4);
x_20 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_25; obj* x_27; obj* x_28; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_2, 3);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_21);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1___boxed), 7, 6);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_1);
lean::closure_set(x_27, 2, x_14);
lean::closure_set(x_27, 3, x_16);
lean::closure_set(x_27, 4, x_18);
lean::closure_set(x_27, 5, x_21);
x_28 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_RBMap_mfor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_mfor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfor___rarg), 3, 0);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_mfor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_mfor(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
uint8 l_RBMap_isEmpty___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_RBMap_isEmpty___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_isEmpty___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBMap_isEmpty___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBMap_isEmpty___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBMap_isEmpty___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_isEmpty___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_isEmpty___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_RBMap_isEmpty(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBMap_isEmpty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBMap_isEmpty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBMap_isEmpty___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_isEmpty(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(x_8, x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_0 = x_2;
x_1 = x_13;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_RBMap_toList___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBMap_toList___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_toList___main___rarg), 1, 0);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_revFold___main___at_RBMap_toList___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_toList___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_toList___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_toList___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_toList___main___rarg(x_0);
return x_1;
}
}
obj* l_RBMap_toList(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_toList___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_toList___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_toList(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_min___main___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_min___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_min___main___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_min___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_min___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_min(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_min___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_min___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_min(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_max___main___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_max___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_max___main___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_max___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_max___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_max(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_max___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_max___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_max(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_String_splitAux___main___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_0);
x_19 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_2, x_9);
x_20 = lean::apply_1(x_0, x_12);
x_21 = l_Prod_HasRepr___rarg___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = l_List_reprAux___main___rarg___closed__1;
x_25 = lean::string_append(x_22, x_24);
x_26 = lean::apply_1(x_1, x_14);
x_27 = lean::string_append(x_25, x_26);
lean::dec(x_26);
x_29 = l_Option_HasRepr___rarg___closed__3;
x_30 = lean::string_append(x_27, x_29);
x_31 = lean::string_append(x_24, x_30);
lean::dec(x_30);
x_33 = lean::string_append(x_31, x_19);
lean::dec(x_19);
return x_33;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
x_37 = l_String_splitAux___main___closed__1;
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_43; obj* x_45; uint8 x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
x_38 = lean::cnstr_get(x_3, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::dec(x_3);
x_43 = lean::cnstr_get(x_38, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 1);
lean::inc(x_45);
lean::dec(x_38);
x_48 = 0;
lean::inc(x_1);
lean::inc(x_0);
x_51 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_48, x_40);
x_52 = lean::apply_1(x_0, x_43);
x_53 = l_Prod_HasRepr___rarg___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_List_reprAux___main___rarg___closed__1;
x_57 = lean::string_append(x_54, x_56);
x_58 = lean::apply_1(x_1, x_45);
x_59 = lean::string_append(x_57, x_58);
lean::dec(x_58);
x_61 = l_Option_HasRepr___rarg___closed__3;
x_62 = lean::string_append(x_59, x_61);
x_63 = lean::string_append(x_62, x_51);
lean::dec(x_51);
return x_63;
}
}
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_List_repr___main___rarg___closed__1;
return x_5;
}
else
{
uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_6 = 1;
x_7 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_6, x_2);
x_8 = l_List_repr___main___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_List_repr___main___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
}
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_RBMap_HasRepr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rbmapOf ");
return x_0;
}
}
obj* l_RBMap_HasRepr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_RBMap_toList___main___rarg(x_2);
x_4 = l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(x_0, x_1, x_3);
x_5 = l_RBMap_HasRepr___rarg___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_RBMap_HasRepr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_HasRepr___rarg), 3, 0);
return x_3;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_repr___main___at_RBMap_HasRepr___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_HasRepr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_HasRepr(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___at_RBMap_insert___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_RBMap_insert___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_RBMap_insert___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBMap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBMap_insert___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_insert___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBMap_insert___main___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___at_RBMap_insert___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_RBMap_insert___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBMap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___at_RBMap_ofList___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_RBMap_ofList___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_RBMap_ofList___main___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___main___at_RBMap_ofList___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBMap_ofList___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_RBMap_ofList___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_RBMap_ofList___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_ofList___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_RBMap_ofList___main___rarg(x_0, x_6);
x_16 = l_RBNode_insert___at_RBMap_ofList___main___spec__2___rarg(x_0, x_15, x_9, x_11);
return x_16;
}
}
}
obj* l_RBMap_ofList___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_ofList___main___rarg), 2, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_ofList___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBMap_ofList___main___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___at_RBMap_ofList___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_RBMap_ofList___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___at_RBMap_ofList___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert___main___at_RBMap_ofList___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_ofList___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_ofList___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_ofList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_ofList___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBMap_ofList(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_ofList___rarg), 2, 0);
return x_3;
}
}
obj* l_RBMap_ofList___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_ofList(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
lean::dec(x_8);
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_findCore___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_findCore___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_findCore___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBMap_findCore___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_findCore___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_findCore(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = lean::box(0);
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBMap_find___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_RBMap_find___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___main___at_RBMap_find___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_RBMap_find___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_RBMap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_RBMap_find(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_find___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_3);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_8);
lean::cnstr_set(x_32, 1, x_10);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_1 = x_12;
x_3 = x_33;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_lowerBound___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_lowerBound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_lowerBound___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_lowerBound___main___at_RBMap_lowerBound___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_lowerBound___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_lowerBound___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_lowerBound___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_lowerBound___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_lowerBound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_lowerBound___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_lowerBound___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_lowerBound(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at_RBMap_contains___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = lean::box(0);
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_RBMap_contains___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_RBMap_contains___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBMap_find___main___at_RBMap_contains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_RBMap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_RBMap_find___main___at_RBMap_contains___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___at_RBMap_contains___spec__1___rarg), 3, 0);
return x_3;
}
}
uint8 l_RBMap_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_RBMap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 1;
return x_6;
}
}
}
obj* l_RBMap_contains(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_contains___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_RBNode_find___main___at_RBMap_contains___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___at_RBMap_contains___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___main___at_RBMap_contains___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_RBMap_contains___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___at_RBMap_contains___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_find___main___at_RBMap_contains___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBMap_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBMap_contains___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_contains(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___at_RBMap_fromList___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBMap_fromList___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBMap_fromList___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_RBMap_fromList___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_RBMap_fromList___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___main___at_RBMap_fromList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBMap_fromList___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_RBMap_fromList___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_RBMap_fromList___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_RBNode_insert___at_RBMap_fromList___spec__2___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_RBMap_fromList___spec__5___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_fromList___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_RBMap_fromList___spec__5___rarg(x_2, x_3, x_0);
return x_4;
}
}
obj* l_RBMap_fromList(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fromList___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBMap_fromList___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_RBMap_fromList___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_RBMap_fromList___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___at_RBMap_fromList___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_RBMap_fromList___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___at_RBMap_fromList___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert___main___at_RBMap_fromList___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_RBMap_fromList___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_fromList___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_fromList___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_RBMap_fromList___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_fromList(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBMap_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_all___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_all___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_all___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_all___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_all___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_all___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_all___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_all(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_all___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_RBMap_all___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_all___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_all___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_all(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_RBMap_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_any___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_any___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_any___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_any___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_any___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_any___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_any___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_any(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_any___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_RBMap_any___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_any___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_any___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_any(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_rbmapOf___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_rbmapOf___spec__4___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_rbmapOf___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_rbmapOf___spec__5___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___at_rbmapOf___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_rbmapOf___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_rbmapOf___spec__5___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_rbmapOf___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_rbmapOf___spec__3___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_insert___main___at_rbmapOf___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_rbmapOf___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_rbmapOf___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_rbmapOf___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_RBNode_insert___at_rbmapOf___spec__3___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_rbmapOf___spec__6___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_fromList___at_rbmapOf___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_foldl___main___at_rbmapOf___spec__6___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBMap_fromList___at_rbmapOf___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fromList___at_rbmapOf___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_rbmapOf___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_fromList___at_rbmapOf___spec__1___rarg(x_2, x_0);
return x_3;
}
}
obj* l_rbmapOf(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmapOf___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_rbmapOf___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_rbmapOf___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___at_rbmapOf___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main___at_rbmapOf___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___at_rbmapOf___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert___at_rbmapOf___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___at_rbmapOf___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_insert___main___at_rbmapOf___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_rbmapOf___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_fromList___at_rbmapOf___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_fromList___at_rbmapOf___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmapOf___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmapOf___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_rbmapOf___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmapOf(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_ordering_basic(obj*);
obj* initialize_init_coe(obj*);
obj* initialize_init_data_option_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_rbmap_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_ordering_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
 l_RBMap_HasRepr___rarg___closed__1 = _init_l_RBMap_HasRepr___rarg___closed__1();
lean::mark_persistent(l_RBMap_HasRepr___rarg___closed__1);
return w;
}
