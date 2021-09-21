// Lean compiler output
// Module: Std.Data.RBMap
// Imports: Init
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Std_RBMap_min_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_depth___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_depth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_revFold(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__11;
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_del(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_find_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_fold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_ofList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_singleton___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_max___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_revFold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_min(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_rbmapOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rbcolor_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__10;
LEAN_EXPORT lean_object* l_Std_RBNode_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balance2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_depth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_lowerBound___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_forIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_depth___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_min___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_appendTrees(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_ofList(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_instReprProd___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBMap_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__6;
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__7;
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_find_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balance2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_revFold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_any___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_max___rarg___boxed(lean_object*);
lean_object* l_Nat_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_depth___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_rbmapOf___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_min_x21___rarg___closed__4;
static lean_object* l_Std_RBMap_min_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Std_RBMap_fromList___spec__1(lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_appendTrees___rarg(lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__9;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBNode_isBlack___rarg(lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__8;
LEAN_EXPORT lean_object* l_Std_RBNode_del___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_fromList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_size(lean_object*, lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_RBMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_min___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_setRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_min___rarg(lean_object*);
static lean_object* l_Std_RBMap_max_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balance1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_setRed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_toList___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balance1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_all___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__3;
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__5;
LEAN_EXPORT lean_object* l_Std_RBNode_isBlack___rarg___boxed(lean_object*);
static lean_object* l_Std_RBMap_max_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_setBlack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_empty(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1(lean_object*, lean_object*);
static lean_object* l_Std_RBMap_find_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instEmptyCollectionRBMap(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_balance_u2083___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_find_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_RBMap_min___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_RBMap_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_any___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_all___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_lowerBound___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_isRed___rarg___boxed(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_findD(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBNode_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_findCore_x3f___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__9;
LEAN_EXPORT lean_object* l_Std_RBMap_min___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__8;
static lean_object* l_Std_RBMap_toList___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_RBMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_maxDepth___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_revFold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__5;
LEAN_EXPORT lean_object* l_Std_RBMap_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_isRed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_isBlack(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBMap_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBNode_all___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balLeft(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBMap_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_rbmapOf___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_lowerBound(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Std_RBMap_size___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_all___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_fold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_max___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_depth___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_size___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rbcolor_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_balance_u2083(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_fromList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_lowerBound(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_RBMap_fromList___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__7;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_RBMap_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instEmptyCollectionRBMap___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_instReprRBMap___rarg___closed__6;
LEAN_EXPORT lean_object* l_Std_RBNode_depth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_findCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Rbcolor_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Std_rbmapOf___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBMap_min_x21___rarg___closed__2;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rbcolor_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Std_Rbcolor_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Rbcolor_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Rbcolor_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Rbcolor_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Rbcolor_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Rbcolor_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Rbcolor_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Rbcolor_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Rbcolor_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_depth___rarg(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_RBNode_depth___rarg(x_1, x_4);
lean_inc(x_1);
x_7 = l_Std_RBNode_depth___rarg(x_1, x_5);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_depth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_depth___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_min___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_min(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_min___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBNode_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_max___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_max___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBNode_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Std_RBNode_fold___rarg(x_1, x_2, x_4);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBNode_fold___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_3(x_1, x_7, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = l_Std_RBNode_foldM___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___rarg___lambda__2), 7, 6);
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
LEAN_EXPORT lean_object* l_Std_RBNode_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Std_RBNode_forIn_visit___rarg(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___rarg___lambda__1), 4, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Std_RBNode_forIn_visit___rarg(x_1, x_2, x_9, x_4);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___rarg___lambda__2), 7, 6);
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
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_forIn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Std_RBNode_forIn_visit___rarg(x_1, x_4, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Std_RBNode_forIn___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_forIn___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Std_RBNode_revFold___rarg(x_1, x_2, x_7);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBNode_revFold___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_RBNode_all___rarg(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_Std_RBNode_all___rarg(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Std_RBNode_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_all___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_RBNode_any___rarg(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Std_RBNode_any___rarg(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Std_RBNode_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_any___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_singleton___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_singleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_singleton___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balance1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = 0;
lean_ctor_set(x_4, 0, x_7);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_11);
x_12 = 1;
x_13 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = 0;
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_16);
x_18 = 1;
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_3);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
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
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = 1;
lean_ctor_set(x_7, 3, x_27);
lean_ctor_set(x_7, 2, x_23);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_31);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_30);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_31);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
x_36 = lean_ctor_get(x_7, 2);
x_37 = lean_ctor_get(x_7, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_38 = 1;
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_22);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_38);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_37);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
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
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_48 = x_7;
} else {
 lean_dec_ref(x_7);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 4, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_49);
x_51 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_1);
lean_ctor_set(x_51, 2, x_2);
lean_ctor_set(x_51, 3, x_3);
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
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_4, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_4, 0);
lean_dec(x_56);
x_57 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_57);
x_58 = 1;
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_1);
lean_ctor_set(x_59, 2, x_2);
lean_ctor_set(x_59, 3, x_3);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_4, 1);
x_61 = lean_ctor_get(x_4, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = 0;
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_6);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set(x_63, 3, x_7);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_62);
x_64 = 1;
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_1);
lean_ctor_set(x_65, 2, x_2);
lean_ctor_set(x_65, 3, x_3);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_4);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_4, 1);
x_69 = lean_ctor_get(x_4, 2);
x_70 = lean_ctor_get(x_4, 3);
x_71 = lean_ctor_get(x_4, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_6);
if (x_72 == 0)
{
uint8_t x_73; uint8_t x_74; lean_object* x_75; 
x_73 = 1;
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_73);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_70);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_73);
x_74 = 0;
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_6);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_4);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_6, 0);
x_77 = lean_ctor_get(x_6, 1);
x_78 = lean_ctor_get(x_6, 2);
x_79 = lean_ctor_get(x_6, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_6);
x_80 = 1;
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_70);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_80);
x_82 = 0;
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_68);
lean_ctor_set(x_83, 2, x_69);
lean_ctor_set(x_83, 3, x_4);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_4, 1);
x_85 = lean_ctor_get(x_4, 2);
x_86 = lean_ctor_get(x_4, 3);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_4);
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_6, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_6, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_6, 3);
lean_inc(x_90);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_91 = x_6;
} else {
 lean_dec_ref(x_6);
 x_91 = lean_box(0);
}
x_92 = 1;
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(1, 4, 1);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_90);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_1);
lean_ctor_set(x_94, 2, x_2);
lean_ctor_set(x_94, 3, x_3);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_92);
x_95 = 0;
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_84);
lean_ctor_set(x_96, 2, x_85);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
return x_96;
}
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_4, 3);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_4);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_4, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_4, 0);
lean_dec(x_100);
x_101 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_101);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_4);
lean_ctor_set(x_103, 1, x_1);
lean_ctor_set(x_103, 2, x_2);
lean_ctor_set(x_103, 3, x_3);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_4, 1);
x_105 = lean_ctor_get(x_4, 2);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_4);
x_106 = 0;
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_6);
lean_ctor_set(x_107, 1, x_104);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_107, 3, x_97);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_1);
lean_ctor_set(x_109, 2, x_2);
lean_ctor_set(x_109, 3, x_3);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
return x_109;
}
}
else
{
uint8_t x_110; 
x_110 = lean_ctor_get_uint8(x_97, sizeof(void*)*4);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_4);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_4, 1);
x_113 = lean_ctor_get(x_4, 2);
x_114 = lean_ctor_get(x_4, 3);
lean_dec(x_114);
x_115 = lean_ctor_get(x_4, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_97);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_117 = lean_ctor_get(x_97, 0);
x_118 = lean_ctor_get(x_97, 1);
x_119 = lean_ctor_get(x_97, 2);
x_120 = lean_ctor_get(x_97, 3);
x_121 = 1;
lean_inc(x_6);
lean_ctor_set(x_97, 3, x_117);
lean_ctor_set(x_97, 2, x_113);
lean_ctor_set(x_97, 1, x_112);
lean_ctor_set(x_97, 0, x_6);
x_122 = !lean_is_exclusive(x_6);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_6, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_6, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_6, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_6, 0);
lean_dec(x_126);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_121);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_120);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_121);
x_127 = 0;
lean_ctor_set(x_4, 3, x_6);
lean_ctor_set(x_4, 2, x_119);
lean_ctor_set(x_4, 1, x_118);
lean_ctor_set(x_4, 0, x_97);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_127);
return x_4;
}
else
{
lean_object* x_128; uint8_t x_129; 
lean_dec(x_6);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_121);
x_128 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set(x_128, 1, x_1);
lean_ctor_set(x_128, 2, x_2);
lean_ctor_set(x_128, 3, x_3);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_121);
x_129 = 0;
lean_ctor_set(x_4, 3, x_128);
lean_ctor_set(x_4, 2, x_119);
lean_ctor_set(x_4, 1, x_118);
lean_ctor_set(x_4, 0, x_97);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_129);
return x_4;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_130 = lean_ctor_get(x_97, 0);
x_131 = lean_ctor_get(x_97, 1);
x_132 = lean_ctor_get(x_97, 2);
x_133 = lean_ctor_get(x_97, 3);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_97);
x_134 = 1;
lean_inc(x_6);
x_135 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_135, 0, x_6);
lean_ctor_set(x_135, 1, x_112);
lean_ctor_set(x_135, 2, x_113);
lean_ctor_set(x_135, 3, x_130);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_136 = x_6;
} else {
 lean_dec_ref(x_6);
 x_136 = lean_box(0);
}
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_134);
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 4, 1);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_1);
lean_ctor_set(x_137, 2, x_2);
lean_ctor_set(x_137, 3, x_3);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_134);
x_138 = 0;
lean_ctor_set(x_4, 3, x_137);
lean_ctor_set(x_4, 2, x_132);
lean_ctor_set(x_4, 1, x_131);
lean_ctor_set(x_4, 0, x_135);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_138);
return x_4;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_139 = lean_ctor_get(x_4, 1);
x_140 = lean_ctor_get(x_4, 2);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_4);
x_141 = lean_ctor_get(x_97, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_97, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_97, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_97, 3);
lean_inc(x_144);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 x_145 = x_97;
} else {
 lean_dec_ref(x_97);
 x_145 = lean_box(0);
}
x_146 = 1;
lean_inc(x_6);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(1, 4, 1);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_6);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_140);
lean_ctor_set(x_147, 3, x_141);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_148 = x_6;
} else {
 lean_dec_ref(x_6);
 x_148 = lean_box(0);
}
lean_ctor_set_uint8(x_147, sizeof(void*)*4, x_146);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 4, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_1);
lean_ctor_set(x_149, 2, x_2);
lean_ctor_set(x_149, 3, x_3);
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_146);
x_150 = 0;
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_142);
lean_ctor_set(x_151, 2, x_143);
lean_ctor_set(x_151, 3, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
return x_151;
}
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_4);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_4, 3);
lean_dec(x_153);
x_154 = lean_ctor_get(x_4, 0);
lean_dec(x_154);
x_155 = !lean_is_exclusive(x_6);
if (x_155 == 0)
{
uint8_t x_156; uint8_t x_157; lean_object* x_158; 
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_110);
x_156 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_156);
x_157 = 1;
x_158 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_158, 0, x_4);
lean_ctor_set(x_158, 1, x_1);
lean_ctor_set(x_158, 2, x_2);
lean_ctor_set(x_158, 3, x_3);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; 
x_159 = lean_ctor_get(x_6, 0);
x_160 = lean_ctor_get(x_6, 1);
x_161 = lean_ctor_get(x_6, 2);
x_162 = lean_ctor_get(x_6, 3);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_6);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_160);
lean_ctor_set(x_163, 2, x_161);
lean_ctor_set(x_163, 3, x_162);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_110);
x_164 = 0;
lean_ctor_set(x_4, 0, x_163);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_164);
x_165 = 1;
x_166 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_166, 0, x_4);
lean_ctor_set(x_166, 1, x_1);
lean_ctor_set(x_166, 2, x_2);
lean_ctor_set(x_166, 3, x_3);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_165);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_167 = lean_ctor_get(x_4, 1);
x_168 = lean_ctor_get(x_4, 2);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_4);
x_169 = lean_ctor_get(x_6, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_6, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_6, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_6, 3);
lean_inc(x_172);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_173 = x_6;
} else {
 lean_dec_ref(x_6);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_169);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_171);
lean_ctor_set(x_174, 3, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_110);
x_175 = 0;
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_167);
lean_ctor_set(x_176, 2, x_168);
lean_ctor_set(x_176, 3, x_97);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_175);
x_177 = 1;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_1);
lean_ctor_set(x_178, 2, x_2);
lean_ctor_set(x_178, 3, x_3);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balance1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_balance1___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balance2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = 0;
lean_ctor_set(x_4, 0, x_7);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_11);
x_12 = 1;
x_13 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = 0;
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_16);
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
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
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
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = 1;
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_31);
lean_ctor_set(x_4, 3, x_30);
lean_ctor_set(x_4, 2, x_29);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_27);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_31);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
x_36 = lean_ctor_get(x_7, 2);
x_37 = lean_ctor_get(x_7, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_38 = 1;
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set(x_39, 3, x_6);
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
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 x_48 = x_7;
} else {
 lean_dec_ref(x_7);
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
lean_ctor_set(x_50, 3, x_6);
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
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_4, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_4, 0);
lean_dec(x_56);
x_57 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_57);
x_58 = 1;
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_3);
lean_ctor_set(x_59, 3, x_4);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_4, 1);
x_61 = lean_ctor_get(x_4, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = 0;
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_6);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_61);
lean_ctor_set(x_63, 3, x_7);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_62);
x_64 = 1;
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_2);
lean_ctor_set(x_65, 2, x_3);
lean_ctor_set(x_65, 3, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_4);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_4, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_6, 0);
x_71 = lean_ctor_get(x_6, 1);
x_72 = lean_ctor_get(x_6, 2);
x_73 = lean_ctor_get(x_6, 3);
x_74 = 1;
lean_ctor_set(x_6, 3, x_70);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_74);
lean_ctor_set(x_4, 0, x_73);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_74);
x_75 = 0;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_4);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_6, 0);
x_78 = lean_ctor_get(x_6, 1);
x_79 = lean_ctor_get(x_6, 2);
x_80 = lean_ctor_get(x_6, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_6);
x_81 = 1;
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_2);
lean_ctor_set(x_82, 2, x_3);
lean_ctor_set(x_82, 3, x_77);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
lean_ctor_set(x_4, 0, x_80);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_81);
x_83 = 0;
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_4);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_4, 1);
x_86 = lean_ctor_get(x_4, 2);
x_87 = lean_ctor_get(x_4, 3);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_4);
x_88 = lean_ctor_get(x_6, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_6, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_6, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_6, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_92 = x_6;
} else {
 lean_dec_ref(x_6);
 x_92 = lean_box(0);
}
x_93 = 1;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(1, 4, 1);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_3);
lean_ctor_set(x_94, 3, x_88);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
x_95 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_85);
lean_ctor_set(x_95, 2, x_86);
lean_ctor_set(x_95, 3, x_87);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_93);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_90);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
return x_97;
}
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_4, 3);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_4);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_4, 3);
lean_dec(x_100);
x_101 = lean_ctor_get(x_4, 0);
lean_dec(x_101);
x_102 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_102);
x_103 = 1;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_3);
lean_ctor_set(x_104, 3, x_4);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_4, 1);
x_106 = lean_ctor_get(x_4, 2);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_4);
x_107 = 0;
x_108 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_108, 2, x_106);
lean_ctor_set(x_108, 3, x_98);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_107);
x_109 = 1;
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_2);
lean_ctor_set(x_110, 2, x_3);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_109);
return x_110;
}
}
else
{
uint8_t x_111; 
x_111 = lean_ctor_get_uint8(x_98, sizeof(void*)*4);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_4);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_4, 3);
lean_dec(x_113);
x_114 = lean_ctor_get(x_4, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_98);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; 
x_116 = lean_ctor_get(x_98, 0);
x_117 = lean_ctor_get(x_98, 1);
x_118 = lean_ctor_get(x_98, 2);
x_119 = lean_ctor_get(x_98, 3);
x_120 = 1;
lean_inc(x_6);
lean_ctor_set(x_98, 3, x_6);
lean_ctor_set(x_98, 2, x_3);
lean_ctor_set(x_98, 1, x_2);
lean_ctor_set(x_98, 0, x_1);
x_121 = !lean_is_exclusive(x_6);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_6, 3);
lean_dec(x_122);
x_123 = lean_ctor_get(x_6, 2);
lean_dec(x_123);
x_124 = lean_ctor_get(x_6, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_6, 0);
lean_dec(x_125);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_120);
lean_ctor_set(x_6, 3, x_119);
lean_ctor_set(x_6, 2, x_118);
lean_ctor_set(x_6, 1, x_117);
lean_ctor_set(x_6, 0, x_116);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_120);
x_126 = 0;
lean_ctor_set(x_4, 3, x_6);
lean_ctor_set(x_4, 0, x_98);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_126);
return x_4;
}
else
{
lean_object* x_127; uint8_t x_128; 
lean_dec(x_6);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_120);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_117);
lean_ctor_set(x_127, 2, x_118);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_120);
x_128 = 0;
lean_ctor_set(x_4, 3, x_127);
lean_ctor_set(x_4, 0, x_98);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_128);
return x_4;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_129 = lean_ctor_get(x_98, 0);
x_130 = lean_ctor_get(x_98, 1);
x_131 = lean_ctor_get(x_98, 2);
x_132 = lean_ctor_get(x_98, 3);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_98);
x_133 = 1;
lean_inc(x_6);
x_134 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_2);
lean_ctor_set(x_134, 2, x_3);
lean_ctor_set(x_134, 3, x_6);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_135 = x_6;
} else {
 lean_dec_ref(x_6);
 x_135 = lean_box(0);
}
lean_ctor_set_uint8(x_134, sizeof(void*)*4, x_133);
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 4, 1);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_131);
lean_ctor_set(x_136, 3, x_132);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_133);
x_137 = 0;
lean_ctor_set(x_4, 3, x_136);
lean_ctor_set(x_4, 0, x_134);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_137);
return x_4;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_138 = lean_ctor_get(x_4, 1);
x_139 = lean_ctor_get(x_4, 2);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_4);
x_140 = lean_ctor_get(x_98, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_98, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_98, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_98, 3);
lean_inc(x_143);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 x_144 = x_98;
} else {
 lean_dec_ref(x_98);
 x_144 = lean_box(0);
}
x_145 = 1;
lean_inc(x_6);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(1, 4, 1);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_2);
lean_ctor_set(x_146, 2, x_3);
lean_ctor_set(x_146, 3, x_6);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_147 = x_6;
} else {
 lean_dec_ref(x_6);
 x_147 = lean_box(0);
}
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_145);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 4, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_141);
lean_ctor_set(x_148, 2, x_142);
lean_ctor_set(x_148, 3, x_143);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_145);
x_149 = 0;
x_150 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_138);
lean_ctor_set(x_150, 2, x_139);
lean_ctor_set(x_150, 3, x_148);
lean_ctor_set_uint8(x_150, sizeof(void*)*4, x_149);
return x_150;
}
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_4);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_4, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_4, 0);
lean_dec(x_153);
x_154 = !lean_is_exclusive(x_6);
if (x_154 == 0)
{
uint8_t x_155; uint8_t x_156; lean_object* x_157; 
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_111);
x_155 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_155);
x_156 = 1;
x_157 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_2);
lean_ctor_set(x_157, 2, x_3);
lean_ctor_set(x_157, 3, x_4);
lean_ctor_set_uint8(x_157, sizeof(void*)*4, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_6, 0);
x_159 = lean_ctor_get(x_6, 1);
x_160 = lean_ctor_get(x_6, 2);
x_161 = lean_ctor_get(x_6, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_6);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_159);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_111);
x_163 = 0;
lean_ctor_set(x_4, 0, x_162);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_163);
x_164 = 1;
x_165 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_2);
lean_ctor_set(x_165, 2, x_3);
lean_ctor_set(x_165, 3, x_4);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_166 = lean_ctor_get(x_4, 1);
x_167 = lean_ctor_get(x_4, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_4);
x_168 = lean_ctor_get(x_6, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_6, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_6, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_6, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_172 = x_6;
} else {
 lean_dec_ref(x_6);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_169);
lean_ctor_set(x_173, 2, x_170);
lean_ctor_set(x_173, 3, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_111);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_98);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
x_176 = 1;
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_1);
lean_ctor_set(x_177, 1, x_2);
lean_ctor_set(x_177, 2, x_3);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
return x_177;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balance2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_balance2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_RBNode_isRed___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_isRed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_isRed___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_isRed___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_RBNode_isRed___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_RBNode_isBlack___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_isBlack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_isBlack___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_isBlack___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_RBNode_isBlack___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_16 = l_Std_RBNode_ins___rarg(x_1, x_10, x_3, x_4);
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
x_19 = l_Std_RBNode_ins___rarg(x_1, x_13, x_3, x_4);
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
x_27 = l_Std_RBNode_ins___rarg(x_1, x_21, x_3, x_4);
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
x_32 = l_Std_RBNode_ins___rarg(x_1, x_24, x_3, x_4);
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
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_36);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___rarg(x_1, x_36, x_3, x_4);
x_44 = 1;
lean_ctor_set(x_2, 0, x_43);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_44);
return x_2;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___rarg(x_1, x_36, x_3, x_4);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_52);
return x_2;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_2, 0, x_56);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_57);
return x_2;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_65);
lean_ctor_set(x_47, 2, x_61);
lean_ctor_set(x_47, 1, x_60);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_68);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_2, 3, x_45);
lean_ctor_set(x_2, 2, x_67);
lean_ctor_set(x_2, 1, x_66);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_70);
return x_2;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_46);
lean_ctor_set(x_76, 1, x_60);
lean_ctor_set(x_76, 2, x_61);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_74);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_2, 3, x_45);
lean_ctor_set(x_2, 2, x_73);
lean_ctor_set(x_2, 1, x_72);
lean_ctor_set(x_2, 0, x_76);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_77);
return x_2;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_46);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_79);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_37);
lean_ctor_set(x_87, 2, x_38);
lean_ctor_set(x_87, 3, x_39);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_2, 3, x_87);
lean_ctor_set(x_2, 2, x_82);
lean_ctor_set(x_2, 1, x_81);
lean_ctor_set(x_2, 0, x_86);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_88);
return x_2;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_93);
return x_2;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_2, 0, x_97);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_98);
return x_2;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_45, 1);
x_102 = lean_ctor_get(x_45, 2);
x_103 = lean_ctor_get(x_45, 3);
x_104 = lean_ctor_get(x_45, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_46);
if (x_105 == 0)
{
uint8_t x_106; uint8_t x_107; 
x_106 = 1;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_106);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_103);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_106);
x_107 = 0;
lean_ctor_set(x_2, 3, x_45);
lean_ctor_set(x_2, 2, x_102);
lean_ctor_set(x_2, 1, x_101);
lean_ctor_set(x_2, 0, x_46);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_107);
return x_2;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_ctor_get(x_46, 0);
x_109 = lean_ctor_get(x_46, 1);
x_110 = lean_ctor_get(x_46, 2);
x_111 = lean_ctor_get(x_46, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_46);
x_112 = 1;
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_103);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_112);
x_114 = 0;
lean_ctor_set(x_2, 3, x_45);
lean_ctor_set(x_2, 2, x_102);
lean_ctor_set(x_2, 1, x_101);
lean_ctor_set(x_2, 0, x_113);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_114);
return x_2;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_115 = lean_ctor_get(x_45, 1);
x_116 = lean_ctor_get(x_45, 2);
x_117 = lean_ctor_get(x_45, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_45);
x_118 = lean_ctor_get(x_46, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_46, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_122 = x_46;
} else {
 lean_dec_ref(x_46);
 x_122 = lean_box(0);
}
x_123 = 1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(1, 4, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_119);
lean_ctor_set(x_124, 2, x_120);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_123);
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_37);
lean_ctor_set(x_125, 2, x_38);
lean_ctor_set(x_125, 3, x_39);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_123);
x_126 = 0;
lean_ctor_set(x_2, 3, x_125);
lean_ctor_set(x_2, 2, x_116);
lean_ctor_set(x_2, 1, x_115);
lean_ctor_set(x_2, 0, x_124);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_126);
return x_2;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_45, 3);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_45);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_45, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_45, 0);
lean_dec(x_130);
x_131 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_131);
x_132 = 1;
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_132);
return x_2;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_45, 1);
x_134 = lean_ctor_get(x_45, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_45);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_46);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
x_137 = 1;
lean_ctor_set(x_2, 0, x_136);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_137);
return x_2;
}
}
else
{
uint8_t x_138; 
x_138 = lean_ctor_get_uint8(x_127, sizeof(void*)*4);
if (x_138 == 0)
{
uint8_t x_139; 
lean_free_object(x_2);
x_139 = !lean_is_exclusive(x_45);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_45, 1);
x_141 = lean_ctor_get(x_45, 2);
x_142 = lean_ctor_get(x_45, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_45, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_127);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_127, 0);
x_146 = lean_ctor_get(x_127, 1);
x_147 = lean_ctor_get(x_127, 2);
x_148 = lean_ctor_get(x_127, 3);
x_149 = 1;
lean_inc(x_46);
lean_ctor_set(x_127, 3, x_145);
lean_ctor_set(x_127, 2, x_141);
lean_ctor_set(x_127, 1, x_140);
lean_ctor_set(x_127, 0, x_46);
x_150 = !lean_is_exclusive(x_46);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_46, 3);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 2);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 1);
lean_dec(x_153);
x_154 = lean_ctor_get(x_46, 0);
lean_dec(x_154);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_149);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 0, x_148);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_149);
x_155 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 2, x_147);
lean_ctor_set(x_45, 1, x_146);
lean_ctor_set(x_45, 0, x_127);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_155);
return x_45;
}
else
{
lean_object* x_156; uint8_t x_157; 
lean_dec(x_46);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_149);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_148);
lean_ctor_set(x_156, 1, x_37);
lean_ctor_set(x_156, 2, x_38);
lean_ctor_set(x_156, 3, x_39);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_149);
x_157 = 0;
lean_ctor_set(x_45, 3, x_156);
lean_ctor_set(x_45, 2, x_147);
lean_ctor_set(x_45, 1, x_146);
lean_ctor_set(x_45, 0, x_127);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_157);
return x_45;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_158 = lean_ctor_get(x_127, 0);
x_159 = lean_ctor_get(x_127, 1);
x_160 = lean_ctor_get(x_127, 2);
x_161 = lean_ctor_get(x_127, 3);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_127);
x_162 = 1;
lean_inc(x_46);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_46);
lean_ctor_set(x_163, 1, x_140);
lean_ctor_set(x_163, 2, x_141);
lean_ctor_set(x_163, 3, x_158);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_164 = x_46;
} else {
 lean_dec_ref(x_46);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_37);
lean_ctor_set(x_165, 2, x_38);
lean_ctor_set(x_165, 3, x_39);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
lean_ctor_set(x_45, 3, x_165);
lean_ctor_set(x_45, 2, x_160);
lean_ctor_set(x_45, 1, x_159);
lean_ctor_set(x_45, 0, x_163);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_166);
return x_45;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_167 = lean_ctor_get(x_45, 1);
x_168 = lean_ctor_get(x_45, 2);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_45);
x_169 = lean_ctor_get(x_127, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_127, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_127, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_127, 3);
lean_inc(x_172);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_173 = x_127;
} else {
 lean_dec_ref(x_127);
 x_173 = lean_box(0);
}
x_174 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_46);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_168);
lean_ctor_set(x_175, 3, x_169);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_176 = x_46;
} else {
 lean_dec_ref(x_46);
 x_176 = lean_box(0);
}
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 4, 1);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_37);
lean_ctor_set(x_177, 2, x_38);
lean_ctor_set(x_177, 3, x_39);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_174);
x_178 = 0;
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_170);
lean_ctor_set(x_179, 2, x_171);
lean_ctor_set(x_179, 3, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_178);
return x_179;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_45);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_45, 3);
lean_dec(x_181);
x_182 = lean_ctor_get(x_45, 0);
lean_dec(x_182);
x_183 = !lean_is_exclusive(x_46);
if (x_183 == 0)
{
uint8_t x_184; uint8_t x_185; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_138);
x_184 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_184);
x_185 = 1;
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_185);
return x_2;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; 
x_186 = lean_ctor_get(x_46, 0);
x_187 = lean_ctor_get(x_46, 1);
x_188 = lean_ctor_get(x_46, 2);
x_189 = lean_ctor_get(x_46, 3);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_46);
x_190 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_190, 0, x_186);
lean_ctor_set(x_190, 1, x_187);
lean_ctor_set(x_190, 2, x_188);
lean_ctor_set(x_190, 3, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_138);
x_191 = 0;
lean_ctor_set(x_45, 0, x_190);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_191);
x_192 = 1;
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_192);
return x_2;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; uint8_t x_203; 
x_193 = lean_ctor_get(x_45, 1);
x_194 = lean_ctor_get(x_45, 2);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_45);
x_195 = lean_ctor_get(x_46, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_46, 3);
lean_inc(x_198);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_199 = x_46;
} else {
 lean_dec_ref(x_46);
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
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_138);
x_201 = 0;
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_193);
lean_ctor_set(x_202, 2, x_194);
lean_ctor_set(x_202, 3, x_127);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_201);
x_203 = 1;
lean_ctor_set(x_2, 0, x_202);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_203);
return x_2;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_204; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_204 = 1;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_204);
return x_2;
}
default: 
{
uint8_t x_205; 
x_205 = l_Std_RBNode_isRed___rarg(x_39);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = l_Std_RBNode_ins___rarg(x_1, x_39, x_3, x_4);
x_207 = 1;
lean_ctor_set(x_2, 3, x_206);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_207);
return x_2;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = l_Std_RBNode_ins___rarg(x_1, x_39, x_3, x_4);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_208, 3);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_208);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_212 = lean_ctor_get(x_208, 3);
lean_dec(x_212);
x_213 = lean_ctor_get(x_208, 0);
lean_dec(x_213);
x_214 = 0;
lean_ctor_set(x_208, 0, x_210);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_214);
x_215 = 1;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_215);
return x_2;
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_208, 1);
x_217 = lean_ctor_get(x_208, 2);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_208);
x_218 = 0;
x_219 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_219, 0, x_210);
lean_ctor_set(x_219, 1, x_216);
lean_ctor_set(x_219, 2, x_217);
lean_ctor_set(x_219, 3, x_210);
lean_ctor_set_uint8(x_219, sizeof(void*)*4, x_218);
x_220 = 1;
lean_ctor_set(x_2, 3, x_219);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_220);
return x_2;
}
}
else
{
uint8_t x_221; 
x_221 = lean_ctor_get_uint8(x_210, sizeof(void*)*4);
if (x_221 == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_208);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_208, 1);
x_224 = lean_ctor_get(x_208, 2);
x_225 = lean_ctor_get(x_208, 3);
lean_dec(x_225);
x_226 = lean_ctor_get(x_208, 0);
lean_dec(x_226);
x_227 = !lean_is_exclusive(x_210);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_210, 0);
x_229 = lean_ctor_get(x_210, 1);
x_230 = lean_ctor_get(x_210, 2);
x_231 = lean_ctor_get(x_210, 3);
x_232 = 1;
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set(x_210, 2, x_38);
lean_ctor_set(x_210, 1, x_37);
lean_ctor_set(x_210, 0, x_36);
lean_ctor_set_uint8(x_210, sizeof(void*)*4, x_232);
lean_ctor_set(x_208, 3, x_231);
lean_ctor_set(x_208, 2, x_230);
lean_ctor_set(x_208, 1, x_229);
lean_ctor_set(x_208, 0, x_228);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_232);
x_233 = 0;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set(x_2, 2, x_224);
lean_ctor_set(x_2, 1, x_223);
lean_ctor_set(x_2, 0, x_210);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_233);
return x_2;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; uint8_t x_240; 
x_234 = lean_ctor_get(x_210, 0);
x_235 = lean_ctor_get(x_210, 1);
x_236 = lean_ctor_get(x_210, 2);
x_237 = lean_ctor_get(x_210, 3);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_210);
x_238 = 1;
x_239 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_239, 0, x_36);
lean_ctor_set(x_239, 1, x_37);
lean_ctor_set(x_239, 2, x_38);
lean_ctor_set(x_239, 3, x_209);
lean_ctor_set_uint8(x_239, sizeof(void*)*4, x_238);
lean_ctor_set(x_208, 3, x_237);
lean_ctor_set(x_208, 2, x_236);
lean_ctor_set(x_208, 1, x_235);
lean_ctor_set(x_208, 0, x_234);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_238);
x_240 = 0;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set(x_2, 2, x_224);
lean_ctor_set(x_2, 1, x_223);
lean_ctor_set(x_2, 0, x_239);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_240);
return x_2;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_241 = lean_ctor_get(x_208, 1);
x_242 = lean_ctor_get(x_208, 2);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_208);
x_243 = lean_ctor_get(x_210, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_210, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_210, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_210, 3);
lean_inc(x_246);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_247 = x_210;
} else {
 lean_dec_ref(x_210);
 x_247 = lean_box(0);
}
x_248 = 1;
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(1, 4, 1);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_36);
lean_ctor_set(x_249, 1, x_37);
lean_ctor_set(x_249, 2, x_38);
lean_ctor_set(x_249, 3, x_209);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_248);
x_250 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_244);
lean_ctor_set(x_250, 2, x_245);
lean_ctor_set(x_250, 3, x_246);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_248);
x_251 = 0;
lean_ctor_set(x_2, 3, x_250);
lean_ctor_set(x_2, 2, x_242);
lean_ctor_set(x_2, 1, x_241);
lean_ctor_set(x_2, 0, x_249);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_251);
return x_2;
}
}
else
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_208);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; uint8_t x_256; 
x_253 = lean_ctor_get(x_208, 3);
lean_dec(x_253);
x_254 = lean_ctor_get(x_208, 0);
lean_dec(x_254);
x_255 = 0;
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_255);
x_256 = 1;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_256);
return x_2;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; uint8_t x_261; 
x_257 = lean_ctor_get(x_208, 1);
x_258 = lean_ctor_get(x_208, 2);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_208);
x_259 = 0;
x_260 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_260, 0, x_209);
lean_ctor_set(x_260, 1, x_257);
lean_ctor_set(x_260, 2, x_258);
lean_ctor_set(x_260, 3, x_210);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_259);
x_261 = 1;
lean_ctor_set(x_2, 3, x_260);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_261);
return x_2;
}
}
}
}
else
{
uint8_t x_262; 
x_262 = lean_ctor_get_uint8(x_209, sizeof(void*)*4);
if (x_262 == 0)
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_208);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_208, 0);
lean_dec(x_264);
x_265 = !lean_is_exclusive(x_209);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_271; 
x_266 = lean_ctor_get(x_209, 0);
x_267 = lean_ctor_get(x_209, 1);
x_268 = lean_ctor_get(x_209, 2);
x_269 = lean_ctor_get(x_209, 3);
x_270 = 1;
lean_ctor_set(x_209, 3, x_266);
lean_ctor_set(x_209, 2, x_38);
lean_ctor_set(x_209, 1, x_37);
lean_ctor_set(x_209, 0, x_36);
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_270);
lean_ctor_set(x_208, 0, x_269);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_270);
x_271 = 0;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set(x_2, 2, x_268);
lean_ctor_set(x_2, 1, x_267);
lean_ctor_set(x_2, 0, x_209);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_271);
return x_2;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; uint8_t x_278; 
x_272 = lean_ctor_get(x_209, 0);
x_273 = lean_ctor_get(x_209, 1);
x_274 = lean_ctor_get(x_209, 2);
x_275 = lean_ctor_get(x_209, 3);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_209);
x_276 = 1;
x_277 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_277, 0, x_36);
lean_ctor_set(x_277, 1, x_37);
lean_ctor_set(x_277, 2, x_38);
lean_ctor_set(x_277, 3, x_272);
lean_ctor_set_uint8(x_277, sizeof(void*)*4, x_276);
lean_ctor_set(x_208, 0, x_275);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_276);
x_278 = 0;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set(x_2, 2, x_274);
lean_ctor_set(x_2, 1, x_273);
lean_ctor_set(x_2, 0, x_277);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_278);
return x_2;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_279 = lean_ctor_get(x_208, 1);
x_280 = lean_ctor_get(x_208, 2);
x_281 = lean_ctor_get(x_208, 3);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_208);
x_282 = lean_ctor_get(x_209, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_209, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_209, 2);
lean_inc(x_284);
x_285 = lean_ctor_get(x_209, 3);
lean_inc(x_285);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 x_286 = x_209;
} else {
 lean_dec_ref(x_209);
 x_286 = lean_box(0);
}
x_287 = 1;
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(1, 4, 1);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_36);
lean_ctor_set(x_288, 1, x_37);
lean_ctor_set(x_288, 2, x_38);
lean_ctor_set(x_288, 3, x_282);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_287);
x_289 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_289, 0, x_285);
lean_ctor_set(x_289, 1, x_279);
lean_ctor_set(x_289, 2, x_280);
lean_ctor_set(x_289, 3, x_281);
lean_ctor_set_uint8(x_289, sizeof(void*)*4, x_287);
x_290 = 0;
lean_ctor_set(x_2, 3, x_289);
lean_ctor_set(x_2, 2, x_284);
lean_ctor_set(x_2, 1, x_283);
lean_ctor_set(x_2, 0, x_288);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_290);
return x_2;
}
}
else
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_208, 3);
lean_inc(x_291);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_208);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_296; 
x_293 = lean_ctor_get(x_208, 3);
lean_dec(x_293);
x_294 = lean_ctor_get(x_208, 0);
lean_dec(x_294);
x_295 = 0;
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_295);
x_296 = 1;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_296);
return x_2;
}
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; uint8_t x_301; 
x_297 = lean_ctor_get(x_208, 1);
x_298 = lean_ctor_get(x_208, 2);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_208);
x_299 = 0;
x_300 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_300, 0, x_209);
lean_ctor_set(x_300, 1, x_297);
lean_ctor_set(x_300, 2, x_298);
lean_ctor_set(x_300, 3, x_291);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_299);
x_301 = 1;
lean_ctor_set(x_2, 3, x_300);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_301);
return x_2;
}
}
else
{
uint8_t x_302; 
x_302 = lean_ctor_get_uint8(x_291, sizeof(void*)*4);
if (x_302 == 0)
{
uint8_t x_303; 
lean_free_object(x_2);
x_303 = !lean_is_exclusive(x_208);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_208, 3);
lean_dec(x_304);
x_305 = lean_ctor_get(x_208, 0);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_291);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; uint8_t x_312; 
x_307 = lean_ctor_get(x_291, 0);
x_308 = lean_ctor_get(x_291, 1);
x_309 = lean_ctor_get(x_291, 2);
x_310 = lean_ctor_get(x_291, 3);
x_311 = 1;
lean_inc(x_209);
lean_ctor_set(x_291, 3, x_209);
lean_ctor_set(x_291, 2, x_38);
lean_ctor_set(x_291, 1, x_37);
lean_ctor_set(x_291, 0, x_36);
x_312 = !lean_is_exclusive(x_209);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_209, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_209, 2);
lean_dec(x_314);
x_315 = lean_ctor_get(x_209, 1);
lean_dec(x_315);
x_316 = lean_ctor_get(x_209, 0);
lean_dec(x_316);
lean_ctor_set_uint8(x_291, sizeof(void*)*4, x_311);
lean_ctor_set(x_209, 3, x_310);
lean_ctor_set(x_209, 2, x_309);
lean_ctor_set(x_209, 1, x_308);
lean_ctor_set(x_209, 0, x_307);
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_311);
x_317 = 0;
lean_ctor_set(x_208, 3, x_209);
lean_ctor_set(x_208, 0, x_291);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_317);
return x_208;
}
else
{
lean_object* x_318; uint8_t x_319; 
lean_dec(x_209);
lean_ctor_set_uint8(x_291, sizeof(void*)*4, x_311);
x_318 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_318, 0, x_307);
lean_ctor_set(x_318, 1, x_308);
lean_ctor_set(x_318, 2, x_309);
lean_ctor_set(x_318, 3, x_310);
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_311);
x_319 = 0;
lean_ctor_set(x_208, 3, x_318);
lean_ctor_set(x_208, 0, x_291);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_319);
return x_208;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_320 = lean_ctor_get(x_291, 0);
x_321 = lean_ctor_get(x_291, 1);
x_322 = lean_ctor_get(x_291, 2);
x_323 = lean_ctor_get(x_291, 3);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_291);
x_324 = 1;
lean_inc(x_209);
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_36);
lean_ctor_set(x_325, 1, x_37);
lean_ctor_set(x_325, 2, x_38);
lean_ctor_set(x_325, 3, x_209);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 x_326 = x_209;
} else {
 lean_dec_ref(x_209);
 x_326 = lean_box(0);
}
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_324);
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 4, 1);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_320);
lean_ctor_set(x_327, 1, x_321);
lean_ctor_set(x_327, 2, x_322);
lean_ctor_set(x_327, 3, x_323);
lean_ctor_set_uint8(x_327, sizeof(void*)*4, x_324);
x_328 = 0;
lean_ctor_set(x_208, 3, x_327);
lean_ctor_set(x_208, 0, x_325);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_328);
return x_208;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; 
x_329 = lean_ctor_get(x_208, 1);
x_330 = lean_ctor_get(x_208, 2);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_208);
x_331 = lean_ctor_get(x_291, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_291, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_291, 2);
lean_inc(x_333);
x_334 = lean_ctor_get(x_291, 3);
lean_inc(x_334);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 lean_ctor_release(x_291, 3);
 x_335 = x_291;
} else {
 lean_dec_ref(x_291);
 x_335 = lean_box(0);
}
x_336 = 1;
lean_inc(x_209);
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(1, 4, 1);
} else {
 x_337 = x_335;
}
lean_ctor_set(x_337, 0, x_36);
lean_ctor_set(x_337, 1, x_37);
lean_ctor_set(x_337, 2, x_38);
lean_ctor_set(x_337, 3, x_209);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 x_338 = x_209;
} else {
 lean_dec_ref(x_209);
 x_338 = lean_box(0);
}
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 4, 1);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_331);
lean_ctor_set(x_339, 1, x_332);
lean_ctor_set(x_339, 2, x_333);
lean_ctor_set(x_339, 3, x_334);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_336);
x_340 = 0;
x_341 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_341, 0, x_337);
lean_ctor_set(x_341, 1, x_329);
lean_ctor_set(x_341, 2, x_330);
lean_ctor_set(x_341, 3, x_339);
lean_ctor_set_uint8(x_341, sizeof(void*)*4, x_340);
return x_341;
}
}
else
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_208);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_343 = lean_ctor_get(x_208, 3);
lean_dec(x_343);
x_344 = lean_ctor_get(x_208, 0);
lean_dec(x_344);
x_345 = !lean_is_exclusive(x_209);
if (x_345 == 0)
{
uint8_t x_346; uint8_t x_347; 
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_302);
x_346 = 0;
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_346);
x_347 = 1;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_347);
return x_2;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; uint8_t x_354; 
x_348 = lean_ctor_get(x_209, 0);
x_349 = lean_ctor_get(x_209, 1);
x_350 = lean_ctor_get(x_209, 2);
x_351 = lean_ctor_get(x_209, 3);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_209);
x_352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_352, 0, x_348);
lean_ctor_set(x_352, 1, x_349);
lean_ctor_set(x_352, 2, x_350);
lean_ctor_set(x_352, 3, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_302);
x_353 = 0;
lean_ctor_set(x_208, 0, x_352);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_353);
x_354 = 1;
lean_ctor_set(x_2, 3, x_208);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_354);
return x_2;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; uint8_t x_365; 
x_355 = lean_ctor_get(x_208, 1);
x_356 = lean_ctor_get(x_208, 2);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_208);
x_357 = lean_ctor_get(x_209, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_209, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_209, 2);
lean_inc(x_359);
x_360 = lean_ctor_get(x_209, 3);
lean_inc(x_360);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 x_361 = x_209;
} else {
 lean_dec_ref(x_209);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 4, 1);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_357);
lean_ctor_set(x_362, 1, x_358);
lean_ctor_set(x_362, 2, x_359);
lean_ctor_set(x_362, 3, x_360);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_302);
x_363 = 0;
x_364 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_355);
lean_ctor_set(x_364, 2, x_356);
lean_ctor_set(x_364, 3, x_291);
lean_ctor_set_uint8(x_364, sizeof(void*)*4, x_363);
x_365 = 1;
lean_ctor_set(x_2, 3, x_364);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_365);
return x_2;
}
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
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_366 = lean_ctor_get(x_2, 0);
x_367 = lean_ctor_get(x_2, 1);
x_368 = lean_ctor_get(x_2, 2);
x_369 = lean_ctor_get(x_2, 3);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_367);
lean_inc(x_3);
x_370 = lean_apply_2(x_1, x_3, x_367);
x_371 = lean_unbox(x_370);
lean_dec(x_370);
switch (x_371) {
case 0:
{
uint8_t x_372; 
x_372 = l_Std_RBNode_isRed___rarg(x_366);
if (x_372 == 0)
{
lean_object* x_373; uint8_t x_374; lean_object* x_375; 
x_373 = l_Std_RBNode_ins___rarg(x_1, x_366, x_3, x_4);
x_374 = 1;
x_375 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_367);
lean_ctor_set(x_375, 2, x_368);
lean_ctor_set(x_375, 3, x_369);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_374);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = l_Std_RBNode_ins___rarg(x_1, x_366, x_3, x_4);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_376, 3);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; 
x_379 = lean_ctor_get(x_376, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_376, 2);
lean_inc(x_380);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_381 = x_376;
} else {
 lean_dec_ref(x_376);
 x_381 = lean_box(0);
}
x_382 = 0;
if (lean_is_scalar(x_381)) {
 x_383 = lean_alloc_ctor(1, 4, 1);
} else {
 x_383 = x_381;
}
lean_ctor_set(x_383, 0, x_378);
lean_ctor_set(x_383, 1, x_379);
lean_ctor_set(x_383, 2, x_380);
lean_ctor_set(x_383, 3, x_378);
lean_ctor_set_uint8(x_383, sizeof(void*)*4, x_382);
x_384 = 1;
x_385 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_367);
lean_ctor_set(x_385, 2, x_368);
lean_ctor_set(x_385, 3, x_369);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
return x_385;
}
else
{
uint8_t x_386; 
x_386 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; 
x_387 = lean_ctor_get(x_376, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_376, 2);
lean_inc(x_388);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_389 = x_376;
} else {
 lean_dec_ref(x_376);
 x_389 = lean_box(0);
}
x_390 = lean_ctor_get(x_378, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_378, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_378, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_378, 3);
lean_inc(x_393);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_394 = x_378;
} else {
 lean_dec_ref(x_378);
 x_394 = lean_box(0);
}
x_395 = 1;
if (lean_is_scalar(x_394)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_394;
}
lean_ctor_set(x_396, 0, x_377);
lean_ctor_set(x_396, 1, x_387);
lean_ctor_set(x_396, 2, x_388);
lean_ctor_set(x_396, 3, x_390);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_395);
if (lean_is_scalar(x_389)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_389;
}
lean_ctor_set(x_397, 0, x_393);
lean_ctor_set(x_397, 1, x_367);
lean_ctor_set(x_397, 2, x_368);
lean_ctor_set(x_397, 3, x_369);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_395);
x_398 = 0;
x_399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_391);
lean_ctor_set(x_399, 2, x_392);
lean_ctor_set(x_399, 3, x_397);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; 
x_400 = lean_ctor_get(x_376, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_376, 2);
lean_inc(x_401);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_402 = x_376;
} else {
 lean_dec_ref(x_376);
 x_402 = lean_box(0);
}
x_403 = 0;
if (lean_is_scalar(x_402)) {
 x_404 = lean_alloc_ctor(1, 4, 1);
} else {
 x_404 = x_402;
}
lean_ctor_set(x_404, 0, x_377);
lean_ctor_set(x_404, 1, x_400);
lean_ctor_set(x_404, 2, x_401);
lean_ctor_set(x_404, 3, x_378);
lean_ctor_set_uint8(x_404, sizeof(void*)*4, x_403);
x_405 = 1;
x_406 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_367);
lean_ctor_set(x_406, 2, x_368);
lean_ctor_set(x_406, 3, x_369);
lean_ctor_set_uint8(x_406, sizeof(void*)*4, x_405);
return x_406;
}
}
}
else
{
uint8_t x_407; 
x_407 = lean_ctor_get_uint8(x_377, sizeof(void*)*4);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
x_408 = lean_ctor_get(x_376, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_376, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_376, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_411 = x_376;
} else {
 lean_dec_ref(x_376);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_377, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_377, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_377, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_377, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_416 = x_377;
} else {
 lean_dec_ref(x_377);
 x_416 = lean_box(0);
}
x_417 = 1;
if (lean_is_scalar(x_416)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_416;
}
lean_ctor_set(x_418, 0, x_412);
lean_ctor_set(x_418, 1, x_413);
lean_ctor_set(x_418, 2, x_414);
lean_ctor_set(x_418, 3, x_415);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_417);
if (lean_is_scalar(x_411)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_411;
}
lean_ctor_set(x_419, 0, x_410);
lean_ctor_set(x_419, 1, x_367);
lean_ctor_set(x_419, 2, x_368);
lean_ctor_set(x_419, 3, x_369);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_417);
x_420 = 0;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_408);
lean_ctor_set(x_421, 2, x_409);
lean_ctor_set(x_421, 3, x_419);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
else
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_376, 3);
lean_inc(x_422);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; 
x_423 = lean_ctor_get(x_376, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_376, 2);
lean_inc(x_424);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_425 = x_376;
} else {
 lean_dec_ref(x_376);
 x_425 = lean_box(0);
}
x_426 = 0;
if (lean_is_scalar(x_425)) {
 x_427 = lean_alloc_ctor(1, 4, 1);
} else {
 x_427 = x_425;
}
lean_ctor_set(x_427, 0, x_377);
lean_ctor_set(x_427, 1, x_423);
lean_ctor_set(x_427, 2, x_424);
lean_ctor_set(x_427, 3, x_422);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_426);
x_428 = 1;
x_429 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_367);
lean_ctor_set(x_429, 2, x_368);
lean_ctor_set(x_429, 3, x_369);
lean_ctor_set_uint8(x_429, sizeof(void*)*4, x_428);
return x_429;
}
else
{
uint8_t x_430; 
x_430 = lean_ctor_get_uint8(x_422, sizeof(void*)*4);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; 
x_431 = lean_ctor_get(x_376, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_376, 2);
lean_inc(x_432);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_433 = x_376;
} else {
 lean_dec_ref(x_376);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_422, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_422, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_422, 2);
lean_inc(x_436);
x_437 = lean_ctor_get(x_422, 3);
lean_inc(x_437);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 lean_ctor_release(x_422, 3);
 x_438 = x_422;
} else {
 lean_dec_ref(x_422);
 x_438 = lean_box(0);
}
x_439 = 1;
lean_inc(x_377);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(1, 4, 1);
} else {
 x_440 = x_438;
}
lean_ctor_set(x_440, 0, x_377);
lean_ctor_set(x_440, 1, x_431);
lean_ctor_set(x_440, 2, x_432);
lean_ctor_set(x_440, 3, x_434);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_441 = x_377;
} else {
 lean_dec_ref(x_377);
 x_441 = lean_box(0);
}
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_439);
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 4, 1);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_437);
lean_ctor_set(x_442, 1, x_367);
lean_ctor_set(x_442, 2, x_368);
lean_ctor_set(x_442, 3, x_369);
lean_ctor_set_uint8(x_442, sizeof(void*)*4, x_439);
x_443 = 0;
if (lean_is_scalar(x_433)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_433;
}
lean_ctor_set(x_444, 0, x_440);
lean_ctor_set(x_444, 1, x_435);
lean_ctor_set(x_444, 2, x_436);
lean_ctor_set(x_444, 3, x_442);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
return x_444;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; uint8_t x_456; lean_object* x_457; 
x_445 = lean_ctor_get(x_376, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_376, 2);
lean_inc(x_446);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_447 = x_376;
} else {
 lean_dec_ref(x_376);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_377, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_377, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_377, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_377, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_452 = x_377;
} else {
 lean_dec_ref(x_377);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_448);
lean_ctor_set(x_453, 1, x_449);
lean_ctor_set(x_453, 2, x_450);
lean_ctor_set(x_453, 3, x_451);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_430);
x_454 = 0;
if (lean_is_scalar(x_447)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_447;
}
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_445);
lean_ctor_set(x_455, 2, x_446);
lean_ctor_set(x_455, 3, x_422);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
x_456 = 1;
x_457 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_367);
lean_ctor_set(x_457, 2, x_368);
lean_ctor_set(x_457, 3, x_369);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_456);
return x_457;
}
}
}
}
}
}
case 1:
{
uint8_t x_458; lean_object* x_459; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_1);
x_458 = 1;
x_459 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_459, 0, x_366);
lean_ctor_set(x_459, 1, x_3);
lean_ctor_set(x_459, 2, x_4);
lean_ctor_set(x_459, 3, x_369);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
return x_459;
}
default: 
{
uint8_t x_460; 
x_460 = l_Std_RBNode_isRed___rarg(x_369);
if (x_460 == 0)
{
lean_object* x_461; uint8_t x_462; lean_object* x_463; 
x_461 = l_Std_RBNode_ins___rarg(x_1, x_369, x_3, x_4);
x_462 = 1;
x_463 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_463, 0, x_366);
lean_ctor_set(x_463, 1, x_367);
lean_ctor_set(x_463, 2, x_368);
lean_ctor_set(x_463, 3, x_461);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = l_Std_RBNode_ins___rarg(x_1, x_369, x_3, x_4);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_464, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; 
x_467 = lean_ctor_get(x_464, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_464, 2);
lean_inc(x_468);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_469 = x_464;
} else {
 lean_dec_ref(x_464);
 x_469 = lean_box(0);
}
x_470 = 0;
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(1, 4, 1);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_466);
lean_ctor_set(x_471, 1, x_467);
lean_ctor_set(x_471, 2, x_468);
lean_ctor_set(x_471, 3, x_466);
lean_ctor_set_uint8(x_471, sizeof(void*)*4, x_470);
x_472 = 1;
x_473 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_473, 0, x_366);
lean_ctor_set(x_473, 1, x_367);
lean_ctor_set(x_473, 2, x_368);
lean_ctor_set(x_473, 3, x_471);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_472);
return x_473;
}
else
{
uint8_t x_474; 
x_474 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; 
x_475 = lean_ctor_get(x_464, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_464, 2);
lean_inc(x_476);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_477 = x_464;
} else {
 lean_dec_ref(x_464);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_466, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_466, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_466, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_466, 3);
lean_inc(x_481);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_482 = x_466;
} else {
 lean_dec_ref(x_466);
 x_482 = lean_box(0);
}
x_483 = 1;
if (lean_is_scalar(x_482)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_482;
}
lean_ctor_set(x_484, 0, x_366);
lean_ctor_set(x_484, 1, x_367);
lean_ctor_set(x_484, 2, x_368);
lean_ctor_set(x_484, 3, x_465);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
if (lean_is_scalar(x_477)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_477;
}
lean_ctor_set(x_485, 0, x_478);
lean_ctor_set(x_485, 1, x_479);
lean_ctor_set(x_485, 2, x_480);
lean_ctor_set(x_485, 3, x_481);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_483);
x_486 = 0;
x_487 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_475);
lean_ctor_set(x_487, 2, x_476);
lean_ctor_set(x_487, 3, x_485);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
return x_487;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; 
x_488 = lean_ctor_get(x_464, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_464, 2);
lean_inc(x_489);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_490 = x_464;
} else {
 lean_dec_ref(x_464);
 x_490 = lean_box(0);
}
x_491 = 0;
if (lean_is_scalar(x_490)) {
 x_492 = lean_alloc_ctor(1, 4, 1);
} else {
 x_492 = x_490;
}
lean_ctor_set(x_492, 0, x_465);
lean_ctor_set(x_492, 1, x_488);
lean_ctor_set(x_492, 2, x_489);
lean_ctor_set(x_492, 3, x_466);
lean_ctor_set_uint8(x_492, sizeof(void*)*4, x_491);
x_493 = 1;
x_494 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_494, 0, x_366);
lean_ctor_set(x_494, 1, x_367);
lean_ctor_set(x_494, 2, x_368);
lean_ctor_set(x_494, 3, x_492);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_493);
return x_494;
}
}
}
else
{
uint8_t x_495; 
x_495 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; lean_object* x_509; 
x_496 = lean_ctor_get(x_464, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_464, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_464, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_499 = x_464;
} else {
 lean_dec_ref(x_464);
 x_499 = lean_box(0);
}
x_500 = lean_ctor_get(x_465, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_465, 1);
lean_inc(x_501);
x_502 = lean_ctor_get(x_465, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_465, 3);
lean_inc(x_503);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_504 = x_465;
} else {
 lean_dec_ref(x_465);
 x_504 = lean_box(0);
}
x_505 = 1;
if (lean_is_scalar(x_504)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_504;
}
lean_ctor_set(x_506, 0, x_366);
lean_ctor_set(x_506, 1, x_367);
lean_ctor_set(x_506, 2, x_368);
lean_ctor_set(x_506, 3, x_500);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_505);
if (lean_is_scalar(x_499)) {
 x_507 = lean_alloc_ctor(1, 4, 1);
} else {
 x_507 = x_499;
}
lean_ctor_set(x_507, 0, x_503);
lean_ctor_set(x_507, 1, x_496);
lean_ctor_set(x_507, 2, x_497);
lean_ctor_set(x_507, 3, x_498);
lean_ctor_set_uint8(x_507, sizeof(void*)*4, x_505);
x_508 = 0;
x_509 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_501);
lean_ctor_set(x_509, 2, x_502);
lean_ctor_set(x_509, 3, x_507);
lean_ctor_set_uint8(x_509, sizeof(void*)*4, x_508);
return x_509;
}
else
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_464, 3);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; lean_object* x_515; uint8_t x_516; lean_object* x_517; 
x_511 = lean_ctor_get(x_464, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_464, 2);
lean_inc(x_512);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_513 = x_464;
} else {
 lean_dec_ref(x_464);
 x_513 = lean_box(0);
}
x_514 = 0;
if (lean_is_scalar(x_513)) {
 x_515 = lean_alloc_ctor(1, 4, 1);
} else {
 x_515 = x_513;
}
lean_ctor_set(x_515, 0, x_465);
lean_ctor_set(x_515, 1, x_511);
lean_ctor_set(x_515, 2, x_512);
lean_ctor_set(x_515, 3, x_510);
lean_ctor_set_uint8(x_515, sizeof(void*)*4, x_514);
x_516 = 1;
x_517 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_517, 0, x_366);
lean_ctor_set(x_517, 1, x_367);
lean_ctor_set(x_517, 2, x_368);
lean_ctor_set(x_517, 3, x_515);
lean_ctor_set_uint8(x_517, sizeof(void*)*4, x_516);
return x_517;
}
else
{
uint8_t x_518; 
x_518 = lean_ctor_get_uint8(x_510, sizeof(void*)*4);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; 
x_519 = lean_ctor_get(x_464, 1);
lean_inc(x_519);
x_520 = lean_ctor_get(x_464, 2);
lean_inc(x_520);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_521 = x_464;
} else {
 lean_dec_ref(x_464);
 x_521 = lean_box(0);
}
x_522 = lean_ctor_get(x_510, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_510, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_510, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_510, 3);
lean_inc(x_525);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 lean_ctor_release(x_510, 2);
 lean_ctor_release(x_510, 3);
 x_526 = x_510;
} else {
 lean_dec_ref(x_510);
 x_526 = lean_box(0);
}
x_527 = 1;
lean_inc(x_465);
if (lean_is_scalar(x_526)) {
 x_528 = lean_alloc_ctor(1, 4, 1);
} else {
 x_528 = x_526;
}
lean_ctor_set(x_528, 0, x_366);
lean_ctor_set(x_528, 1, x_367);
lean_ctor_set(x_528, 2, x_368);
lean_ctor_set(x_528, 3, x_465);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_529 = x_465;
} else {
 lean_dec_ref(x_465);
 x_529 = lean_box(0);
}
lean_ctor_set_uint8(x_528, sizeof(void*)*4, x_527);
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 4, 1);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_522);
lean_ctor_set(x_530, 1, x_523);
lean_ctor_set(x_530, 2, x_524);
lean_ctor_set(x_530, 3, x_525);
lean_ctor_set_uint8(x_530, sizeof(void*)*4, x_527);
x_531 = 0;
if (lean_is_scalar(x_521)) {
 x_532 = lean_alloc_ctor(1, 4, 1);
} else {
 x_532 = x_521;
}
lean_ctor_set(x_532, 0, x_528);
lean_ctor_set(x_532, 1, x_519);
lean_ctor_set(x_532, 2, x_520);
lean_ctor_set(x_532, 3, x_530);
lean_ctor_set_uint8(x_532, sizeof(void*)*4, x_531);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; 
x_533 = lean_ctor_get(x_464, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_464, 2);
lean_inc(x_534);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_535 = x_464;
} else {
 lean_dec_ref(x_464);
 x_535 = lean_box(0);
}
x_536 = lean_ctor_get(x_465, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_465, 1);
lean_inc(x_537);
x_538 = lean_ctor_get(x_465, 2);
lean_inc(x_538);
x_539 = lean_ctor_get(x_465, 3);
lean_inc(x_539);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_540 = x_465;
} else {
 lean_dec_ref(x_465);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(1, 4, 1);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_536);
lean_ctor_set(x_541, 1, x_537);
lean_ctor_set(x_541, 2, x_538);
lean_ctor_set(x_541, 3, x_539);
lean_ctor_set_uint8(x_541, sizeof(void*)*4, x_518);
x_542 = 0;
if (lean_is_scalar(x_535)) {
 x_543 = lean_alloc_ctor(1, 4, 1);
} else {
 x_543 = x_535;
}
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_533);
lean_ctor_set(x_543, 2, x_534);
lean_ctor_set(x_543, 3, x_510);
lean_ctor_set_uint8(x_543, sizeof(void*)*4, x_542);
x_544 = 1;
x_545 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_545, 0, x_366);
lean_ctor_set(x_545, 1, x_367);
lean_ctor_set(x_545, 2, x_368);
lean_ctor_set(x_545, 3, x_543);
lean_ctor_set_uint8(x_545, sizeof(void*)*4, x_544);
return x_545;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_ins___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_setBlack___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_setBlack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_setBlack___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_RBNode_isRed___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Std_RBNode_ins___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_RBNode_ins___rarg(x_1, x_2, x_3, x_4);
x_8 = l_Std_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_insert___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balance_u2083___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_4);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*4);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 2);
x_22 = lean_ctor_get(x_9, 3);
x_23 = 1;
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_23);
lean_ctor_set(x_4, 3, x_22);
lean_ctor_set(x_4, 2, x_21);
lean_ctor_set(x_4, 1, x_20);
lean_ctor_set(x_4, 0, x_19);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_23);
x_24 = 0;
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_4);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
x_28 = lean_ctor_get(x_9, 2);
x_29 = lean_ctor_get(x_9, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_30 = 1;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_3);
lean_ctor_set(x_31, 3, x_8);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
lean_ctor_set(x_4, 3, x_29);
lean_ctor_set(x_4, 2, x_28);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_26);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_15);
lean_ctor_set(x_33, 3, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_4, 1);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 3);
lean_inc(x_39);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_40 = x_9;
} else {
 lean_dec_ref(x_9);
 x_40 = lean_box(0);
}
x_41 = 1;
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 4, 1);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set(x_42, 3, x_8);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_41);
x_43 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_41);
x_44 = 0;
x_45 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_9);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_9, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_9, 2);
lean_dec(x_48);
x_49 = lean_ctor_get(x_9, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_9, 0);
lean_dec(x_50);
x_51 = 1;
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_51);
return x_9;
}
else
{
uint8_t x_52; lean_object* x_53; 
lean_dec(x_9);
x_52 = 1;
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_2);
lean_ctor_set(x_53, 2, x_3);
lean_ctor_set(x_53, 3, x_4);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_4, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_4);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_4, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_4, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_8);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_8, 0);
x_61 = lean_ctor_get(x_8, 1);
x_62 = lean_ctor_get(x_8, 2);
x_63 = lean_ctor_get(x_8, 3);
x_64 = 1;
lean_ctor_set(x_8, 3, x_60);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_64);
lean_ctor_set(x_4, 0, x_63);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_64);
x_65 = 0;
x_66 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_66, 0, x_8);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_4);
lean_ctor_set_uint8(x_66, sizeof(void*)*4, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_8, 0);
x_68 = lean_ctor_get(x_8, 1);
x_69 = lean_ctor_get(x_8, 2);
x_70 = lean_ctor_get(x_8, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_8);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 2, x_3);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_4, 0, x_70);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_71);
x_73 = 0;
x_74 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_4);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_73);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_4, 1);
x_76 = lean_ctor_get(x_4, 2);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_4);
x_77 = lean_ctor_get(x_8, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_8, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_8, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_8, 3);
lean_inc(x_80);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_81 = x_8;
} else {
 lean_dec_ref(x_8);
 x_81 = lean_box(0);
}
x_82 = 1;
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(1, 4, 1);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
lean_ctor_set(x_83, 2, x_3);
lean_ctor_set(x_83, 3, x_77);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_55);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_82);
x_85 = 0;
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_79);
lean_ctor_set(x_86, 3, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_4);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_4, 1);
x_90 = lean_ctor_get(x_4, 2);
x_91 = lean_ctor_get(x_4, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_55);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_8, 0);
x_96 = lean_ctor_get(x_8, 1);
x_97 = lean_ctor_get(x_8, 2);
x_98 = lean_ctor_get(x_8, 3);
x_99 = lean_ctor_get(x_55, 0);
x_100 = lean_ctor_get(x_55, 1);
x_101 = lean_ctor_get(x_55, 2);
x_102 = lean_ctor_get(x_55, 3);
lean_ctor_set(x_55, 3, x_98);
lean_ctor_set(x_55, 2, x_97);
lean_ctor_set(x_55, 1, x_96);
lean_ctor_set(x_55, 0, x_95);
x_103 = 1;
lean_ctor_set(x_8, 3, x_55);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_103);
lean_ctor_set(x_4, 3, x_102);
lean_ctor_set(x_4, 2, x_101);
lean_ctor_set(x_4, 1, x_100);
lean_ctor_set(x_4, 0, x_99);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_103);
x_104 = 0;
x_105 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_105, 0, x_8);
lean_ctor_set(x_105, 1, x_89);
lean_ctor_set(x_105, 2, x_90);
lean_ctor_set(x_105, 3, x_4);
lean_ctor_set_uint8(x_105, sizeof(void*)*4, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; 
x_106 = lean_ctor_get(x_8, 0);
x_107 = lean_ctor_get(x_8, 1);
x_108 = lean_ctor_get(x_8, 2);
x_109 = lean_ctor_get(x_8, 3);
x_110 = lean_ctor_get(x_55, 0);
x_111 = lean_ctor_get(x_55, 1);
x_112 = lean_ctor_get(x_55, 2);
x_113 = lean_ctor_get(x_55, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_55);
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_87);
x_115 = 1;
lean_ctor_set(x_8, 3, x_114);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_115);
lean_ctor_set(x_4, 3, x_113);
lean_ctor_set(x_4, 2, x_112);
lean_ctor_set(x_4, 1, x_111);
lean_ctor_set(x_4, 0, x_110);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_115);
x_116 = 0;
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_8);
lean_ctor_set(x_117, 1, x_89);
lean_ctor_set(x_117, 2, x_90);
lean_ctor_set(x_117, 3, x_4);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; 
x_118 = lean_ctor_get(x_8, 0);
x_119 = lean_ctor_get(x_8, 1);
x_120 = lean_ctor_get(x_8, 2);
x_121 = lean_ctor_get(x_8, 3);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_8);
x_122 = lean_ctor_get(x_55, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_55, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_55, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_55, 3);
lean_inc(x_125);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_126 = x_55;
} else {
 lean_dec_ref(x_55);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 4, 1);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_87);
x_128 = 1;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 2, x_3);
lean_ctor_set(x_129, 3, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_4, 3, x_125);
lean_ctor_set(x_4, 2, x_124);
lean_ctor_set(x_4, 1, x_123);
lean_ctor_set(x_4, 0, x_122);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_128);
x_130 = 0;
x_131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_89);
lean_ctor_set(x_131, 2, x_90);
lean_ctor_set(x_131, 3, x_4);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_132 = lean_ctor_get(x_4, 1);
x_133 = lean_ctor_get(x_4, 2);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_4);
x_134 = lean_ctor_get(x_8, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_8, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_8, 3);
lean_inc(x_137);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_138 = x_8;
} else {
 lean_dec_ref(x_8);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_55, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_55, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_55, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_55, 3);
lean_inc(x_142);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_143 = x_55;
} else {
 lean_dec_ref(x_55);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 4, 1);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_135);
lean_ctor_set(x_144, 2, x_136);
lean_ctor_set(x_144, 3, x_137);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_87);
x_145 = 1;
if (lean_is_scalar(x_138)) {
 x_146 = lean_alloc_ctor(1, 4, 1);
} else {
 x_146 = x_138;
}
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_2);
lean_ctor_set(x_146, 2, x_3);
lean_ctor_set(x_146, 3, x_144);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_145);
x_147 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_147, 0, x_139);
lean_ctor_set(x_147, 1, x_140);
lean_ctor_set(x_147, 2, x_141);
lean_ctor_set(x_147, 3, x_142);
lean_ctor_set_uint8(x_147, sizeof(void*)*4, x_145);
x_148 = 0;
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_132);
lean_ctor_set(x_149, 2, x_133);
lean_ctor_set(x_149, 3, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_148);
return x_149;
}
}
else
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_4);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_4, 3);
lean_dec(x_151);
x_152 = lean_ctor_get(x_4, 0);
lean_dec(x_152);
x_153 = !lean_is_exclusive(x_8);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_8, 0);
x_155 = lean_ctor_get(x_8, 1);
x_156 = lean_ctor_get(x_8, 2);
x_157 = lean_ctor_get(x_8, 3);
x_158 = 1;
lean_ctor_set(x_8, 3, x_154);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_158);
lean_ctor_set(x_4, 0, x_157);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_158);
x_159 = 0;
x_160 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_160, 0, x_8);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set(x_160, 2, x_156);
lean_ctor_set(x_160, 3, x_4);
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_8, 0);
x_162 = lean_ctor_get(x_8, 1);
x_163 = lean_ctor_get(x_8, 2);
x_164 = lean_ctor_get(x_8, 3);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_8);
x_165 = 1;
x_166 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_2);
lean_ctor_set(x_166, 2, x_3);
lean_ctor_set(x_166, 3, x_161);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_165);
lean_ctor_set(x_4, 0, x_164);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_165);
x_167 = 0;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_4);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_169 = lean_ctor_get(x_4, 1);
x_170 = lean_ctor_get(x_4, 2);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_4);
x_171 = lean_ctor_get(x_8, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_8, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_8, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_8, 3);
lean_inc(x_174);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_175 = x_8;
} else {
 lean_dec_ref(x_8);
 x_175 = lean_box(0);
}
x_176 = 1;
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(1, 4, 1);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_1);
lean_ctor_set(x_177, 1, x_2);
lean_ctor_set(x_177, 2, x_3);
lean_ctor_set(x_177, 3, x_171);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_170);
lean_ctor_set(x_178, 3, x_55);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_176);
x_179 = 0;
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_172);
lean_ctor_set(x_180, 2, x_173);
lean_ctor_set(x_180, 3, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
return x_180;
}
}
}
}
else
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_4, 3);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_8);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_8, 3);
lean_dec(x_183);
x_184 = lean_ctor_get(x_8, 2);
lean_dec(x_184);
x_185 = lean_ctor_get(x_8, 1);
lean_dec(x_185);
x_186 = lean_ctor_get(x_8, 0);
lean_dec(x_186);
x_187 = 1;
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_187);
return x_8;
}
else
{
uint8_t x_188; lean_object* x_189; 
lean_dec(x_8);
x_188 = 1;
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_189, 1, x_2);
lean_ctor_set(x_189, 2, x_3);
lean_ctor_set(x_189, 3, x_4);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_188);
return x_189;
}
}
else
{
uint8_t x_190; 
x_190 = lean_ctor_get_uint8(x_181, sizeof(void*)*4);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_4);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_4, 3);
lean_dec(x_192);
x_193 = lean_ctor_get(x_4, 0);
lean_dec(x_193);
x_194 = !lean_is_exclusive(x_181);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; 
x_195 = lean_ctor_get(x_181, 0);
x_196 = lean_ctor_get(x_181, 1);
x_197 = lean_ctor_get(x_181, 2);
x_198 = lean_ctor_get(x_181, 3);
x_199 = 1;
lean_inc(x_8);
lean_ctor_set(x_181, 3, x_8);
lean_ctor_set(x_181, 2, x_3);
lean_ctor_set(x_181, 1, x_2);
lean_ctor_set(x_181, 0, x_1);
x_200 = !lean_is_exclusive(x_8);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_8, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_8, 2);
lean_dec(x_202);
x_203 = lean_ctor_get(x_8, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_8, 0);
lean_dec(x_204);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_199);
lean_ctor_set(x_8, 3, x_198);
lean_ctor_set(x_8, 2, x_197);
lean_ctor_set(x_8, 1, x_196);
lean_ctor_set(x_8, 0, x_195);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_199);
x_205 = 0;
lean_ctor_set(x_4, 3, x_8);
lean_ctor_set(x_4, 0, x_181);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_205);
return x_4;
}
else
{
lean_object* x_206; uint8_t x_207; 
lean_dec(x_8);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_199);
x_206 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_206, 0, x_195);
lean_ctor_set(x_206, 1, x_196);
lean_ctor_set(x_206, 2, x_197);
lean_ctor_set(x_206, 3, x_198);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_199);
x_207 = 0;
lean_ctor_set(x_4, 3, x_206);
lean_ctor_set(x_4, 0, x_181);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_207);
return x_4;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_208 = lean_ctor_get(x_181, 0);
x_209 = lean_ctor_get(x_181, 1);
x_210 = lean_ctor_get(x_181, 2);
x_211 = lean_ctor_get(x_181, 3);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_181);
x_212 = 1;
lean_inc(x_8);
x_213 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_213, 0, x_1);
lean_ctor_set(x_213, 1, x_2);
lean_ctor_set(x_213, 2, x_3);
lean_ctor_set(x_213, 3, x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_214 = x_8;
} else {
 lean_dec_ref(x_8);
 x_214 = lean_box(0);
}
lean_ctor_set_uint8(x_213, sizeof(void*)*4, x_212);
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 4, 1);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_209);
lean_ctor_set(x_215, 2, x_210);
lean_ctor_set(x_215, 3, x_211);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_212);
x_216 = 0;
lean_ctor_set(x_4, 3, x_215);
lean_ctor_set(x_4, 0, x_213);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_216);
return x_4;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; 
x_217 = lean_ctor_get(x_4, 1);
x_218 = lean_ctor_get(x_4, 2);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_4);
x_219 = lean_ctor_get(x_181, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_181, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_181, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_181, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 x_223 = x_181;
} else {
 lean_dec_ref(x_181);
 x_223 = lean_box(0);
}
x_224 = 1;
lean_inc(x_8);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_1);
lean_ctor_set(x_225, 1, x_2);
lean_ctor_set(x_225, 2, x_3);
lean_ctor_set(x_225, 3, x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_226 = x_8;
} else {
 lean_dec_ref(x_8);
 x_226 = lean_box(0);
}
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_224);
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 4, 1);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_220);
lean_ctor_set(x_227, 2, x_221);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_224);
x_228 = 0;
x_229 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_217);
lean_ctor_set(x_229, 2, x_218);
lean_ctor_set(x_229, 3, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*4, x_228);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_8);
x_230 = !lean_is_exclusive(x_181);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_181, 3);
lean_dec(x_231);
x_232 = lean_ctor_get(x_181, 2);
lean_dec(x_232);
x_233 = lean_ctor_get(x_181, 1);
lean_dec(x_233);
x_234 = lean_ctor_get(x_181, 0);
lean_dec(x_234);
x_235 = 1;
lean_ctor_set(x_181, 3, x_4);
lean_ctor_set(x_181, 2, x_3);
lean_ctor_set(x_181, 1, x_2);
lean_ctor_set(x_181, 0, x_1);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_235);
return x_181;
}
else
{
uint8_t x_236; lean_object* x_237; 
lean_dec(x_181);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_1);
lean_ctor_set(x_237, 1, x_2);
lean_ctor_set(x_237, 2, x_3);
lean_ctor_set(x_237, 3, x_4);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
return x_237;
}
}
}
}
}
}
else
{
uint8_t x_238; lean_object* x_239; 
x_238 = 1;
x_239 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_239, 0, x_1);
lean_ctor_set(x_239, 1, x_2);
lean_ctor_set(x_239, 2, x_3);
lean_ctor_set(x_239, 3, x_4);
lean_ctor_set_uint8(x_239, sizeof(void*)*4, x_238);
return x_239;
}
}
}
else
{
uint8_t x_240; 
x_240 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_240 == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_1, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_1, 3);
lean_inc(x_242);
if (lean_obj_tag(x_242) == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_1);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_1, 3);
lean_dec(x_244);
x_245 = lean_ctor_get(x_1, 0);
lean_dec(x_245);
lean_ctor_set(x_1, 0, x_242);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_246; lean_object* x_247; 
x_246 = 1;
x_247 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_247, 0, x_1);
lean_ctor_set(x_247, 1, x_2);
lean_ctor_set(x_247, 2, x_3);
lean_ctor_set(x_247, 3, x_4);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
return x_247;
}
else
{
uint8_t x_248; 
x_248 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_4, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_4, 3);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; lean_object* x_252; 
x_251 = 1;
x_252 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_252, 0, x_1);
lean_ctor_set(x_252, 1, x_2);
lean_ctor_set(x_252, 2, x_3);
lean_ctor_set(x_252, 3, x_4);
lean_ctor_set_uint8(x_252, sizeof(void*)*4, x_251);
return x_252;
}
else
{
uint8_t x_253; 
x_253 = lean_ctor_get_uint8(x_250, sizeof(void*)*4);
if (x_253 == 0)
{
uint8_t x_254; 
x_254 = !lean_is_exclusive(x_4);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_4, 1);
x_256 = lean_ctor_get(x_4, 2);
x_257 = lean_ctor_get(x_4, 3);
lean_dec(x_257);
x_258 = lean_ctor_get(x_4, 0);
lean_dec(x_258);
x_259 = !lean_is_exclusive(x_250);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_250, 0);
x_261 = lean_ctor_get(x_250, 1);
x_262 = lean_ctor_get(x_250, 2);
x_263 = lean_ctor_get(x_250, 3);
x_264 = 1;
lean_ctor_set(x_250, 3, x_249);
lean_ctor_set(x_250, 2, x_3);
lean_ctor_set(x_250, 1, x_2);
lean_ctor_set(x_250, 0, x_1);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_264);
lean_ctor_set(x_4, 3, x_263);
lean_ctor_set(x_4, 2, x_262);
lean_ctor_set(x_4, 1, x_261);
lean_ctor_set(x_4, 0, x_260);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_264);
x_265 = 0;
x_266 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_266, 0, x_250);
lean_ctor_set(x_266, 1, x_255);
lean_ctor_set(x_266, 2, x_256);
lean_ctor_set(x_266, 3, x_4);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_250, 0);
x_268 = lean_ctor_get(x_250, 1);
x_269 = lean_ctor_get(x_250, 2);
x_270 = lean_ctor_get(x_250, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_250);
x_271 = 1;
x_272 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_272, 0, x_1);
lean_ctor_set(x_272, 1, x_2);
lean_ctor_set(x_272, 2, x_3);
lean_ctor_set(x_272, 3, x_249);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_271);
lean_ctor_set(x_4, 3, x_270);
lean_ctor_set(x_4, 2, x_269);
lean_ctor_set(x_4, 1, x_268);
lean_ctor_set(x_4, 0, x_267);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_271);
x_273 = 0;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_255);
lean_ctor_set(x_274, 2, x_256);
lean_ctor_set(x_274, 3, x_4);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; 
x_275 = lean_ctor_get(x_4, 1);
x_276 = lean_ctor_get(x_4, 2);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_4);
x_277 = lean_ctor_get(x_250, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_250, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_250, 2);
lean_inc(x_279);
x_280 = lean_ctor_get(x_250, 3);
lean_inc(x_280);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 x_281 = x_250;
} else {
 lean_dec_ref(x_250);
 x_281 = lean_box(0);
}
x_282 = 1;
if (lean_is_scalar(x_281)) {
 x_283 = lean_alloc_ctor(1, 4, 1);
} else {
 x_283 = x_281;
}
lean_ctor_set(x_283, 0, x_1);
lean_ctor_set(x_283, 1, x_2);
lean_ctor_set(x_283, 2, x_3);
lean_ctor_set(x_283, 3, x_249);
lean_ctor_set_uint8(x_283, sizeof(void*)*4, x_282);
x_284 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set(x_284, 1, x_278);
lean_ctor_set(x_284, 2, x_279);
lean_ctor_set(x_284, 3, x_280);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_282);
x_285 = 0;
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_275);
lean_ctor_set(x_286, 2, x_276);
lean_ctor_set(x_286, 3, x_284);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_285);
return x_286;
}
}
else
{
uint8_t x_287; 
x_287 = !lean_is_exclusive(x_250);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_288 = lean_ctor_get(x_250, 3);
lean_dec(x_288);
x_289 = lean_ctor_get(x_250, 2);
lean_dec(x_289);
x_290 = lean_ctor_get(x_250, 1);
lean_dec(x_290);
x_291 = lean_ctor_get(x_250, 0);
lean_dec(x_291);
x_292 = 1;
lean_ctor_set(x_250, 3, x_4);
lean_ctor_set(x_250, 2, x_3);
lean_ctor_set(x_250, 1, x_2);
lean_ctor_set(x_250, 0, x_1);
lean_ctor_set_uint8(x_250, sizeof(void*)*4, x_292);
return x_250;
}
else
{
uint8_t x_293; lean_object* x_294; 
lean_dec(x_250);
x_293 = 1;
x_294 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_294, 0, x_1);
lean_ctor_set(x_294, 1, x_2);
lean_ctor_set(x_294, 2, x_3);
lean_ctor_set(x_294, 3, x_4);
lean_ctor_set_uint8(x_294, sizeof(void*)*4, x_293);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
x_295 = lean_ctor_get_uint8(x_249, sizeof(void*)*4);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_4, 3);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_4);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_ctor_get(x_4, 3);
lean_dec(x_298);
x_299 = lean_ctor_get(x_4, 0);
lean_dec(x_299);
x_300 = !lean_is_exclusive(x_249);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_306; lean_object* x_307; 
x_301 = lean_ctor_get(x_249, 0);
x_302 = lean_ctor_get(x_249, 1);
x_303 = lean_ctor_get(x_249, 2);
x_304 = lean_ctor_get(x_249, 3);
x_305 = 1;
lean_ctor_set(x_249, 3, x_301);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 1, x_2);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_305);
lean_ctor_set(x_4, 0, x_304);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_305);
x_306 = 0;
x_307 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_307, 0, x_249);
lean_ctor_set(x_307, 1, x_302);
lean_ctor_set(x_307, 2, x_303);
lean_ctor_set(x_307, 3, x_4);
lean_ctor_set_uint8(x_307, sizeof(void*)*4, x_306);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; 
x_308 = lean_ctor_get(x_249, 0);
x_309 = lean_ctor_get(x_249, 1);
x_310 = lean_ctor_get(x_249, 2);
x_311 = lean_ctor_get(x_249, 3);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_249);
x_312 = 1;
x_313 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_313, 0, x_1);
lean_ctor_set(x_313, 1, x_2);
lean_ctor_set(x_313, 2, x_3);
lean_ctor_set(x_313, 3, x_308);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_312);
lean_ctor_set(x_4, 0, x_311);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_312);
x_314 = 0;
x_315 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_309);
lean_ctor_set(x_315, 2, x_310);
lean_ctor_set(x_315, 3, x_4);
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
return x_315;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; 
x_316 = lean_ctor_get(x_4, 1);
x_317 = lean_ctor_get(x_4, 2);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_4);
x_318 = lean_ctor_get(x_249, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_249, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_249, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_249, 3);
lean_inc(x_321);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 x_322 = x_249;
} else {
 lean_dec_ref(x_249);
 x_322 = lean_box(0);
}
x_323 = 1;
if (lean_is_scalar(x_322)) {
 x_324 = lean_alloc_ctor(1, 4, 1);
} else {
 x_324 = x_322;
}
lean_ctor_set(x_324, 0, x_1);
lean_ctor_set(x_324, 1, x_2);
lean_ctor_set(x_324, 2, x_3);
lean_ctor_set(x_324, 3, x_318);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_321);
lean_ctor_set(x_325, 1, x_316);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_296);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_323);
x_326 = 0;
x_327 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_319);
lean_ctor_set(x_327, 2, x_320);
lean_ctor_set(x_327, 3, x_325);
lean_ctor_set_uint8(x_327, sizeof(void*)*4, x_326);
return x_327;
}
}
else
{
uint8_t x_328; 
x_328 = lean_ctor_get_uint8(x_296, sizeof(void*)*4);
if (x_328 == 0)
{
uint8_t x_329; 
x_329 = !lean_is_exclusive(x_4);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_330 = lean_ctor_get(x_4, 1);
x_331 = lean_ctor_get(x_4, 2);
x_332 = lean_ctor_get(x_4, 3);
lean_dec(x_332);
x_333 = lean_ctor_get(x_4, 0);
lean_dec(x_333);
x_334 = !lean_is_exclusive(x_249);
if (x_334 == 0)
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_296);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; 
x_336 = lean_ctor_get(x_249, 0);
x_337 = lean_ctor_get(x_249, 1);
x_338 = lean_ctor_get(x_249, 2);
x_339 = lean_ctor_get(x_249, 3);
x_340 = lean_ctor_get(x_296, 0);
x_341 = lean_ctor_get(x_296, 1);
x_342 = lean_ctor_get(x_296, 2);
x_343 = lean_ctor_get(x_296, 3);
lean_ctor_set(x_296, 3, x_339);
lean_ctor_set(x_296, 2, x_338);
lean_ctor_set(x_296, 1, x_337);
lean_ctor_set(x_296, 0, x_336);
x_344 = 1;
lean_ctor_set(x_249, 3, x_296);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 1, x_2);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_344);
lean_ctor_set(x_4, 3, x_343);
lean_ctor_set(x_4, 2, x_342);
lean_ctor_set(x_4, 1, x_341);
lean_ctor_set(x_4, 0, x_340);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_344);
x_345 = 0;
x_346 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_346, 0, x_249);
lean_ctor_set(x_346, 1, x_330);
lean_ctor_set(x_346, 2, x_331);
lean_ctor_set(x_346, 3, x_4);
lean_ctor_set_uint8(x_346, sizeof(void*)*4, x_345);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; uint8_t x_357; lean_object* x_358; 
x_347 = lean_ctor_get(x_249, 0);
x_348 = lean_ctor_get(x_249, 1);
x_349 = lean_ctor_get(x_249, 2);
x_350 = lean_ctor_get(x_249, 3);
x_351 = lean_ctor_get(x_296, 0);
x_352 = lean_ctor_get(x_296, 1);
x_353 = lean_ctor_get(x_296, 2);
x_354 = lean_ctor_get(x_296, 3);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_296);
x_355 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_355, 0, x_347);
lean_ctor_set(x_355, 1, x_348);
lean_ctor_set(x_355, 2, x_349);
lean_ctor_set(x_355, 3, x_350);
lean_ctor_set_uint8(x_355, sizeof(void*)*4, x_328);
x_356 = 1;
lean_ctor_set(x_249, 3, x_355);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 1, x_2);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_356);
lean_ctor_set(x_4, 3, x_354);
lean_ctor_set(x_4, 2, x_353);
lean_ctor_set(x_4, 1, x_352);
lean_ctor_set(x_4, 0, x_351);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_356);
x_357 = 0;
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_249);
lean_ctor_set(x_358, 1, x_330);
lean_ctor_set(x_358, 2, x_331);
lean_ctor_set(x_358, 3, x_4);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; 
x_359 = lean_ctor_get(x_249, 0);
x_360 = lean_ctor_get(x_249, 1);
x_361 = lean_ctor_get(x_249, 2);
x_362 = lean_ctor_get(x_249, 3);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_249);
x_363 = lean_ctor_get(x_296, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_296, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_296, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_296, 3);
lean_inc(x_366);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 lean_ctor_release(x_296, 2);
 lean_ctor_release(x_296, 3);
 x_367 = x_296;
} else {
 lean_dec_ref(x_296);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_359);
lean_ctor_set(x_368, 1, x_360);
lean_ctor_set(x_368, 2, x_361);
lean_ctor_set(x_368, 3, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_328);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_1);
lean_ctor_set(x_370, 1, x_2);
lean_ctor_set(x_370, 2, x_3);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
lean_ctor_set(x_4, 3, x_366);
lean_ctor_set(x_4, 2, x_365);
lean_ctor_set(x_4, 1, x_364);
lean_ctor_set(x_4, 0, x_363);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_369);
x_371 = 0;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_330);
lean_ctor_set(x_372, 2, x_331);
lean_ctor_set(x_372, 3, x_4);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; 
x_373 = lean_ctor_get(x_4, 1);
x_374 = lean_ctor_get(x_4, 2);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_4);
x_375 = lean_ctor_get(x_249, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_249, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_249, 2);
lean_inc(x_377);
x_378 = lean_ctor_get(x_249, 3);
lean_inc(x_378);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 x_379 = x_249;
} else {
 lean_dec_ref(x_249);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_296, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_296, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_296, 2);
lean_inc(x_382);
x_383 = lean_ctor_get(x_296, 3);
lean_inc(x_383);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 lean_ctor_release(x_296, 2);
 lean_ctor_release(x_296, 3);
 x_384 = x_296;
} else {
 lean_dec_ref(x_296);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_375);
lean_ctor_set(x_385, 1, x_376);
lean_ctor_set(x_385, 2, x_377);
lean_ctor_set(x_385, 3, x_378);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_328);
x_386 = 1;
if (lean_is_scalar(x_379)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_379;
}
lean_ctor_set(x_387, 0, x_1);
lean_ctor_set(x_387, 1, x_2);
lean_ctor_set(x_387, 2, x_3);
lean_ctor_set(x_387, 3, x_385);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_386);
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_380);
lean_ctor_set(x_388, 1, x_381);
lean_ctor_set(x_388, 2, x_382);
lean_ctor_set(x_388, 3, x_383);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_386);
x_389 = 0;
x_390 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_373);
lean_ctor_set(x_390, 2, x_374);
lean_ctor_set(x_390, 3, x_388);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_389);
return x_390;
}
}
else
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_4);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_392 = lean_ctor_get(x_4, 3);
lean_dec(x_392);
x_393 = lean_ctor_get(x_4, 0);
lean_dec(x_393);
x_394 = !lean_is_exclusive(x_249);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_249, 0);
x_396 = lean_ctor_get(x_249, 1);
x_397 = lean_ctor_get(x_249, 2);
x_398 = lean_ctor_get(x_249, 3);
x_399 = 1;
lean_ctor_set(x_249, 3, x_395);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 1, x_2);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_399);
lean_ctor_set(x_4, 0, x_398);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_399);
x_400 = 0;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_249);
lean_ctor_set(x_401, 1, x_396);
lean_ctor_set(x_401, 2, x_397);
lean_ctor_set(x_401, 3, x_4);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; 
x_402 = lean_ctor_get(x_249, 0);
x_403 = lean_ctor_get(x_249, 1);
x_404 = lean_ctor_get(x_249, 2);
x_405 = lean_ctor_get(x_249, 3);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_249);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_1);
lean_ctor_set(x_407, 1, x_2);
lean_ctor_set(x_407, 2, x_3);
lean_ctor_set(x_407, 3, x_402);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
lean_ctor_set(x_4, 0, x_405);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_406);
x_408 = 0;
x_409 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_403);
lean_ctor_set(x_409, 2, x_404);
lean_ctor_set(x_409, 3, x_4);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_408);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
x_410 = lean_ctor_get(x_4, 1);
x_411 = lean_ctor_get(x_4, 2);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_4);
x_412 = lean_ctor_get(x_249, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_249, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_249, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_249, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 x_416 = x_249;
} else {
 lean_dec_ref(x_249);
 x_416 = lean_box(0);
}
x_417 = 1;
if (lean_is_scalar(x_416)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_416;
}
lean_ctor_set(x_418, 0, x_1);
lean_ctor_set(x_418, 1, x_2);
lean_ctor_set(x_418, 2, x_3);
lean_ctor_set(x_418, 3, x_412);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_417);
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_415);
lean_ctor_set(x_419, 1, x_410);
lean_ctor_set(x_419, 2, x_411);
lean_ctor_set(x_419, 3, x_296);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_417);
x_420 = 0;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_413);
lean_ctor_set(x_421, 2, x_414);
lean_ctor_set(x_421, 3, x_419);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
}
}
else
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_4, 3);
lean_inc(x_422);
if (lean_obj_tag(x_422) == 0)
{
uint8_t x_423; 
x_423 = !lean_is_exclusive(x_249);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_424 = lean_ctor_get(x_249, 3);
lean_dec(x_424);
x_425 = lean_ctor_get(x_249, 2);
lean_dec(x_425);
x_426 = lean_ctor_get(x_249, 1);
lean_dec(x_426);
x_427 = lean_ctor_get(x_249, 0);
lean_dec(x_427);
x_428 = 1;
lean_ctor_set(x_249, 3, x_4);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 1, x_2);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_428);
return x_249;
}
else
{
uint8_t x_429; lean_object* x_430; 
lean_dec(x_249);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_1);
lean_ctor_set(x_430, 1, x_2);
lean_ctor_set(x_430, 2, x_3);
lean_ctor_set(x_430, 3, x_4);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_422, sizeof(void*)*4);
if (x_431 == 0)
{
uint8_t x_432; 
x_432 = !lean_is_exclusive(x_4);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_433 = lean_ctor_get(x_4, 3);
lean_dec(x_433);
x_434 = lean_ctor_get(x_4, 0);
lean_dec(x_434);
x_435 = !lean_is_exclusive(x_422);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; uint8_t x_441; 
x_436 = lean_ctor_get(x_422, 0);
x_437 = lean_ctor_get(x_422, 1);
x_438 = lean_ctor_get(x_422, 2);
x_439 = lean_ctor_get(x_422, 3);
x_440 = 1;
lean_inc(x_249);
lean_ctor_set(x_422, 3, x_249);
lean_ctor_set(x_422, 2, x_3);
lean_ctor_set(x_422, 1, x_2);
lean_ctor_set(x_422, 0, x_1);
x_441 = !lean_is_exclusive(x_249);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_442 = lean_ctor_get(x_249, 3);
lean_dec(x_442);
x_443 = lean_ctor_get(x_249, 2);
lean_dec(x_443);
x_444 = lean_ctor_get(x_249, 1);
lean_dec(x_444);
x_445 = lean_ctor_get(x_249, 0);
lean_dec(x_445);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_440);
lean_ctor_set(x_249, 3, x_439);
lean_ctor_set(x_249, 2, x_438);
lean_ctor_set(x_249, 1, x_437);
lean_ctor_set(x_249, 0, x_436);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_440);
x_446 = 0;
lean_ctor_set(x_4, 3, x_249);
lean_ctor_set(x_4, 0, x_422);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_446);
return x_4;
}
else
{
lean_object* x_447; uint8_t x_448; 
lean_dec(x_249);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_440);
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_436);
lean_ctor_set(x_447, 1, x_437);
lean_ctor_set(x_447, 2, x_438);
lean_ctor_set(x_447, 3, x_439);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_440);
x_448 = 0;
lean_ctor_set(x_4, 3, x_447);
lean_ctor_set(x_4, 0, x_422);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_448);
return x_4;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_449 = lean_ctor_get(x_422, 0);
x_450 = lean_ctor_get(x_422, 1);
x_451 = lean_ctor_get(x_422, 2);
x_452 = lean_ctor_get(x_422, 3);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_422);
x_453 = 1;
lean_inc(x_249);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_1);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_249);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 x_455 = x_249;
} else {
 lean_dec_ref(x_249);
 x_455 = lean_box(0);
}
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_449);
lean_ctor_set(x_456, 1, x_450);
lean_ctor_set(x_456, 2, x_451);
lean_ctor_set(x_456, 3, x_452);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_453);
x_457 = 0;
lean_ctor_set(x_4, 3, x_456);
lean_ctor_set(x_4, 0, x_454);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_457);
return x_4;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; 
x_458 = lean_ctor_get(x_4, 1);
x_459 = lean_ctor_get(x_4, 2);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_4);
x_460 = lean_ctor_get(x_422, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_422, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_422, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_422, 3);
lean_inc(x_463);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 lean_ctor_release(x_422, 3);
 x_464 = x_422;
} else {
 lean_dec_ref(x_422);
 x_464 = lean_box(0);
}
x_465 = 1;
lean_inc(x_249);
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_1);
lean_ctor_set(x_466, 1, x_2);
lean_ctor_set(x_466, 2, x_3);
lean_ctor_set(x_466, 3, x_249);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 x_467 = x_249;
} else {
 lean_dec_ref(x_249);
 x_467 = lean_box(0);
}
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_460);
lean_ctor_set(x_468, 1, x_461);
lean_ctor_set(x_468, 2, x_462);
lean_ctor_set(x_468, 3, x_463);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_465);
x_469 = 0;
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_466);
lean_ctor_set(x_470, 1, x_458);
lean_ctor_set(x_470, 2, x_459);
lean_ctor_set(x_470, 3, x_468);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
return x_470;
}
}
else
{
uint8_t x_471; 
lean_dec(x_249);
x_471 = !lean_is_exclusive(x_422);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_472 = lean_ctor_get(x_422, 3);
lean_dec(x_472);
x_473 = lean_ctor_get(x_422, 2);
lean_dec(x_473);
x_474 = lean_ctor_get(x_422, 1);
lean_dec(x_474);
x_475 = lean_ctor_get(x_422, 0);
lean_dec(x_475);
x_476 = 1;
lean_ctor_set(x_422, 3, x_4);
lean_ctor_set(x_422, 2, x_3);
lean_ctor_set(x_422, 1, x_2);
lean_ctor_set(x_422, 0, x_1);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_476);
return x_422;
}
else
{
uint8_t x_477; lean_object* x_478; 
lean_dec(x_422);
x_477 = 1;
x_478 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_478, 0, x_1);
lean_ctor_set(x_478, 1, x_2);
lean_ctor_set(x_478, 2, x_3);
lean_ctor_set(x_478, 3, x_4);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_477);
return x_478;
}
}
}
}
}
}
else
{
uint8_t x_479; lean_object* x_480; 
x_479 = 1;
x_480 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_480, 0, x_1);
lean_ctor_set(x_480, 1, x_2);
lean_ctor_set(x_480, 2, x_3);
lean_ctor_set(x_480, 3, x_4);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
return x_480;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_1, 1);
x_482 = lean_ctor_get(x_1, 2);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_1);
x_483 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_483, 0, x_242);
lean_ctor_set(x_483, 1, x_481);
lean_ctor_set(x_483, 2, x_482);
lean_ctor_set(x_483, 3, x_242);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_240);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_484; lean_object* x_485; 
x_484 = 1;
x_485 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_2);
lean_ctor_set(x_485, 2, x_3);
lean_ctor_set(x_485, 3, x_4);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
return x_485;
}
else
{
uint8_t x_486; 
x_486 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_486 == 0)
{
lean_object* x_487; 
x_487 = lean_ctor_get(x_4, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; 
x_488 = lean_ctor_get(x_4, 3);
lean_inc(x_488);
if (lean_obj_tag(x_488) == 0)
{
uint8_t x_489; lean_object* x_490; 
x_489 = 1;
x_490 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_490, 0, x_483);
lean_ctor_set(x_490, 1, x_2);
lean_ctor_set(x_490, 2, x_3);
lean_ctor_set(x_490, 3, x_4);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_489);
return x_490;
}
else
{
uint8_t x_491; 
x_491 = lean_ctor_get_uint8(x_488, sizeof(void*)*4);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_492 = lean_ctor_get(x_4, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_4, 2);
lean_inc(x_493);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_494 = x_4;
} else {
 lean_dec_ref(x_4);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_488, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_488, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_488, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_488, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 lean_ctor_release(x_488, 2);
 lean_ctor_release(x_488, 3);
 x_499 = x_488;
} else {
 lean_dec_ref(x_488);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_483);
lean_ctor_set(x_501, 1, x_2);
lean_ctor_set(x_501, 2, x_3);
lean_ctor_set(x_501, 3, x_487);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_495);
lean_ctor_set(x_502, 1, x_496);
lean_ctor_set(x_502, 2, x_497);
lean_ctor_set(x_502, 3, x_498);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_492);
lean_ctor_set(x_504, 2, x_493);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; uint8_t x_506; lean_object* x_507; 
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 lean_ctor_release(x_488, 2);
 lean_ctor_release(x_488, 3);
 x_505 = x_488;
} else {
 lean_dec_ref(x_488);
 x_505 = lean_box(0);
}
x_506 = 1;
if (lean_is_scalar(x_505)) {
 x_507 = lean_alloc_ctor(1, 4, 1);
} else {
 x_507 = x_505;
}
lean_ctor_set(x_507, 0, x_483);
lean_ctor_set(x_507, 1, x_2);
lean_ctor_set(x_507, 2, x_3);
lean_ctor_set(x_507, 3, x_4);
lean_ctor_set_uint8(x_507, sizeof(void*)*4, x_506);
return x_507;
}
}
}
else
{
uint8_t x_508; 
x_508 = lean_ctor_get_uint8(x_487, sizeof(void*)*4);
if (x_508 == 0)
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_4, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; lean_object* x_522; 
x_510 = lean_ctor_get(x_4, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_4, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_512 = x_4;
} else {
 lean_dec_ref(x_4);
 x_512 = lean_box(0);
}
x_513 = lean_ctor_get(x_487, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_487, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_487, 2);
lean_inc(x_515);
x_516 = lean_ctor_get(x_487, 3);
lean_inc(x_516);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 x_517 = x_487;
} else {
 lean_dec_ref(x_487);
 x_517 = lean_box(0);
}
x_518 = 1;
if (lean_is_scalar(x_517)) {
 x_519 = lean_alloc_ctor(1, 4, 1);
} else {
 x_519 = x_517;
}
lean_ctor_set(x_519, 0, x_483);
lean_ctor_set(x_519, 1, x_2);
lean_ctor_set(x_519, 2, x_3);
lean_ctor_set(x_519, 3, x_513);
lean_ctor_set_uint8(x_519, sizeof(void*)*4, x_518);
if (lean_is_scalar(x_512)) {
 x_520 = lean_alloc_ctor(1, 4, 1);
} else {
 x_520 = x_512;
}
lean_ctor_set(x_520, 0, x_516);
lean_ctor_set(x_520, 1, x_510);
lean_ctor_set(x_520, 2, x_511);
lean_ctor_set(x_520, 3, x_509);
lean_ctor_set_uint8(x_520, sizeof(void*)*4, x_518);
x_521 = 0;
x_522 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_514);
lean_ctor_set(x_522, 2, x_515);
lean_ctor_set(x_522, 3, x_520);
lean_ctor_set_uint8(x_522, sizeof(void*)*4, x_521);
return x_522;
}
else
{
uint8_t x_523; 
x_523 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; 
x_524 = lean_ctor_get(x_4, 1);
lean_inc(x_524);
x_525 = lean_ctor_get(x_4, 2);
lean_inc(x_525);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_526 = x_4;
} else {
 lean_dec_ref(x_4);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_487, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_487, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_487, 2);
lean_inc(x_529);
x_530 = lean_ctor_get(x_487, 3);
lean_inc(x_530);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 x_531 = x_487;
} else {
 lean_dec_ref(x_487);
 x_531 = lean_box(0);
}
x_532 = lean_ctor_get(x_509, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_509, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_509, 2);
lean_inc(x_534);
x_535 = lean_ctor_get(x_509, 3);
lean_inc(x_535);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_536 = x_509;
} else {
 lean_dec_ref(x_509);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 4, 1);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_527);
lean_ctor_set(x_537, 1, x_528);
lean_ctor_set(x_537, 2, x_529);
lean_ctor_set(x_537, 3, x_530);
lean_ctor_set_uint8(x_537, sizeof(void*)*4, x_523);
x_538 = 1;
if (lean_is_scalar(x_531)) {
 x_539 = lean_alloc_ctor(1, 4, 1);
} else {
 x_539 = x_531;
}
lean_ctor_set(x_539, 0, x_483);
lean_ctor_set(x_539, 1, x_2);
lean_ctor_set(x_539, 2, x_3);
lean_ctor_set(x_539, 3, x_537);
lean_ctor_set_uint8(x_539, sizeof(void*)*4, x_538);
if (lean_is_scalar(x_526)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_526;
}
lean_ctor_set(x_540, 0, x_532);
lean_ctor_set(x_540, 1, x_533);
lean_ctor_set(x_540, 2, x_534);
lean_ctor_set(x_540, 3, x_535);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_538);
x_541 = 0;
x_542 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_524);
lean_ctor_set(x_542, 2, x_525);
lean_ctor_set(x_542, 3, x_540);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
return x_542;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; 
x_543 = lean_ctor_get(x_4, 1);
lean_inc(x_543);
x_544 = lean_ctor_get(x_4, 2);
lean_inc(x_544);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_545 = x_4;
} else {
 lean_dec_ref(x_4);
 x_545 = lean_box(0);
}
x_546 = lean_ctor_get(x_487, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_487, 1);
lean_inc(x_547);
x_548 = lean_ctor_get(x_487, 2);
lean_inc(x_548);
x_549 = lean_ctor_get(x_487, 3);
lean_inc(x_549);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 x_550 = x_487;
} else {
 lean_dec_ref(x_487);
 x_550 = lean_box(0);
}
x_551 = 1;
if (lean_is_scalar(x_550)) {
 x_552 = lean_alloc_ctor(1, 4, 1);
} else {
 x_552 = x_550;
}
lean_ctor_set(x_552, 0, x_483);
lean_ctor_set(x_552, 1, x_2);
lean_ctor_set(x_552, 2, x_3);
lean_ctor_set(x_552, 3, x_546);
lean_ctor_set_uint8(x_552, sizeof(void*)*4, x_551);
if (lean_is_scalar(x_545)) {
 x_553 = lean_alloc_ctor(1, 4, 1);
} else {
 x_553 = x_545;
}
lean_ctor_set(x_553, 0, x_549);
lean_ctor_set(x_553, 1, x_543);
lean_ctor_set(x_553, 2, x_544);
lean_ctor_set(x_553, 3, x_509);
lean_ctor_set_uint8(x_553, sizeof(void*)*4, x_551);
x_554 = 0;
x_555 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set(x_555, 1, x_547);
lean_ctor_set(x_555, 2, x_548);
lean_ctor_set(x_555, 3, x_553);
lean_ctor_set_uint8(x_555, sizeof(void*)*4, x_554);
return x_555;
}
}
}
else
{
lean_object* x_556; 
x_556 = lean_ctor_get(x_4, 3);
lean_inc(x_556);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; uint8_t x_558; lean_object* x_559; 
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 x_557 = x_487;
} else {
 lean_dec_ref(x_487);
 x_557 = lean_box(0);
}
x_558 = 1;
if (lean_is_scalar(x_557)) {
 x_559 = lean_alloc_ctor(1, 4, 1);
} else {
 x_559 = x_557;
}
lean_ctor_set(x_559, 0, x_483);
lean_ctor_set(x_559, 1, x_2);
lean_ctor_set(x_559, 2, x_3);
lean_ctor_set(x_559, 3, x_4);
lean_ctor_set_uint8(x_559, sizeof(void*)*4, x_558);
return x_559;
}
else
{
uint8_t x_560; 
x_560 = lean_ctor_get_uint8(x_556, sizeof(void*)*4);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; 
x_561 = lean_ctor_get(x_4, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_4, 2);
lean_inc(x_562);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_563 = x_4;
} else {
 lean_dec_ref(x_4);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_556, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_556, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_556, 2);
lean_inc(x_566);
x_567 = lean_ctor_get(x_556, 3);
lean_inc(x_567);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 lean_ctor_release(x_556, 2);
 lean_ctor_release(x_556, 3);
 x_568 = x_556;
} else {
 lean_dec_ref(x_556);
 x_568 = lean_box(0);
}
x_569 = 1;
lean_inc(x_487);
if (lean_is_scalar(x_568)) {
 x_570 = lean_alloc_ctor(1, 4, 1);
} else {
 x_570 = x_568;
}
lean_ctor_set(x_570, 0, x_483);
lean_ctor_set(x_570, 1, x_2);
lean_ctor_set(x_570, 2, x_3);
lean_ctor_set(x_570, 3, x_487);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 lean_ctor_release(x_487, 2);
 lean_ctor_release(x_487, 3);
 x_571 = x_487;
} else {
 lean_dec_ref(x_487);
 x_571 = lean_box(0);
}
lean_ctor_set_uint8(x_570, sizeof(void*)*4, x_569);
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(1, 4, 1);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_564);
lean_ctor_set(x_572, 1, x_565);
lean_ctor_set(x_572, 2, x_566);
lean_ctor_set(x_572, 3, x_567);
lean_ctor_set_uint8(x_572, sizeof(void*)*4, x_569);
x_573 = 0;
if (lean_is_scalar(x_563)) {
 x_574 = lean_alloc_ctor(1, 4, 1);
} else {
 x_574 = x_563;
}
lean_ctor_set(x_574, 0, x_570);
lean_ctor_set(x_574, 1, x_561);
lean_ctor_set(x_574, 2, x_562);
lean_ctor_set(x_574, 3, x_572);
lean_ctor_set_uint8(x_574, sizeof(void*)*4, x_573);
return x_574;
}
else
{
lean_object* x_575; uint8_t x_576; lean_object* x_577; 
lean_dec(x_487);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 lean_ctor_release(x_556, 2);
 lean_ctor_release(x_556, 3);
 x_575 = x_556;
} else {
 lean_dec_ref(x_556);
 x_575 = lean_box(0);
}
x_576 = 1;
if (lean_is_scalar(x_575)) {
 x_577 = lean_alloc_ctor(1, 4, 1);
} else {
 x_577 = x_575;
}
lean_ctor_set(x_577, 0, x_483);
lean_ctor_set(x_577, 1, x_2);
lean_ctor_set(x_577, 2, x_3);
lean_ctor_set(x_577, 3, x_4);
lean_ctor_set_uint8(x_577, sizeof(void*)*4, x_576);
return x_577;
}
}
}
}
}
else
{
uint8_t x_578; lean_object* x_579; 
x_578 = 1;
x_579 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_579, 0, x_483);
lean_ctor_set(x_579, 1, x_2);
lean_ctor_set(x_579, 2, x_3);
lean_ctor_set(x_579, 3, x_4);
lean_ctor_set_uint8(x_579, sizeof(void*)*4, x_578);
return x_579;
}
}
}
}
else
{
uint8_t x_580; 
x_580 = lean_ctor_get_uint8(x_242, sizeof(void*)*4);
if (x_580 == 0)
{
uint8_t x_581; 
x_581 = !lean_is_exclusive(x_1);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; 
x_582 = lean_ctor_get(x_1, 1);
x_583 = lean_ctor_get(x_1, 2);
x_584 = lean_ctor_get(x_1, 3);
lean_dec(x_584);
x_585 = lean_ctor_get(x_1, 0);
lean_dec(x_585);
x_586 = !lean_is_exclusive(x_242);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; uint8_t x_592; lean_object* x_593; 
x_587 = lean_ctor_get(x_242, 0);
x_588 = lean_ctor_get(x_242, 1);
x_589 = lean_ctor_get(x_242, 2);
x_590 = lean_ctor_get(x_242, 3);
x_591 = 1;
lean_ctor_set(x_242, 3, x_587);
lean_ctor_set(x_242, 2, x_583);
lean_ctor_set(x_242, 1, x_582);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_591);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_590);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_591);
x_592 = 0;
x_593 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_593, 0, x_242);
lean_ctor_set(x_593, 1, x_588);
lean_ctor_set(x_593, 2, x_589);
lean_ctor_set(x_593, 3, x_1);
lean_ctor_set_uint8(x_593, sizeof(void*)*4, x_592);
return x_593;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; uint8_t x_600; lean_object* x_601; 
x_594 = lean_ctor_get(x_242, 0);
x_595 = lean_ctor_get(x_242, 1);
x_596 = lean_ctor_get(x_242, 2);
x_597 = lean_ctor_get(x_242, 3);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_242);
x_598 = 1;
x_599 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_599, 0, x_241);
lean_ctor_set(x_599, 1, x_582);
lean_ctor_set(x_599, 2, x_583);
lean_ctor_set(x_599, 3, x_594);
lean_ctor_set_uint8(x_599, sizeof(void*)*4, x_598);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_597);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_598);
x_600 = 0;
x_601 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_595);
lean_ctor_set(x_601, 2, x_596);
lean_ctor_set(x_601, 3, x_1);
lean_ctor_set_uint8(x_601, sizeof(void*)*4, x_600);
return x_601;
}
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; lean_object* x_613; 
x_602 = lean_ctor_get(x_1, 1);
x_603 = lean_ctor_get(x_1, 2);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_1);
x_604 = lean_ctor_get(x_242, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_242, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_242, 2);
lean_inc(x_606);
x_607 = lean_ctor_get(x_242, 3);
lean_inc(x_607);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 lean_ctor_release(x_242, 3);
 x_608 = x_242;
} else {
 lean_dec_ref(x_242);
 x_608 = lean_box(0);
}
x_609 = 1;
if (lean_is_scalar(x_608)) {
 x_610 = lean_alloc_ctor(1, 4, 1);
} else {
 x_610 = x_608;
}
lean_ctor_set(x_610, 0, x_241);
lean_ctor_set(x_610, 1, x_602);
lean_ctor_set(x_610, 2, x_603);
lean_ctor_set(x_610, 3, x_604);
lean_ctor_set_uint8(x_610, sizeof(void*)*4, x_609);
x_611 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_611, 0, x_607);
lean_ctor_set(x_611, 1, x_2);
lean_ctor_set(x_611, 2, x_3);
lean_ctor_set(x_611, 3, x_4);
lean_ctor_set_uint8(x_611, sizeof(void*)*4, x_609);
x_612 = 0;
x_613 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_605);
lean_ctor_set(x_613, 2, x_606);
lean_ctor_set(x_613, 3, x_611);
lean_ctor_set_uint8(x_613, sizeof(void*)*4, x_612);
return x_613;
}
}
else
{
uint8_t x_614; 
x_614 = !lean_is_exclusive(x_242);
if (x_614 == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_615 = lean_ctor_get(x_242, 3);
lean_dec(x_615);
x_616 = lean_ctor_get(x_242, 2);
lean_dec(x_616);
x_617 = lean_ctor_get(x_242, 1);
lean_dec(x_617);
x_618 = lean_ctor_get(x_242, 0);
lean_dec(x_618);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_619; 
x_619 = 1;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_3);
lean_ctor_set(x_242, 1, x_2);
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_619);
return x_242;
}
else
{
uint8_t x_620; 
x_620 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_620 == 0)
{
lean_object* x_621; 
x_621 = lean_ctor_get(x_4, 0);
lean_inc(x_621);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; 
x_622 = lean_ctor_get(x_4, 3);
lean_inc(x_622);
if (lean_obj_tag(x_622) == 0)
{
uint8_t x_623; 
x_623 = 1;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_3);
lean_ctor_set(x_242, 1, x_2);
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_623);
return x_242;
}
else
{
uint8_t x_624; 
x_624 = lean_ctor_get_uint8(x_622, sizeof(void*)*4);
if (x_624 == 0)
{
uint8_t x_625; 
x_625 = !lean_is_exclusive(x_4);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_626 = lean_ctor_get(x_4, 1);
x_627 = lean_ctor_get(x_4, 2);
x_628 = lean_ctor_get(x_4, 3);
lean_dec(x_628);
x_629 = lean_ctor_get(x_4, 0);
lean_dec(x_629);
x_630 = !lean_is_exclusive(x_622);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; uint8_t x_636; 
x_631 = lean_ctor_get(x_622, 0);
x_632 = lean_ctor_get(x_622, 1);
x_633 = lean_ctor_get(x_622, 2);
x_634 = lean_ctor_get(x_622, 3);
x_635 = 1;
lean_ctor_set(x_622, 3, x_621);
lean_ctor_set(x_622, 2, x_3);
lean_ctor_set(x_622, 1, x_2);
lean_ctor_set(x_622, 0, x_1);
lean_ctor_set_uint8(x_622, sizeof(void*)*4, x_635);
lean_ctor_set(x_4, 3, x_634);
lean_ctor_set(x_4, 2, x_633);
lean_ctor_set(x_4, 1, x_632);
lean_ctor_set(x_4, 0, x_631);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_635);
x_636 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_627);
lean_ctor_set(x_242, 1, x_626);
lean_ctor_set(x_242, 0, x_622);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_636);
return x_242;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; lean_object* x_642; uint8_t x_643; 
x_637 = lean_ctor_get(x_622, 0);
x_638 = lean_ctor_get(x_622, 1);
x_639 = lean_ctor_get(x_622, 2);
x_640 = lean_ctor_get(x_622, 3);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_622);
x_641 = 1;
x_642 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_642, 0, x_1);
lean_ctor_set(x_642, 1, x_2);
lean_ctor_set(x_642, 2, x_3);
lean_ctor_set(x_642, 3, x_621);
lean_ctor_set_uint8(x_642, sizeof(void*)*4, x_641);
lean_ctor_set(x_4, 3, x_640);
lean_ctor_set(x_4, 2, x_639);
lean_ctor_set(x_4, 1, x_638);
lean_ctor_set(x_4, 0, x_637);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_641);
x_643 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_627);
lean_ctor_set(x_242, 1, x_626);
lean_ctor_set(x_242, 0, x_642);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_643);
return x_242;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; 
x_644 = lean_ctor_get(x_4, 1);
x_645 = lean_ctor_get(x_4, 2);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_4);
x_646 = lean_ctor_get(x_622, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_622, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_622, 2);
lean_inc(x_648);
x_649 = lean_ctor_get(x_622, 3);
lean_inc(x_649);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 lean_ctor_release(x_622, 2);
 lean_ctor_release(x_622, 3);
 x_650 = x_622;
} else {
 lean_dec_ref(x_622);
 x_650 = lean_box(0);
}
x_651 = 1;
if (lean_is_scalar(x_650)) {
 x_652 = lean_alloc_ctor(1, 4, 1);
} else {
 x_652 = x_650;
}
lean_ctor_set(x_652, 0, x_1);
lean_ctor_set(x_652, 1, x_2);
lean_ctor_set(x_652, 2, x_3);
lean_ctor_set(x_652, 3, x_621);
lean_ctor_set_uint8(x_652, sizeof(void*)*4, x_651);
x_653 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_653, 0, x_646);
lean_ctor_set(x_653, 1, x_647);
lean_ctor_set(x_653, 2, x_648);
lean_ctor_set(x_653, 3, x_649);
lean_ctor_set_uint8(x_653, sizeof(void*)*4, x_651);
x_654 = 0;
lean_ctor_set(x_242, 3, x_653);
lean_ctor_set(x_242, 2, x_645);
lean_ctor_set(x_242, 1, x_644);
lean_ctor_set(x_242, 0, x_652);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_654);
return x_242;
}
}
else
{
uint8_t x_655; 
lean_free_object(x_242);
x_655 = !lean_is_exclusive(x_622);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_656 = lean_ctor_get(x_622, 3);
lean_dec(x_656);
x_657 = lean_ctor_get(x_622, 2);
lean_dec(x_657);
x_658 = lean_ctor_get(x_622, 1);
lean_dec(x_658);
x_659 = lean_ctor_get(x_622, 0);
lean_dec(x_659);
x_660 = 1;
lean_ctor_set(x_622, 3, x_4);
lean_ctor_set(x_622, 2, x_3);
lean_ctor_set(x_622, 1, x_2);
lean_ctor_set(x_622, 0, x_1);
lean_ctor_set_uint8(x_622, sizeof(void*)*4, x_660);
return x_622;
}
else
{
uint8_t x_661; lean_object* x_662; 
lean_dec(x_622);
x_661 = 1;
x_662 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_662, 0, x_1);
lean_ctor_set(x_662, 1, x_2);
lean_ctor_set(x_662, 2, x_3);
lean_ctor_set(x_662, 3, x_4);
lean_ctor_set_uint8(x_662, sizeof(void*)*4, x_661);
return x_662;
}
}
}
}
else
{
uint8_t x_663; 
x_663 = lean_ctor_get_uint8(x_621, sizeof(void*)*4);
if (x_663 == 0)
{
lean_object* x_664; 
x_664 = lean_ctor_get(x_4, 3);
lean_inc(x_664);
if (lean_obj_tag(x_664) == 0)
{
uint8_t x_665; 
x_665 = !lean_is_exclusive(x_4);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; uint8_t x_668; 
x_666 = lean_ctor_get(x_4, 3);
lean_dec(x_666);
x_667 = lean_ctor_get(x_4, 0);
lean_dec(x_667);
x_668 = !lean_is_exclusive(x_621);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_674; 
x_669 = lean_ctor_get(x_621, 0);
x_670 = lean_ctor_get(x_621, 1);
x_671 = lean_ctor_get(x_621, 2);
x_672 = lean_ctor_get(x_621, 3);
x_673 = 1;
lean_ctor_set(x_621, 3, x_669);
lean_ctor_set(x_621, 2, x_3);
lean_ctor_set(x_621, 1, x_2);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_673);
lean_ctor_set(x_4, 0, x_672);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_673);
x_674 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_671);
lean_ctor_set(x_242, 1, x_670);
lean_ctor_set(x_242, 0, x_621);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_674);
return x_242;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; lean_object* x_680; uint8_t x_681; 
x_675 = lean_ctor_get(x_621, 0);
x_676 = lean_ctor_get(x_621, 1);
x_677 = lean_ctor_get(x_621, 2);
x_678 = lean_ctor_get(x_621, 3);
lean_inc(x_678);
lean_inc(x_677);
lean_inc(x_676);
lean_inc(x_675);
lean_dec(x_621);
x_679 = 1;
x_680 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_680, 0, x_1);
lean_ctor_set(x_680, 1, x_2);
lean_ctor_set(x_680, 2, x_3);
lean_ctor_set(x_680, 3, x_675);
lean_ctor_set_uint8(x_680, sizeof(void*)*4, x_679);
lean_ctor_set(x_4, 0, x_678);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_679);
x_681 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_677);
lean_ctor_set(x_242, 1, x_676);
lean_ctor_set(x_242, 0, x_680);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_681);
return x_242;
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; uint8_t x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
x_682 = lean_ctor_get(x_4, 1);
x_683 = lean_ctor_get(x_4, 2);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_4);
x_684 = lean_ctor_get(x_621, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_621, 1);
lean_inc(x_685);
x_686 = lean_ctor_get(x_621, 2);
lean_inc(x_686);
x_687 = lean_ctor_get(x_621, 3);
lean_inc(x_687);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 lean_ctor_release(x_621, 2);
 lean_ctor_release(x_621, 3);
 x_688 = x_621;
} else {
 lean_dec_ref(x_621);
 x_688 = lean_box(0);
}
x_689 = 1;
if (lean_is_scalar(x_688)) {
 x_690 = lean_alloc_ctor(1, 4, 1);
} else {
 x_690 = x_688;
}
lean_ctor_set(x_690, 0, x_1);
lean_ctor_set(x_690, 1, x_2);
lean_ctor_set(x_690, 2, x_3);
lean_ctor_set(x_690, 3, x_684);
lean_ctor_set_uint8(x_690, sizeof(void*)*4, x_689);
x_691 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_691, 0, x_687);
lean_ctor_set(x_691, 1, x_682);
lean_ctor_set(x_691, 2, x_683);
lean_ctor_set(x_691, 3, x_664);
lean_ctor_set_uint8(x_691, sizeof(void*)*4, x_689);
x_692 = 0;
lean_ctor_set(x_242, 3, x_691);
lean_ctor_set(x_242, 2, x_686);
lean_ctor_set(x_242, 1, x_685);
lean_ctor_set(x_242, 0, x_690);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_692);
return x_242;
}
}
else
{
uint8_t x_693; 
x_693 = lean_ctor_get_uint8(x_664, sizeof(void*)*4);
if (x_693 == 0)
{
uint8_t x_694; 
x_694 = !lean_is_exclusive(x_4);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; 
x_695 = lean_ctor_get(x_4, 1);
x_696 = lean_ctor_get(x_4, 2);
x_697 = lean_ctor_get(x_4, 3);
lean_dec(x_697);
x_698 = lean_ctor_get(x_4, 0);
lean_dec(x_698);
x_699 = !lean_is_exclusive(x_621);
if (x_699 == 0)
{
uint8_t x_700; 
x_700 = !lean_is_exclusive(x_664);
if (x_700 == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; uint8_t x_710; 
x_701 = lean_ctor_get(x_621, 0);
x_702 = lean_ctor_get(x_621, 1);
x_703 = lean_ctor_get(x_621, 2);
x_704 = lean_ctor_get(x_621, 3);
x_705 = lean_ctor_get(x_664, 0);
x_706 = lean_ctor_get(x_664, 1);
x_707 = lean_ctor_get(x_664, 2);
x_708 = lean_ctor_get(x_664, 3);
lean_ctor_set(x_664, 3, x_704);
lean_ctor_set(x_664, 2, x_703);
lean_ctor_set(x_664, 1, x_702);
lean_ctor_set(x_664, 0, x_701);
x_709 = 1;
lean_ctor_set(x_621, 3, x_664);
lean_ctor_set(x_621, 2, x_3);
lean_ctor_set(x_621, 1, x_2);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_709);
lean_ctor_set(x_4, 3, x_708);
lean_ctor_set(x_4, 2, x_707);
lean_ctor_set(x_4, 1, x_706);
lean_ctor_set(x_4, 0, x_705);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_709);
x_710 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_696);
lean_ctor_set(x_242, 1, x_695);
lean_ctor_set(x_242, 0, x_621);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_710);
return x_242;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; uint8_t x_721; 
x_711 = lean_ctor_get(x_621, 0);
x_712 = lean_ctor_get(x_621, 1);
x_713 = lean_ctor_get(x_621, 2);
x_714 = lean_ctor_get(x_621, 3);
x_715 = lean_ctor_get(x_664, 0);
x_716 = lean_ctor_get(x_664, 1);
x_717 = lean_ctor_get(x_664, 2);
x_718 = lean_ctor_get(x_664, 3);
lean_inc(x_718);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_664);
x_719 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_719, 0, x_711);
lean_ctor_set(x_719, 1, x_712);
lean_ctor_set(x_719, 2, x_713);
lean_ctor_set(x_719, 3, x_714);
lean_ctor_set_uint8(x_719, sizeof(void*)*4, x_693);
x_720 = 1;
lean_ctor_set(x_621, 3, x_719);
lean_ctor_set(x_621, 2, x_3);
lean_ctor_set(x_621, 1, x_2);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_720);
lean_ctor_set(x_4, 3, x_718);
lean_ctor_set(x_4, 2, x_717);
lean_ctor_set(x_4, 1, x_716);
lean_ctor_set(x_4, 0, x_715);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_720);
x_721 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_696);
lean_ctor_set(x_242, 1, x_695);
lean_ctor_set(x_242, 0, x_621);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_721);
return x_242;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; uint8_t x_732; lean_object* x_733; uint8_t x_734; 
x_722 = lean_ctor_get(x_621, 0);
x_723 = lean_ctor_get(x_621, 1);
x_724 = lean_ctor_get(x_621, 2);
x_725 = lean_ctor_get(x_621, 3);
lean_inc(x_725);
lean_inc(x_724);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_621);
x_726 = lean_ctor_get(x_664, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_664, 1);
lean_inc(x_727);
x_728 = lean_ctor_get(x_664, 2);
lean_inc(x_728);
x_729 = lean_ctor_get(x_664, 3);
lean_inc(x_729);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 lean_ctor_release(x_664, 2);
 lean_ctor_release(x_664, 3);
 x_730 = x_664;
} else {
 lean_dec_ref(x_664);
 x_730 = lean_box(0);
}
if (lean_is_scalar(x_730)) {
 x_731 = lean_alloc_ctor(1, 4, 1);
} else {
 x_731 = x_730;
}
lean_ctor_set(x_731, 0, x_722);
lean_ctor_set(x_731, 1, x_723);
lean_ctor_set(x_731, 2, x_724);
lean_ctor_set(x_731, 3, x_725);
lean_ctor_set_uint8(x_731, sizeof(void*)*4, x_693);
x_732 = 1;
x_733 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_733, 0, x_1);
lean_ctor_set(x_733, 1, x_2);
lean_ctor_set(x_733, 2, x_3);
lean_ctor_set(x_733, 3, x_731);
lean_ctor_set_uint8(x_733, sizeof(void*)*4, x_732);
lean_ctor_set(x_4, 3, x_729);
lean_ctor_set(x_4, 2, x_728);
lean_ctor_set(x_4, 1, x_727);
lean_ctor_set(x_4, 0, x_726);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_732);
x_734 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_696);
lean_ctor_set(x_242, 1, x_695);
lean_ctor_set(x_242, 0, x_733);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_734);
return x_242;
}
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_735 = lean_ctor_get(x_4, 1);
x_736 = lean_ctor_get(x_4, 2);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_4);
x_737 = lean_ctor_get(x_621, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_621, 1);
lean_inc(x_738);
x_739 = lean_ctor_get(x_621, 2);
lean_inc(x_739);
x_740 = lean_ctor_get(x_621, 3);
lean_inc(x_740);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 lean_ctor_release(x_621, 2);
 lean_ctor_release(x_621, 3);
 x_741 = x_621;
} else {
 lean_dec_ref(x_621);
 x_741 = lean_box(0);
}
x_742 = lean_ctor_get(x_664, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_664, 1);
lean_inc(x_743);
x_744 = lean_ctor_get(x_664, 2);
lean_inc(x_744);
x_745 = lean_ctor_get(x_664, 3);
lean_inc(x_745);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 lean_ctor_release(x_664, 2);
 lean_ctor_release(x_664, 3);
 x_746 = x_664;
} else {
 lean_dec_ref(x_664);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(1, 4, 1);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_737);
lean_ctor_set(x_747, 1, x_738);
lean_ctor_set(x_747, 2, x_739);
lean_ctor_set(x_747, 3, x_740);
lean_ctor_set_uint8(x_747, sizeof(void*)*4, x_693);
x_748 = 1;
if (lean_is_scalar(x_741)) {
 x_749 = lean_alloc_ctor(1, 4, 1);
} else {
 x_749 = x_741;
}
lean_ctor_set(x_749, 0, x_1);
lean_ctor_set(x_749, 1, x_2);
lean_ctor_set(x_749, 2, x_3);
lean_ctor_set(x_749, 3, x_747);
lean_ctor_set_uint8(x_749, sizeof(void*)*4, x_748);
x_750 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_750, 0, x_742);
lean_ctor_set(x_750, 1, x_743);
lean_ctor_set(x_750, 2, x_744);
lean_ctor_set(x_750, 3, x_745);
lean_ctor_set_uint8(x_750, sizeof(void*)*4, x_748);
x_751 = 0;
lean_ctor_set(x_242, 3, x_750);
lean_ctor_set(x_242, 2, x_736);
lean_ctor_set(x_242, 1, x_735);
lean_ctor_set(x_242, 0, x_749);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_751);
return x_242;
}
}
else
{
uint8_t x_752; 
x_752 = !lean_is_exclusive(x_4);
if (x_752 == 0)
{
lean_object* x_753; lean_object* x_754; uint8_t x_755; 
x_753 = lean_ctor_get(x_4, 3);
lean_dec(x_753);
x_754 = lean_ctor_get(x_4, 0);
lean_dec(x_754);
x_755 = !lean_is_exclusive(x_621);
if (x_755 == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; uint8_t x_761; 
x_756 = lean_ctor_get(x_621, 0);
x_757 = lean_ctor_get(x_621, 1);
x_758 = lean_ctor_get(x_621, 2);
x_759 = lean_ctor_get(x_621, 3);
x_760 = 1;
lean_ctor_set(x_621, 3, x_756);
lean_ctor_set(x_621, 2, x_3);
lean_ctor_set(x_621, 1, x_2);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_760);
lean_ctor_set(x_4, 0, x_759);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_760);
x_761 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_758);
lean_ctor_set(x_242, 1, x_757);
lean_ctor_set(x_242, 0, x_621);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_761);
return x_242;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; uint8_t x_768; 
x_762 = lean_ctor_get(x_621, 0);
x_763 = lean_ctor_get(x_621, 1);
x_764 = lean_ctor_get(x_621, 2);
x_765 = lean_ctor_get(x_621, 3);
lean_inc(x_765);
lean_inc(x_764);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_621);
x_766 = 1;
x_767 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_767, 0, x_1);
lean_ctor_set(x_767, 1, x_2);
lean_ctor_set(x_767, 2, x_3);
lean_ctor_set(x_767, 3, x_762);
lean_ctor_set_uint8(x_767, sizeof(void*)*4, x_766);
lean_ctor_set(x_4, 0, x_765);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_766);
x_768 = 0;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_764);
lean_ctor_set(x_242, 1, x_763);
lean_ctor_set(x_242, 0, x_767);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_768);
return x_242;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; lean_object* x_777; lean_object* x_778; uint8_t x_779; 
x_769 = lean_ctor_get(x_4, 1);
x_770 = lean_ctor_get(x_4, 2);
lean_inc(x_770);
lean_inc(x_769);
lean_dec(x_4);
x_771 = lean_ctor_get(x_621, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_621, 1);
lean_inc(x_772);
x_773 = lean_ctor_get(x_621, 2);
lean_inc(x_773);
x_774 = lean_ctor_get(x_621, 3);
lean_inc(x_774);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 lean_ctor_release(x_621, 2);
 lean_ctor_release(x_621, 3);
 x_775 = x_621;
} else {
 lean_dec_ref(x_621);
 x_775 = lean_box(0);
}
x_776 = 1;
if (lean_is_scalar(x_775)) {
 x_777 = lean_alloc_ctor(1, 4, 1);
} else {
 x_777 = x_775;
}
lean_ctor_set(x_777, 0, x_1);
lean_ctor_set(x_777, 1, x_2);
lean_ctor_set(x_777, 2, x_3);
lean_ctor_set(x_777, 3, x_771);
lean_ctor_set_uint8(x_777, sizeof(void*)*4, x_776);
x_778 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_778, 0, x_774);
lean_ctor_set(x_778, 1, x_769);
lean_ctor_set(x_778, 2, x_770);
lean_ctor_set(x_778, 3, x_664);
lean_ctor_set_uint8(x_778, sizeof(void*)*4, x_776);
x_779 = 0;
lean_ctor_set(x_242, 3, x_778);
lean_ctor_set(x_242, 2, x_773);
lean_ctor_set(x_242, 1, x_772);
lean_ctor_set(x_242, 0, x_777);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_779);
return x_242;
}
}
}
}
else
{
lean_object* x_780; 
lean_free_object(x_242);
x_780 = lean_ctor_get(x_4, 3);
lean_inc(x_780);
if (lean_obj_tag(x_780) == 0)
{
uint8_t x_781; 
x_781 = !lean_is_exclusive(x_621);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; 
x_782 = lean_ctor_get(x_621, 3);
lean_dec(x_782);
x_783 = lean_ctor_get(x_621, 2);
lean_dec(x_783);
x_784 = lean_ctor_get(x_621, 1);
lean_dec(x_784);
x_785 = lean_ctor_get(x_621, 0);
lean_dec(x_785);
x_786 = 1;
lean_ctor_set(x_621, 3, x_4);
lean_ctor_set(x_621, 2, x_3);
lean_ctor_set(x_621, 1, x_2);
lean_ctor_set(x_621, 0, x_1);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_786);
return x_621;
}
else
{
uint8_t x_787; lean_object* x_788; 
lean_dec(x_621);
x_787 = 1;
x_788 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_788, 0, x_1);
lean_ctor_set(x_788, 1, x_2);
lean_ctor_set(x_788, 2, x_3);
lean_ctor_set(x_788, 3, x_4);
lean_ctor_set_uint8(x_788, sizeof(void*)*4, x_787);
return x_788;
}
}
else
{
uint8_t x_789; 
x_789 = lean_ctor_get_uint8(x_780, sizeof(void*)*4);
if (x_789 == 0)
{
uint8_t x_790; 
x_790 = !lean_is_exclusive(x_4);
if (x_790 == 0)
{
lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_791 = lean_ctor_get(x_4, 3);
lean_dec(x_791);
x_792 = lean_ctor_get(x_4, 0);
lean_dec(x_792);
x_793 = !lean_is_exclusive(x_780);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; uint8_t x_799; 
x_794 = lean_ctor_get(x_780, 0);
x_795 = lean_ctor_get(x_780, 1);
x_796 = lean_ctor_get(x_780, 2);
x_797 = lean_ctor_get(x_780, 3);
x_798 = 1;
lean_inc(x_621);
lean_ctor_set(x_780, 3, x_621);
lean_ctor_set(x_780, 2, x_3);
lean_ctor_set(x_780, 1, x_2);
lean_ctor_set(x_780, 0, x_1);
x_799 = !lean_is_exclusive(x_621);
if (x_799 == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
x_800 = lean_ctor_get(x_621, 3);
lean_dec(x_800);
x_801 = lean_ctor_get(x_621, 2);
lean_dec(x_801);
x_802 = lean_ctor_get(x_621, 1);
lean_dec(x_802);
x_803 = lean_ctor_get(x_621, 0);
lean_dec(x_803);
lean_ctor_set_uint8(x_780, sizeof(void*)*4, x_798);
lean_ctor_set(x_621, 3, x_797);
lean_ctor_set(x_621, 2, x_796);
lean_ctor_set(x_621, 1, x_795);
lean_ctor_set(x_621, 0, x_794);
lean_ctor_set_uint8(x_621, sizeof(void*)*4, x_798);
x_804 = 0;
lean_ctor_set(x_4, 3, x_621);
lean_ctor_set(x_4, 0, x_780);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_804);
return x_4;
}
else
{
lean_object* x_805; uint8_t x_806; 
lean_dec(x_621);
lean_ctor_set_uint8(x_780, sizeof(void*)*4, x_798);
x_805 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_805, 0, x_794);
lean_ctor_set(x_805, 1, x_795);
lean_ctor_set(x_805, 2, x_796);
lean_ctor_set(x_805, 3, x_797);
lean_ctor_set_uint8(x_805, sizeof(void*)*4, x_798);
x_806 = 0;
lean_ctor_set(x_4, 3, x_805);
lean_ctor_set(x_4, 0, x_780);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_806);
return x_4;
}
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_807 = lean_ctor_get(x_780, 0);
x_808 = lean_ctor_get(x_780, 1);
x_809 = lean_ctor_get(x_780, 2);
x_810 = lean_ctor_get(x_780, 3);
lean_inc(x_810);
lean_inc(x_809);
lean_inc(x_808);
lean_inc(x_807);
lean_dec(x_780);
x_811 = 1;
lean_inc(x_621);
x_812 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_812, 0, x_1);
lean_ctor_set(x_812, 1, x_2);
lean_ctor_set(x_812, 2, x_3);
lean_ctor_set(x_812, 3, x_621);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 lean_ctor_release(x_621, 2);
 lean_ctor_release(x_621, 3);
 x_813 = x_621;
} else {
 lean_dec_ref(x_621);
 x_813 = lean_box(0);
}
lean_ctor_set_uint8(x_812, sizeof(void*)*4, x_811);
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 4, 1);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_807);
lean_ctor_set(x_814, 1, x_808);
lean_ctor_set(x_814, 2, x_809);
lean_ctor_set(x_814, 3, x_810);
lean_ctor_set_uint8(x_814, sizeof(void*)*4, x_811);
x_815 = 0;
lean_ctor_set(x_4, 3, x_814);
lean_ctor_set(x_4, 0, x_812);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_815);
return x_4;
}
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; uint8_t x_827; lean_object* x_828; 
x_816 = lean_ctor_get(x_4, 1);
x_817 = lean_ctor_get(x_4, 2);
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_4);
x_818 = lean_ctor_get(x_780, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_780, 1);
lean_inc(x_819);
x_820 = lean_ctor_get(x_780, 2);
lean_inc(x_820);
x_821 = lean_ctor_get(x_780, 3);
lean_inc(x_821);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 lean_ctor_release(x_780, 2);
 lean_ctor_release(x_780, 3);
 x_822 = x_780;
} else {
 lean_dec_ref(x_780);
 x_822 = lean_box(0);
}
x_823 = 1;
lean_inc(x_621);
if (lean_is_scalar(x_822)) {
 x_824 = lean_alloc_ctor(1, 4, 1);
} else {
 x_824 = x_822;
}
lean_ctor_set(x_824, 0, x_1);
lean_ctor_set(x_824, 1, x_2);
lean_ctor_set(x_824, 2, x_3);
lean_ctor_set(x_824, 3, x_621);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 lean_ctor_release(x_621, 2);
 lean_ctor_release(x_621, 3);
 x_825 = x_621;
} else {
 lean_dec_ref(x_621);
 x_825 = lean_box(0);
}
lean_ctor_set_uint8(x_824, sizeof(void*)*4, x_823);
if (lean_is_scalar(x_825)) {
 x_826 = lean_alloc_ctor(1, 4, 1);
} else {
 x_826 = x_825;
}
lean_ctor_set(x_826, 0, x_818);
lean_ctor_set(x_826, 1, x_819);
lean_ctor_set(x_826, 2, x_820);
lean_ctor_set(x_826, 3, x_821);
lean_ctor_set_uint8(x_826, sizeof(void*)*4, x_823);
x_827 = 0;
x_828 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_828, 0, x_824);
lean_ctor_set(x_828, 1, x_816);
lean_ctor_set(x_828, 2, x_817);
lean_ctor_set(x_828, 3, x_826);
lean_ctor_set_uint8(x_828, sizeof(void*)*4, x_827);
return x_828;
}
}
else
{
uint8_t x_829; 
lean_dec(x_621);
x_829 = !lean_is_exclusive(x_780);
if (x_829 == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; 
x_830 = lean_ctor_get(x_780, 3);
lean_dec(x_830);
x_831 = lean_ctor_get(x_780, 2);
lean_dec(x_831);
x_832 = lean_ctor_get(x_780, 1);
lean_dec(x_832);
x_833 = lean_ctor_get(x_780, 0);
lean_dec(x_833);
x_834 = 1;
lean_ctor_set(x_780, 3, x_4);
lean_ctor_set(x_780, 2, x_3);
lean_ctor_set(x_780, 1, x_2);
lean_ctor_set(x_780, 0, x_1);
lean_ctor_set_uint8(x_780, sizeof(void*)*4, x_834);
return x_780;
}
else
{
uint8_t x_835; lean_object* x_836; 
lean_dec(x_780);
x_835 = 1;
x_836 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_836, 0, x_1);
lean_ctor_set(x_836, 1, x_2);
lean_ctor_set(x_836, 2, x_3);
lean_ctor_set(x_836, 3, x_4);
lean_ctor_set_uint8(x_836, sizeof(void*)*4, x_835);
return x_836;
}
}
}
}
}
}
else
{
uint8_t x_837; 
x_837 = 1;
lean_ctor_set(x_242, 3, x_4);
lean_ctor_set(x_242, 2, x_3);
lean_ctor_set(x_242, 1, x_2);
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_837);
return x_242;
}
}
}
else
{
lean_dec(x_242);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_838; lean_object* x_839; 
x_838 = 1;
x_839 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_839, 0, x_1);
lean_ctor_set(x_839, 1, x_2);
lean_ctor_set(x_839, 2, x_3);
lean_ctor_set(x_839, 3, x_4);
lean_ctor_set_uint8(x_839, sizeof(void*)*4, x_838);
return x_839;
}
else
{
uint8_t x_840; 
x_840 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_840 == 0)
{
lean_object* x_841; 
x_841 = lean_ctor_get(x_4, 0);
lean_inc(x_841);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; 
x_842 = lean_ctor_get(x_4, 3);
lean_inc(x_842);
if (lean_obj_tag(x_842) == 0)
{
uint8_t x_843; lean_object* x_844; 
x_843 = 1;
x_844 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_844, 0, x_1);
lean_ctor_set(x_844, 1, x_2);
lean_ctor_set(x_844, 2, x_3);
lean_ctor_set(x_844, 3, x_4);
lean_ctor_set_uint8(x_844, sizeof(void*)*4, x_843);
return x_844;
}
else
{
uint8_t x_845; 
x_845 = lean_ctor_get_uint8(x_842, sizeof(void*)*4);
if (x_845 == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; 
x_846 = lean_ctor_get(x_4, 1);
lean_inc(x_846);
x_847 = lean_ctor_get(x_4, 2);
lean_inc(x_847);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_848 = x_4;
} else {
 lean_dec_ref(x_4);
 x_848 = lean_box(0);
}
x_849 = lean_ctor_get(x_842, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_842, 1);
lean_inc(x_850);
x_851 = lean_ctor_get(x_842, 2);
lean_inc(x_851);
x_852 = lean_ctor_get(x_842, 3);
lean_inc(x_852);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 lean_ctor_release(x_842, 2);
 lean_ctor_release(x_842, 3);
 x_853 = x_842;
} else {
 lean_dec_ref(x_842);
 x_853 = lean_box(0);
}
x_854 = 1;
if (lean_is_scalar(x_853)) {
 x_855 = lean_alloc_ctor(1, 4, 1);
} else {
 x_855 = x_853;
}
lean_ctor_set(x_855, 0, x_1);
lean_ctor_set(x_855, 1, x_2);
lean_ctor_set(x_855, 2, x_3);
lean_ctor_set(x_855, 3, x_841);
lean_ctor_set_uint8(x_855, sizeof(void*)*4, x_854);
if (lean_is_scalar(x_848)) {
 x_856 = lean_alloc_ctor(1, 4, 1);
} else {
 x_856 = x_848;
}
lean_ctor_set(x_856, 0, x_849);
lean_ctor_set(x_856, 1, x_850);
lean_ctor_set(x_856, 2, x_851);
lean_ctor_set(x_856, 3, x_852);
lean_ctor_set_uint8(x_856, sizeof(void*)*4, x_854);
x_857 = 0;
x_858 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_846);
lean_ctor_set(x_858, 2, x_847);
lean_ctor_set(x_858, 3, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*4, x_857);
return x_858;
}
else
{
lean_object* x_859; uint8_t x_860; lean_object* x_861; 
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 lean_ctor_release(x_842, 2);
 lean_ctor_release(x_842, 3);
 x_859 = x_842;
} else {
 lean_dec_ref(x_842);
 x_859 = lean_box(0);
}
x_860 = 1;
if (lean_is_scalar(x_859)) {
 x_861 = lean_alloc_ctor(1, 4, 1);
} else {
 x_861 = x_859;
}
lean_ctor_set(x_861, 0, x_1);
lean_ctor_set(x_861, 1, x_2);
lean_ctor_set(x_861, 2, x_3);
lean_ctor_set(x_861, 3, x_4);
lean_ctor_set_uint8(x_861, sizeof(void*)*4, x_860);
return x_861;
}
}
}
else
{
uint8_t x_862; 
x_862 = lean_ctor_get_uint8(x_841, sizeof(void*)*4);
if (x_862 == 0)
{
lean_object* x_863; 
x_863 = lean_ctor_get(x_4, 3);
lean_inc(x_863);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; uint8_t x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_876; 
x_864 = lean_ctor_get(x_4, 1);
lean_inc(x_864);
x_865 = lean_ctor_get(x_4, 2);
lean_inc(x_865);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_866 = x_4;
} else {
 lean_dec_ref(x_4);
 x_866 = lean_box(0);
}
x_867 = lean_ctor_get(x_841, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_841, 1);
lean_inc(x_868);
x_869 = lean_ctor_get(x_841, 2);
lean_inc(x_869);
x_870 = lean_ctor_get(x_841, 3);
lean_inc(x_870);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 lean_ctor_release(x_841, 2);
 lean_ctor_release(x_841, 3);
 x_871 = x_841;
} else {
 lean_dec_ref(x_841);
 x_871 = lean_box(0);
}
x_872 = 1;
if (lean_is_scalar(x_871)) {
 x_873 = lean_alloc_ctor(1, 4, 1);
} else {
 x_873 = x_871;
}
lean_ctor_set(x_873, 0, x_1);
lean_ctor_set(x_873, 1, x_2);
lean_ctor_set(x_873, 2, x_3);
lean_ctor_set(x_873, 3, x_867);
lean_ctor_set_uint8(x_873, sizeof(void*)*4, x_872);
if (lean_is_scalar(x_866)) {
 x_874 = lean_alloc_ctor(1, 4, 1);
} else {
 x_874 = x_866;
}
lean_ctor_set(x_874, 0, x_870);
lean_ctor_set(x_874, 1, x_864);
lean_ctor_set(x_874, 2, x_865);
lean_ctor_set(x_874, 3, x_863);
lean_ctor_set_uint8(x_874, sizeof(void*)*4, x_872);
x_875 = 0;
x_876 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_868);
lean_ctor_set(x_876, 2, x_869);
lean_ctor_set(x_876, 3, x_874);
lean_ctor_set_uint8(x_876, sizeof(void*)*4, x_875);
return x_876;
}
else
{
uint8_t x_877; 
x_877 = lean_ctor_get_uint8(x_863, sizeof(void*)*4);
if (x_877 == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; lean_object* x_893; lean_object* x_894; uint8_t x_895; lean_object* x_896; 
x_878 = lean_ctor_get(x_4, 1);
lean_inc(x_878);
x_879 = lean_ctor_get(x_4, 2);
lean_inc(x_879);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_880 = x_4;
} else {
 lean_dec_ref(x_4);
 x_880 = lean_box(0);
}
x_881 = lean_ctor_get(x_841, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_841, 1);
lean_inc(x_882);
x_883 = lean_ctor_get(x_841, 2);
lean_inc(x_883);
x_884 = lean_ctor_get(x_841, 3);
lean_inc(x_884);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 lean_ctor_release(x_841, 2);
 lean_ctor_release(x_841, 3);
 x_885 = x_841;
} else {
 lean_dec_ref(x_841);
 x_885 = lean_box(0);
}
x_886 = lean_ctor_get(x_863, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_863, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_863, 2);
lean_inc(x_888);
x_889 = lean_ctor_get(x_863, 3);
lean_inc(x_889);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 lean_ctor_release(x_863, 2);
 lean_ctor_release(x_863, 3);
 x_890 = x_863;
} else {
 lean_dec_ref(x_863);
 x_890 = lean_box(0);
}
if (lean_is_scalar(x_890)) {
 x_891 = lean_alloc_ctor(1, 4, 1);
} else {
 x_891 = x_890;
}
lean_ctor_set(x_891, 0, x_881);
lean_ctor_set(x_891, 1, x_882);
lean_ctor_set(x_891, 2, x_883);
lean_ctor_set(x_891, 3, x_884);
lean_ctor_set_uint8(x_891, sizeof(void*)*4, x_877);
x_892 = 1;
if (lean_is_scalar(x_885)) {
 x_893 = lean_alloc_ctor(1, 4, 1);
} else {
 x_893 = x_885;
}
lean_ctor_set(x_893, 0, x_1);
lean_ctor_set(x_893, 1, x_2);
lean_ctor_set(x_893, 2, x_3);
lean_ctor_set(x_893, 3, x_891);
lean_ctor_set_uint8(x_893, sizeof(void*)*4, x_892);
if (lean_is_scalar(x_880)) {
 x_894 = lean_alloc_ctor(1, 4, 1);
} else {
 x_894 = x_880;
}
lean_ctor_set(x_894, 0, x_886);
lean_ctor_set(x_894, 1, x_887);
lean_ctor_set(x_894, 2, x_888);
lean_ctor_set(x_894, 3, x_889);
lean_ctor_set_uint8(x_894, sizeof(void*)*4, x_892);
x_895 = 0;
x_896 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_878);
lean_ctor_set(x_896, 2, x_879);
lean_ctor_set(x_896, 3, x_894);
lean_ctor_set_uint8(x_896, sizeof(void*)*4, x_895);
return x_896;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; uint8_t x_905; lean_object* x_906; lean_object* x_907; uint8_t x_908; lean_object* x_909; 
x_897 = lean_ctor_get(x_4, 1);
lean_inc(x_897);
x_898 = lean_ctor_get(x_4, 2);
lean_inc(x_898);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_899 = x_4;
} else {
 lean_dec_ref(x_4);
 x_899 = lean_box(0);
}
x_900 = lean_ctor_get(x_841, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_841, 1);
lean_inc(x_901);
x_902 = lean_ctor_get(x_841, 2);
lean_inc(x_902);
x_903 = lean_ctor_get(x_841, 3);
lean_inc(x_903);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 lean_ctor_release(x_841, 2);
 lean_ctor_release(x_841, 3);
 x_904 = x_841;
} else {
 lean_dec_ref(x_841);
 x_904 = lean_box(0);
}
x_905 = 1;
if (lean_is_scalar(x_904)) {
 x_906 = lean_alloc_ctor(1, 4, 1);
} else {
 x_906 = x_904;
}
lean_ctor_set(x_906, 0, x_1);
lean_ctor_set(x_906, 1, x_2);
lean_ctor_set(x_906, 2, x_3);
lean_ctor_set(x_906, 3, x_900);
lean_ctor_set_uint8(x_906, sizeof(void*)*4, x_905);
if (lean_is_scalar(x_899)) {
 x_907 = lean_alloc_ctor(1, 4, 1);
} else {
 x_907 = x_899;
}
lean_ctor_set(x_907, 0, x_903);
lean_ctor_set(x_907, 1, x_897);
lean_ctor_set(x_907, 2, x_898);
lean_ctor_set(x_907, 3, x_863);
lean_ctor_set_uint8(x_907, sizeof(void*)*4, x_905);
x_908 = 0;
x_909 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_901);
lean_ctor_set(x_909, 2, x_902);
lean_ctor_set(x_909, 3, x_907);
lean_ctor_set_uint8(x_909, sizeof(void*)*4, x_908);
return x_909;
}
}
}
else
{
lean_object* x_910; 
x_910 = lean_ctor_get(x_4, 3);
lean_inc(x_910);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; uint8_t x_912; lean_object* x_913; 
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 lean_ctor_release(x_841, 2);
 lean_ctor_release(x_841, 3);
 x_911 = x_841;
} else {
 lean_dec_ref(x_841);
 x_911 = lean_box(0);
}
x_912 = 1;
if (lean_is_scalar(x_911)) {
 x_913 = lean_alloc_ctor(1, 4, 1);
} else {
 x_913 = x_911;
}
lean_ctor_set(x_913, 0, x_1);
lean_ctor_set(x_913, 1, x_2);
lean_ctor_set(x_913, 2, x_3);
lean_ctor_set(x_913, 3, x_4);
lean_ctor_set_uint8(x_913, sizeof(void*)*4, x_912);
return x_913;
}
else
{
uint8_t x_914; 
x_914 = lean_ctor_get_uint8(x_910, sizeof(void*)*4);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; uint8_t x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; uint8_t x_927; lean_object* x_928; 
x_915 = lean_ctor_get(x_4, 1);
lean_inc(x_915);
x_916 = lean_ctor_get(x_4, 2);
lean_inc(x_916);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_917 = x_4;
} else {
 lean_dec_ref(x_4);
 x_917 = lean_box(0);
}
x_918 = lean_ctor_get(x_910, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_910, 1);
lean_inc(x_919);
x_920 = lean_ctor_get(x_910, 2);
lean_inc(x_920);
x_921 = lean_ctor_get(x_910, 3);
lean_inc(x_921);
if (lean_is_exclusive(x_910)) {
 lean_ctor_release(x_910, 0);
 lean_ctor_release(x_910, 1);
 lean_ctor_release(x_910, 2);
 lean_ctor_release(x_910, 3);
 x_922 = x_910;
} else {
 lean_dec_ref(x_910);
 x_922 = lean_box(0);
}
x_923 = 1;
lean_inc(x_841);
if (lean_is_scalar(x_922)) {
 x_924 = lean_alloc_ctor(1, 4, 1);
} else {
 x_924 = x_922;
}
lean_ctor_set(x_924, 0, x_1);
lean_ctor_set(x_924, 1, x_2);
lean_ctor_set(x_924, 2, x_3);
lean_ctor_set(x_924, 3, x_841);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 lean_ctor_release(x_841, 2);
 lean_ctor_release(x_841, 3);
 x_925 = x_841;
} else {
 lean_dec_ref(x_841);
 x_925 = lean_box(0);
}
lean_ctor_set_uint8(x_924, sizeof(void*)*4, x_923);
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(1, 4, 1);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_918);
lean_ctor_set(x_926, 1, x_919);
lean_ctor_set(x_926, 2, x_920);
lean_ctor_set(x_926, 3, x_921);
lean_ctor_set_uint8(x_926, sizeof(void*)*4, x_923);
x_927 = 0;
if (lean_is_scalar(x_917)) {
 x_928 = lean_alloc_ctor(1, 4, 1);
} else {
 x_928 = x_917;
}
lean_ctor_set(x_928, 0, x_924);
lean_ctor_set(x_928, 1, x_915);
lean_ctor_set(x_928, 2, x_916);
lean_ctor_set(x_928, 3, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*4, x_927);
return x_928;
}
else
{
lean_object* x_929; uint8_t x_930; lean_object* x_931; 
lean_dec(x_841);
if (lean_is_exclusive(x_910)) {
 lean_ctor_release(x_910, 0);
 lean_ctor_release(x_910, 1);
 lean_ctor_release(x_910, 2);
 lean_ctor_release(x_910, 3);
 x_929 = x_910;
} else {
 lean_dec_ref(x_910);
 x_929 = lean_box(0);
}
x_930 = 1;
if (lean_is_scalar(x_929)) {
 x_931 = lean_alloc_ctor(1, 4, 1);
} else {
 x_931 = x_929;
}
lean_ctor_set(x_931, 0, x_1);
lean_ctor_set(x_931, 1, x_2);
lean_ctor_set(x_931, 2, x_3);
lean_ctor_set(x_931, 3, x_4);
lean_ctor_set_uint8(x_931, sizeof(void*)*4, x_930);
return x_931;
}
}
}
}
}
else
{
uint8_t x_932; lean_object* x_933; 
x_932 = 1;
x_933 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_933, 0, x_1);
lean_ctor_set(x_933, 1, x_2);
lean_ctor_set(x_933, 2, x_3);
lean_ctor_set(x_933, 3, x_4);
lean_ctor_set_uint8(x_933, sizeof(void*)*4, x_932);
return x_933;
}
}
}
}
}
}
else
{
uint8_t x_934; 
x_934 = lean_ctor_get_uint8(x_241, sizeof(void*)*4);
if (x_934 == 0)
{
uint8_t x_935; 
x_935 = !lean_is_exclusive(x_1);
if (x_935 == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; uint8_t x_940; 
x_936 = lean_ctor_get(x_1, 1);
x_937 = lean_ctor_get(x_1, 2);
x_938 = lean_ctor_get(x_1, 3);
x_939 = lean_ctor_get(x_1, 0);
lean_dec(x_939);
x_940 = !lean_is_exclusive(x_241);
if (x_940 == 0)
{
uint8_t x_941; uint8_t x_942; lean_object* x_943; 
x_941 = 1;
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_941);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_938);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_941);
x_942 = 0;
x_943 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_943, 0, x_241);
lean_ctor_set(x_943, 1, x_936);
lean_ctor_set(x_943, 2, x_937);
lean_ctor_set(x_943, 3, x_1);
lean_ctor_set_uint8(x_943, sizeof(void*)*4, x_942);
return x_943;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_948; lean_object* x_949; uint8_t x_950; lean_object* x_951; 
x_944 = lean_ctor_get(x_241, 0);
x_945 = lean_ctor_get(x_241, 1);
x_946 = lean_ctor_get(x_241, 2);
x_947 = lean_ctor_get(x_241, 3);
lean_inc(x_947);
lean_inc(x_946);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_241);
x_948 = 1;
x_949 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_949, 0, x_944);
lean_ctor_set(x_949, 1, x_945);
lean_ctor_set(x_949, 2, x_946);
lean_ctor_set(x_949, 3, x_947);
lean_ctor_set_uint8(x_949, sizeof(void*)*4, x_948);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_938);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_948);
x_950 = 0;
x_951 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_951, 0, x_949);
lean_ctor_set(x_951, 1, x_936);
lean_ctor_set(x_951, 2, x_937);
lean_ctor_set(x_951, 3, x_1);
lean_ctor_set_uint8(x_951, sizeof(void*)*4, x_950);
return x_951;
}
}
else
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint8_t x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; lean_object* x_964; 
x_952 = lean_ctor_get(x_1, 1);
x_953 = lean_ctor_get(x_1, 2);
x_954 = lean_ctor_get(x_1, 3);
lean_inc(x_954);
lean_inc(x_953);
lean_inc(x_952);
lean_dec(x_1);
x_955 = lean_ctor_get(x_241, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_241, 1);
lean_inc(x_956);
x_957 = lean_ctor_get(x_241, 2);
lean_inc(x_957);
x_958 = lean_ctor_get(x_241, 3);
lean_inc(x_958);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_959 = x_241;
} else {
 lean_dec_ref(x_241);
 x_959 = lean_box(0);
}
x_960 = 1;
if (lean_is_scalar(x_959)) {
 x_961 = lean_alloc_ctor(1, 4, 1);
} else {
 x_961 = x_959;
}
lean_ctor_set(x_961, 0, x_955);
lean_ctor_set(x_961, 1, x_956);
lean_ctor_set(x_961, 2, x_957);
lean_ctor_set(x_961, 3, x_958);
lean_ctor_set_uint8(x_961, sizeof(void*)*4, x_960);
x_962 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_962, 0, x_954);
lean_ctor_set(x_962, 1, x_2);
lean_ctor_set(x_962, 2, x_3);
lean_ctor_set(x_962, 3, x_4);
lean_ctor_set_uint8(x_962, sizeof(void*)*4, x_960);
x_963 = 0;
x_964 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_964, 0, x_961);
lean_ctor_set(x_964, 1, x_952);
lean_ctor_set(x_964, 2, x_953);
lean_ctor_set(x_964, 3, x_962);
lean_ctor_set_uint8(x_964, sizeof(void*)*4, x_963);
return x_964;
}
}
else
{
lean_object* x_965; 
x_965 = lean_ctor_get(x_1, 3);
lean_inc(x_965);
if (lean_obj_tag(x_965) == 0)
{
uint8_t x_966; 
x_966 = !lean_is_exclusive(x_241);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_967 = lean_ctor_get(x_241, 3);
lean_dec(x_967);
x_968 = lean_ctor_get(x_241, 2);
lean_dec(x_968);
x_969 = lean_ctor_get(x_241, 1);
lean_dec(x_969);
x_970 = lean_ctor_get(x_241, 0);
lean_dec(x_970);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_971; 
x_971 = 1;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_3);
lean_ctor_set(x_241, 1, x_2);
lean_ctor_set(x_241, 0, x_1);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_971);
return x_241;
}
else
{
uint8_t x_972; 
x_972 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_972 == 0)
{
lean_object* x_973; 
x_973 = lean_ctor_get(x_4, 0);
lean_inc(x_973);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; 
x_974 = lean_ctor_get(x_4, 3);
lean_inc(x_974);
if (lean_obj_tag(x_974) == 0)
{
uint8_t x_975; 
x_975 = 1;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_3);
lean_ctor_set(x_241, 1, x_2);
lean_ctor_set(x_241, 0, x_1);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_975);
return x_241;
}
else
{
uint8_t x_976; 
x_976 = lean_ctor_get_uint8(x_974, sizeof(void*)*4);
if (x_976 == 0)
{
uint8_t x_977; 
x_977 = !lean_is_exclusive(x_4);
if (x_977 == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; uint8_t x_982; 
x_978 = lean_ctor_get(x_4, 1);
x_979 = lean_ctor_get(x_4, 2);
x_980 = lean_ctor_get(x_4, 3);
lean_dec(x_980);
x_981 = lean_ctor_get(x_4, 0);
lean_dec(x_981);
x_982 = !lean_is_exclusive(x_974);
if (x_982 == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; uint8_t x_987; uint8_t x_988; 
x_983 = lean_ctor_get(x_974, 0);
x_984 = lean_ctor_get(x_974, 1);
x_985 = lean_ctor_get(x_974, 2);
x_986 = lean_ctor_get(x_974, 3);
x_987 = 1;
lean_ctor_set(x_974, 3, x_973);
lean_ctor_set(x_974, 2, x_3);
lean_ctor_set(x_974, 1, x_2);
lean_ctor_set(x_974, 0, x_1);
lean_ctor_set_uint8(x_974, sizeof(void*)*4, x_987);
lean_ctor_set(x_4, 3, x_986);
lean_ctor_set(x_4, 2, x_985);
lean_ctor_set(x_4, 1, x_984);
lean_ctor_set(x_4, 0, x_983);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_987);
x_988 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_979);
lean_ctor_set(x_241, 1, x_978);
lean_ctor_set(x_241, 0, x_974);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_988);
return x_241;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; uint8_t x_993; lean_object* x_994; uint8_t x_995; 
x_989 = lean_ctor_get(x_974, 0);
x_990 = lean_ctor_get(x_974, 1);
x_991 = lean_ctor_get(x_974, 2);
x_992 = lean_ctor_get(x_974, 3);
lean_inc(x_992);
lean_inc(x_991);
lean_inc(x_990);
lean_inc(x_989);
lean_dec(x_974);
x_993 = 1;
x_994 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_994, 0, x_1);
lean_ctor_set(x_994, 1, x_2);
lean_ctor_set(x_994, 2, x_3);
lean_ctor_set(x_994, 3, x_973);
lean_ctor_set_uint8(x_994, sizeof(void*)*4, x_993);
lean_ctor_set(x_4, 3, x_992);
lean_ctor_set(x_4, 2, x_991);
lean_ctor_set(x_4, 1, x_990);
lean_ctor_set(x_4, 0, x_989);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_993);
x_995 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_979);
lean_ctor_set(x_241, 1, x_978);
lean_ctor_set(x_241, 0, x_994);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_995);
return x_241;
}
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; lean_object* x_1004; lean_object* x_1005; uint8_t x_1006; 
x_996 = lean_ctor_get(x_4, 1);
x_997 = lean_ctor_get(x_4, 2);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_4);
x_998 = lean_ctor_get(x_974, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_974, 1);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_974, 2);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_974, 3);
lean_inc(x_1001);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 lean_ctor_release(x_974, 2);
 lean_ctor_release(x_974, 3);
 x_1002 = x_974;
} else {
 lean_dec_ref(x_974);
 x_1002 = lean_box(0);
}
x_1003 = 1;
if (lean_is_scalar(x_1002)) {
 x_1004 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1004 = x_1002;
}
lean_ctor_set(x_1004, 0, x_1);
lean_ctor_set(x_1004, 1, x_2);
lean_ctor_set(x_1004, 2, x_3);
lean_ctor_set(x_1004, 3, x_973);
lean_ctor_set_uint8(x_1004, sizeof(void*)*4, x_1003);
x_1005 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1005, 0, x_998);
lean_ctor_set(x_1005, 1, x_999);
lean_ctor_set(x_1005, 2, x_1000);
lean_ctor_set(x_1005, 3, x_1001);
lean_ctor_set_uint8(x_1005, sizeof(void*)*4, x_1003);
x_1006 = 0;
lean_ctor_set(x_241, 3, x_1005);
lean_ctor_set(x_241, 2, x_997);
lean_ctor_set(x_241, 1, x_996);
lean_ctor_set(x_241, 0, x_1004);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1006);
return x_241;
}
}
else
{
uint8_t x_1007; 
lean_free_object(x_241);
x_1007 = !lean_is_exclusive(x_974);
if (x_1007 == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; uint8_t x_1012; 
x_1008 = lean_ctor_get(x_974, 3);
lean_dec(x_1008);
x_1009 = lean_ctor_get(x_974, 2);
lean_dec(x_1009);
x_1010 = lean_ctor_get(x_974, 1);
lean_dec(x_1010);
x_1011 = lean_ctor_get(x_974, 0);
lean_dec(x_1011);
x_1012 = 1;
lean_ctor_set(x_974, 3, x_4);
lean_ctor_set(x_974, 2, x_3);
lean_ctor_set(x_974, 1, x_2);
lean_ctor_set(x_974, 0, x_1);
lean_ctor_set_uint8(x_974, sizeof(void*)*4, x_1012);
return x_974;
}
else
{
uint8_t x_1013; lean_object* x_1014; 
lean_dec(x_974);
x_1013 = 1;
x_1014 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1014, 0, x_1);
lean_ctor_set(x_1014, 1, x_2);
lean_ctor_set(x_1014, 2, x_3);
lean_ctor_set(x_1014, 3, x_4);
lean_ctor_set_uint8(x_1014, sizeof(void*)*4, x_1013);
return x_1014;
}
}
}
}
else
{
uint8_t x_1015; 
x_1015 = lean_ctor_get_uint8(x_973, sizeof(void*)*4);
if (x_1015 == 0)
{
lean_object* x_1016; 
x_1016 = lean_ctor_get(x_4, 3);
lean_inc(x_1016);
if (lean_obj_tag(x_1016) == 0)
{
uint8_t x_1017; 
x_1017 = !lean_is_exclusive(x_4);
if (x_1017 == 0)
{
lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; 
x_1018 = lean_ctor_get(x_4, 3);
lean_dec(x_1018);
x_1019 = lean_ctor_get(x_4, 0);
lean_dec(x_1019);
x_1020 = !lean_is_exclusive(x_973);
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; uint8_t x_1025; uint8_t x_1026; 
x_1021 = lean_ctor_get(x_973, 0);
x_1022 = lean_ctor_get(x_973, 1);
x_1023 = lean_ctor_get(x_973, 2);
x_1024 = lean_ctor_get(x_973, 3);
x_1025 = 1;
lean_ctor_set(x_973, 3, x_1021);
lean_ctor_set(x_973, 2, x_3);
lean_ctor_set(x_973, 1, x_2);
lean_ctor_set(x_973, 0, x_1);
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_1025);
lean_ctor_set(x_4, 0, x_1024);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1025);
x_1026 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1023);
lean_ctor_set(x_241, 1, x_1022);
lean_ctor_set(x_241, 0, x_973);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1026);
return x_241;
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; uint8_t x_1031; lean_object* x_1032; uint8_t x_1033; 
x_1027 = lean_ctor_get(x_973, 0);
x_1028 = lean_ctor_get(x_973, 1);
x_1029 = lean_ctor_get(x_973, 2);
x_1030 = lean_ctor_get(x_973, 3);
lean_inc(x_1030);
lean_inc(x_1029);
lean_inc(x_1028);
lean_inc(x_1027);
lean_dec(x_973);
x_1031 = 1;
x_1032 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1032, 0, x_1);
lean_ctor_set(x_1032, 1, x_2);
lean_ctor_set(x_1032, 2, x_3);
lean_ctor_set(x_1032, 3, x_1027);
lean_ctor_set_uint8(x_1032, sizeof(void*)*4, x_1031);
lean_ctor_set(x_4, 0, x_1030);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1031);
x_1033 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1029);
lean_ctor_set(x_241, 1, x_1028);
lean_ctor_set(x_241, 0, x_1032);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1033);
return x_241;
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; uint8_t x_1041; lean_object* x_1042; lean_object* x_1043; uint8_t x_1044; 
x_1034 = lean_ctor_get(x_4, 1);
x_1035 = lean_ctor_get(x_4, 2);
lean_inc(x_1035);
lean_inc(x_1034);
lean_dec(x_4);
x_1036 = lean_ctor_get(x_973, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_973, 1);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_973, 2);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_973, 3);
lean_inc(x_1039);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 lean_ctor_release(x_973, 2);
 lean_ctor_release(x_973, 3);
 x_1040 = x_973;
} else {
 lean_dec_ref(x_973);
 x_1040 = lean_box(0);
}
x_1041 = 1;
if (lean_is_scalar(x_1040)) {
 x_1042 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1042 = x_1040;
}
lean_ctor_set(x_1042, 0, x_1);
lean_ctor_set(x_1042, 1, x_2);
lean_ctor_set(x_1042, 2, x_3);
lean_ctor_set(x_1042, 3, x_1036);
lean_ctor_set_uint8(x_1042, sizeof(void*)*4, x_1041);
x_1043 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1043, 0, x_1039);
lean_ctor_set(x_1043, 1, x_1034);
lean_ctor_set(x_1043, 2, x_1035);
lean_ctor_set(x_1043, 3, x_1016);
lean_ctor_set_uint8(x_1043, sizeof(void*)*4, x_1041);
x_1044 = 0;
lean_ctor_set(x_241, 3, x_1043);
lean_ctor_set(x_241, 2, x_1038);
lean_ctor_set(x_241, 1, x_1037);
lean_ctor_set(x_241, 0, x_1042);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1044);
return x_241;
}
}
else
{
uint8_t x_1045; 
x_1045 = lean_ctor_get_uint8(x_1016, sizeof(void*)*4);
if (x_1045 == 0)
{
uint8_t x_1046; 
x_1046 = !lean_is_exclusive(x_4);
if (x_1046 == 0)
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; uint8_t x_1051; 
x_1047 = lean_ctor_get(x_4, 1);
x_1048 = lean_ctor_get(x_4, 2);
x_1049 = lean_ctor_get(x_4, 3);
lean_dec(x_1049);
x_1050 = lean_ctor_get(x_4, 0);
lean_dec(x_1050);
x_1051 = !lean_is_exclusive(x_973);
if (x_1051 == 0)
{
uint8_t x_1052; 
x_1052 = !lean_is_exclusive(x_1016);
if (x_1052 == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; uint8_t x_1062; 
x_1053 = lean_ctor_get(x_973, 0);
x_1054 = lean_ctor_get(x_973, 1);
x_1055 = lean_ctor_get(x_973, 2);
x_1056 = lean_ctor_get(x_973, 3);
x_1057 = lean_ctor_get(x_1016, 0);
x_1058 = lean_ctor_get(x_1016, 1);
x_1059 = lean_ctor_get(x_1016, 2);
x_1060 = lean_ctor_get(x_1016, 3);
lean_ctor_set(x_1016, 3, x_1056);
lean_ctor_set(x_1016, 2, x_1055);
lean_ctor_set(x_1016, 1, x_1054);
lean_ctor_set(x_1016, 0, x_1053);
x_1061 = 1;
lean_ctor_set(x_973, 3, x_1016);
lean_ctor_set(x_973, 2, x_3);
lean_ctor_set(x_973, 1, x_2);
lean_ctor_set(x_973, 0, x_1);
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_1061);
lean_ctor_set(x_4, 3, x_1060);
lean_ctor_set(x_4, 2, x_1059);
lean_ctor_set(x_4, 1, x_1058);
lean_ctor_set(x_4, 0, x_1057);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1061);
x_1062 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1048);
lean_ctor_set(x_241, 1, x_1047);
lean_ctor_set(x_241, 0, x_973);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1062);
return x_241;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; uint8_t x_1072; uint8_t x_1073; 
x_1063 = lean_ctor_get(x_973, 0);
x_1064 = lean_ctor_get(x_973, 1);
x_1065 = lean_ctor_get(x_973, 2);
x_1066 = lean_ctor_get(x_973, 3);
x_1067 = lean_ctor_get(x_1016, 0);
x_1068 = lean_ctor_get(x_1016, 1);
x_1069 = lean_ctor_get(x_1016, 2);
x_1070 = lean_ctor_get(x_1016, 3);
lean_inc(x_1070);
lean_inc(x_1069);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_1016);
x_1071 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1071, 0, x_1063);
lean_ctor_set(x_1071, 1, x_1064);
lean_ctor_set(x_1071, 2, x_1065);
lean_ctor_set(x_1071, 3, x_1066);
lean_ctor_set_uint8(x_1071, sizeof(void*)*4, x_1045);
x_1072 = 1;
lean_ctor_set(x_973, 3, x_1071);
lean_ctor_set(x_973, 2, x_3);
lean_ctor_set(x_973, 1, x_2);
lean_ctor_set(x_973, 0, x_1);
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_1072);
lean_ctor_set(x_4, 3, x_1070);
lean_ctor_set(x_4, 2, x_1069);
lean_ctor_set(x_4, 1, x_1068);
lean_ctor_set(x_4, 0, x_1067);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1072);
x_1073 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1048);
lean_ctor_set(x_241, 1, x_1047);
lean_ctor_set(x_241, 0, x_973);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1073);
return x_241;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; uint8_t x_1084; lean_object* x_1085; uint8_t x_1086; 
x_1074 = lean_ctor_get(x_973, 0);
x_1075 = lean_ctor_get(x_973, 1);
x_1076 = lean_ctor_get(x_973, 2);
x_1077 = lean_ctor_get(x_973, 3);
lean_inc(x_1077);
lean_inc(x_1076);
lean_inc(x_1075);
lean_inc(x_1074);
lean_dec(x_973);
x_1078 = lean_ctor_get(x_1016, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1016, 1);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1016, 2);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1016, 3);
lean_inc(x_1081);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 lean_ctor_release(x_1016, 2);
 lean_ctor_release(x_1016, 3);
 x_1082 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1082 = lean_box(0);
}
if (lean_is_scalar(x_1082)) {
 x_1083 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1083 = x_1082;
}
lean_ctor_set(x_1083, 0, x_1074);
lean_ctor_set(x_1083, 1, x_1075);
lean_ctor_set(x_1083, 2, x_1076);
lean_ctor_set(x_1083, 3, x_1077);
lean_ctor_set_uint8(x_1083, sizeof(void*)*4, x_1045);
x_1084 = 1;
x_1085 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1085, 0, x_1);
lean_ctor_set(x_1085, 1, x_2);
lean_ctor_set(x_1085, 2, x_3);
lean_ctor_set(x_1085, 3, x_1083);
lean_ctor_set_uint8(x_1085, sizeof(void*)*4, x_1084);
lean_ctor_set(x_4, 3, x_1081);
lean_ctor_set(x_4, 2, x_1080);
lean_ctor_set(x_4, 1, x_1079);
lean_ctor_set(x_4, 0, x_1078);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1084);
x_1086 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1048);
lean_ctor_set(x_241, 1, x_1047);
lean_ctor_set(x_241, 0, x_1085);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1086);
return x_241;
}
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; uint8_t x_1100; lean_object* x_1101; lean_object* x_1102; uint8_t x_1103; 
x_1087 = lean_ctor_get(x_4, 1);
x_1088 = lean_ctor_get(x_4, 2);
lean_inc(x_1088);
lean_inc(x_1087);
lean_dec(x_4);
x_1089 = lean_ctor_get(x_973, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_973, 1);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_973, 2);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_973, 3);
lean_inc(x_1092);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 lean_ctor_release(x_973, 2);
 lean_ctor_release(x_973, 3);
 x_1093 = x_973;
} else {
 lean_dec_ref(x_973);
 x_1093 = lean_box(0);
}
x_1094 = lean_ctor_get(x_1016, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1016, 1);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1016, 2);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1016, 3);
lean_inc(x_1097);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 lean_ctor_release(x_1016, 2);
 lean_ctor_release(x_1016, 3);
 x_1098 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_1089);
lean_ctor_set(x_1099, 1, x_1090);
lean_ctor_set(x_1099, 2, x_1091);
lean_ctor_set(x_1099, 3, x_1092);
lean_ctor_set_uint8(x_1099, sizeof(void*)*4, x_1045);
x_1100 = 1;
if (lean_is_scalar(x_1093)) {
 x_1101 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1101 = x_1093;
}
lean_ctor_set(x_1101, 0, x_1);
lean_ctor_set(x_1101, 1, x_2);
lean_ctor_set(x_1101, 2, x_3);
lean_ctor_set(x_1101, 3, x_1099);
lean_ctor_set_uint8(x_1101, sizeof(void*)*4, x_1100);
x_1102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1102, 0, x_1094);
lean_ctor_set(x_1102, 1, x_1095);
lean_ctor_set(x_1102, 2, x_1096);
lean_ctor_set(x_1102, 3, x_1097);
lean_ctor_set_uint8(x_1102, sizeof(void*)*4, x_1100);
x_1103 = 0;
lean_ctor_set(x_241, 3, x_1102);
lean_ctor_set(x_241, 2, x_1088);
lean_ctor_set(x_241, 1, x_1087);
lean_ctor_set(x_241, 0, x_1101);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1103);
return x_241;
}
}
else
{
uint8_t x_1104; 
x_1104 = !lean_is_exclusive(x_4);
if (x_1104 == 0)
{
lean_object* x_1105; lean_object* x_1106; uint8_t x_1107; 
x_1105 = lean_ctor_get(x_4, 3);
lean_dec(x_1105);
x_1106 = lean_ctor_get(x_4, 0);
lean_dec(x_1106);
x_1107 = !lean_is_exclusive(x_973);
if (x_1107 == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; uint8_t x_1112; uint8_t x_1113; 
x_1108 = lean_ctor_get(x_973, 0);
x_1109 = lean_ctor_get(x_973, 1);
x_1110 = lean_ctor_get(x_973, 2);
x_1111 = lean_ctor_get(x_973, 3);
x_1112 = 1;
lean_ctor_set(x_973, 3, x_1108);
lean_ctor_set(x_973, 2, x_3);
lean_ctor_set(x_973, 1, x_2);
lean_ctor_set(x_973, 0, x_1);
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_1112);
lean_ctor_set(x_4, 0, x_1111);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1112);
x_1113 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1110);
lean_ctor_set(x_241, 1, x_1109);
lean_ctor_set(x_241, 0, x_973);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1113);
return x_241;
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; uint8_t x_1118; lean_object* x_1119; uint8_t x_1120; 
x_1114 = lean_ctor_get(x_973, 0);
x_1115 = lean_ctor_get(x_973, 1);
x_1116 = lean_ctor_get(x_973, 2);
x_1117 = lean_ctor_get(x_973, 3);
lean_inc(x_1117);
lean_inc(x_1116);
lean_inc(x_1115);
lean_inc(x_1114);
lean_dec(x_973);
x_1118 = 1;
x_1119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1119, 0, x_1);
lean_ctor_set(x_1119, 1, x_2);
lean_ctor_set(x_1119, 2, x_3);
lean_ctor_set(x_1119, 3, x_1114);
lean_ctor_set_uint8(x_1119, sizeof(void*)*4, x_1118);
lean_ctor_set(x_4, 0, x_1117);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1118);
x_1120 = 0;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_1116);
lean_ctor_set(x_241, 1, x_1115);
lean_ctor_set(x_241, 0, x_1119);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1120);
return x_241;
}
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; 
x_1121 = lean_ctor_get(x_4, 1);
x_1122 = lean_ctor_get(x_4, 2);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_4);
x_1123 = lean_ctor_get(x_973, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_973, 1);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_973, 2);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_973, 3);
lean_inc(x_1126);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 lean_ctor_release(x_973, 2);
 lean_ctor_release(x_973, 3);
 x_1127 = x_973;
} else {
 lean_dec_ref(x_973);
 x_1127 = lean_box(0);
}
x_1128 = 1;
if (lean_is_scalar(x_1127)) {
 x_1129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1129 = x_1127;
}
lean_ctor_set(x_1129, 0, x_1);
lean_ctor_set(x_1129, 1, x_2);
lean_ctor_set(x_1129, 2, x_3);
lean_ctor_set(x_1129, 3, x_1123);
lean_ctor_set_uint8(x_1129, sizeof(void*)*4, x_1128);
x_1130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1130, 0, x_1126);
lean_ctor_set(x_1130, 1, x_1121);
lean_ctor_set(x_1130, 2, x_1122);
lean_ctor_set(x_1130, 3, x_1016);
lean_ctor_set_uint8(x_1130, sizeof(void*)*4, x_1128);
x_1131 = 0;
lean_ctor_set(x_241, 3, x_1130);
lean_ctor_set(x_241, 2, x_1125);
lean_ctor_set(x_241, 1, x_1124);
lean_ctor_set(x_241, 0, x_1129);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1131);
return x_241;
}
}
}
}
else
{
lean_object* x_1132; 
lean_free_object(x_241);
x_1132 = lean_ctor_get(x_4, 3);
lean_inc(x_1132);
if (lean_obj_tag(x_1132) == 0)
{
uint8_t x_1133; 
x_1133 = !lean_is_exclusive(x_973);
if (x_1133 == 0)
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; uint8_t x_1138; 
x_1134 = lean_ctor_get(x_973, 3);
lean_dec(x_1134);
x_1135 = lean_ctor_get(x_973, 2);
lean_dec(x_1135);
x_1136 = lean_ctor_get(x_973, 1);
lean_dec(x_1136);
x_1137 = lean_ctor_get(x_973, 0);
lean_dec(x_1137);
x_1138 = 1;
lean_ctor_set(x_973, 3, x_4);
lean_ctor_set(x_973, 2, x_3);
lean_ctor_set(x_973, 1, x_2);
lean_ctor_set(x_973, 0, x_1);
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_1138);
return x_973;
}
else
{
uint8_t x_1139; lean_object* x_1140; 
lean_dec(x_973);
x_1139 = 1;
x_1140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1140, 0, x_1);
lean_ctor_set(x_1140, 1, x_2);
lean_ctor_set(x_1140, 2, x_3);
lean_ctor_set(x_1140, 3, x_4);
lean_ctor_set_uint8(x_1140, sizeof(void*)*4, x_1139);
return x_1140;
}
}
else
{
uint8_t x_1141; 
x_1141 = lean_ctor_get_uint8(x_1132, sizeof(void*)*4);
if (x_1141 == 0)
{
uint8_t x_1142; 
x_1142 = !lean_is_exclusive(x_4);
if (x_1142 == 0)
{
lean_object* x_1143; lean_object* x_1144; uint8_t x_1145; 
x_1143 = lean_ctor_get(x_4, 3);
lean_dec(x_1143);
x_1144 = lean_ctor_get(x_4, 0);
lean_dec(x_1144);
x_1145 = !lean_is_exclusive(x_1132);
if (x_1145 == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; uint8_t x_1151; 
x_1146 = lean_ctor_get(x_1132, 0);
x_1147 = lean_ctor_get(x_1132, 1);
x_1148 = lean_ctor_get(x_1132, 2);
x_1149 = lean_ctor_get(x_1132, 3);
x_1150 = 1;
lean_inc(x_973);
lean_ctor_set(x_1132, 3, x_973);
lean_ctor_set(x_1132, 2, x_3);
lean_ctor_set(x_1132, 1, x_2);
lean_ctor_set(x_1132, 0, x_1);
x_1151 = !lean_is_exclusive(x_973);
if (x_1151 == 0)
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; 
x_1152 = lean_ctor_get(x_973, 3);
lean_dec(x_1152);
x_1153 = lean_ctor_get(x_973, 2);
lean_dec(x_1153);
x_1154 = lean_ctor_get(x_973, 1);
lean_dec(x_1154);
x_1155 = lean_ctor_get(x_973, 0);
lean_dec(x_1155);
lean_ctor_set_uint8(x_1132, sizeof(void*)*4, x_1150);
lean_ctor_set(x_973, 3, x_1149);
lean_ctor_set(x_973, 2, x_1148);
lean_ctor_set(x_973, 1, x_1147);
lean_ctor_set(x_973, 0, x_1146);
lean_ctor_set_uint8(x_973, sizeof(void*)*4, x_1150);
x_1156 = 0;
lean_ctor_set(x_4, 3, x_973);
lean_ctor_set(x_4, 0, x_1132);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1156);
return x_4;
}
else
{
lean_object* x_1157; uint8_t x_1158; 
lean_dec(x_973);
lean_ctor_set_uint8(x_1132, sizeof(void*)*4, x_1150);
x_1157 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1157, 0, x_1146);
lean_ctor_set(x_1157, 1, x_1147);
lean_ctor_set(x_1157, 2, x_1148);
lean_ctor_set(x_1157, 3, x_1149);
lean_ctor_set_uint8(x_1157, sizeof(void*)*4, x_1150);
x_1158 = 0;
lean_ctor_set(x_4, 3, x_1157);
lean_ctor_set(x_4, 0, x_1132);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1158);
return x_4;
}
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; uint8_t x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; uint8_t x_1167; 
x_1159 = lean_ctor_get(x_1132, 0);
x_1160 = lean_ctor_get(x_1132, 1);
x_1161 = lean_ctor_get(x_1132, 2);
x_1162 = lean_ctor_get(x_1132, 3);
lean_inc(x_1162);
lean_inc(x_1161);
lean_inc(x_1160);
lean_inc(x_1159);
lean_dec(x_1132);
x_1163 = 1;
lean_inc(x_973);
x_1164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1164, 0, x_1);
lean_ctor_set(x_1164, 1, x_2);
lean_ctor_set(x_1164, 2, x_3);
lean_ctor_set(x_1164, 3, x_973);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 lean_ctor_release(x_973, 2);
 lean_ctor_release(x_973, 3);
 x_1165 = x_973;
} else {
 lean_dec_ref(x_973);
 x_1165 = lean_box(0);
}
lean_ctor_set_uint8(x_1164, sizeof(void*)*4, x_1163);
if (lean_is_scalar(x_1165)) {
 x_1166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1166 = x_1165;
}
lean_ctor_set(x_1166, 0, x_1159);
lean_ctor_set(x_1166, 1, x_1160);
lean_ctor_set(x_1166, 2, x_1161);
lean_ctor_set(x_1166, 3, x_1162);
lean_ctor_set_uint8(x_1166, sizeof(void*)*4, x_1163);
x_1167 = 0;
lean_ctor_set(x_4, 3, x_1166);
lean_ctor_set(x_4, 0, x_1164);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1167);
return x_4;
}
}
else
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; lean_object* x_1180; 
x_1168 = lean_ctor_get(x_4, 1);
x_1169 = lean_ctor_get(x_4, 2);
lean_inc(x_1169);
lean_inc(x_1168);
lean_dec(x_4);
x_1170 = lean_ctor_get(x_1132, 0);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1132, 1);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1132, 2);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1132, 3);
lean_inc(x_1173);
if (lean_is_exclusive(x_1132)) {
 lean_ctor_release(x_1132, 0);
 lean_ctor_release(x_1132, 1);
 lean_ctor_release(x_1132, 2);
 lean_ctor_release(x_1132, 3);
 x_1174 = x_1132;
} else {
 lean_dec_ref(x_1132);
 x_1174 = lean_box(0);
}
x_1175 = 1;
lean_inc(x_973);
if (lean_is_scalar(x_1174)) {
 x_1176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1176 = x_1174;
}
lean_ctor_set(x_1176, 0, x_1);
lean_ctor_set(x_1176, 1, x_2);
lean_ctor_set(x_1176, 2, x_3);
lean_ctor_set(x_1176, 3, x_973);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 lean_ctor_release(x_973, 2);
 lean_ctor_release(x_973, 3);
 x_1177 = x_973;
} else {
 lean_dec_ref(x_973);
 x_1177 = lean_box(0);
}
lean_ctor_set_uint8(x_1176, sizeof(void*)*4, x_1175);
if (lean_is_scalar(x_1177)) {
 x_1178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1178 = x_1177;
}
lean_ctor_set(x_1178, 0, x_1170);
lean_ctor_set(x_1178, 1, x_1171);
lean_ctor_set(x_1178, 2, x_1172);
lean_ctor_set(x_1178, 3, x_1173);
lean_ctor_set_uint8(x_1178, sizeof(void*)*4, x_1175);
x_1179 = 0;
x_1180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1180, 0, x_1176);
lean_ctor_set(x_1180, 1, x_1168);
lean_ctor_set(x_1180, 2, x_1169);
lean_ctor_set(x_1180, 3, x_1178);
lean_ctor_set_uint8(x_1180, sizeof(void*)*4, x_1179);
return x_1180;
}
}
else
{
uint8_t x_1181; 
lean_dec(x_973);
x_1181 = !lean_is_exclusive(x_1132);
if (x_1181 == 0)
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
x_1182 = lean_ctor_get(x_1132, 3);
lean_dec(x_1182);
x_1183 = lean_ctor_get(x_1132, 2);
lean_dec(x_1183);
x_1184 = lean_ctor_get(x_1132, 1);
lean_dec(x_1184);
x_1185 = lean_ctor_get(x_1132, 0);
lean_dec(x_1185);
x_1186 = 1;
lean_ctor_set(x_1132, 3, x_4);
lean_ctor_set(x_1132, 2, x_3);
lean_ctor_set(x_1132, 1, x_2);
lean_ctor_set(x_1132, 0, x_1);
lean_ctor_set_uint8(x_1132, sizeof(void*)*4, x_1186);
return x_1132;
}
else
{
uint8_t x_1187; lean_object* x_1188; 
lean_dec(x_1132);
x_1187 = 1;
x_1188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1188, 0, x_1);
lean_ctor_set(x_1188, 1, x_2);
lean_ctor_set(x_1188, 2, x_3);
lean_ctor_set(x_1188, 3, x_4);
lean_ctor_set_uint8(x_1188, sizeof(void*)*4, x_1187);
return x_1188;
}
}
}
}
}
}
else
{
uint8_t x_1189; 
x_1189 = 1;
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_3);
lean_ctor_set(x_241, 1, x_2);
lean_ctor_set(x_241, 0, x_1);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1189);
return x_241;
}
}
}
else
{
lean_dec(x_241);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1190; lean_object* x_1191; 
x_1190 = 1;
x_1191 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1191, 0, x_1);
lean_ctor_set(x_1191, 1, x_2);
lean_ctor_set(x_1191, 2, x_3);
lean_ctor_set(x_1191, 3, x_4);
lean_ctor_set_uint8(x_1191, sizeof(void*)*4, x_1190);
return x_1191;
}
else
{
uint8_t x_1192; 
x_1192 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1192 == 0)
{
lean_object* x_1193; 
x_1193 = lean_ctor_get(x_4, 0);
lean_inc(x_1193);
if (lean_obj_tag(x_1193) == 0)
{
lean_object* x_1194; 
x_1194 = lean_ctor_get(x_4, 3);
lean_inc(x_1194);
if (lean_obj_tag(x_1194) == 0)
{
uint8_t x_1195; lean_object* x_1196; 
x_1195 = 1;
x_1196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1196, 0, x_1);
lean_ctor_set(x_1196, 1, x_2);
lean_ctor_set(x_1196, 2, x_3);
lean_ctor_set(x_1196, 3, x_4);
lean_ctor_set_uint8(x_1196, sizeof(void*)*4, x_1195);
return x_1196;
}
else
{
uint8_t x_1197; 
x_1197 = lean_ctor_get_uint8(x_1194, sizeof(void*)*4);
if (x_1197 == 0)
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; uint8_t x_1206; lean_object* x_1207; lean_object* x_1208; uint8_t x_1209; lean_object* x_1210; 
x_1198 = lean_ctor_get(x_4, 1);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_4, 2);
lean_inc(x_1199);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1200 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1200 = lean_box(0);
}
x_1201 = lean_ctor_get(x_1194, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1194, 1);
lean_inc(x_1202);
x_1203 = lean_ctor_get(x_1194, 2);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1194, 3);
lean_inc(x_1204);
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 lean_ctor_release(x_1194, 1);
 lean_ctor_release(x_1194, 2);
 lean_ctor_release(x_1194, 3);
 x_1205 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1205 = lean_box(0);
}
x_1206 = 1;
if (lean_is_scalar(x_1205)) {
 x_1207 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1207 = x_1205;
}
lean_ctor_set(x_1207, 0, x_1);
lean_ctor_set(x_1207, 1, x_2);
lean_ctor_set(x_1207, 2, x_3);
lean_ctor_set(x_1207, 3, x_1193);
lean_ctor_set_uint8(x_1207, sizeof(void*)*4, x_1206);
if (lean_is_scalar(x_1200)) {
 x_1208 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1208 = x_1200;
}
lean_ctor_set(x_1208, 0, x_1201);
lean_ctor_set(x_1208, 1, x_1202);
lean_ctor_set(x_1208, 2, x_1203);
lean_ctor_set(x_1208, 3, x_1204);
lean_ctor_set_uint8(x_1208, sizeof(void*)*4, x_1206);
x_1209 = 0;
x_1210 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1210, 0, x_1207);
lean_ctor_set(x_1210, 1, x_1198);
lean_ctor_set(x_1210, 2, x_1199);
lean_ctor_set(x_1210, 3, x_1208);
lean_ctor_set_uint8(x_1210, sizeof(void*)*4, x_1209);
return x_1210;
}
else
{
lean_object* x_1211; uint8_t x_1212; lean_object* x_1213; 
if (lean_is_exclusive(x_1194)) {
 lean_ctor_release(x_1194, 0);
 lean_ctor_release(x_1194, 1);
 lean_ctor_release(x_1194, 2);
 lean_ctor_release(x_1194, 3);
 x_1211 = x_1194;
} else {
 lean_dec_ref(x_1194);
 x_1211 = lean_box(0);
}
x_1212 = 1;
if (lean_is_scalar(x_1211)) {
 x_1213 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1213 = x_1211;
}
lean_ctor_set(x_1213, 0, x_1);
lean_ctor_set(x_1213, 1, x_2);
lean_ctor_set(x_1213, 2, x_3);
lean_ctor_set(x_1213, 3, x_4);
lean_ctor_set_uint8(x_1213, sizeof(void*)*4, x_1212);
return x_1213;
}
}
}
else
{
uint8_t x_1214; 
x_1214 = lean_ctor_get_uint8(x_1193, sizeof(void*)*4);
if (x_1214 == 0)
{
lean_object* x_1215; 
x_1215 = lean_ctor_get(x_4, 3);
lean_inc(x_1215);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; uint8_t x_1224; lean_object* x_1225; lean_object* x_1226; uint8_t x_1227; lean_object* x_1228; 
x_1216 = lean_ctor_get(x_4, 1);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_4, 2);
lean_inc(x_1217);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1218 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1218 = lean_box(0);
}
x_1219 = lean_ctor_get(x_1193, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1193, 1);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1193, 2);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1193, 3);
lean_inc(x_1222);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 lean_ctor_release(x_1193, 2);
 lean_ctor_release(x_1193, 3);
 x_1223 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1223 = lean_box(0);
}
x_1224 = 1;
if (lean_is_scalar(x_1223)) {
 x_1225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1225 = x_1223;
}
lean_ctor_set(x_1225, 0, x_1);
lean_ctor_set(x_1225, 1, x_2);
lean_ctor_set(x_1225, 2, x_3);
lean_ctor_set(x_1225, 3, x_1219);
lean_ctor_set_uint8(x_1225, sizeof(void*)*4, x_1224);
if (lean_is_scalar(x_1218)) {
 x_1226 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1226 = x_1218;
}
lean_ctor_set(x_1226, 0, x_1222);
lean_ctor_set(x_1226, 1, x_1216);
lean_ctor_set(x_1226, 2, x_1217);
lean_ctor_set(x_1226, 3, x_1215);
lean_ctor_set_uint8(x_1226, sizeof(void*)*4, x_1224);
x_1227 = 0;
x_1228 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1228, 0, x_1225);
lean_ctor_set(x_1228, 1, x_1220);
lean_ctor_set(x_1228, 2, x_1221);
lean_ctor_set(x_1228, 3, x_1226);
lean_ctor_set_uint8(x_1228, sizeof(void*)*4, x_1227);
return x_1228;
}
else
{
uint8_t x_1229; 
x_1229 = lean_ctor_get_uint8(x_1215, sizeof(void*)*4);
if (x_1229 == 0)
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; uint8_t x_1244; lean_object* x_1245; lean_object* x_1246; uint8_t x_1247; lean_object* x_1248; 
x_1230 = lean_ctor_get(x_4, 1);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_4, 2);
lean_inc(x_1231);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1232 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1232 = lean_box(0);
}
x_1233 = lean_ctor_get(x_1193, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1193, 1);
lean_inc(x_1234);
x_1235 = lean_ctor_get(x_1193, 2);
lean_inc(x_1235);
x_1236 = lean_ctor_get(x_1193, 3);
lean_inc(x_1236);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 lean_ctor_release(x_1193, 2);
 lean_ctor_release(x_1193, 3);
 x_1237 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1237 = lean_box(0);
}
x_1238 = lean_ctor_get(x_1215, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1215, 1);
lean_inc(x_1239);
x_1240 = lean_ctor_get(x_1215, 2);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1215, 3);
lean_inc(x_1241);
if (lean_is_exclusive(x_1215)) {
 lean_ctor_release(x_1215, 0);
 lean_ctor_release(x_1215, 1);
 lean_ctor_release(x_1215, 2);
 lean_ctor_release(x_1215, 3);
 x_1242 = x_1215;
} else {
 lean_dec_ref(x_1215);
 x_1242 = lean_box(0);
}
if (lean_is_scalar(x_1242)) {
 x_1243 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1243 = x_1242;
}
lean_ctor_set(x_1243, 0, x_1233);
lean_ctor_set(x_1243, 1, x_1234);
lean_ctor_set(x_1243, 2, x_1235);
lean_ctor_set(x_1243, 3, x_1236);
lean_ctor_set_uint8(x_1243, sizeof(void*)*4, x_1229);
x_1244 = 1;
if (lean_is_scalar(x_1237)) {
 x_1245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1245 = x_1237;
}
lean_ctor_set(x_1245, 0, x_1);
lean_ctor_set(x_1245, 1, x_2);
lean_ctor_set(x_1245, 2, x_3);
lean_ctor_set(x_1245, 3, x_1243);
lean_ctor_set_uint8(x_1245, sizeof(void*)*4, x_1244);
if (lean_is_scalar(x_1232)) {
 x_1246 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1246 = x_1232;
}
lean_ctor_set(x_1246, 0, x_1238);
lean_ctor_set(x_1246, 1, x_1239);
lean_ctor_set(x_1246, 2, x_1240);
lean_ctor_set(x_1246, 3, x_1241);
lean_ctor_set_uint8(x_1246, sizeof(void*)*4, x_1244);
x_1247 = 0;
x_1248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1248, 0, x_1245);
lean_ctor_set(x_1248, 1, x_1230);
lean_ctor_set(x_1248, 2, x_1231);
lean_ctor_set(x_1248, 3, x_1246);
lean_ctor_set_uint8(x_1248, sizeof(void*)*4, x_1247);
return x_1248;
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; uint8_t x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; lean_object* x_1261; 
x_1249 = lean_ctor_get(x_4, 1);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_4, 2);
lean_inc(x_1250);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1251 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1251 = lean_box(0);
}
x_1252 = lean_ctor_get(x_1193, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1193, 1);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1193, 2);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1193, 3);
lean_inc(x_1255);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 lean_ctor_release(x_1193, 2);
 lean_ctor_release(x_1193, 3);
 x_1256 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1256 = lean_box(0);
}
x_1257 = 1;
if (lean_is_scalar(x_1256)) {
 x_1258 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1258 = x_1256;
}
lean_ctor_set(x_1258, 0, x_1);
lean_ctor_set(x_1258, 1, x_2);
lean_ctor_set(x_1258, 2, x_3);
lean_ctor_set(x_1258, 3, x_1252);
lean_ctor_set_uint8(x_1258, sizeof(void*)*4, x_1257);
if (lean_is_scalar(x_1251)) {
 x_1259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1259 = x_1251;
}
lean_ctor_set(x_1259, 0, x_1255);
lean_ctor_set(x_1259, 1, x_1249);
lean_ctor_set(x_1259, 2, x_1250);
lean_ctor_set(x_1259, 3, x_1215);
lean_ctor_set_uint8(x_1259, sizeof(void*)*4, x_1257);
x_1260 = 0;
x_1261 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1261, 0, x_1258);
lean_ctor_set(x_1261, 1, x_1253);
lean_ctor_set(x_1261, 2, x_1254);
lean_ctor_set(x_1261, 3, x_1259);
lean_ctor_set_uint8(x_1261, sizeof(void*)*4, x_1260);
return x_1261;
}
}
}
else
{
lean_object* x_1262; 
x_1262 = lean_ctor_get(x_4, 3);
lean_inc(x_1262);
if (lean_obj_tag(x_1262) == 0)
{
lean_object* x_1263; uint8_t x_1264; lean_object* x_1265; 
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 lean_ctor_release(x_1193, 2);
 lean_ctor_release(x_1193, 3);
 x_1263 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1263 = lean_box(0);
}
x_1264 = 1;
if (lean_is_scalar(x_1263)) {
 x_1265 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1265 = x_1263;
}
lean_ctor_set(x_1265, 0, x_1);
lean_ctor_set(x_1265, 1, x_2);
lean_ctor_set(x_1265, 2, x_3);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1264);
return x_1265;
}
else
{
uint8_t x_1266; 
x_1266 = lean_ctor_get_uint8(x_1262, sizeof(void*)*4);
if (x_1266 == 0)
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; uint8_t x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; uint8_t x_1279; lean_object* x_1280; 
x_1267 = lean_ctor_get(x_4, 1);
lean_inc(x_1267);
x_1268 = lean_ctor_get(x_4, 2);
lean_inc(x_1268);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1269 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1269 = lean_box(0);
}
x_1270 = lean_ctor_get(x_1262, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1262, 1);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1262, 2);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1262, 3);
lean_inc(x_1273);
if (lean_is_exclusive(x_1262)) {
 lean_ctor_release(x_1262, 0);
 lean_ctor_release(x_1262, 1);
 lean_ctor_release(x_1262, 2);
 lean_ctor_release(x_1262, 3);
 x_1274 = x_1262;
} else {
 lean_dec_ref(x_1262);
 x_1274 = lean_box(0);
}
x_1275 = 1;
lean_inc(x_1193);
if (lean_is_scalar(x_1274)) {
 x_1276 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1276 = x_1274;
}
lean_ctor_set(x_1276, 0, x_1);
lean_ctor_set(x_1276, 1, x_2);
lean_ctor_set(x_1276, 2, x_3);
lean_ctor_set(x_1276, 3, x_1193);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 lean_ctor_release(x_1193, 2);
 lean_ctor_release(x_1193, 3);
 x_1277 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1277 = lean_box(0);
}
lean_ctor_set_uint8(x_1276, sizeof(void*)*4, x_1275);
if (lean_is_scalar(x_1277)) {
 x_1278 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1278 = x_1277;
}
lean_ctor_set(x_1278, 0, x_1270);
lean_ctor_set(x_1278, 1, x_1271);
lean_ctor_set(x_1278, 2, x_1272);
lean_ctor_set(x_1278, 3, x_1273);
lean_ctor_set_uint8(x_1278, sizeof(void*)*4, x_1275);
x_1279 = 0;
if (lean_is_scalar(x_1269)) {
 x_1280 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1280 = x_1269;
}
lean_ctor_set(x_1280, 0, x_1276);
lean_ctor_set(x_1280, 1, x_1267);
lean_ctor_set(x_1280, 2, x_1268);
lean_ctor_set(x_1280, 3, x_1278);
lean_ctor_set_uint8(x_1280, sizeof(void*)*4, x_1279);
return x_1280;
}
else
{
lean_object* x_1281; uint8_t x_1282; lean_object* x_1283; 
lean_dec(x_1193);
if (lean_is_exclusive(x_1262)) {
 lean_ctor_release(x_1262, 0);
 lean_ctor_release(x_1262, 1);
 lean_ctor_release(x_1262, 2);
 lean_ctor_release(x_1262, 3);
 x_1281 = x_1262;
} else {
 lean_dec_ref(x_1262);
 x_1281 = lean_box(0);
}
x_1282 = 1;
if (lean_is_scalar(x_1281)) {
 x_1283 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1283 = x_1281;
}
lean_ctor_set(x_1283, 0, x_1);
lean_ctor_set(x_1283, 1, x_2);
lean_ctor_set(x_1283, 2, x_3);
lean_ctor_set(x_1283, 3, x_4);
lean_ctor_set_uint8(x_1283, sizeof(void*)*4, x_1282);
return x_1283;
}
}
}
}
}
else
{
uint8_t x_1284; lean_object* x_1285; 
x_1284 = 1;
x_1285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1285, 0, x_1);
lean_ctor_set(x_1285, 1, x_2);
lean_ctor_set(x_1285, 2, x_3);
lean_ctor_set(x_1285, 3, x_4);
lean_ctor_set_uint8(x_1285, sizeof(void*)*4, x_1284);
return x_1285;
}
}
}
}
else
{
uint8_t x_1286; 
x_1286 = lean_ctor_get_uint8(x_965, sizeof(void*)*4);
if (x_1286 == 0)
{
uint8_t x_1287; 
x_1287 = !lean_is_exclusive(x_1);
if (x_1287 == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; uint8_t x_1292; 
x_1288 = lean_ctor_get(x_1, 1);
x_1289 = lean_ctor_get(x_1, 2);
x_1290 = lean_ctor_get(x_1, 3);
lean_dec(x_1290);
x_1291 = lean_ctor_get(x_1, 0);
lean_dec(x_1291);
x_1292 = !lean_is_exclusive(x_965);
if (x_1292 == 0)
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; uint8_t x_1297; uint8_t x_1298; 
x_1293 = lean_ctor_get(x_965, 0);
x_1294 = lean_ctor_get(x_965, 1);
x_1295 = lean_ctor_get(x_965, 2);
x_1296 = lean_ctor_get(x_965, 3);
x_1297 = 1;
lean_inc(x_241);
lean_ctor_set(x_965, 3, x_1293);
lean_ctor_set(x_965, 2, x_1289);
lean_ctor_set(x_965, 1, x_1288);
lean_ctor_set(x_965, 0, x_241);
x_1298 = !lean_is_exclusive(x_241);
if (x_1298 == 0)
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; uint8_t x_1303; 
x_1299 = lean_ctor_get(x_241, 3);
lean_dec(x_1299);
x_1300 = lean_ctor_get(x_241, 2);
lean_dec(x_1300);
x_1301 = lean_ctor_get(x_241, 1);
lean_dec(x_1301);
x_1302 = lean_ctor_get(x_241, 0);
lean_dec(x_1302);
lean_ctor_set_uint8(x_965, sizeof(void*)*4, x_1297);
lean_ctor_set(x_241, 3, x_4);
lean_ctor_set(x_241, 2, x_3);
lean_ctor_set(x_241, 1, x_2);
lean_ctor_set(x_241, 0, x_1296);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1297);
x_1303 = 0;
lean_ctor_set(x_1, 3, x_241);
lean_ctor_set(x_1, 2, x_1295);
lean_ctor_set(x_1, 1, x_1294);
lean_ctor_set(x_1, 0, x_965);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1303);
return x_1;
}
else
{
lean_object* x_1304; uint8_t x_1305; 
lean_dec(x_241);
lean_ctor_set_uint8(x_965, sizeof(void*)*4, x_1297);
x_1304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1304, 0, x_1296);
lean_ctor_set(x_1304, 1, x_2);
lean_ctor_set(x_1304, 2, x_3);
lean_ctor_set(x_1304, 3, x_4);
lean_ctor_set_uint8(x_1304, sizeof(void*)*4, x_1297);
x_1305 = 0;
lean_ctor_set(x_1, 3, x_1304);
lean_ctor_set(x_1, 2, x_1295);
lean_ctor_set(x_1, 1, x_1294);
lean_ctor_set(x_1, 0, x_965);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1305);
return x_1;
}
}
else
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; uint8_t x_1314; 
x_1306 = lean_ctor_get(x_965, 0);
x_1307 = lean_ctor_get(x_965, 1);
x_1308 = lean_ctor_get(x_965, 2);
x_1309 = lean_ctor_get(x_965, 3);
lean_inc(x_1309);
lean_inc(x_1308);
lean_inc(x_1307);
lean_inc(x_1306);
lean_dec(x_965);
x_1310 = 1;
lean_inc(x_241);
x_1311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1311, 0, x_241);
lean_ctor_set(x_1311, 1, x_1288);
lean_ctor_set(x_1311, 2, x_1289);
lean_ctor_set(x_1311, 3, x_1306);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_1312 = x_241;
} else {
 lean_dec_ref(x_241);
 x_1312 = lean_box(0);
}
lean_ctor_set_uint8(x_1311, sizeof(void*)*4, x_1310);
if (lean_is_scalar(x_1312)) {
 x_1313 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1313 = x_1312;
}
lean_ctor_set(x_1313, 0, x_1309);
lean_ctor_set(x_1313, 1, x_2);
lean_ctor_set(x_1313, 2, x_3);
lean_ctor_set(x_1313, 3, x_4);
lean_ctor_set_uint8(x_1313, sizeof(void*)*4, x_1310);
x_1314 = 0;
lean_ctor_set(x_1, 3, x_1313);
lean_ctor_set(x_1, 2, x_1308);
lean_ctor_set(x_1, 1, x_1307);
lean_ctor_set(x_1, 0, x_1311);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1314);
return x_1;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; uint8_t x_1326; lean_object* x_1327; 
x_1315 = lean_ctor_get(x_1, 1);
x_1316 = lean_ctor_get(x_1, 2);
lean_inc(x_1316);
lean_inc(x_1315);
lean_dec(x_1);
x_1317 = lean_ctor_get(x_965, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_965, 1);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_965, 2);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_965, 3);
lean_inc(x_1320);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 lean_ctor_release(x_965, 2);
 lean_ctor_release(x_965, 3);
 x_1321 = x_965;
} else {
 lean_dec_ref(x_965);
 x_1321 = lean_box(0);
}
x_1322 = 1;
lean_inc(x_241);
if (lean_is_scalar(x_1321)) {
 x_1323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1323 = x_1321;
}
lean_ctor_set(x_1323, 0, x_241);
lean_ctor_set(x_1323, 1, x_1315);
lean_ctor_set(x_1323, 2, x_1316);
lean_ctor_set(x_1323, 3, x_1317);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_1324 = x_241;
} else {
 lean_dec_ref(x_241);
 x_1324 = lean_box(0);
}
lean_ctor_set_uint8(x_1323, sizeof(void*)*4, x_1322);
if (lean_is_scalar(x_1324)) {
 x_1325 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1325 = x_1324;
}
lean_ctor_set(x_1325, 0, x_1320);
lean_ctor_set(x_1325, 1, x_2);
lean_ctor_set(x_1325, 2, x_3);
lean_ctor_set(x_1325, 3, x_4);
lean_ctor_set_uint8(x_1325, sizeof(void*)*4, x_1322);
x_1326 = 0;
x_1327 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1327, 0, x_1323);
lean_ctor_set(x_1327, 1, x_1318);
lean_ctor_set(x_1327, 2, x_1319);
lean_ctor_set(x_1327, 3, x_1325);
lean_ctor_set_uint8(x_1327, sizeof(void*)*4, x_1326);
return x_1327;
}
}
else
{
uint8_t x_1328; 
x_1328 = !lean_is_exclusive(x_1);
if (x_1328 == 0)
{
lean_object* x_1329; lean_object* x_1330; uint8_t x_1331; 
x_1329 = lean_ctor_get(x_1, 3);
lean_dec(x_1329);
x_1330 = lean_ctor_get(x_1, 0);
lean_dec(x_1330);
x_1331 = !lean_is_exclusive(x_241);
if (x_1331 == 0)
{
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_1286);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1332; lean_object* x_1333; 
x_1332 = 1;
x_1333 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1333, 0, x_1);
lean_ctor_set(x_1333, 1, x_2);
lean_ctor_set(x_1333, 2, x_3);
lean_ctor_set(x_1333, 3, x_4);
lean_ctor_set_uint8(x_1333, sizeof(void*)*4, x_1332);
return x_1333;
}
else
{
uint8_t x_1334; 
x_1334 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1334 == 0)
{
lean_object* x_1335; 
x_1335 = lean_ctor_get(x_4, 0);
lean_inc(x_1335);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; 
x_1336 = lean_ctor_get(x_4, 3);
lean_inc(x_1336);
if (lean_obj_tag(x_1336) == 0)
{
uint8_t x_1337; lean_object* x_1338; 
x_1337 = 1;
x_1338 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1338, 0, x_1);
lean_ctor_set(x_1338, 1, x_2);
lean_ctor_set(x_1338, 2, x_3);
lean_ctor_set(x_1338, 3, x_4);
lean_ctor_set_uint8(x_1338, sizeof(void*)*4, x_1337);
return x_1338;
}
else
{
uint8_t x_1339; 
x_1339 = lean_ctor_get_uint8(x_1336, sizeof(void*)*4);
if (x_1339 == 0)
{
uint8_t x_1340; 
x_1340 = !lean_is_exclusive(x_4);
if (x_1340 == 0)
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; uint8_t x_1345; 
x_1341 = lean_ctor_get(x_4, 1);
x_1342 = lean_ctor_get(x_4, 2);
x_1343 = lean_ctor_get(x_4, 3);
lean_dec(x_1343);
x_1344 = lean_ctor_get(x_4, 0);
lean_dec(x_1344);
x_1345 = !lean_is_exclusive(x_1336);
if (x_1345 == 0)
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; uint8_t x_1350; uint8_t x_1351; lean_object* x_1352; 
x_1346 = lean_ctor_get(x_1336, 0);
x_1347 = lean_ctor_get(x_1336, 1);
x_1348 = lean_ctor_get(x_1336, 2);
x_1349 = lean_ctor_get(x_1336, 3);
x_1350 = 1;
lean_ctor_set(x_1336, 3, x_1335);
lean_ctor_set(x_1336, 2, x_3);
lean_ctor_set(x_1336, 1, x_2);
lean_ctor_set(x_1336, 0, x_1);
lean_ctor_set_uint8(x_1336, sizeof(void*)*4, x_1350);
lean_ctor_set(x_4, 3, x_1349);
lean_ctor_set(x_4, 2, x_1348);
lean_ctor_set(x_4, 1, x_1347);
lean_ctor_set(x_4, 0, x_1346);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1350);
x_1351 = 0;
x_1352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1352, 0, x_1336);
lean_ctor_set(x_1352, 1, x_1341);
lean_ctor_set(x_1352, 2, x_1342);
lean_ctor_set(x_1352, 3, x_4);
lean_ctor_set_uint8(x_1352, sizeof(void*)*4, x_1351);
return x_1352;
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; uint8_t x_1357; lean_object* x_1358; uint8_t x_1359; lean_object* x_1360; 
x_1353 = lean_ctor_get(x_1336, 0);
x_1354 = lean_ctor_get(x_1336, 1);
x_1355 = lean_ctor_get(x_1336, 2);
x_1356 = lean_ctor_get(x_1336, 3);
lean_inc(x_1356);
lean_inc(x_1355);
lean_inc(x_1354);
lean_inc(x_1353);
lean_dec(x_1336);
x_1357 = 1;
x_1358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1358, 0, x_1);
lean_ctor_set(x_1358, 1, x_2);
lean_ctor_set(x_1358, 2, x_3);
lean_ctor_set(x_1358, 3, x_1335);
lean_ctor_set_uint8(x_1358, sizeof(void*)*4, x_1357);
lean_ctor_set(x_4, 3, x_1356);
lean_ctor_set(x_4, 2, x_1355);
lean_ctor_set(x_4, 1, x_1354);
lean_ctor_set(x_4, 0, x_1353);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1357);
x_1359 = 0;
x_1360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1360, 0, x_1358);
lean_ctor_set(x_1360, 1, x_1341);
lean_ctor_set(x_1360, 2, x_1342);
lean_ctor_set(x_1360, 3, x_4);
lean_ctor_set_uint8(x_1360, sizeof(void*)*4, x_1359);
return x_1360;
}
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; uint8_t x_1368; lean_object* x_1369; lean_object* x_1370; uint8_t x_1371; lean_object* x_1372; 
x_1361 = lean_ctor_get(x_4, 1);
x_1362 = lean_ctor_get(x_4, 2);
lean_inc(x_1362);
lean_inc(x_1361);
lean_dec(x_4);
x_1363 = lean_ctor_get(x_1336, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1336, 1);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1336, 2);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1336, 3);
lean_inc(x_1366);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 lean_ctor_release(x_1336, 2);
 lean_ctor_release(x_1336, 3);
 x_1367 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1367 = lean_box(0);
}
x_1368 = 1;
if (lean_is_scalar(x_1367)) {
 x_1369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1369 = x_1367;
}
lean_ctor_set(x_1369, 0, x_1);
lean_ctor_set(x_1369, 1, x_2);
lean_ctor_set(x_1369, 2, x_3);
lean_ctor_set(x_1369, 3, x_1335);
lean_ctor_set_uint8(x_1369, sizeof(void*)*4, x_1368);
x_1370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1370, 0, x_1363);
lean_ctor_set(x_1370, 1, x_1364);
lean_ctor_set(x_1370, 2, x_1365);
lean_ctor_set(x_1370, 3, x_1366);
lean_ctor_set_uint8(x_1370, sizeof(void*)*4, x_1368);
x_1371 = 0;
x_1372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1372, 0, x_1369);
lean_ctor_set(x_1372, 1, x_1361);
lean_ctor_set(x_1372, 2, x_1362);
lean_ctor_set(x_1372, 3, x_1370);
lean_ctor_set_uint8(x_1372, sizeof(void*)*4, x_1371);
return x_1372;
}
}
else
{
uint8_t x_1373; 
x_1373 = !lean_is_exclusive(x_1336);
if (x_1373 == 0)
{
lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; uint8_t x_1378; 
x_1374 = lean_ctor_get(x_1336, 3);
lean_dec(x_1374);
x_1375 = lean_ctor_get(x_1336, 2);
lean_dec(x_1375);
x_1376 = lean_ctor_get(x_1336, 1);
lean_dec(x_1376);
x_1377 = lean_ctor_get(x_1336, 0);
lean_dec(x_1377);
x_1378 = 1;
lean_ctor_set(x_1336, 3, x_4);
lean_ctor_set(x_1336, 2, x_3);
lean_ctor_set(x_1336, 1, x_2);
lean_ctor_set(x_1336, 0, x_1);
lean_ctor_set_uint8(x_1336, sizeof(void*)*4, x_1378);
return x_1336;
}
else
{
uint8_t x_1379; lean_object* x_1380; 
lean_dec(x_1336);
x_1379 = 1;
x_1380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1380, 0, x_1);
lean_ctor_set(x_1380, 1, x_2);
lean_ctor_set(x_1380, 2, x_3);
lean_ctor_set(x_1380, 3, x_4);
lean_ctor_set_uint8(x_1380, sizeof(void*)*4, x_1379);
return x_1380;
}
}
}
}
else
{
uint8_t x_1381; 
x_1381 = lean_ctor_get_uint8(x_1335, sizeof(void*)*4);
if (x_1381 == 0)
{
lean_object* x_1382; 
x_1382 = lean_ctor_get(x_4, 3);
lean_inc(x_1382);
if (lean_obj_tag(x_1382) == 0)
{
uint8_t x_1383; 
x_1383 = !lean_is_exclusive(x_4);
if (x_1383 == 0)
{
lean_object* x_1384; lean_object* x_1385; uint8_t x_1386; 
x_1384 = lean_ctor_get(x_4, 3);
lean_dec(x_1384);
x_1385 = lean_ctor_get(x_4, 0);
lean_dec(x_1385);
x_1386 = !lean_is_exclusive(x_1335);
if (x_1386 == 0)
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; uint8_t x_1391; uint8_t x_1392; lean_object* x_1393; 
x_1387 = lean_ctor_get(x_1335, 0);
x_1388 = lean_ctor_get(x_1335, 1);
x_1389 = lean_ctor_get(x_1335, 2);
x_1390 = lean_ctor_get(x_1335, 3);
x_1391 = 1;
lean_ctor_set(x_1335, 3, x_1387);
lean_ctor_set(x_1335, 2, x_3);
lean_ctor_set(x_1335, 1, x_2);
lean_ctor_set(x_1335, 0, x_1);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1391);
lean_ctor_set(x_4, 0, x_1390);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1391);
x_1392 = 0;
x_1393 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1393, 0, x_1335);
lean_ctor_set(x_1393, 1, x_1388);
lean_ctor_set(x_1393, 2, x_1389);
lean_ctor_set(x_1393, 3, x_4);
lean_ctor_set_uint8(x_1393, sizeof(void*)*4, x_1392);
return x_1393;
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; uint8_t x_1398; lean_object* x_1399; uint8_t x_1400; lean_object* x_1401; 
x_1394 = lean_ctor_get(x_1335, 0);
x_1395 = lean_ctor_get(x_1335, 1);
x_1396 = lean_ctor_get(x_1335, 2);
x_1397 = lean_ctor_get(x_1335, 3);
lean_inc(x_1397);
lean_inc(x_1396);
lean_inc(x_1395);
lean_inc(x_1394);
lean_dec(x_1335);
x_1398 = 1;
x_1399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1399, 0, x_1);
lean_ctor_set(x_1399, 1, x_2);
lean_ctor_set(x_1399, 2, x_3);
lean_ctor_set(x_1399, 3, x_1394);
lean_ctor_set_uint8(x_1399, sizeof(void*)*4, x_1398);
lean_ctor_set(x_4, 0, x_1397);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1398);
x_1400 = 0;
x_1401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1401, 0, x_1399);
lean_ctor_set(x_1401, 1, x_1395);
lean_ctor_set(x_1401, 2, x_1396);
lean_ctor_set(x_1401, 3, x_4);
lean_ctor_set_uint8(x_1401, sizeof(void*)*4, x_1400);
return x_1401;
}
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; uint8_t x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1412; lean_object* x_1413; 
x_1402 = lean_ctor_get(x_4, 1);
x_1403 = lean_ctor_get(x_4, 2);
lean_inc(x_1403);
lean_inc(x_1402);
lean_dec(x_4);
x_1404 = lean_ctor_get(x_1335, 0);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1335, 1);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1335, 2);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1335, 3);
lean_inc(x_1407);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 lean_ctor_release(x_1335, 2);
 lean_ctor_release(x_1335, 3);
 x_1408 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1408 = lean_box(0);
}
x_1409 = 1;
if (lean_is_scalar(x_1408)) {
 x_1410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1410 = x_1408;
}
lean_ctor_set(x_1410, 0, x_1);
lean_ctor_set(x_1410, 1, x_2);
lean_ctor_set(x_1410, 2, x_3);
lean_ctor_set(x_1410, 3, x_1404);
lean_ctor_set_uint8(x_1410, sizeof(void*)*4, x_1409);
x_1411 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1411, 0, x_1407);
lean_ctor_set(x_1411, 1, x_1402);
lean_ctor_set(x_1411, 2, x_1403);
lean_ctor_set(x_1411, 3, x_1382);
lean_ctor_set_uint8(x_1411, sizeof(void*)*4, x_1409);
x_1412 = 0;
x_1413 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1413, 0, x_1410);
lean_ctor_set(x_1413, 1, x_1405);
lean_ctor_set(x_1413, 2, x_1406);
lean_ctor_set(x_1413, 3, x_1411);
lean_ctor_set_uint8(x_1413, sizeof(void*)*4, x_1412);
return x_1413;
}
}
else
{
uint8_t x_1414; 
x_1414 = lean_ctor_get_uint8(x_1382, sizeof(void*)*4);
if (x_1414 == 0)
{
uint8_t x_1415; 
x_1415 = !lean_is_exclusive(x_4);
if (x_1415 == 0)
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; uint8_t x_1420; 
x_1416 = lean_ctor_get(x_4, 1);
x_1417 = lean_ctor_get(x_4, 2);
x_1418 = lean_ctor_get(x_4, 3);
lean_dec(x_1418);
x_1419 = lean_ctor_get(x_4, 0);
lean_dec(x_1419);
x_1420 = !lean_is_exclusive(x_1335);
if (x_1420 == 0)
{
uint8_t x_1421; 
x_1421 = !lean_is_exclusive(x_1382);
if (x_1421 == 0)
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; uint8_t x_1430; uint8_t x_1431; lean_object* x_1432; 
x_1422 = lean_ctor_get(x_1335, 0);
x_1423 = lean_ctor_get(x_1335, 1);
x_1424 = lean_ctor_get(x_1335, 2);
x_1425 = lean_ctor_get(x_1335, 3);
x_1426 = lean_ctor_get(x_1382, 0);
x_1427 = lean_ctor_get(x_1382, 1);
x_1428 = lean_ctor_get(x_1382, 2);
x_1429 = lean_ctor_get(x_1382, 3);
lean_ctor_set(x_1382, 3, x_1425);
lean_ctor_set(x_1382, 2, x_1424);
lean_ctor_set(x_1382, 1, x_1423);
lean_ctor_set(x_1382, 0, x_1422);
x_1430 = 1;
lean_ctor_set(x_1335, 3, x_1382);
lean_ctor_set(x_1335, 2, x_3);
lean_ctor_set(x_1335, 1, x_2);
lean_ctor_set(x_1335, 0, x_1);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1430);
lean_ctor_set(x_4, 3, x_1429);
lean_ctor_set(x_4, 2, x_1428);
lean_ctor_set(x_4, 1, x_1427);
lean_ctor_set(x_4, 0, x_1426);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1430);
x_1431 = 0;
x_1432 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1432, 0, x_1335);
lean_ctor_set(x_1432, 1, x_1416);
lean_ctor_set(x_1432, 2, x_1417);
lean_ctor_set(x_1432, 3, x_4);
lean_ctor_set_uint8(x_1432, sizeof(void*)*4, x_1431);
return x_1432;
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; uint8_t x_1442; uint8_t x_1443; lean_object* x_1444; 
x_1433 = lean_ctor_get(x_1335, 0);
x_1434 = lean_ctor_get(x_1335, 1);
x_1435 = lean_ctor_get(x_1335, 2);
x_1436 = lean_ctor_get(x_1335, 3);
x_1437 = lean_ctor_get(x_1382, 0);
x_1438 = lean_ctor_get(x_1382, 1);
x_1439 = lean_ctor_get(x_1382, 2);
x_1440 = lean_ctor_get(x_1382, 3);
lean_inc(x_1440);
lean_inc(x_1439);
lean_inc(x_1438);
lean_inc(x_1437);
lean_dec(x_1382);
x_1441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1441, 0, x_1433);
lean_ctor_set(x_1441, 1, x_1434);
lean_ctor_set(x_1441, 2, x_1435);
lean_ctor_set(x_1441, 3, x_1436);
lean_ctor_set_uint8(x_1441, sizeof(void*)*4, x_1414);
x_1442 = 1;
lean_ctor_set(x_1335, 3, x_1441);
lean_ctor_set(x_1335, 2, x_3);
lean_ctor_set(x_1335, 1, x_2);
lean_ctor_set(x_1335, 0, x_1);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1442);
lean_ctor_set(x_4, 3, x_1440);
lean_ctor_set(x_4, 2, x_1439);
lean_ctor_set(x_4, 1, x_1438);
lean_ctor_set(x_4, 0, x_1437);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1442);
x_1443 = 0;
x_1444 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1444, 0, x_1335);
lean_ctor_set(x_1444, 1, x_1416);
lean_ctor_set(x_1444, 2, x_1417);
lean_ctor_set(x_1444, 3, x_4);
lean_ctor_set_uint8(x_1444, sizeof(void*)*4, x_1443);
return x_1444;
}
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; uint8_t x_1455; lean_object* x_1456; uint8_t x_1457; lean_object* x_1458; 
x_1445 = lean_ctor_get(x_1335, 0);
x_1446 = lean_ctor_get(x_1335, 1);
x_1447 = lean_ctor_get(x_1335, 2);
x_1448 = lean_ctor_get(x_1335, 3);
lean_inc(x_1448);
lean_inc(x_1447);
lean_inc(x_1446);
lean_inc(x_1445);
lean_dec(x_1335);
x_1449 = lean_ctor_get(x_1382, 0);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1382, 1);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1382, 2);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1382, 3);
lean_inc(x_1452);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 lean_ctor_release(x_1382, 2);
 lean_ctor_release(x_1382, 3);
 x_1453 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1453 = lean_box(0);
}
if (lean_is_scalar(x_1453)) {
 x_1454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1454 = x_1453;
}
lean_ctor_set(x_1454, 0, x_1445);
lean_ctor_set(x_1454, 1, x_1446);
lean_ctor_set(x_1454, 2, x_1447);
lean_ctor_set(x_1454, 3, x_1448);
lean_ctor_set_uint8(x_1454, sizeof(void*)*4, x_1414);
x_1455 = 1;
x_1456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1456, 0, x_1);
lean_ctor_set(x_1456, 1, x_2);
lean_ctor_set(x_1456, 2, x_3);
lean_ctor_set(x_1456, 3, x_1454);
lean_ctor_set_uint8(x_1456, sizeof(void*)*4, x_1455);
lean_ctor_set(x_4, 3, x_1452);
lean_ctor_set(x_4, 2, x_1451);
lean_ctor_set(x_4, 1, x_1450);
lean_ctor_set(x_4, 0, x_1449);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1455);
x_1457 = 0;
x_1458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1458, 0, x_1456);
lean_ctor_set(x_1458, 1, x_1416);
lean_ctor_set(x_1458, 2, x_1417);
lean_ctor_set(x_1458, 3, x_4);
lean_ctor_set_uint8(x_1458, sizeof(void*)*4, x_1457);
return x_1458;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; uint8_t x_1472; lean_object* x_1473; lean_object* x_1474; uint8_t x_1475; lean_object* x_1476; 
x_1459 = lean_ctor_get(x_4, 1);
x_1460 = lean_ctor_get(x_4, 2);
lean_inc(x_1460);
lean_inc(x_1459);
lean_dec(x_4);
x_1461 = lean_ctor_get(x_1335, 0);
lean_inc(x_1461);
x_1462 = lean_ctor_get(x_1335, 1);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1335, 2);
lean_inc(x_1463);
x_1464 = lean_ctor_get(x_1335, 3);
lean_inc(x_1464);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 lean_ctor_release(x_1335, 2);
 lean_ctor_release(x_1335, 3);
 x_1465 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1465 = lean_box(0);
}
x_1466 = lean_ctor_get(x_1382, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1382, 1);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1382, 2);
lean_inc(x_1468);
x_1469 = lean_ctor_get(x_1382, 3);
lean_inc(x_1469);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 lean_ctor_release(x_1382, 2);
 lean_ctor_release(x_1382, 3);
 x_1470 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1470 = lean_box(0);
}
if (lean_is_scalar(x_1470)) {
 x_1471 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1471 = x_1470;
}
lean_ctor_set(x_1471, 0, x_1461);
lean_ctor_set(x_1471, 1, x_1462);
lean_ctor_set(x_1471, 2, x_1463);
lean_ctor_set(x_1471, 3, x_1464);
lean_ctor_set_uint8(x_1471, sizeof(void*)*4, x_1414);
x_1472 = 1;
if (lean_is_scalar(x_1465)) {
 x_1473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1473 = x_1465;
}
lean_ctor_set(x_1473, 0, x_1);
lean_ctor_set(x_1473, 1, x_2);
lean_ctor_set(x_1473, 2, x_3);
lean_ctor_set(x_1473, 3, x_1471);
lean_ctor_set_uint8(x_1473, sizeof(void*)*4, x_1472);
x_1474 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1474, 0, x_1466);
lean_ctor_set(x_1474, 1, x_1467);
lean_ctor_set(x_1474, 2, x_1468);
lean_ctor_set(x_1474, 3, x_1469);
lean_ctor_set_uint8(x_1474, sizeof(void*)*4, x_1472);
x_1475 = 0;
x_1476 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1476, 0, x_1473);
lean_ctor_set(x_1476, 1, x_1459);
lean_ctor_set(x_1476, 2, x_1460);
lean_ctor_set(x_1476, 3, x_1474);
lean_ctor_set_uint8(x_1476, sizeof(void*)*4, x_1475);
return x_1476;
}
}
else
{
uint8_t x_1477; 
x_1477 = !lean_is_exclusive(x_4);
if (x_1477 == 0)
{
lean_object* x_1478; lean_object* x_1479; uint8_t x_1480; 
x_1478 = lean_ctor_get(x_4, 3);
lean_dec(x_1478);
x_1479 = lean_ctor_get(x_4, 0);
lean_dec(x_1479);
x_1480 = !lean_is_exclusive(x_1335);
if (x_1480 == 0)
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; uint8_t x_1485; uint8_t x_1486; lean_object* x_1487; 
x_1481 = lean_ctor_get(x_1335, 0);
x_1482 = lean_ctor_get(x_1335, 1);
x_1483 = lean_ctor_get(x_1335, 2);
x_1484 = lean_ctor_get(x_1335, 3);
x_1485 = 1;
lean_ctor_set(x_1335, 3, x_1481);
lean_ctor_set(x_1335, 2, x_3);
lean_ctor_set(x_1335, 1, x_2);
lean_ctor_set(x_1335, 0, x_1);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1485);
lean_ctor_set(x_4, 0, x_1484);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1485);
x_1486 = 0;
x_1487 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1487, 0, x_1335);
lean_ctor_set(x_1487, 1, x_1482);
lean_ctor_set(x_1487, 2, x_1483);
lean_ctor_set(x_1487, 3, x_4);
lean_ctor_set_uint8(x_1487, sizeof(void*)*4, x_1486);
return x_1487;
}
else
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; uint8_t x_1492; lean_object* x_1493; uint8_t x_1494; lean_object* x_1495; 
x_1488 = lean_ctor_get(x_1335, 0);
x_1489 = lean_ctor_get(x_1335, 1);
x_1490 = lean_ctor_get(x_1335, 2);
x_1491 = lean_ctor_get(x_1335, 3);
lean_inc(x_1491);
lean_inc(x_1490);
lean_inc(x_1489);
lean_inc(x_1488);
lean_dec(x_1335);
x_1492 = 1;
x_1493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1493, 0, x_1);
lean_ctor_set(x_1493, 1, x_2);
lean_ctor_set(x_1493, 2, x_3);
lean_ctor_set(x_1493, 3, x_1488);
lean_ctor_set_uint8(x_1493, sizeof(void*)*4, x_1492);
lean_ctor_set(x_4, 0, x_1491);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1492);
x_1494 = 0;
x_1495 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1495, 0, x_1493);
lean_ctor_set(x_1495, 1, x_1489);
lean_ctor_set(x_1495, 2, x_1490);
lean_ctor_set(x_1495, 3, x_4);
lean_ctor_set_uint8(x_1495, sizeof(void*)*4, x_1494);
return x_1495;
}
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; uint8_t x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; lean_object* x_1507; 
x_1496 = lean_ctor_get(x_4, 1);
x_1497 = lean_ctor_get(x_4, 2);
lean_inc(x_1497);
lean_inc(x_1496);
lean_dec(x_4);
x_1498 = lean_ctor_get(x_1335, 0);
lean_inc(x_1498);
x_1499 = lean_ctor_get(x_1335, 1);
lean_inc(x_1499);
x_1500 = lean_ctor_get(x_1335, 2);
lean_inc(x_1500);
x_1501 = lean_ctor_get(x_1335, 3);
lean_inc(x_1501);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 lean_ctor_release(x_1335, 2);
 lean_ctor_release(x_1335, 3);
 x_1502 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1502 = lean_box(0);
}
x_1503 = 1;
if (lean_is_scalar(x_1502)) {
 x_1504 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1504 = x_1502;
}
lean_ctor_set(x_1504, 0, x_1);
lean_ctor_set(x_1504, 1, x_2);
lean_ctor_set(x_1504, 2, x_3);
lean_ctor_set(x_1504, 3, x_1498);
lean_ctor_set_uint8(x_1504, sizeof(void*)*4, x_1503);
x_1505 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1505, 0, x_1501);
lean_ctor_set(x_1505, 1, x_1496);
lean_ctor_set(x_1505, 2, x_1497);
lean_ctor_set(x_1505, 3, x_1382);
lean_ctor_set_uint8(x_1505, sizeof(void*)*4, x_1503);
x_1506 = 0;
x_1507 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1507, 0, x_1504);
lean_ctor_set(x_1507, 1, x_1499);
lean_ctor_set(x_1507, 2, x_1500);
lean_ctor_set(x_1507, 3, x_1505);
lean_ctor_set_uint8(x_1507, sizeof(void*)*4, x_1506);
return x_1507;
}
}
}
}
else
{
lean_object* x_1508; 
x_1508 = lean_ctor_get(x_4, 3);
lean_inc(x_1508);
if (lean_obj_tag(x_1508) == 0)
{
uint8_t x_1509; 
x_1509 = !lean_is_exclusive(x_1335);
if (x_1509 == 0)
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; uint8_t x_1514; 
x_1510 = lean_ctor_get(x_1335, 3);
lean_dec(x_1510);
x_1511 = lean_ctor_get(x_1335, 2);
lean_dec(x_1511);
x_1512 = lean_ctor_get(x_1335, 1);
lean_dec(x_1512);
x_1513 = lean_ctor_get(x_1335, 0);
lean_dec(x_1513);
x_1514 = 1;
lean_ctor_set(x_1335, 3, x_4);
lean_ctor_set(x_1335, 2, x_3);
lean_ctor_set(x_1335, 1, x_2);
lean_ctor_set(x_1335, 0, x_1);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1514);
return x_1335;
}
else
{
uint8_t x_1515; lean_object* x_1516; 
lean_dec(x_1335);
x_1515 = 1;
x_1516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1516, 0, x_1);
lean_ctor_set(x_1516, 1, x_2);
lean_ctor_set(x_1516, 2, x_3);
lean_ctor_set(x_1516, 3, x_4);
lean_ctor_set_uint8(x_1516, sizeof(void*)*4, x_1515);
return x_1516;
}
}
else
{
uint8_t x_1517; 
x_1517 = lean_ctor_get_uint8(x_1508, sizeof(void*)*4);
if (x_1517 == 0)
{
uint8_t x_1518; 
x_1518 = !lean_is_exclusive(x_4);
if (x_1518 == 0)
{
lean_object* x_1519; lean_object* x_1520; uint8_t x_1521; 
x_1519 = lean_ctor_get(x_4, 3);
lean_dec(x_1519);
x_1520 = lean_ctor_get(x_4, 0);
lean_dec(x_1520);
x_1521 = !lean_is_exclusive(x_1508);
if (x_1521 == 0)
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; uint8_t x_1526; uint8_t x_1527; 
x_1522 = lean_ctor_get(x_1508, 0);
x_1523 = lean_ctor_get(x_1508, 1);
x_1524 = lean_ctor_get(x_1508, 2);
x_1525 = lean_ctor_get(x_1508, 3);
x_1526 = 1;
lean_inc(x_1335);
lean_ctor_set(x_1508, 3, x_1335);
lean_ctor_set(x_1508, 2, x_3);
lean_ctor_set(x_1508, 1, x_2);
lean_ctor_set(x_1508, 0, x_1);
x_1527 = !lean_is_exclusive(x_1335);
if (x_1527 == 0)
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; uint8_t x_1532; 
x_1528 = lean_ctor_get(x_1335, 3);
lean_dec(x_1528);
x_1529 = lean_ctor_get(x_1335, 2);
lean_dec(x_1529);
x_1530 = lean_ctor_get(x_1335, 1);
lean_dec(x_1530);
x_1531 = lean_ctor_get(x_1335, 0);
lean_dec(x_1531);
lean_ctor_set_uint8(x_1508, sizeof(void*)*4, x_1526);
lean_ctor_set(x_1335, 3, x_1525);
lean_ctor_set(x_1335, 2, x_1524);
lean_ctor_set(x_1335, 1, x_1523);
lean_ctor_set(x_1335, 0, x_1522);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1526);
x_1532 = 0;
lean_ctor_set(x_4, 3, x_1335);
lean_ctor_set(x_4, 0, x_1508);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1532);
return x_4;
}
else
{
lean_object* x_1533; uint8_t x_1534; 
lean_dec(x_1335);
lean_ctor_set_uint8(x_1508, sizeof(void*)*4, x_1526);
x_1533 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1533, 0, x_1522);
lean_ctor_set(x_1533, 1, x_1523);
lean_ctor_set(x_1533, 2, x_1524);
lean_ctor_set(x_1533, 3, x_1525);
lean_ctor_set_uint8(x_1533, sizeof(void*)*4, x_1526);
x_1534 = 0;
lean_ctor_set(x_4, 3, x_1533);
lean_ctor_set(x_4, 0, x_1508);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1534);
return x_4;
}
}
else
{
lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; uint8_t x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; uint8_t x_1543; 
x_1535 = lean_ctor_get(x_1508, 0);
x_1536 = lean_ctor_get(x_1508, 1);
x_1537 = lean_ctor_get(x_1508, 2);
x_1538 = lean_ctor_get(x_1508, 3);
lean_inc(x_1538);
lean_inc(x_1537);
lean_inc(x_1536);
lean_inc(x_1535);
lean_dec(x_1508);
x_1539 = 1;
lean_inc(x_1335);
x_1540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1540, 0, x_1);
lean_ctor_set(x_1540, 1, x_2);
lean_ctor_set(x_1540, 2, x_3);
lean_ctor_set(x_1540, 3, x_1335);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 lean_ctor_release(x_1335, 2);
 lean_ctor_release(x_1335, 3);
 x_1541 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1541 = lean_box(0);
}
lean_ctor_set_uint8(x_1540, sizeof(void*)*4, x_1539);
if (lean_is_scalar(x_1541)) {
 x_1542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1542 = x_1541;
}
lean_ctor_set(x_1542, 0, x_1535);
lean_ctor_set(x_1542, 1, x_1536);
lean_ctor_set(x_1542, 2, x_1537);
lean_ctor_set(x_1542, 3, x_1538);
lean_ctor_set_uint8(x_1542, sizeof(void*)*4, x_1539);
x_1543 = 0;
lean_ctor_set(x_4, 3, x_1542);
lean_ctor_set(x_4, 0, x_1540);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1543);
return x_4;
}
}
else
{
lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; uint8_t x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; uint8_t x_1555; lean_object* x_1556; 
x_1544 = lean_ctor_get(x_4, 1);
x_1545 = lean_ctor_get(x_4, 2);
lean_inc(x_1545);
lean_inc(x_1544);
lean_dec(x_4);
x_1546 = lean_ctor_get(x_1508, 0);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1508, 1);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1508, 2);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1508, 3);
lean_inc(x_1549);
if (lean_is_exclusive(x_1508)) {
 lean_ctor_release(x_1508, 0);
 lean_ctor_release(x_1508, 1);
 lean_ctor_release(x_1508, 2);
 lean_ctor_release(x_1508, 3);
 x_1550 = x_1508;
} else {
 lean_dec_ref(x_1508);
 x_1550 = lean_box(0);
}
x_1551 = 1;
lean_inc(x_1335);
if (lean_is_scalar(x_1550)) {
 x_1552 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1552 = x_1550;
}
lean_ctor_set(x_1552, 0, x_1);
lean_ctor_set(x_1552, 1, x_2);
lean_ctor_set(x_1552, 2, x_3);
lean_ctor_set(x_1552, 3, x_1335);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 lean_ctor_release(x_1335, 2);
 lean_ctor_release(x_1335, 3);
 x_1553 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1553 = lean_box(0);
}
lean_ctor_set_uint8(x_1552, sizeof(void*)*4, x_1551);
if (lean_is_scalar(x_1553)) {
 x_1554 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1554 = x_1553;
}
lean_ctor_set(x_1554, 0, x_1546);
lean_ctor_set(x_1554, 1, x_1547);
lean_ctor_set(x_1554, 2, x_1548);
lean_ctor_set(x_1554, 3, x_1549);
lean_ctor_set_uint8(x_1554, sizeof(void*)*4, x_1551);
x_1555 = 0;
x_1556 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1556, 0, x_1552);
lean_ctor_set(x_1556, 1, x_1544);
lean_ctor_set(x_1556, 2, x_1545);
lean_ctor_set(x_1556, 3, x_1554);
lean_ctor_set_uint8(x_1556, sizeof(void*)*4, x_1555);
return x_1556;
}
}
else
{
uint8_t x_1557; 
lean_dec(x_1335);
x_1557 = !lean_is_exclusive(x_1508);
if (x_1557 == 0)
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; uint8_t x_1562; 
x_1558 = lean_ctor_get(x_1508, 3);
lean_dec(x_1558);
x_1559 = lean_ctor_get(x_1508, 2);
lean_dec(x_1559);
x_1560 = lean_ctor_get(x_1508, 1);
lean_dec(x_1560);
x_1561 = lean_ctor_get(x_1508, 0);
lean_dec(x_1561);
x_1562 = 1;
lean_ctor_set(x_1508, 3, x_4);
lean_ctor_set(x_1508, 2, x_3);
lean_ctor_set(x_1508, 1, x_2);
lean_ctor_set(x_1508, 0, x_1);
lean_ctor_set_uint8(x_1508, sizeof(void*)*4, x_1562);
return x_1508;
}
else
{
uint8_t x_1563; lean_object* x_1564; 
lean_dec(x_1508);
x_1563 = 1;
x_1564 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1564, 0, x_1);
lean_ctor_set(x_1564, 1, x_2);
lean_ctor_set(x_1564, 2, x_3);
lean_ctor_set(x_1564, 3, x_4);
lean_ctor_set_uint8(x_1564, sizeof(void*)*4, x_1563);
return x_1564;
}
}
}
}
}
}
else
{
uint8_t x_1565; lean_object* x_1566; 
x_1565 = 1;
x_1566 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1566, 0, x_1);
lean_ctor_set(x_1566, 1, x_2);
lean_ctor_set(x_1566, 2, x_3);
lean_ctor_set(x_1566, 3, x_4);
lean_ctor_set_uint8(x_1566, sizeof(void*)*4, x_1565);
return x_1566;
}
}
}
else
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; 
x_1567 = lean_ctor_get(x_241, 0);
x_1568 = lean_ctor_get(x_241, 1);
x_1569 = lean_ctor_get(x_241, 2);
x_1570 = lean_ctor_get(x_241, 3);
lean_inc(x_1570);
lean_inc(x_1569);
lean_inc(x_1568);
lean_inc(x_1567);
lean_dec(x_241);
x_1571 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1571, 0, x_1567);
lean_ctor_set(x_1571, 1, x_1568);
lean_ctor_set(x_1571, 2, x_1569);
lean_ctor_set(x_1571, 3, x_1570);
lean_ctor_set_uint8(x_1571, sizeof(void*)*4, x_1286);
lean_ctor_set(x_1, 0, x_1571);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1572; lean_object* x_1573; 
x_1572 = 1;
x_1573 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1573, 0, x_1);
lean_ctor_set(x_1573, 1, x_2);
lean_ctor_set(x_1573, 2, x_3);
lean_ctor_set(x_1573, 3, x_4);
lean_ctor_set_uint8(x_1573, sizeof(void*)*4, x_1572);
return x_1573;
}
else
{
uint8_t x_1574; 
x_1574 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1574 == 0)
{
lean_object* x_1575; 
x_1575 = lean_ctor_get(x_4, 0);
lean_inc(x_1575);
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1576; 
x_1576 = lean_ctor_get(x_4, 3);
lean_inc(x_1576);
if (lean_obj_tag(x_1576) == 0)
{
uint8_t x_1577; lean_object* x_1578; 
x_1577 = 1;
x_1578 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1578, 0, x_1);
lean_ctor_set(x_1578, 1, x_2);
lean_ctor_set(x_1578, 2, x_3);
lean_ctor_set(x_1578, 3, x_4);
lean_ctor_set_uint8(x_1578, sizeof(void*)*4, x_1577);
return x_1578;
}
else
{
uint8_t x_1579; 
x_1579 = lean_ctor_get_uint8(x_1576, sizeof(void*)*4);
if (x_1579 == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; uint8_t x_1588; lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; lean_object* x_1592; 
x_1580 = lean_ctor_get(x_4, 1);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_4, 2);
lean_inc(x_1581);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1582 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1582 = lean_box(0);
}
x_1583 = lean_ctor_get(x_1576, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1576, 1);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1576, 2);
lean_inc(x_1585);
x_1586 = lean_ctor_get(x_1576, 3);
lean_inc(x_1586);
if (lean_is_exclusive(x_1576)) {
 lean_ctor_release(x_1576, 0);
 lean_ctor_release(x_1576, 1);
 lean_ctor_release(x_1576, 2);
 lean_ctor_release(x_1576, 3);
 x_1587 = x_1576;
} else {
 lean_dec_ref(x_1576);
 x_1587 = lean_box(0);
}
x_1588 = 1;
if (lean_is_scalar(x_1587)) {
 x_1589 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1589 = x_1587;
}
lean_ctor_set(x_1589, 0, x_1);
lean_ctor_set(x_1589, 1, x_2);
lean_ctor_set(x_1589, 2, x_3);
lean_ctor_set(x_1589, 3, x_1575);
lean_ctor_set_uint8(x_1589, sizeof(void*)*4, x_1588);
if (lean_is_scalar(x_1582)) {
 x_1590 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1590 = x_1582;
}
lean_ctor_set(x_1590, 0, x_1583);
lean_ctor_set(x_1590, 1, x_1584);
lean_ctor_set(x_1590, 2, x_1585);
lean_ctor_set(x_1590, 3, x_1586);
lean_ctor_set_uint8(x_1590, sizeof(void*)*4, x_1588);
x_1591 = 0;
x_1592 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1592, 0, x_1589);
lean_ctor_set(x_1592, 1, x_1580);
lean_ctor_set(x_1592, 2, x_1581);
lean_ctor_set(x_1592, 3, x_1590);
lean_ctor_set_uint8(x_1592, sizeof(void*)*4, x_1591);
return x_1592;
}
else
{
lean_object* x_1593; uint8_t x_1594; lean_object* x_1595; 
if (lean_is_exclusive(x_1576)) {
 lean_ctor_release(x_1576, 0);
 lean_ctor_release(x_1576, 1);
 lean_ctor_release(x_1576, 2);
 lean_ctor_release(x_1576, 3);
 x_1593 = x_1576;
} else {
 lean_dec_ref(x_1576);
 x_1593 = lean_box(0);
}
x_1594 = 1;
if (lean_is_scalar(x_1593)) {
 x_1595 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1595 = x_1593;
}
lean_ctor_set(x_1595, 0, x_1);
lean_ctor_set(x_1595, 1, x_2);
lean_ctor_set(x_1595, 2, x_3);
lean_ctor_set(x_1595, 3, x_4);
lean_ctor_set_uint8(x_1595, sizeof(void*)*4, x_1594);
return x_1595;
}
}
}
else
{
uint8_t x_1596; 
x_1596 = lean_ctor_get_uint8(x_1575, sizeof(void*)*4);
if (x_1596 == 0)
{
lean_object* x_1597; 
x_1597 = lean_ctor_get(x_4, 3);
lean_inc(x_1597);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; uint8_t x_1606; lean_object* x_1607; lean_object* x_1608; uint8_t x_1609; lean_object* x_1610; 
x_1598 = lean_ctor_get(x_4, 1);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_4, 2);
lean_inc(x_1599);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1600 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1600 = lean_box(0);
}
x_1601 = lean_ctor_get(x_1575, 0);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1575, 1);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1575, 2);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1575, 3);
lean_inc(x_1604);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 lean_ctor_release(x_1575, 2);
 lean_ctor_release(x_1575, 3);
 x_1605 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1605 = lean_box(0);
}
x_1606 = 1;
if (lean_is_scalar(x_1605)) {
 x_1607 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1607 = x_1605;
}
lean_ctor_set(x_1607, 0, x_1);
lean_ctor_set(x_1607, 1, x_2);
lean_ctor_set(x_1607, 2, x_3);
lean_ctor_set(x_1607, 3, x_1601);
lean_ctor_set_uint8(x_1607, sizeof(void*)*4, x_1606);
if (lean_is_scalar(x_1600)) {
 x_1608 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1608 = x_1600;
}
lean_ctor_set(x_1608, 0, x_1604);
lean_ctor_set(x_1608, 1, x_1598);
lean_ctor_set(x_1608, 2, x_1599);
lean_ctor_set(x_1608, 3, x_1597);
lean_ctor_set_uint8(x_1608, sizeof(void*)*4, x_1606);
x_1609 = 0;
x_1610 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1610, 0, x_1607);
lean_ctor_set(x_1610, 1, x_1602);
lean_ctor_set(x_1610, 2, x_1603);
lean_ctor_set(x_1610, 3, x_1608);
lean_ctor_set_uint8(x_1610, sizeof(void*)*4, x_1609);
return x_1610;
}
else
{
uint8_t x_1611; 
x_1611 = lean_ctor_get_uint8(x_1597, sizeof(void*)*4);
if (x_1611 == 0)
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; uint8_t x_1626; lean_object* x_1627; lean_object* x_1628; uint8_t x_1629; lean_object* x_1630; 
x_1612 = lean_ctor_get(x_4, 1);
lean_inc(x_1612);
x_1613 = lean_ctor_get(x_4, 2);
lean_inc(x_1613);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1614 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1614 = lean_box(0);
}
x_1615 = lean_ctor_get(x_1575, 0);
lean_inc(x_1615);
x_1616 = lean_ctor_get(x_1575, 1);
lean_inc(x_1616);
x_1617 = lean_ctor_get(x_1575, 2);
lean_inc(x_1617);
x_1618 = lean_ctor_get(x_1575, 3);
lean_inc(x_1618);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 lean_ctor_release(x_1575, 2);
 lean_ctor_release(x_1575, 3);
 x_1619 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1619 = lean_box(0);
}
x_1620 = lean_ctor_get(x_1597, 0);
lean_inc(x_1620);
x_1621 = lean_ctor_get(x_1597, 1);
lean_inc(x_1621);
x_1622 = lean_ctor_get(x_1597, 2);
lean_inc(x_1622);
x_1623 = lean_ctor_get(x_1597, 3);
lean_inc(x_1623);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 lean_ctor_release(x_1597, 2);
 lean_ctor_release(x_1597, 3);
 x_1624 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1624 = lean_box(0);
}
if (lean_is_scalar(x_1624)) {
 x_1625 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1625 = x_1624;
}
lean_ctor_set(x_1625, 0, x_1615);
lean_ctor_set(x_1625, 1, x_1616);
lean_ctor_set(x_1625, 2, x_1617);
lean_ctor_set(x_1625, 3, x_1618);
lean_ctor_set_uint8(x_1625, sizeof(void*)*4, x_1611);
x_1626 = 1;
if (lean_is_scalar(x_1619)) {
 x_1627 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1627 = x_1619;
}
lean_ctor_set(x_1627, 0, x_1);
lean_ctor_set(x_1627, 1, x_2);
lean_ctor_set(x_1627, 2, x_3);
lean_ctor_set(x_1627, 3, x_1625);
lean_ctor_set_uint8(x_1627, sizeof(void*)*4, x_1626);
if (lean_is_scalar(x_1614)) {
 x_1628 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1628 = x_1614;
}
lean_ctor_set(x_1628, 0, x_1620);
lean_ctor_set(x_1628, 1, x_1621);
lean_ctor_set(x_1628, 2, x_1622);
lean_ctor_set(x_1628, 3, x_1623);
lean_ctor_set_uint8(x_1628, sizeof(void*)*4, x_1626);
x_1629 = 0;
x_1630 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1630, 0, x_1627);
lean_ctor_set(x_1630, 1, x_1612);
lean_ctor_set(x_1630, 2, x_1613);
lean_ctor_set(x_1630, 3, x_1628);
lean_ctor_set_uint8(x_1630, sizeof(void*)*4, x_1629);
return x_1630;
}
else
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; uint8_t x_1639; lean_object* x_1640; lean_object* x_1641; uint8_t x_1642; lean_object* x_1643; 
x_1631 = lean_ctor_get(x_4, 1);
lean_inc(x_1631);
x_1632 = lean_ctor_get(x_4, 2);
lean_inc(x_1632);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1633 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1633 = lean_box(0);
}
x_1634 = lean_ctor_get(x_1575, 0);
lean_inc(x_1634);
x_1635 = lean_ctor_get(x_1575, 1);
lean_inc(x_1635);
x_1636 = lean_ctor_get(x_1575, 2);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1575, 3);
lean_inc(x_1637);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 lean_ctor_release(x_1575, 2);
 lean_ctor_release(x_1575, 3);
 x_1638 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1638 = lean_box(0);
}
x_1639 = 1;
if (lean_is_scalar(x_1638)) {
 x_1640 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1640 = x_1638;
}
lean_ctor_set(x_1640, 0, x_1);
lean_ctor_set(x_1640, 1, x_2);
lean_ctor_set(x_1640, 2, x_3);
lean_ctor_set(x_1640, 3, x_1634);
lean_ctor_set_uint8(x_1640, sizeof(void*)*4, x_1639);
if (lean_is_scalar(x_1633)) {
 x_1641 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1641 = x_1633;
}
lean_ctor_set(x_1641, 0, x_1637);
lean_ctor_set(x_1641, 1, x_1631);
lean_ctor_set(x_1641, 2, x_1632);
lean_ctor_set(x_1641, 3, x_1597);
lean_ctor_set_uint8(x_1641, sizeof(void*)*4, x_1639);
x_1642 = 0;
x_1643 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1643, 0, x_1640);
lean_ctor_set(x_1643, 1, x_1635);
lean_ctor_set(x_1643, 2, x_1636);
lean_ctor_set(x_1643, 3, x_1641);
lean_ctor_set_uint8(x_1643, sizeof(void*)*4, x_1642);
return x_1643;
}
}
}
else
{
lean_object* x_1644; 
x_1644 = lean_ctor_get(x_4, 3);
lean_inc(x_1644);
if (lean_obj_tag(x_1644) == 0)
{
lean_object* x_1645; uint8_t x_1646; lean_object* x_1647; 
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 lean_ctor_release(x_1575, 2);
 lean_ctor_release(x_1575, 3);
 x_1645 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1645 = lean_box(0);
}
x_1646 = 1;
if (lean_is_scalar(x_1645)) {
 x_1647 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1647 = x_1645;
}
lean_ctor_set(x_1647, 0, x_1);
lean_ctor_set(x_1647, 1, x_2);
lean_ctor_set(x_1647, 2, x_3);
lean_ctor_set(x_1647, 3, x_4);
lean_ctor_set_uint8(x_1647, sizeof(void*)*4, x_1646);
return x_1647;
}
else
{
uint8_t x_1648; 
x_1648 = lean_ctor_get_uint8(x_1644, sizeof(void*)*4);
if (x_1648 == 0)
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; uint8_t x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; uint8_t x_1661; lean_object* x_1662; 
x_1649 = lean_ctor_get(x_4, 1);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_4, 2);
lean_inc(x_1650);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1651 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1651 = lean_box(0);
}
x_1652 = lean_ctor_get(x_1644, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1644, 1);
lean_inc(x_1653);
x_1654 = lean_ctor_get(x_1644, 2);
lean_inc(x_1654);
x_1655 = lean_ctor_get(x_1644, 3);
lean_inc(x_1655);
if (lean_is_exclusive(x_1644)) {
 lean_ctor_release(x_1644, 0);
 lean_ctor_release(x_1644, 1);
 lean_ctor_release(x_1644, 2);
 lean_ctor_release(x_1644, 3);
 x_1656 = x_1644;
} else {
 lean_dec_ref(x_1644);
 x_1656 = lean_box(0);
}
x_1657 = 1;
lean_inc(x_1575);
if (lean_is_scalar(x_1656)) {
 x_1658 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1658 = x_1656;
}
lean_ctor_set(x_1658, 0, x_1);
lean_ctor_set(x_1658, 1, x_2);
lean_ctor_set(x_1658, 2, x_3);
lean_ctor_set(x_1658, 3, x_1575);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 lean_ctor_release(x_1575, 2);
 lean_ctor_release(x_1575, 3);
 x_1659 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1659 = lean_box(0);
}
lean_ctor_set_uint8(x_1658, sizeof(void*)*4, x_1657);
if (lean_is_scalar(x_1659)) {
 x_1660 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1660 = x_1659;
}
lean_ctor_set(x_1660, 0, x_1652);
lean_ctor_set(x_1660, 1, x_1653);
lean_ctor_set(x_1660, 2, x_1654);
lean_ctor_set(x_1660, 3, x_1655);
lean_ctor_set_uint8(x_1660, sizeof(void*)*4, x_1657);
x_1661 = 0;
if (lean_is_scalar(x_1651)) {
 x_1662 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1662 = x_1651;
}
lean_ctor_set(x_1662, 0, x_1658);
lean_ctor_set(x_1662, 1, x_1649);
lean_ctor_set(x_1662, 2, x_1650);
lean_ctor_set(x_1662, 3, x_1660);
lean_ctor_set_uint8(x_1662, sizeof(void*)*4, x_1661);
return x_1662;
}
else
{
lean_object* x_1663; uint8_t x_1664; lean_object* x_1665; 
lean_dec(x_1575);
if (lean_is_exclusive(x_1644)) {
 lean_ctor_release(x_1644, 0);
 lean_ctor_release(x_1644, 1);
 lean_ctor_release(x_1644, 2);
 lean_ctor_release(x_1644, 3);
 x_1663 = x_1644;
} else {
 lean_dec_ref(x_1644);
 x_1663 = lean_box(0);
}
x_1664 = 1;
if (lean_is_scalar(x_1663)) {
 x_1665 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1665 = x_1663;
}
lean_ctor_set(x_1665, 0, x_1);
lean_ctor_set(x_1665, 1, x_2);
lean_ctor_set(x_1665, 2, x_3);
lean_ctor_set(x_1665, 3, x_4);
lean_ctor_set_uint8(x_1665, sizeof(void*)*4, x_1664);
return x_1665;
}
}
}
}
}
else
{
uint8_t x_1666; lean_object* x_1667; 
x_1666 = 1;
x_1667 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1667, 0, x_1);
lean_ctor_set(x_1667, 1, x_2);
lean_ctor_set(x_1667, 2, x_3);
lean_ctor_set(x_1667, 3, x_4);
lean_ctor_set_uint8(x_1667, sizeof(void*)*4, x_1666);
return x_1667;
}
}
}
}
else
{
lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
x_1668 = lean_ctor_get(x_1, 1);
x_1669 = lean_ctor_get(x_1, 2);
lean_inc(x_1669);
lean_inc(x_1668);
lean_dec(x_1);
x_1670 = lean_ctor_get(x_241, 0);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_241, 1);
lean_inc(x_1671);
x_1672 = lean_ctor_get(x_241, 2);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_241, 3);
lean_inc(x_1673);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_1674 = x_241;
} else {
 lean_dec_ref(x_241);
 x_1674 = lean_box(0);
}
if (lean_is_scalar(x_1674)) {
 x_1675 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1675 = x_1674;
}
lean_ctor_set(x_1675, 0, x_1670);
lean_ctor_set(x_1675, 1, x_1671);
lean_ctor_set(x_1675, 2, x_1672);
lean_ctor_set(x_1675, 3, x_1673);
lean_ctor_set_uint8(x_1675, sizeof(void*)*4, x_1286);
x_1676 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1676, 0, x_1675);
lean_ctor_set(x_1676, 1, x_1668);
lean_ctor_set(x_1676, 2, x_1669);
lean_ctor_set(x_1676, 3, x_965);
lean_ctor_set_uint8(x_1676, sizeof(void*)*4, x_240);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1677; lean_object* x_1678; 
x_1677 = 1;
x_1678 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1678, 0, x_1676);
lean_ctor_set(x_1678, 1, x_2);
lean_ctor_set(x_1678, 2, x_3);
lean_ctor_set(x_1678, 3, x_4);
lean_ctor_set_uint8(x_1678, sizeof(void*)*4, x_1677);
return x_1678;
}
else
{
uint8_t x_1679; 
x_1679 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1679 == 0)
{
lean_object* x_1680; 
x_1680 = lean_ctor_get(x_4, 0);
lean_inc(x_1680);
if (lean_obj_tag(x_1680) == 0)
{
lean_object* x_1681; 
x_1681 = lean_ctor_get(x_4, 3);
lean_inc(x_1681);
if (lean_obj_tag(x_1681) == 0)
{
uint8_t x_1682; lean_object* x_1683; 
x_1682 = 1;
x_1683 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1683, 0, x_1676);
lean_ctor_set(x_1683, 1, x_2);
lean_ctor_set(x_1683, 2, x_3);
lean_ctor_set(x_1683, 3, x_4);
lean_ctor_set_uint8(x_1683, sizeof(void*)*4, x_1682);
return x_1683;
}
else
{
uint8_t x_1684; 
x_1684 = lean_ctor_get_uint8(x_1681, sizeof(void*)*4);
if (x_1684 == 0)
{
lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; uint8_t x_1693; lean_object* x_1694; lean_object* x_1695; uint8_t x_1696; lean_object* x_1697; 
x_1685 = lean_ctor_get(x_4, 1);
lean_inc(x_1685);
x_1686 = lean_ctor_get(x_4, 2);
lean_inc(x_1686);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1687 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1687 = lean_box(0);
}
x_1688 = lean_ctor_get(x_1681, 0);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1681, 1);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1681, 2);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1681, 3);
lean_inc(x_1691);
if (lean_is_exclusive(x_1681)) {
 lean_ctor_release(x_1681, 0);
 lean_ctor_release(x_1681, 1);
 lean_ctor_release(x_1681, 2);
 lean_ctor_release(x_1681, 3);
 x_1692 = x_1681;
} else {
 lean_dec_ref(x_1681);
 x_1692 = lean_box(0);
}
x_1693 = 1;
if (lean_is_scalar(x_1692)) {
 x_1694 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1694 = x_1692;
}
lean_ctor_set(x_1694, 0, x_1676);
lean_ctor_set(x_1694, 1, x_2);
lean_ctor_set(x_1694, 2, x_3);
lean_ctor_set(x_1694, 3, x_1680);
lean_ctor_set_uint8(x_1694, sizeof(void*)*4, x_1693);
if (lean_is_scalar(x_1687)) {
 x_1695 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1695 = x_1687;
}
lean_ctor_set(x_1695, 0, x_1688);
lean_ctor_set(x_1695, 1, x_1689);
lean_ctor_set(x_1695, 2, x_1690);
lean_ctor_set(x_1695, 3, x_1691);
lean_ctor_set_uint8(x_1695, sizeof(void*)*4, x_1693);
x_1696 = 0;
x_1697 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1697, 0, x_1694);
lean_ctor_set(x_1697, 1, x_1685);
lean_ctor_set(x_1697, 2, x_1686);
lean_ctor_set(x_1697, 3, x_1695);
lean_ctor_set_uint8(x_1697, sizeof(void*)*4, x_1696);
return x_1697;
}
else
{
lean_object* x_1698; uint8_t x_1699; lean_object* x_1700; 
if (lean_is_exclusive(x_1681)) {
 lean_ctor_release(x_1681, 0);
 lean_ctor_release(x_1681, 1);
 lean_ctor_release(x_1681, 2);
 lean_ctor_release(x_1681, 3);
 x_1698 = x_1681;
} else {
 lean_dec_ref(x_1681);
 x_1698 = lean_box(0);
}
x_1699 = 1;
if (lean_is_scalar(x_1698)) {
 x_1700 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1700 = x_1698;
}
lean_ctor_set(x_1700, 0, x_1676);
lean_ctor_set(x_1700, 1, x_2);
lean_ctor_set(x_1700, 2, x_3);
lean_ctor_set(x_1700, 3, x_4);
lean_ctor_set_uint8(x_1700, sizeof(void*)*4, x_1699);
return x_1700;
}
}
}
else
{
uint8_t x_1701; 
x_1701 = lean_ctor_get_uint8(x_1680, sizeof(void*)*4);
if (x_1701 == 0)
{
lean_object* x_1702; 
x_1702 = lean_ctor_get(x_4, 3);
lean_inc(x_1702);
if (lean_obj_tag(x_1702) == 0)
{
lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; uint8_t x_1711; lean_object* x_1712; lean_object* x_1713; uint8_t x_1714; lean_object* x_1715; 
x_1703 = lean_ctor_get(x_4, 1);
lean_inc(x_1703);
x_1704 = lean_ctor_get(x_4, 2);
lean_inc(x_1704);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1705 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1705 = lean_box(0);
}
x_1706 = lean_ctor_get(x_1680, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1680, 1);
lean_inc(x_1707);
x_1708 = lean_ctor_get(x_1680, 2);
lean_inc(x_1708);
x_1709 = lean_ctor_get(x_1680, 3);
lean_inc(x_1709);
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 lean_ctor_release(x_1680, 2);
 lean_ctor_release(x_1680, 3);
 x_1710 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1710 = lean_box(0);
}
x_1711 = 1;
if (lean_is_scalar(x_1710)) {
 x_1712 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1712 = x_1710;
}
lean_ctor_set(x_1712, 0, x_1676);
lean_ctor_set(x_1712, 1, x_2);
lean_ctor_set(x_1712, 2, x_3);
lean_ctor_set(x_1712, 3, x_1706);
lean_ctor_set_uint8(x_1712, sizeof(void*)*4, x_1711);
if (lean_is_scalar(x_1705)) {
 x_1713 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1713 = x_1705;
}
lean_ctor_set(x_1713, 0, x_1709);
lean_ctor_set(x_1713, 1, x_1703);
lean_ctor_set(x_1713, 2, x_1704);
lean_ctor_set(x_1713, 3, x_1702);
lean_ctor_set_uint8(x_1713, sizeof(void*)*4, x_1711);
x_1714 = 0;
x_1715 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1715, 0, x_1712);
lean_ctor_set(x_1715, 1, x_1707);
lean_ctor_set(x_1715, 2, x_1708);
lean_ctor_set(x_1715, 3, x_1713);
lean_ctor_set_uint8(x_1715, sizeof(void*)*4, x_1714);
return x_1715;
}
else
{
uint8_t x_1716; 
x_1716 = lean_ctor_get_uint8(x_1702, sizeof(void*)*4);
if (x_1716 == 0)
{
lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; uint8_t x_1731; lean_object* x_1732; lean_object* x_1733; uint8_t x_1734; lean_object* x_1735; 
x_1717 = lean_ctor_get(x_4, 1);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_4, 2);
lean_inc(x_1718);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1719 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1719 = lean_box(0);
}
x_1720 = lean_ctor_get(x_1680, 0);
lean_inc(x_1720);
x_1721 = lean_ctor_get(x_1680, 1);
lean_inc(x_1721);
x_1722 = lean_ctor_get(x_1680, 2);
lean_inc(x_1722);
x_1723 = lean_ctor_get(x_1680, 3);
lean_inc(x_1723);
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 lean_ctor_release(x_1680, 2);
 lean_ctor_release(x_1680, 3);
 x_1724 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1724 = lean_box(0);
}
x_1725 = lean_ctor_get(x_1702, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1702, 1);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1702, 2);
lean_inc(x_1727);
x_1728 = lean_ctor_get(x_1702, 3);
lean_inc(x_1728);
if (lean_is_exclusive(x_1702)) {
 lean_ctor_release(x_1702, 0);
 lean_ctor_release(x_1702, 1);
 lean_ctor_release(x_1702, 2);
 lean_ctor_release(x_1702, 3);
 x_1729 = x_1702;
} else {
 lean_dec_ref(x_1702);
 x_1729 = lean_box(0);
}
if (lean_is_scalar(x_1729)) {
 x_1730 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1730 = x_1729;
}
lean_ctor_set(x_1730, 0, x_1720);
lean_ctor_set(x_1730, 1, x_1721);
lean_ctor_set(x_1730, 2, x_1722);
lean_ctor_set(x_1730, 3, x_1723);
lean_ctor_set_uint8(x_1730, sizeof(void*)*4, x_1716);
x_1731 = 1;
if (lean_is_scalar(x_1724)) {
 x_1732 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1732 = x_1724;
}
lean_ctor_set(x_1732, 0, x_1676);
lean_ctor_set(x_1732, 1, x_2);
lean_ctor_set(x_1732, 2, x_3);
lean_ctor_set(x_1732, 3, x_1730);
lean_ctor_set_uint8(x_1732, sizeof(void*)*4, x_1731);
if (lean_is_scalar(x_1719)) {
 x_1733 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1733 = x_1719;
}
lean_ctor_set(x_1733, 0, x_1725);
lean_ctor_set(x_1733, 1, x_1726);
lean_ctor_set(x_1733, 2, x_1727);
lean_ctor_set(x_1733, 3, x_1728);
lean_ctor_set_uint8(x_1733, sizeof(void*)*4, x_1731);
x_1734 = 0;
x_1735 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1735, 0, x_1732);
lean_ctor_set(x_1735, 1, x_1717);
lean_ctor_set(x_1735, 2, x_1718);
lean_ctor_set(x_1735, 3, x_1733);
lean_ctor_set_uint8(x_1735, sizeof(void*)*4, x_1734);
return x_1735;
}
else
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; uint8_t x_1744; lean_object* x_1745; lean_object* x_1746; uint8_t x_1747; lean_object* x_1748; 
x_1736 = lean_ctor_get(x_4, 1);
lean_inc(x_1736);
x_1737 = lean_ctor_get(x_4, 2);
lean_inc(x_1737);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1738 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1738 = lean_box(0);
}
x_1739 = lean_ctor_get(x_1680, 0);
lean_inc(x_1739);
x_1740 = lean_ctor_get(x_1680, 1);
lean_inc(x_1740);
x_1741 = lean_ctor_get(x_1680, 2);
lean_inc(x_1741);
x_1742 = lean_ctor_get(x_1680, 3);
lean_inc(x_1742);
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 lean_ctor_release(x_1680, 2);
 lean_ctor_release(x_1680, 3);
 x_1743 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1743 = lean_box(0);
}
x_1744 = 1;
if (lean_is_scalar(x_1743)) {
 x_1745 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1745 = x_1743;
}
lean_ctor_set(x_1745, 0, x_1676);
lean_ctor_set(x_1745, 1, x_2);
lean_ctor_set(x_1745, 2, x_3);
lean_ctor_set(x_1745, 3, x_1739);
lean_ctor_set_uint8(x_1745, sizeof(void*)*4, x_1744);
if (lean_is_scalar(x_1738)) {
 x_1746 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1746 = x_1738;
}
lean_ctor_set(x_1746, 0, x_1742);
lean_ctor_set(x_1746, 1, x_1736);
lean_ctor_set(x_1746, 2, x_1737);
lean_ctor_set(x_1746, 3, x_1702);
lean_ctor_set_uint8(x_1746, sizeof(void*)*4, x_1744);
x_1747 = 0;
x_1748 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1748, 0, x_1745);
lean_ctor_set(x_1748, 1, x_1740);
lean_ctor_set(x_1748, 2, x_1741);
lean_ctor_set(x_1748, 3, x_1746);
lean_ctor_set_uint8(x_1748, sizeof(void*)*4, x_1747);
return x_1748;
}
}
}
else
{
lean_object* x_1749; 
x_1749 = lean_ctor_get(x_4, 3);
lean_inc(x_1749);
if (lean_obj_tag(x_1749) == 0)
{
lean_object* x_1750; uint8_t x_1751; lean_object* x_1752; 
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 lean_ctor_release(x_1680, 2);
 lean_ctor_release(x_1680, 3);
 x_1750 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1750 = lean_box(0);
}
x_1751 = 1;
if (lean_is_scalar(x_1750)) {
 x_1752 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1752 = x_1750;
}
lean_ctor_set(x_1752, 0, x_1676);
lean_ctor_set(x_1752, 1, x_2);
lean_ctor_set(x_1752, 2, x_3);
lean_ctor_set(x_1752, 3, x_4);
lean_ctor_set_uint8(x_1752, sizeof(void*)*4, x_1751);
return x_1752;
}
else
{
uint8_t x_1753; 
x_1753 = lean_ctor_get_uint8(x_1749, sizeof(void*)*4);
if (x_1753 == 0)
{
lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; uint8_t x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; uint8_t x_1766; lean_object* x_1767; 
x_1754 = lean_ctor_get(x_4, 1);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_4, 2);
lean_inc(x_1755);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1756 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1756 = lean_box(0);
}
x_1757 = lean_ctor_get(x_1749, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1749, 1);
lean_inc(x_1758);
x_1759 = lean_ctor_get(x_1749, 2);
lean_inc(x_1759);
x_1760 = lean_ctor_get(x_1749, 3);
lean_inc(x_1760);
if (lean_is_exclusive(x_1749)) {
 lean_ctor_release(x_1749, 0);
 lean_ctor_release(x_1749, 1);
 lean_ctor_release(x_1749, 2);
 lean_ctor_release(x_1749, 3);
 x_1761 = x_1749;
} else {
 lean_dec_ref(x_1749);
 x_1761 = lean_box(0);
}
x_1762 = 1;
lean_inc(x_1680);
if (lean_is_scalar(x_1761)) {
 x_1763 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1763 = x_1761;
}
lean_ctor_set(x_1763, 0, x_1676);
lean_ctor_set(x_1763, 1, x_2);
lean_ctor_set(x_1763, 2, x_3);
lean_ctor_set(x_1763, 3, x_1680);
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 lean_ctor_release(x_1680, 2);
 lean_ctor_release(x_1680, 3);
 x_1764 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1764 = lean_box(0);
}
lean_ctor_set_uint8(x_1763, sizeof(void*)*4, x_1762);
if (lean_is_scalar(x_1764)) {
 x_1765 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1765 = x_1764;
}
lean_ctor_set(x_1765, 0, x_1757);
lean_ctor_set(x_1765, 1, x_1758);
lean_ctor_set(x_1765, 2, x_1759);
lean_ctor_set(x_1765, 3, x_1760);
lean_ctor_set_uint8(x_1765, sizeof(void*)*4, x_1762);
x_1766 = 0;
if (lean_is_scalar(x_1756)) {
 x_1767 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1767 = x_1756;
}
lean_ctor_set(x_1767, 0, x_1763);
lean_ctor_set(x_1767, 1, x_1754);
lean_ctor_set(x_1767, 2, x_1755);
lean_ctor_set(x_1767, 3, x_1765);
lean_ctor_set_uint8(x_1767, sizeof(void*)*4, x_1766);
return x_1767;
}
else
{
lean_object* x_1768; uint8_t x_1769; lean_object* x_1770; 
lean_dec(x_1680);
if (lean_is_exclusive(x_1749)) {
 lean_ctor_release(x_1749, 0);
 lean_ctor_release(x_1749, 1);
 lean_ctor_release(x_1749, 2);
 lean_ctor_release(x_1749, 3);
 x_1768 = x_1749;
} else {
 lean_dec_ref(x_1749);
 x_1768 = lean_box(0);
}
x_1769 = 1;
if (lean_is_scalar(x_1768)) {
 x_1770 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1770 = x_1768;
}
lean_ctor_set(x_1770, 0, x_1676);
lean_ctor_set(x_1770, 1, x_2);
lean_ctor_set(x_1770, 2, x_3);
lean_ctor_set(x_1770, 3, x_4);
lean_ctor_set_uint8(x_1770, sizeof(void*)*4, x_1769);
return x_1770;
}
}
}
}
}
else
{
uint8_t x_1771; lean_object* x_1772; 
x_1771 = 1;
x_1772 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1772, 0, x_1676);
lean_ctor_set(x_1772, 1, x_2);
lean_ctor_set(x_1772, 2, x_3);
lean_ctor_set(x_1772, 3, x_4);
lean_ctor_set_uint8(x_1772, sizeof(void*)*4, x_1771);
return x_1772;
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
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1773; lean_object* x_1774; 
x_1773 = 1;
x_1774 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1774, 0, x_1);
lean_ctor_set(x_1774, 1, x_2);
lean_ctor_set(x_1774, 2, x_3);
lean_ctor_set(x_1774, 3, x_4);
lean_ctor_set_uint8(x_1774, sizeof(void*)*4, x_1773);
return x_1774;
}
else
{
uint8_t x_1775; 
x_1775 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1775 == 0)
{
lean_object* x_1776; 
x_1776 = lean_ctor_get(x_4, 0);
lean_inc(x_1776);
if (lean_obj_tag(x_1776) == 0)
{
lean_object* x_1777; 
x_1777 = lean_ctor_get(x_4, 3);
lean_inc(x_1777);
if (lean_obj_tag(x_1777) == 0)
{
uint8_t x_1778; lean_object* x_1779; 
x_1778 = 1;
x_1779 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1779, 0, x_1);
lean_ctor_set(x_1779, 1, x_2);
lean_ctor_set(x_1779, 2, x_3);
lean_ctor_set(x_1779, 3, x_4);
lean_ctor_set_uint8(x_1779, sizeof(void*)*4, x_1778);
return x_1779;
}
else
{
uint8_t x_1780; 
x_1780 = lean_ctor_get_uint8(x_1777, sizeof(void*)*4);
if (x_1780 == 0)
{
uint8_t x_1781; 
x_1781 = !lean_is_exclusive(x_4);
if (x_1781 == 0)
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; uint8_t x_1786; 
x_1782 = lean_ctor_get(x_4, 1);
x_1783 = lean_ctor_get(x_4, 2);
x_1784 = lean_ctor_get(x_4, 3);
lean_dec(x_1784);
x_1785 = lean_ctor_get(x_4, 0);
lean_dec(x_1785);
x_1786 = !lean_is_exclusive(x_1777);
if (x_1786 == 0)
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; uint8_t x_1791; uint8_t x_1792; 
x_1787 = lean_ctor_get(x_1777, 0);
x_1788 = lean_ctor_get(x_1777, 1);
x_1789 = lean_ctor_get(x_1777, 2);
x_1790 = lean_ctor_get(x_1777, 3);
x_1791 = 1;
lean_inc(x_1);
lean_ctor_set(x_1777, 3, x_1776);
lean_ctor_set(x_1777, 2, x_3);
lean_ctor_set(x_1777, 1, x_2);
lean_ctor_set(x_1777, 0, x_1);
x_1792 = !lean_is_exclusive(x_1);
if (x_1792 == 0)
{
lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; uint8_t x_1797; 
x_1793 = lean_ctor_get(x_1, 3);
lean_dec(x_1793);
x_1794 = lean_ctor_get(x_1, 2);
lean_dec(x_1794);
x_1795 = lean_ctor_get(x_1, 1);
lean_dec(x_1795);
x_1796 = lean_ctor_get(x_1, 0);
lean_dec(x_1796);
lean_ctor_set_uint8(x_1777, sizeof(void*)*4, x_1791);
lean_ctor_set(x_4, 3, x_1790);
lean_ctor_set(x_4, 2, x_1789);
lean_ctor_set(x_4, 1, x_1788);
lean_ctor_set(x_4, 0, x_1787);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1791);
x_1797 = 0;
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_1783);
lean_ctor_set(x_1, 1, x_1782);
lean_ctor_set(x_1, 0, x_1777);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1797);
return x_1;
}
else
{
uint8_t x_1798; lean_object* x_1799; 
lean_dec(x_1);
lean_ctor_set_uint8(x_1777, sizeof(void*)*4, x_1791);
lean_ctor_set(x_4, 3, x_1790);
lean_ctor_set(x_4, 2, x_1789);
lean_ctor_set(x_4, 1, x_1788);
lean_ctor_set(x_4, 0, x_1787);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1791);
x_1798 = 0;
x_1799 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1799, 0, x_1777);
lean_ctor_set(x_1799, 1, x_1782);
lean_ctor_set(x_1799, 2, x_1783);
lean_ctor_set(x_1799, 3, x_4);
lean_ctor_set_uint8(x_1799, sizeof(void*)*4, x_1798);
return x_1799;
}
}
else
{
lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; uint8_t x_1804; lean_object* x_1805; lean_object* x_1806; uint8_t x_1807; lean_object* x_1808; 
x_1800 = lean_ctor_get(x_1777, 0);
x_1801 = lean_ctor_get(x_1777, 1);
x_1802 = lean_ctor_get(x_1777, 2);
x_1803 = lean_ctor_get(x_1777, 3);
lean_inc(x_1803);
lean_inc(x_1802);
lean_inc(x_1801);
lean_inc(x_1800);
lean_dec(x_1777);
x_1804 = 1;
lean_inc(x_1);
x_1805 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1805, 0, x_1);
lean_ctor_set(x_1805, 1, x_2);
lean_ctor_set(x_1805, 2, x_3);
lean_ctor_set(x_1805, 3, x_1776);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1806 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1806 = lean_box(0);
}
lean_ctor_set_uint8(x_1805, sizeof(void*)*4, x_1804);
lean_ctor_set(x_4, 3, x_1803);
lean_ctor_set(x_4, 2, x_1802);
lean_ctor_set(x_4, 1, x_1801);
lean_ctor_set(x_4, 0, x_1800);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1804);
x_1807 = 0;
if (lean_is_scalar(x_1806)) {
 x_1808 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1808 = x_1806;
}
lean_ctor_set(x_1808, 0, x_1805);
lean_ctor_set(x_1808, 1, x_1782);
lean_ctor_set(x_1808, 2, x_1783);
lean_ctor_set(x_1808, 3, x_4);
lean_ctor_set_uint8(x_1808, sizeof(void*)*4, x_1807);
return x_1808;
}
}
else
{
lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; uint8_t x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; uint8_t x_1820; lean_object* x_1821; 
x_1809 = lean_ctor_get(x_4, 1);
x_1810 = lean_ctor_get(x_4, 2);
lean_inc(x_1810);
lean_inc(x_1809);
lean_dec(x_4);
x_1811 = lean_ctor_get(x_1777, 0);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1777, 1);
lean_inc(x_1812);
x_1813 = lean_ctor_get(x_1777, 2);
lean_inc(x_1813);
x_1814 = lean_ctor_get(x_1777, 3);
lean_inc(x_1814);
if (lean_is_exclusive(x_1777)) {
 lean_ctor_release(x_1777, 0);
 lean_ctor_release(x_1777, 1);
 lean_ctor_release(x_1777, 2);
 lean_ctor_release(x_1777, 3);
 x_1815 = x_1777;
} else {
 lean_dec_ref(x_1777);
 x_1815 = lean_box(0);
}
x_1816 = 1;
lean_inc(x_1);
if (lean_is_scalar(x_1815)) {
 x_1817 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1817 = x_1815;
}
lean_ctor_set(x_1817, 0, x_1);
lean_ctor_set(x_1817, 1, x_2);
lean_ctor_set(x_1817, 2, x_3);
lean_ctor_set(x_1817, 3, x_1776);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1818 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1818 = lean_box(0);
}
lean_ctor_set_uint8(x_1817, sizeof(void*)*4, x_1816);
x_1819 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1819, 0, x_1811);
lean_ctor_set(x_1819, 1, x_1812);
lean_ctor_set(x_1819, 2, x_1813);
lean_ctor_set(x_1819, 3, x_1814);
lean_ctor_set_uint8(x_1819, sizeof(void*)*4, x_1816);
x_1820 = 0;
if (lean_is_scalar(x_1818)) {
 x_1821 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1821 = x_1818;
}
lean_ctor_set(x_1821, 0, x_1817);
lean_ctor_set(x_1821, 1, x_1809);
lean_ctor_set(x_1821, 2, x_1810);
lean_ctor_set(x_1821, 3, x_1819);
lean_ctor_set_uint8(x_1821, sizeof(void*)*4, x_1820);
return x_1821;
}
}
else
{
uint8_t x_1822; 
x_1822 = !lean_is_exclusive(x_1777);
if (x_1822 == 0)
{
lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; uint8_t x_1827; 
x_1823 = lean_ctor_get(x_1777, 3);
lean_dec(x_1823);
x_1824 = lean_ctor_get(x_1777, 2);
lean_dec(x_1824);
x_1825 = lean_ctor_get(x_1777, 1);
lean_dec(x_1825);
x_1826 = lean_ctor_get(x_1777, 0);
lean_dec(x_1826);
x_1827 = 1;
lean_ctor_set(x_1777, 3, x_4);
lean_ctor_set(x_1777, 2, x_3);
lean_ctor_set(x_1777, 1, x_2);
lean_ctor_set(x_1777, 0, x_1);
lean_ctor_set_uint8(x_1777, sizeof(void*)*4, x_1827);
return x_1777;
}
else
{
uint8_t x_1828; lean_object* x_1829; 
lean_dec(x_1777);
x_1828 = 1;
x_1829 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1829, 0, x_1);
lean_ctor_set(x_1829, 1, x_2);
lean_ctor_set(x_1829, 2, x_3);
lean_ctor_set(x_1829, 3, x_4);
lean_ctor_set_uint8(x_1829, sizeof(void*)*4, x_1828);
return x_1829;
}
}
}
}
else
{
uint8_t x_1830; 
x_1830 = lean_ctor_get_uint8(x_1776, sizeof(void*)*4);
if (x_1830 == 0)
{
lean_object* x_1831; 
x_1831 = lean_ctor_get(x_4, 3);
lean_inc(x_1831);
if (lean_obj_tag(x_1831) == 0)
{
uint8_t x_1832; 
x_1832 = !lean_is_exclusive(x_4);
if (x_1832 == 0)
{
lean_object* x_1833; lean_object* x_1834; uint8_t x_1835; 
x_1833 = lean_ctor_get(x_4, 3);
lean_dec(x_1833);
x_1834 = lean_ctor_get(x_4, 0);
lean_dec(x_1834);
x_1835 = !lean_is_exclusive(x_1776);
if (x_1835 == 0)
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; uint8_t x_1840; uint8_t x_1841; 
x_1836 = lean_ctor_get(x_1776, 0);
x_1837 = lean_ctor_get(x_1776, 1);
x_1838 = lean_ctor_get(x_1776, 2);
x_1839 = lean_ctor_get(x_1776, 3);
x_1840 = 1;
lean_inc(x_1);
lean_ctor_set(x_1776, 3, x_1836);
lean_ctor_set(x_1776, 2, x_3);
lean_ctor_set(x_1776, 1, x_2);
lean_ctor_set(x_1776, 0, x_1);
x_1841 = !lean_is_exclusive(x_1);
if (x_1841 == 0)
{
lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; uint8_t x_1846; 
x_1842 = lean_ctor_get(x_1, 3);
lean_dec(x_1842);
x_1843 = lean_ctor_get(x_1, 2);
lean_dec(x_1843);
x_1844 = lean_ctor_get(x_1, 1);
lean_dec(x_1844);
x_1845 = lean_ctor_get(x_1, 0);
lean_dec(x_1845);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1840);
lean_ctor_set(x_4, 0, x_1839);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1840);
x_1846 = 0;
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_1838);
lean_ctor_set(x_1, 1, x_1837);
lean_ctor_set(x_1, 0, x_1776);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1846);
return x_1;
}
else
{
uint8_t x_1847; lean_object* x_1848; 
lean_dec(x_1);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1840);
lean_ctor_set(x_4, 0, x_1839);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1840);
x_1847 = 0;
x_1848 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1848, 0, x_1776);
lean_ctor_set(x_1848, 1, x_1837);
lean_ctor_set(x_1848, 2, x_1838);
lean_ctor_set(x_1848, 3, x_4);
lean_ctor_set_uint8(x_1848, sizeof(void*)*4, x_1847);
return x_1848;
}
}
else
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; uint8_t x_1853; lean_object* x_1854; lean_object* x_1855; uint8_t x_1856; lean_object* x_1857; 
x_1849 = lean_ctor_get(x_1776, 0);
x_1850 = lean_ctor_get(x_1776, 1);
x_1851 = lean_ctor_get(x_1776, 2);
x_1852 = lean_ctor_get(x_1776, 3);
lean_inc(x_1852);
lean_inc(x_1851);
lean_inc(x_1850);
lean_inc(x_1849);
lean_dec(x_1776);
x_1853 = 1;
lean_inc(x_1);
x_1854 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1854, 0, x_1);
lean_ctor_set(x_1854, 1, x_2);
lean_ctor_set(x_1854, 2, x_3);
lean_ctor_set(x_1854, 3, x_1849);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1855 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1855 = lean_box(0);
}
lean_ctor_set_uint8(x_1854, sizeof(void*)*4, x_1853);
lean_ctor_set(x_4, 0, x_1852);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1853);
x_1856 = 0;
if (lean_is_scalar(x_1855)) {
 x_1857 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1857 = x_1855;
}
lean_ctor_set(x_1857, 0, x_1854);
lean_ctor_set(x_1857, 1, x_1850);
lean_ctor_set(x_1857, 2, x_1851);
lean_ctor_set(x_1857, 3, x_4);
lean_ctor_set_uint8(x_1857, sizeof(void*)*4, x_1856);
return x_1857;
}
}
else
{
lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; uint8_t x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; uint8_t x_1869; lean_object* x_1870; 
x_1858 = lean_ctor_get(x_4, 1);
x_1859 = lean_ctor_get(x_4, 2);
lean_inc(x_1859);
lean_inc(x_1858);
lean_dec(x_4);
x_1860 = lean_ctor_get(x_1776, 0);
lean_inc(x_1860);
x_1861 = lean_ctor_get(x_1776, 1);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1776, 2);
lean_inc(x_1862);
x_1863 = lean_ctor_get(x_1776, 3);
lean_inc(x_1863);
if (lean_is_exclusive(x_1776)) {
 lean_ctor_release(x_1776, 0);
 lean_ctor_release(x_1776, 1);
 lean_ctor_release(x_1776, 2);
 lean_ctor_release(x_1776, 3);
 x_1864 = x_1776;
} else {
 lean_dec_ref(x_1776);
 x_1864 = lean_box(0);
}
x_1865 = 1;
lean_inc(x_1);
if (lean_is_scalar(x_1864)) {
 x_1866 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1866 = x_1864;
}
lean_ctor_set(x_1866, 0, x_1);
lean_ctor_set(x_1866, 1, x_2);
lean_ctor_set(x_1866, 2, x_3);
lean_ctor_set(x_1866, 3, x_1860);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1867 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1867 = lean_box(0);
}
lean_ctor_set_uint8(x_1866, sizeof(void*)*4, x_1865);
x_1868 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1868, 0, x_1863);
lean_ctor_set(x_1868, 1, x_1858);
lean_ctor_set(x_1868, 2, x_1859);
lean_ctor_set(x_1868, 3, x_1831);
lean_ctor_set_uint8(x_1868, sizeof(void*)*4, x_1865);
x_1869 = 0;
if (lean_is_scalar(x_1867)) {
 x_1870 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1870 = x_1867;
}
lean_ctor_set(x_1870, 0, x_1866);
lean_ctor_set(x_1870, 1, x_1861);
lean_ctor_set(x_1870, 2, x_1862);
lean_ctor_set(x_1870, 3, x_1868);
lean_ctor_set_uint8(x_1870, sizeof(void*)*4, x_1869);
return x_1870;
}
}
else
{
uint8_t x_1871; 
x_1871 = lean_ctor_get_uint8(x_1831, sizeof(void*)*4);
if (x_1871 == 0)
{
uint8_t x_1872; 
x_1872 = !lean_is_exclusive(x_4);
if (x_1872 == 0)
{
lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; uint8_t x_1877; 
x_1873 = lean_ctor_get(x_4, 1);
x_1874 = lean_ctor_get(x_4, 2);
x_1875 = lean_ctor_get(x_4, 3);
lean_dec(x_1875);
x_1876 = lean_ctor_get(x_4, 0);
lean_dec(x_1876);
x_1877 = !lean_is_exclusive(x_1776);
if (x_1877 == 0)
{
uint8_t x_1878; 
x_1878 = !lean_is_exclusive(x_1831);
if (x_1878 == 0)
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; uint8_t x_1887; uint8_t x_1888; 
x_1879 = lean_ctor_get(x_1776, 0);
x_1880 = lean_ctor_get(x_1776, 1);
x_1881 = lean_ctor_get(x_1776, 2);
x_1882 = lean_ctor_get(x_1776, 3);
x_1883 = lean_ctor_get(x_1831, 0);
x_1884 = lean_ctor_get(x_1831, 1);
x_1885 = lean_ctor_get(x_1831, 2);
x_1886 = lean_ctor_get(x_1831, 3);
lean_ctor_set(x_1831, 3, x_1882);
lean_ctor_set(x_1831, 2, x_1881);
lean_ctor_set(x_1831, 1, x_1880);
lean_ctor_set(x_1831, 0, x_1879);
x_1887 = 1;
lean_inc(x_1);
lean_ctor_set(x_1776, 3, x_1831);
lean_ctor_set(x_1776, 2, x_3);
lean_ctor_set(x_1776, 1, x_2);
lean_ctor_set(x_1776, 0, x_1);
x_1888 = !lean_is_exclusive(x_1);
if (x_1888 == 0)
{
lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; uint8_t x_1893; 
x_1889 = lean_ctor_get(x_1, 3);
lean_dec(x_1889);
x_1890 = lean_ctor_get(x_1, 2);
lean_dec(x_1890);
x_1891 = lean_ctor_get(x_1, 1);
lean_dec(x_1891);
x_1892 = lean_ctor_get(x_1, 0);
lean_dec(x_1892);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1887);
lean_ctor_set(x_4, 3, x_1886);
lean_ctor_set(x_4, 2, x_1885);
lean_ctor_set(x_4, 1, x_1884);
lean_ctor_set(x_4, 0, x_1883);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1887);
x_1893 = 0;
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_1874);
lean_ctor_set(x_1, 1, x_1873);
lean_ctor_set(x_1, 0, x_1776);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1893);
return x_1;
}
else
{
uint8_t x_1894; lean_object* x_1895; 
lean_dec(x_1);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1887);
lean_ctor_set(x_4, 3, x_1886);
lean_ctor_set(x_4, 2, x_1885);
lean_ctor_set(x_4, 1, x_1884);
lean_ctor_set(x_4, 0, x_1883);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1887);
x_1894 = 0;
x_1895 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1895, 0, x_1776);
lean_ctor_set(x_1895, 1, x_1873);
lean_ctor_set(x_1895, 2, x_1874);
lean_ctor_set(x_1895, 3, x_4);
lean_ctor_set_uint8(x_1895, sizeof(void*)*4, x_1894);
return x_1895;
}
}
else
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; uint8_t x_1905; lean_object* x_1906; uint8_t x_1907; lean_object* x_1908; 
x_1896 = lean_ctor_get(x_1776, 0);
x_1897 = lean_ctor_get(x_1776, 1);
x_1898 = lean_ctor_get(x_1776, 2);
x_1899 = lean_ctor_get(x_1776, 3);
x_1900 = lean_ctor_get(x_1831, 0);
x_1901 = lean_ctor_get(x_1831, 1);
x_1902 = lean_ctor_get(x_1831, 2);
x_1903 = lean_ctor_get(x_1831, 3);
lean_inc(x_1903);
lean_inc(x_1902);
lean_inc(x_1901);
lean_inc(x_1900);
lean_dec(x_1831);
x_1904 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1904, 0, x_1896);
lean_ctor_set(x_1904, 1, x_1897);
lean_ctor_set(x_1904, 2, x_1898);
lean_ctor_set(x_1904, 3, x_1899);
lean_ctor_set_uint8(x_1904, sizeof(void*)*4, x_1871);
x_1905 = 1;
lean_inc(x_1);
lean_ctor_set(x_1776, 3, x_1904);
lean_ctor_set(x_1776, 2, x_3);
lean_ctor_set(x_1776, 1, x_2);
lean_ctor_set(x_1776, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1906 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1906 = lean_box(0);
}
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1905);
lean_ctor_set(x_4, 3, x_1903);
lean_ctor_set(x_4, 2, x_1902);
lean_ctor_set(x_4, 1, x_1901);
lean_ctor_set(x_4, 0, x_1900);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1905);
x_1907 = 0;
if (lean_is_scalar(x_1906)) {
 x_1908 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1908 = x_1906;
}
lean_ctor_set(x_1908, 0, x_1776);
lean_ctor_set(x_1908, 1, x_1873);
lean_ctor_set(x_1908, 2, x_1874);
lean_ctor_set(x_1908, 3, x_4);
lean_ctor_set_uint8(x_1908, sizeof(void*)*4, x_1907);
return x_1908;
}
}
else
{
lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; uint8_t x_1919; lean_object* x_1920; lean_object* x_1921; uint8_t x_1922; lean_object* x_1923; 
x_1909 = lean_ctor_get(x_1776, 0);
x_1910 = lean_ctor_get(x_1776, 1);
x_1911 = lean_ctor_get(x_1776, 2);
x_1912 = lean_ctor_get(x_1776, 3);
lean_inc(x_1912);
lean_inc(x_1911);
lean_inc(x_1910);
lean_inc(x_1909);
lean_dec(x_1776);
x_1913 = lean_ctor_get(x_1831, 0);
lean_inc(x_1913);
x_1914 = lean_ctor_get(x_1831, 1);
lean_inc(x_1914);
x_1915 = lean_ctor_get(x_1831, 2);
lean_inc(x_1915);
x_1916 = lean_ctor_get(x_1831, 3);
lean_inc(x_1916);
if (lean_is_exclusive(x_1831)) {
 lean_ctor_release(x_1831, 0);
 lean_ctor_release(x_1831, 1);
 lean_ctor_release(x_1831, 2);
 lean_ctor_release(x_1831, 3);
 x_1917 = x_1831;
} else {
 lean_dec_ref(x_1831);
 x_1917 = lean_box(0);
}
if (lean_is_scalar(x_1917)) {
 x_1918 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1918 = x_1917;
}
lean_ctor_set(x_1918, 0, x_1909);
lean_ctor_set(x_1918, 1, x_1910);
lean_ctor_set(x_1918, 2, x_1911);
lean_ctor_set(x_1918, 3, x_1912);
lean_ctor_set_uint8(x_1918, sizeof(void*)*4, x_1871);
x_1919 = 1;
lean_inc(x_1);
x_1920 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1920, 0, x_1);
lean_ctor_set(x_1920, 1, x_2);
lean_ctor_set(x_1920, 2, x_3);
lean_ctor_set(x_1920, 3, x_1918);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1921 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1921 = lean_box(0);
}
lean_ctor_set_uint8(x_1920, sizeof(void*)*4, x_1919);
lean_ctor_set(x_4, 3, x_1916);
lean_ctor_set(x_4, 2, x_1915);
lean_ctor_set(x_4, 1, x_1914);
lean_ctor_set(x_4, 0, x_1913);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1919);
x_1922 = 0;
if (lean_is_scalar(x_1921)) {
 x_1923 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1923 = x_1921;
}
lean_ctor_set(x_1923, 0, x_1920);
lean_ctor_set(x_1923, 1, x_1873);
lean_ctor_set(x_1923, 2, x_1874);
lean_ctor_set(x_1923, 3, x_4);
lean_ctor_set_uint8(x_1923, sizeof(void*)*4, x_1922);
return x_1923;
}
}
else
{
lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; uint8_t x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; uint8_t x_1941; lean_object* x_1942; 
x_1924 = lean_ctor_get(x_4, 1);
x_1925 = lean_ctor_get(x_4, 2);
lean_inc(x_1925);
lean_inc(x_1924);
lean_dec(x_4);
x_1926 = lean_ctor_get(x_1776, 0);
lean_inc(x_1926);
x_1927 = lean_ctor_get(x_1776, 1);
lean_inc(x_1927);
x_1928 = lean_ctor_get(x_1776, 2);
lean_inc(x_1928);
x_1929 = lean_ctor_get(x_1776, 3);
lean_inc(x_1929);
if (lean_is_exclusive(x_1776)) {
 lean_ctor_release(x_1776, 0);
 lean_ctor_release(x_1776, 1);
 lean_ctor_release(x_1776, 2);
 lean_ctor_release(x_1776, 3);
 x_1930 = x_1776;
} else {
 lean_dec_ref(x_1776);
 x_1930 = lean_box(0);
}
x_1931 = lean_ctor_get(x_1831, 0);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1831, 1);
lean_inc(x_1932);
x_1933 = lean_ctor_get(x_1831, 2);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_1831, 3);
lean_inc(x_1934);
if (lean_is_exclusive(x_1831)) {
 lean_ctor_release(x_1831, 0);
 lean_ctor_release(x_1831, 1);
 lean_ctor_release(x_1831, 2);
 lean_ctor_release(x_1831, 3);
 x_1935 = x_1831;
} else {
 lean_dec_ref(x_1831);
 x_1935 = lean_box(0);
}
if (lean_is_scalar(x_1935)) {
 x_1936 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1936 = x_1935;
}
lean_ctor_set(x_1936, 0, x_1926);
lean_ctor_set(x_1936, 1, x_1927);
lean_ctor_set(x_1936, 2, x_1928);
lean_ctor_set(x_1936, 3, x_1929);
lean_ctor_set_uint8(x_1936, sizeof(void*)*4, x_1871);
x_1937 = 1;
lean_inc(x_1);
if (lean_is_scalar(x_1930)) {
 x_1938 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1938 = x_1930;
}
lean_ctor_set(x_1938, 0, x_1);
lean_ctor_set(x_1938, 1, x_2);
lean_ctor_set(x_1938, 2, x_3);
lean_ctor_set(x_1938, 3, x_1936);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1939 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1939 = lean_box(0);
}
lean_ctor_set_uint8(x_1938, sizeof(void*)*4, x_1937);
x_1940 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1940, 0, x_1931);
lean_ctor_set(x_1940, 1, x_1932);
lean_ctor_set(x_1940, 2, x_1933);
lean_ctor_set(x_1940, 3, x_1934);
lean_ctor_set_uint8(x_1940, sizeof(void*)*4, x_1937);
x_1941 = 0;
if (lean_is_scalar(x_1939)) {
 x_1942 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1942 = x_1939;
}
lean_ctor_set(x_1942, 0, x_1938);
lean_ctor_set(x_1942, 1, x_1924);
lean_ctor_set(x_1942, 2, x_1925);
lean_ctor_set(x_1942, 3, x_1940);
lean_ctor_set_uint8(x_1942, sizeof(void*)*4, x_1941);
return x_1942;
}
}
else
{
uint8_t x_1943; 
x_1943 = !lean_is_exclusive(x_4);
if (x_1943 == 0)
{
lean_object* x_1944; lean_object* x_1945; uint8_t x_1946; 
x_1944 = lean_ctor_get(x_4, 3);
lean_dec(x_1944);
x_1945 = lean_ctor_get(x_4, 0);
lean_dec(x_1945);
x_1946 = !lean_is_exclusive(x_1776);
if (x_1946 == 0)
{
lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; uint8_t x_1951; uint8_t x_1952; 
x_1947 = lean_ctor_get(x_1776, 0);
x_1948 = lean_ctor_get(x_1776, 1);
x_1949 = lean_ctor_get(x_1776, 2);
x_1950 = lean_ctor_get(x_1776, 3);
x_1951 = 1;
lean_inc(x_1);
lean_ctor_set(x_1776, 3, x_1947);
lean_ctor_set(x_1776, 2, x_3);
lean_ctor_set(x_1776, 1, x_2);
lean_ctor_set(x_1776, 0, x_1);
x_1952 = !lean_is_exclusive(x_1);
if (x_1952 == 0)
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; uint8_t x_1957; 
x_1953 = lean_ctor_get(x_1, 3);
lean_dec(x_1953);
x_1954 = lean_ctor_get(x_1, 2);
lean_dec(x_1954);
x_1955 = lean_ctor_get(x_1, 1);
lean_dec(x_1955);
x_1956 = lean_ctor_get(x_1, 0);
lean_dec(x_1956);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1951);
lean_ctor_set(x_4, 0, x_1950);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1951);
x_1957 = 0;
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_1949);
lean_ctor_set(x_1, 1, x_1948);
lean_ctor_set(x_1, 0, x_1776);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1957);
return x_1;
}
else
{
uint8_t x_1958; lean_object* x_1959; 
lean_dec(x_1);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1951);
lean_ctor_set(x_4, 0, x_1950);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1951);
x_1958 = 0;
x_1959 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1959, 0, x_1776);
lean_ctor_set(x_1959, 1, x_1948);
lean_ctor_set(x_1959, 2, x_1949);
lean_ctor_set(x_1959, 3, x_4);
lean_ctor_set_uint8(x_1959, sizeof(void*)*4, x_1958);
return x_1959;
}
}
else
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; uint8_t x_1964; lean_object* x_1965; lean_object* x_1966; uint8_t x_1967; lean_object* x_1968; 
x_1960 = lean_ctor_get(x_1776, 0);
x_1961 = lean_ctor_get(x_1776, 1);
x_1962 = lean_ctor_get(x_1776, 2);
x_1963 = lean_ctor_get(x_1776, 3);
lean_inc(x_1963);
lean_inc(x_1962);
lean_inc(x_1961);
lean_inc(x_1960);
lean_dec(x_1776);
x_1964 = 1;
lean_inc(x_1);
x_1965 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1965, 0, x_1);
lean_ctor_set(x_1965, 1, x_2);
lean_ctor_set(x_1965, 2, x_3);
lean_ctor_set(x_1965, 3, x_1960);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1966 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1966 = lean_box(0);
}
lean_ctor_set_uint8(x_1965, sizeof(void*)*4, x_1964);
lean_ctor_set(x_4, 0, x_1963);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1964);
x_1967 = 0;
if (lean_is_scalar(x_1966)) {
 x_1968 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1968 = x_1966;
}
lean_ctor_set(x_1968, 0, x_1965);
lean_ctor_set(x_1968, 1, x_1961);
lean_ctor_set(x_1968, 2, x_1962);
lean_ctor_set(x_1968, 3, x_4);
lean_ctor_set_uint8(x_1968, sizeof(void*)*4, x_1967);
return x_1968;
}
}
else
{
lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; uint8_t x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; uint8_t x_1980; lean_object* x_1981; 
x_1969 = lean_ctor_get(x_4, 1);
x_1970 = lean_ctor_get(x_4, 2);
lean_inc(x_1970);
lean_inc(x_1969);
lean_dec(x_4);
x_1971 = lean_ctor_get(x_1776, 0);
lean_inc(x_1971);
x_1972 = lean_ctor_get(x_1776, 1);
lean_inc(x_1972);
x_1973 = lean_ctor_get(x_1776, 2);
lean_inc(x_1973);
x_1974 = lean_ctor_get(x_1776, 3);
lean_inc(x_1974);
if (lean_is_exclusive(x_1776)) {
 lean_ctor_release(x_1776, 0);
 lean_ctor_release(x_1776, 1);
 lean_ctor_release(x_1776, 2);
 lean_ctor_release(x_1776, 3);
 x_1975 = x_1776;
} else {
 lean_dec_ref(x_1776);
 x_1975 = lean_box(0);
}
x_1976 = 1;
lean_inc(x_1);
if (lean_is_scalar(x_1975)) {
 x_1977 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1977 = x_1975;
}
lean_ctor_set(x_1977, 0, x_1);
lean_ctor_set(x_1977, 1, x_2);
lean_ctor_set(x_1977, 2, x_3);
lean_ctor_set(x_1977, 3, x_1971);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1978 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1978 = lean_box(0);
}
lean_ctor_set_uint8(x_1977, sizeof(void*)*4, x_1976);
x_1979 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1979, 0, x_1974);
lean_ctor_set(x_1979, 1, x_1969);
lean_ctor_set(x_1979, 2, x_1970);
lean_ctor_set(x_1979, 3, x_1831);
lean_ctor_set_uint8(x_1979, sizeof(void*)*4, x_1976);
x_1980 = 0;
if (lean_is_scalar(x_1978)) {
 x_1981 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1981 = x_1978;
}
lean_ctor_set(x_1981, 0, x_1977);
lean_ctor_set(x_1981, 1, x_1972);
lean_ctor_set(x_1981, 2, x_1973);
lean_ctor_set(x_1981, 3, x_1979);
lean_ctor_set_uint8(x_1981, sizeof(void*)*4, x_1980);
return x_1981;
}
}
}
}
else
{
lean_object* x_1982; 
x_1982 = lean_ctor_get(x_4, 3);
lean_inc(x_1982);
if (lean_obj_tag(x_1982) == 0)
{
uint8_t x_1983; 
x_1983 = !lean_is_exclusive(x_1776);
if (x_1983 == 0)
{
lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; uint8_t x_1988; 
x_1984 = lean_ctor_get(x_1776, 3);
lean_dec(x_1984);
x_1985 = lean_ctor_get(x_1776, 2);
lean_dec(x_1985);
x_1986 = lean_ctor_get(x_1776, 1);
lean_dec(x_1986);
x_1987 = lean_ctor_get(x_1776, 0);
lean_dec(x_1987);
x_1988 = 1;
lean_ctor_set(x_1776, 3, x_4);
lean_ctor_set(x_1776, 2, x_3);
lean_ctor_set(x_1776, 1, x_2);
lean_ctor_set(x_1776, 0, x_1);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_1988);
return x_1776;
}
else
{
uint8_t x_1989; lean_object* x_1990; 
lean_dec(x_1776);
x_1989 = 1;
x_1990 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1990, 0, x_1);
lean_ctor_set(x_1990, 1, x_2);
lean_ctor_set(x_1990, 2, x_3);
lean_ctor_set(x_1990, 3, x_4);
lean_ctor_set_uint8(x_1990, sizeof(void*)*4, x_1989);
return x_1990;
}
}
else
{
uint8_t x_1991; 
x_1991 = lean_ctor_get_uint8(x_1982, sizeof(void*)*4);
if (x_1991 == 0)
{
uint8_t x_1992; 
x_1992 = !lean_is_exclusive(x_4);
if (x_1992 == 0)
{
lean_object* x_1993; lean_object* x_1994; uint8_t x_1995; 
x_1993 = lean_ctor_get(x_4, 3);
lean_dec(x_1993);
x_1994 = lean_ctor_get(x_4, 0);
lean_dec(x_1994);
x_1995 = !lean_is_exclusive(x_1982);
if (x_1995 == 0)
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; uint8_t x_2000; uint8_t x_2001; 
x_1996 = lean_ctor_get(x_1982, 0);
x_1997 = lean_ctor_get(x_1982, 1);
x_1998 = lean_ctor_get(x_1982, 2);
x_1999 = lean_ctor_get(x_1982, 3);
x_2000 = 1;
lean_inc(x_1776);
lean_ctor_set(x_1982, 3, x_1776);
lean_ctor_set(x_1982, 2, x_3);
lean_ctor_set(x_1982, 1, x_2);
lean_ctor_set(x_1982, 0, x_1);
x_2001 = !lean_is_exclusive(x_1776);
if (x_2001 == 0)
{
lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; uint8_t x_2006; 
x_2002 = lean_ctor_get(x_1776, 3);
lean_dec(x_2002);
x_2003 = lean_ctor_get(x_1776, 2);
lean_dec(x_2003);
x_2004 = lean_ctor_get(x_1776, 1);
lean_dec(x_2004);
x_2005 = lean_ctor_get(x_1776, 0);
lean_dec(x_2005);
lean_ctor_set_uint8(x_1982, sizeof(void*)*4, x_2000);
lean_ctor_set(x_1776, 3, x_1999);
lean_ctor_set(x_1776, 2, x_1998);
lean_ctor_set(x_1776, 1, x_1997);
lean_ctor_set(x_1776, 0, x_1996);
lean_ctor_set_uint8(x_1776, sizeof(void*)*4, x_2000);
x_2006 = 0;
lean_ctor_set(x_4, 3, x_1776);
lean_ctor_set(x_4, 0, x_1982);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2006);
return x_4;
}
else
{
lean_object* x_2007; uint8_t x_2008; 
lean_dec(x_1776);
lean_ctor_set_uint8(x_1982, sizeof(void*)*4, x_2000);
x_2007 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2007, 0, x_1996);
lean_ctor_set(x_2007, 1, x_1997);
lean_ctor_set(x_2007, 2, x_1998);
lean_ctor_set(x_2007, 3, x_1999);
lean_ctor_set_uint8(x_2007, sizeof(void*)*4, x_2000);
x_2008 = 0;
lean_ctor_set(x_4, 3, x_2007);
lean_ctor_set(x_4, 0, x_1982);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2008);
return x_4;
}
}
else
{
lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; uint8_t x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; uint8_t x_2017; 
x_2009 = lean_ctor_get(x_1982, 0);
x_2010 = lean_ctor_get(x_1982, 1);
x_2011 = lean_ctor_get(x_1982, 2);
x_2012 = lean_ctor_get(x_1982, 3);
lean_inc(x_2012);
lean_inc(x_2011);
lean_inc(x_2010);
lean_inc(x_2009);
lean_dec(x_1982);
x_2013 = 1;
lean_inc(x_1776);
x_2014 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2014, 0, x_1);
lean_ctor_set(x_2014, 1, x_2);
lean_ctor_set(x_2014, 2, x_3);
lean_ctor_set(x_2014, 3, x_1776);
if (lean_is_exclusive(x_1776)) {
 lean_ctor_release(x_1776, 0);
 lean_ctor_release(x_1776, 1);
 lean_ctor_release(x_1776, 2);
 lean_ctor_release(x_1776, 3);
 x_2015 = x_1776;
} else {
 lean_dec_ref(x_1776);
 x_2015 = lean_box(0);
}
lean_ctor_set_uint8(x_2014, sizeof(void*)*4, x_2013);
if (lean_is_scalar(x_2015)) {
 x_2016 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2016 = x_2015;
}
lean_ctor_set(x_2016, 0, x_2009);
lean_ctor_set(x_2016, 1, x_2010);
lean_ctor_set(x_2016, 2, x_2011);
lean_ctor_set(x_2016, 3, x_2012);
lean_ctor_set_uint8(x_2016, sizeof(void*)*4, x_2013);
x_2017 = 0;
lean_ctor_set(x_4, 3, x_2016);
lean_ctor_set(x_4, 0, x_2014);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2017);
return x_4;
}
}
else
{
lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; uint8_t x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; uint8_t x_2029; lean_object* x_2030; 
x_2018 = lean_ctor_get(x_4, 1);
x_2019 = lean_ctor_get(x_4, 2);
lean_inc(x_2019);
lean_inc(x_2018);
lean_dec(x_4);
x_2020 = lean_ctor_get(x_1982, 0);
lean_inc(x_2020);
x_2021 = lean_ctor_get(x_1982, 1);
lean_inc(x_2021);
x_2022 = lean_ctor_get(x_1982, 2);
lean_inc(x_2022);
x_2023 = lean_ctor_get(x_1982, 3);
lean_inc(x_2023);
if (lean_is_exclusive(x_1982)) {
 lean_ctor_release(x_1982, 0);
 lean_ctor_release(x_1982, 1);
 lean_ctor_release(x_1982, 2);
 lean_ctor_release(x_1982, 3);
 x_2024 = x_1982;
} else {
 lean_dec_ref(x_1982);
 x_2024 = lean_box(0);
}
x_2025 = 1;
lean_inc(x_1776);
if (lean_is_scalar(x_2024)) {
 x_2026 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2026 = x_2024;
}
lean_ctor_set(x_2026, 0, x_1);
lean_ctor_set(x_2026, 1, x_2);
lean_ctor_set(x_2026, 2, x_3);
lean_ctor_set(x_2026, 3, x_1776);
if (lean_is_exclusive(x_1776)) {
 lean_ctor_release(x_1776, 0);
 lean_ctor_release(x_1776, 1);
 lean_ctor_release(x_1776, 2);
 lean_ctor_release(x_1776, 3);
 x_2027 = x_1776;
} else {
 lean_dec_ref(x_1776);
 x_2027 = lean_box(0);
}
lean_ctor_set_uint8(x_2026, sizeof(void*)*4, x_2025);
if (lean_is_scalar(x_2027)) {
 x_2028 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2028 = x_2027;
}
lean_ctor_set(x_2028, 0, x_2020);
lean_ctor_set(x_2028, 1, x_2021);
lean_ctor_set(x_2028, 2, x_2022);
lean_ctor_set(x_2028, 3, x_2023);
lean_ctor_set_uint8(x_2028, sizeof(void*)*4, x_2025);
x_2029 = 0;
x_2030 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2030, 0, x_2026);
lean_ctor_set(x_2030, 1, x_2018);
lean_ctor_set(x_2030, 2, x_2019);
lean_ctor_set(x_2030, 3, x_2028);
lean_ctor_set_uint8(x_2030, sizeof(void*)*4, x_2029);
return x_2030;
}
}
else
{
uint8_t x_2031; 
lean_dec(x_1776);
x_2031 = !lean_is_exclusive(x_1982);
if (x_2031 == 0)
{
lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; uint8_t x_2036; 
x_2032 = lean_ctor_get(x_1982, 3);
lean_dec(x_2032);
x_2033 = lean_ctor_get(x_1982, 2);
lean_dec(x_2033);
x_2034 = lean_ctor_get(x_1982, 1);
lean_dec(x_2034);
x_2035 = lean_ctor_get(x_1982, 0);
lean_dec(x_2035);
x_2036 = 1;
lean_ctor_set(x_1982, 3, x_4);
lean_ctor_set(x_1982, 2, x_3);
lean_ctor_set(x_1982, 1, x_2);
lean_ctor_set(x_1982, 0, x_1);
lean_ctor_set_uint8(x_1982, sizeof(void*)*4, x_2036);
return x_1982;
}
else
{
uint8_t x_2037; lean_object* x_2038; 
lean_dec(x_1982);
x_2037 = 1;
x_2038 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2038, 0, x_1);
lean_ctor_set(x_2038, 1, x_2);
lean_ctor_set(x_2038, 2, x_3);
lean_ctor_set(x_2038, 3, x_4);
lean_ctor_set_uint8(x_2038, sizeof(void*)*4, x_2037);
return x_2038;
}
}
}
}
}
}
else
{
uint8_t x_2039; lean_object* x_2040; 
x_2039 = 1;
x_2040 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2040, 0, x_1);
lean_ctor_set(x_2040, 1, x_2);
lean_ctor_set(x_2040, 2, x_3);
lean_ctor_set(x_2040, 3, x_4);
lean_ctor_set_uint8(x_2040, sizeof(void*)*4, x_2039);
return x_2040;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balance_u2083(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_balance_u2083___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_setRed___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_setRed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_setRed___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balLeft___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
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
x_33 = l_Std_RBNode_setRed___rarg(x_25);
x_34 = l_Std_RBNode_balance_u2083___rarg(x_31, x_23, x_24, x_33);
x_35 = 0;
lean_ctor_set(x_4, 3, x_34);
lean_ctor_set(x_4, 2, x_30);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_35);
return x_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
x_38 = lean_ctor_get(x_8, 2);
x_39 = lean_ctor_get(x_8, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_40 = 1;
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
x_42 = l_Std_RBNode_setRed___rarg(x_25);
x_43 = l_Std_RBNode_balance_u2083___rarg(x_39, x_23, x_24, x_42);
x_44 = 0;
lean_ctor_set(x_4, 3, x_43);
lean_ctor_set(x_4, 2, x_38);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_41);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_44);
return x_4;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_4, 1);
x_46 = lean_ctor_get(x_4, 2);
x_47 = lean_ctor_get(x_4, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_48 = lean_ctor_get(x_8, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_8, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 3);
lean_inc(x_51);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_52 = x_8;
} else {
 lean_dec_ref(x_8);
 x_52 = lean_box(0);
}
x_53 = 1;
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 4, 1);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = l_Std_RBNode_setRed___rarg(x_47);
x_56 = l_Std_RBNode_balance_u2083___rarg(x_51, x_45, x_46, x_55);
x_57 = 0;
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; 
x_60 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_60);
x_61 = l_Std_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_4, 0);
x_63 = lean_ctor_get(x_4, 1);
x_64 = lean_ctor_get(x_4, 2);
x_65 = lean_ctor_get(x_4, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_4);
x_66 = 0;
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = l_Std_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_69 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_1);
if (x_70 == 0)
{
uint8_t x_71; uint8_t x_72; lean_object* x_73; 
x_71 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_71);
x_72 = 0;
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set(x_73, 3, x_4);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get(x_1, 1);
x_76 = lean_ctor_get(x_1, 2);
x_77 = lean_ctor_get(x_1, 3);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_1);
x_78 = 1;
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
x_80 = 0;
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_3);
lean_ctor_set(x_81, 3, x_4);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_4, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_1);
if (x_84 == 0)
{
uint8_t x_85; uint8_t x_86; lean_object* x_87; 
x_85 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_85);
x_86 = 0;
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_3);
lean_ctor_set(x_87, 3, x_4);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
x_90 = lean_ctor_get(x_1, 2);
x_91 = lean_ctor_get(x_1, 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_1);
x_92 = 1;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 0;
x_95 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_2);
lean_ctor_set(x_95, 2, x_3);
lean_ctor_set(x_95, 3, x_4);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_94);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = lean_ctor_get_uint8(x_83, sizeof(void*)*4);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_1);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_4);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_4, 0);
lean_dec(x_99);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_96);
x_100 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_100);
x_101 = 0;
x_102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_2);
lean_ctor_set(x_102, 2, x_3);
lean_ctor_set(x_102, 3, x_4);
lean_ctor_set_uint8(x_102, sizeof(void*)*4, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_4, 1);
x_104 = lean_ctor_get(x_4, 2);
x_105 = lean_ctor_get(x_4, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_4);
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_83);
lean_ctor_set(x_106, 1, x_103);
lean_ctor_set(x_106, 2, x_104);
lean_ctor_set(x_106, 3, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_96);
x_107 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_107);
x_108 = 0;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_2);
lean_ctor_set(x_109, 2, x_3);
lean_ctor_set(x_109, 3, x_106);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_110 = lean_ctor_get(x_1, 0);
x_111 = lean_ctor_get(x_1, 1);
x_112 = lean_ctor_get(x_1, 2);
x_113 = lean_ctor_get(x_1, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_1);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_117 = x_4;
} else {
 lean_dec_ref(x_4);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 4, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_83);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_96);
x_119 = 1;
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_111);
lean_ctor_set(x_120, 2, x_112);
lean_ctor_set(x_120, 3, x_113);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = 0;
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_2);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set(x_122, 3, x_118);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_121);
return x_122;
}
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_83);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = lean_ctor_get(x_83, 3);
lean_dec(x_124);
x_125 = lean_ctor_get(x_83, 2);
lean_dec(x_125);
x_126 = lean_ctor_get(x_83, 1);
lean_dec(x_126);
x_127 = lean_ctor_get(x_83, 0);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_1);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; 
x_129 = lean_ctor_get(x_1, 0);
x_130 = lean_ctor_get(x_1, 1);
x_131 = lean_ctor_get(x_1, 2);
x_132 = lean_ctor_get(x_1, 3);
x_133 = 1;
lean_ctor_set(x_83, 3, x_132);
lean_ctor_set(x_83, 2, x_131);
lean_ctor_set(x_83, 1, x_130);
lean_ctor_set(x_83, 0, x_129);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_133);
x_134 = 0;
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_134);
return x_1;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_1, 0);
x_136 = lean_ctor_get(x_1, 1);
x_137 = lean_ctor_get(x_1, 2);
x_138 = lean_ctor_get(x_1, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_1);
x_139 = 1;
lean_ctor_set(x_83, 3, x_138);
lean_ctor_set(x_83, 2, x_137);
lean_ctor_set(x_83, 1, x_136);
lean_ctor_set(x_83, 0, x_135);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_139);
x_140 = 0;
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_83);
lean_ctor_set(x_141, 1, x_2);
lean_ctor_set(x_141, 2, x_3);
lean_ctor_set(x_141, 3, x_4);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_140);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
lean_dec(x_83);
x_142 = lean_ctor_get(x_1, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_1, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 3);
lean_inc(x_145);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_146 = x_1;
} else {
 lean_dec_ref(x_1);
 x_146 = lean_box(0);
}
x_147 = 1;
x_148 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_147);
x_149 = 0;
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(1, 4, 1);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_2);
lean_ctor_set(x_150, 2, x_3);
lean_ctor_set(x_150, 3, x_4);
lean_ctor_set_uint8(x_150, sizeof(void*)*4, x_149);
return x_150;
}
}
}
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_1);
if (x_151 == 0)
{
uint8_t x_152; uint8_t x_153; lean_object* x_154; 
x_152 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_152);
x_153 = 0;
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_1);
lean_ctor_set(x_154, 1, x_2);
lean_ctor_set(x_154, 2, x_3);
lean_ctor_set(x_154, 3, x_4);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_153);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_1, 0);
x_156 = lean_ctor_get(x_1, 1);
x_157 = lean_ctor_get(x_1, 2);
x_158 = lean_ctor_get(x_1, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_1);
x_159 = 1;
x_160 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_159);
x_161 = 0;
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_2);
lean_ctor_set(x_162, 2, x_3);
lean_ctor_set(x_162, 3, x_4);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
return x_162;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_163; lean_object* x_164; 
x_163 = 0;
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_2);
lean_ctor_set(x_164, 2, x_3);
lean_ctor_set(x_164, 3, x_4);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_163);
return x_164;
}
else
{
uint8_t x_165; 
x_165 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_165 == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_4, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; lean_object* x_168; 
x_167 = 0;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_3);
lean_ctor_set(x_168, 3, x_4);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
else
{
uint8_t x_169; 
x_169 = lean_ctor_get_uint8(x_166, sizeof(void*)*4);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_4);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_4, 0);
lean_dec(x_171);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_169);
x_172 = 0;
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_2);
lean_ctor_set(x_173, 2, x_3);
lean_ctor_set(x_173, 3, x_4);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_4, 1);
x_175 = lean_ctor_get(x_4, 2);
x_176 = lean_ctor_get(x_4, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_4);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_169);
x_178 = 0;
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_2);
lean_ctor_set(x_179, 2, x_3);
lean_ctor_set(x_179, 3, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_178);
return x_179;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_1);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_4);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_182 = lean_ctor_get(x_1, 0);
x_183 = lean_ctor_get(x_1, 1);
x_184 = lean_ctor_get(x_1, 2);
x_185 = lean_ctor_get(x_1, 3);
x_186 = lean_ctor_get(x_4, 1);
x_187 = lean_ctor_get(x_4, 2);
x_188 = lean_ctor_get(x_4, 3);
x_189 = lean_ctor_get(x_4, 0);
lean_dec(x_189);
x_190 = !lean_is_exclusive(x_166);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_191 = lean_ctor_get(x_166, 0);
x_192 = lean_ctor_get(x_166, 1);
x_193 = lean_ctor_get(x_166, 2);
x_194 = lean_ctor_get(x_166, 3);
lean_ctor_set(x_166, 3, x_185);
lean_ctor_set(x_166, 2, x_184);
lean_ctor_set(x_166, 1, x_183);
lean_ctor_set(x_166, 0, x_182);
x_195 = 1;
lean_ctor_set(x_4, 3, x_191);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_195);
x_196 = l_Std_RBNode_setRed___rarg(x_188);
x_197 = l_Std_RBNode_balance_u2083___rarg(x_194, x_186, x_187, x_196);
x_198 = 0;
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_193);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_199 = lean_ctor_get(x_166, 0);
x_200 = lean_ctor_get(x_166, 1);
x_201 = lean_ctor_get(x_166, 2);
x_202 = lean_ctor_get(x_166, 3);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_166);
x_203 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_183);
lean_ctor_set(x_203, 2, x_184);
lean_ctor_set(x_203, 3, x_185);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_169);
x_204 = 1;
lean_ctor_set(x_4, 3, x_199);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_203);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_204);
x_205 = l_Std_RBNode_setRed___rarg(x_188);
x_206 = l_Std_RBNode_balance_u2083___rarg(x_202, x_186, x_187, x_205);
x_207 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_201);
lean_ctor_set(x_1, 1, x_200);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_208 = lean_ctor_get(x_1, 0);
x_209 = lean_ctor_get(x_1, 1);
x_210 = lean_ctor_get(x_1, 2);
x_211 = lean_ctor_get(x_1, 3);
x_212 = lean_ctor_get(x_4, 1);
x_213 = lean_ctor_get(x_4, 2);
x_214 = lean_ctor_get(x_4, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_4);
x_215 = lean_ctor_get(x_166, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_166, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_166, 2);
lean_inc(x_217);
x_218 = lean_ctor_get(x_166, 3);
lean_inc(x_218);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_219 = x_166;
} else {
 lean_dec_ref(x_166);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 4, 1);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_208);
lean_ctor_set(x_220, 1, x_209);
lean_ctor_set(x_220, 2, x_210);
lean_ctor_set(x_220, 3, x_211);
lean_ctor_set_uint8(x_220, sizeof(void*)*4, x_169);
x_221 = 1;
x_222 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_2);
lean_ctor_set(x_222, 2, x_3);
lean_ctor_set(x_222, 3, x_215);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_221);
x_223 = l_Std_RBNode_setRed___rarg(x_214);
x_224 = l_Std_RBNode_balance_u2083___rarg(x_218, x_212, x_213, x_223);
x_225 = 0;
lean_ctor_set(x_1, 3, x_224);
lean_ctor_set(x_1, 2, x_217);
lean_ctor_set(x_1, 1, x_216);
lean_ctor_set(x_1, 0, x_222);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_225);
return x_1;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_226 = lean_ctor_get(x_1, 0);
x_227 = lean_ctor_get(x_1, 1);
x_228 = lean_ctor_get(x_1, 2);
x_229 = lean_ctor_get(x_1, 3);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_1);
x_230 = lean_ctor_get(x_4, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_4, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_4, 3);
lean_inc(x_232);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_233 = x_4;
} else {
 lean_dec_ref(x_4);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_166, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_166, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_166, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_166, 3);
lean_inc(x_237);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_238 = x_166;
} else {
 lean_dec_ref(x_166);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 4, 1);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_226);
lean_ctor_set(x_239, 1, x_227);
lean_ctor_set(x_239, 2, x_228);
lean_ctor_set(x_239, 3, x_229);
lean_ctor_set_uint8(x_239, sizeof(void*)*4, x_169);
x_240 = 1;
if (lean_is_scalar(x_233)) {
 x_241 = lean_alloc_ctor(1, 4, 1);
} else {
 x_241 = x_233;
}
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_2);
lean_ctor_set(x_241, 2, x_3);
lean_ctor_set(x_241, 3, x_234);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
x_242 = l_Std_RBNode_setRed___rarg(x_232);
x_243 = l_Std_RBNode_balance_u2083___rarg(x_237, x_230, x_231, x_242);
x_244 = 0;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_241);
lean_ctor_set(x_245, 1, x_235);
lean_ctor_set(x_245, 2, x_236);
lean_ctor_set(x_245, 3, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
return x_245;
}
}
}
}
else
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_1);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_4);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; 
x_248 = lean_ctor_get(x_1, 0);
x_249 = lean_ctor_get(x_1, 1);
x_250 = lean_ctor_get(x_1, 2);
x_251 = lean_ctor_get(x_1, 3);
x_252 = lean_ctor_get(x_4, 0);
x_253 = lean_ctor_get(x_4, 1);
x_254 = lean_ctor_get(x_4, 2);
x_255 = lean_ctor_get(x_4, 3);
lean_ctor_set(x_4, 3, x_251);
lean_ctor_set(x_4, 2, x_250);
lean_ctor_set(x_4, 1, x_249);
lean_ctor_set(x_4, 0, x_248);
x_256 = 0;
lean_ctor_set(x_1, 3, x_255);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_252);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_256);
x_257 = l_Std_RBNode_balance_u2083___rarg(x_4, x_2, x_3, x_1);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_258 = lean_ctor_get(x_1, 0);
x_259 = lean_ctor_get(x_1, 1);
x_260 = lean_ctor_get(x_1, 2);
x_261 = lean_ctor_get(x_1, 3);
x_262 = lean_ctor_get(x_4, 0);
x_263 = lean_ctor_get(x_4, 1);
x_264 = lean_ctor_get(x_4, 2);
x_265 = lean_ctor_get(x_4, 3);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_4);
x_266 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_266, 0, x_258);
lean_ctor_set(x_266, 1, x_259);
lean_ctor_set(x_266, 2, x_260);
lean_ctor_set(x_266, 3, x_261);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_165);
x_267 = 0;
lean_ctor_set(x_1, 3, x_265);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_262);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
x_268 = l_Std_RBNode_balance_u2083___rarg(x_266, x_2, x_3, x_1);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; 
x_269 = lean_ctor_get(x_1, 0);
x_270 = lean_ctor_get(x_1, 1);
x_271 = lean_ctor_get(x_1, 2);
x_272 = lean_ctor_get(x_1, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_1);
x_273 = lean_ctor_get(x_4, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_4, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_4, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_4, 3);
lean_inc(x_276);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_277 = x_4;
} else {
 lean_dec_ref(x_4);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 4, 1);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_269);
lean_ctor_set(x_278, 1, x_270);
lean_ctor_set(x_278, 2, x_271);
lean_ctor_set(x_278, 3, x_272);
lean_ctor_set_uint8(x_278, sizeof(void*)*4, x_165);
x_279 = 0;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_273);
lean_ctor_set(x_280, 1, x_274);
lean_ctor_set(x_280, 2, x_275);
lean_ctor_set(x_280, 3, x_276);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
x_281 = l_Std_RBNode_balance_u2083___rarg(x_278, x_2, x_3, x_280);
return x_281;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_balLeft___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balRight___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
x_28 = lean_ctor_get(x_8, 2);
x_29 = lean_ctor_get(x_8, 3);
x_30 = l_Std_RBNode_setRed___rarg(x_21);
x_31 = l_Std_RBNode_balance_u2083___rarg(x_30, x_22, x_23, x_26);
x_32 = 1;
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_29);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_32);
x_33 = 0;
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_31);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_33);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
x_36 = lean_ctor_get(x_8, 2);
x_37 = lean_ctor_get(x_8, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_38 = l_Std_RBNode_setRed___rarg(x_21);
x_39 = l_Std_RBNode_balance_u2083___rarg(x_38, x_22, x_23, x_34);
x_40 = 1;
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_41, 3, x_4);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_40);
x_42 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_36);
lean_ctor_set(x_1, 1, x_35);
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_42);
return x_1;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_1);
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_8, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 3);
lean_inc(x_49);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_50 = x_8;
} else {
 lean_dec_ref(x_8);
 x_50 = lean_box(0);
}
x_51 = l_Std_RBNode_setRed___rarg(x_43);
x_52 = l_Std_RBNode_balance_u2083___rarg(x_51, x_44, x_45, x_46);
x_53 = 1;
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(1, 4, 1);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_4);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set(x_56, 3, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
uint8_t x_58; lean_object* x_59; 
x_58 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
x_59 = l_Std_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 1);
x_62 = lean_ctor_get(x_1, 2);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_1);
x_64 = 0;
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_64);
x_66 = l_Std_RBNode_balance_u2083___rarg(x_65, x_2, x_3, x_4);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
x_67 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_4);
if (x_68 == 0)
{
uint8_t x_69; uint8_t x_70; lean_object* x_71; 
x_69 = 1;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_69);
x_70 = 0;
x_71 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
lean_ctor_set(x_71, 2, x_3);
lean_ctor_set(x_71, 3, x_4);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_4, 0);
x_73 = lean_ctor_get(x_4, 1);
x_74 = lean_ctor_get(x_4, 2);
x_75 = lean_ctor_get(x_4, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_4);
x_76 = 1;
x_77 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_76);
x_78 = 0;
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_2);
lean_ctor_set(x_79, 2, x_3);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
return x_79;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_80; lean_object* x_81; 
x_80 = 0;
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_3);
lean_ctor_set(x_81, 3, x_4);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_1, 3);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; lean_object* x_85; 
x_84 = 0;
x_85 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_2);
lean_ctor_set(x_85, 2, x_3);
lean_ctor_set(x_85, 3, x_4);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_83, sizeof(void*)*4);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_83, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_83, 2);
lean_dec(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_83, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set(x_83, 3, x_4);
lean_ctor_set(x_83, 2, x_3);
lean_ctor_set(x_83, 1, x_2);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_92);
return x_83;
}
else
{
uint8_t x_93; lean_object* x_94; 
lean_dec(x_83);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_3);
lean_ctor_set(x_94, 3, x_4);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_1);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_1, 0);
x_97 = lean_ctor_get(x_1, 1);
x_98 = lean_ctor_get(x_1, 2);
x_99 = lean_ctor_get(x_1, 3);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_83);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_101 = lean_ctor_get(x_83, 0);
x_102 = lean_ctor_get(x_83, 1);
x_103 = lean_ctor_get(x_83, 2);
x_104 = lean_ctor_get(x_83, 3);
x_105 = l_Std_RBNode_setRed___rarg(x_96);
x_106 = l_Std_RBNode_balance_u2083___rarg(x_105, x_97, x_98, x_101);
x_107 = 1;
lean_ctor_set(x_83, 3, x_4);
lean_ctor_set(x_83, 2, x_3);
lean_ctor_set(x_83, 1, x_2);
lean_ctor_set(x_83, 0, x_104);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_106);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; uint8_t x_117; 
x_109 = lean_ctor_get(x_83, 0);
x_110 = lean_ctor_get(x_83, 1);
x_111 = lean_ctor_get(x_83, 2);
x_112 = lean_ctor_get(x_83, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_83);
x_113 = l_Std_RBNode_setRed___rarg(x_96);
x_114 = l_Std_RBNode_balance_u2083___rarg(x_113, x_97, x_98, x_109);
x_115 = 1;
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_2);
lean_ctor_set(x_116, 2, x_3);
lean_ctor_set(x_116, 3, x_4);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
x_117 = 0;
lean_ctor_set(x_1, 3, x_116);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_117);
return x_1;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; 
x_118 = lean_ctor_get(x_1, 0);
x_119 = lean_ctor_get(x_1, 1);
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_1);
x_121 = lean_ctor_get(x_83, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_83, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_83, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_83, 3);
lean_inc(x_124);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 x_125 = x_83;
} else {
 lean_dec_ref(x_83);
 x_125 = lean_box(0);
}
x_126 = l_Std_RBNode_setRed___rarg(x_118);
x_127 = l_Std_RBNode_balance_u2083___rarg(x_126, x_119, x_120, x_121);
x_128 = 1;
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 2, x_3);
lean_ctor_set(x_129, 3, x_4);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
x_130 = 0;
x_131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_1);
if (x_132 == 0)
{
uint8_t x_133; lean_object* x_134; 
x_133 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
x_134 = l_Std_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_1, 0);
x_136 = lean_ctor_get(x_1, 1);
x_137 = lean_ctor_get(x_1, 2);
x_138 = lean_ctor_get(x_1, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_1);
x_139 = 0;
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_136);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_139);
x_141 = l_Std_RBNode_balance_u2083___rarg(x_140, x_2, x_3, x_4);
return x_141;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_balRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_balRight___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_appendTrees___rarg(lean_object* x_1, lean_object* x_2) {
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
x_12 = l_Std_RBNode_appendTrees___rarg(x_10, x_11);
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
x_36 = l_Std_RBNode_appendTrees___rarg(x_31, x_32);
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
x_59 = l_Std_RBNode_appendTrees___rarg(x_53, x_54);
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
x_80 = l_Std_RBNode_appendTrees___rarg(x_79, x_2);
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
x_92 = l_Std_RBNode_appendTrees___rarg(x_1, x_91);
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
x_98 = l_Std_RBNode_appendTrees___rarg(x_1, x_94);
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
x_108 = l_Std_RBNode_appendTrees___rarg(x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; lean_object* x_110; 
lean_free_object(x_1);
x_109 = 1;
lean_ctor_set(x_2, 0, x_108);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_109);
x_110 = l_Std_RBNode_balLeft___rarg(x_103, x_104, x_105, x_2);
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
x_127 = l_Std_RBNode_balLeft___rarg(x_103, x_104, x_105, x_2);
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
x_136 = l_Std_RBNode_appendTrees___rarg(x_131, x_132);
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
x_139 = l_Std_RBNode_balLeft___rarg(x_128, x_129, x_130, x_138);
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
x_152 = l_Std_RBNode_balLeft___rarg(x_128, x_129, x_130, x_151);
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
x_162 = l_Std_RBNode_appendTrees___rarg(x_156, x_157);
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
x_165 = l_Std_RBNode_balLeft___rarg(x_153, x_154, x_155, x_164);
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
x_179 = l_Std_RBNode_balLeft___rarg(x_153, x_154, x_155, x_178);
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
LEAN_EXPORT lean_object* l_Std_RBNode_appendTrees(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_appendTrees___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Std_RBNode_isBlack___rarg(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Std_RBNode_del___rarg(x_1, x_2, x_6);
x_14 = 0;
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_3);
x_15 = l_Std_RBNode_del___rarg(x_1, x_2, x_6);
x_16 = l_Std_RBNode_balLeft___rarg(x_15, x_7, x_8, x_9);
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
x_17 = l_Std_RBNode_appendTrees___rarg(x_6, x_9);
return x_17;
}
default: 
{
uint8_t x_18; 
x_18 = l_Std_RBNode_isBlack___rarg(x_9);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Std_RBNode_del___rarg(x_1, x_2, x_9);
x_20 = 0;
lean_ctor_set(x_3, 3, x_19);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_20);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_3);
x_21 = l_Std_RBNode_del___rarg(x_1, x_2, x_9);
x_22 = l_Std_RBNode_balRight___rarg(x_6, x_7, x_8, x_21);
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
x_29 = l_Std_RBNode_isBlack___rarg(x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Std_RBNode_del___rarg(x_1, x_2, x_23);
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
x_33 = l_Std_RBNode_del___rarg(x_1, x_2, x_23);
x_34 = l_Std_RBNode_balLeft___rarg(x_33, x_24, x_25, x_26);
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
x_35 = l_Std_RBNode_appendTrees___rarg(x_23, x_26);
return x_35;
}
default: 
{
uint8_t x_36; 
x_36 = l_Std_RBNode_isBlack___rarg(x_26);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = l_Std_RBNode_del___rarg(x_1, x_2, x_26);
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
x_40 = l_Std_RBNode_del___rarg(x_1, x_2, x_26);
x_41 = l_Std_RBNode_balRight___rarg(x_23, x_24, x_25, x_40);
return x_41;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_del___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_RBNode_del___rarg(x_1, x_2, x_3);
x_5 = l_Std_RBNode_setBlack___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_erase___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_findCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_findCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_findCore___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_find(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_RBNode_find___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_lowerBound___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_lowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_lowerBound___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_mkRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_mkRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_mkRBMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_empty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_instEmptyCollectionRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_instEmptyCollectionRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_instEmptyCollectionRBMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_depth___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_depth___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_depth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_depth___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBMap_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_depth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_depth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_fold___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBMap_fold___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBMap_fold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_revFold___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBMap_revFold___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBMap_revFold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_RBMap_foldM___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBMap_foldM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__2___boxed), 7, 6);
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
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBMap_forM___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_RBNode_foldM___at_Std_RBMap_forM___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBMap_forM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_5);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg(x_1, x_2, x_9, x_4);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg___lambda__2), 7, 6);
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
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_forIn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Std_RBNode_forIn_visit___at_Std_RBMap_forIn___spec__1___rarg(x_1, x_4, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Std_RBNode_forIn___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_forIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_RBMap_forIn___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_forIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBMap_forIn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_5);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg(x_1, x_2, x_9, x_4);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg___lambda__2), 7, 6);
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
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Std_RBNode_forIn_visit___at_Std_RBMap_instForInRBMapProd___spec__1___rarg(x_1, x_4, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Std_RBMap_instForInRBMapProd___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_RBMap_instForInRBMapProd___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instForInRBMapProd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBMap_instForInRBMapProd(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_RBMap_isEmpty___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_isEmpty___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_RBMap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_isEmpty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_toList___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Std_RBMap_toList___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_RBMap_toList___rarg___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Std_RBMap_toList___rarg___closed__1;
x_4 = l_Std_RBNode_revFold___rarg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_toList___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_toList(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBNode_min___rarg(x_1);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_min___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBMap_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_min(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBNode_max___rarg(x_1);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_max___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBMap_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_max(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_apply_2(x_1, x_4, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_2, x_5, x_6);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_reverse___rarg(x_11);
x_13 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3;
x_14 = l_Std_Format_joinSep___at_instReprProd___spec__1(x_12, x_13);
lean_dec(x_12);
x_15 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__7;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__9;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__6;
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = 0;
x_22 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_repr___at_Std_RBMap_instReprRBMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg(x_1, x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg(x_1, x_2, x_9);
lean_inc(x_4);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2___rarg(x_1, x_2, x_6, x_4);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.rbmapOf ");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__2;
x_2 = l_Std_RBMap_instReprRBMap___rarg___closed__4;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__6;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__7;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_instReprRBMap___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_RBMap_instReprRBMap___rarg___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBMap_toList___rarg(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Std_RBMap_instReprRBMap___rarg___closed__5;
x_7 = l_Repr_addAppParen(x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3;
x_9 = l_Std_Format_joinSep___at_Std_RBMap_instReprRBMap___spec__2___rarg(x_1, x_2, x_5, x_8);
x_10 = l_Std_RBMap_instReprRBMap___rarg___closed__9;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Std_RBMap_instReprRBMap___rarg___closed__11;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_RBMap_instReprRBMap___rarg___closed__8;
x_15 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = 0;
x_17 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = l_Std_RBMap_instReprRBMap___rarg___closed__2;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Repr_addAppParen(x_19, x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_instReprRBMap___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBMap_instReprRBMap___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_instReprRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_instReprRBMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_insert___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_erase___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_erase___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_ofList___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Std_RBMap_ofList___rarg(x_1, x_5);
x_9 = l_Std_RBNode_insert___rarg(x_1, x_8, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_ofList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_ofList___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_findCore_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_findCore___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_findCore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_findCore_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_find_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_RBMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_findD___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBMap_findD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_lowerBound___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_RBNode_lowerBound___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_lowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_lowerBound___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_RBMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_RBMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_contains___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_RBMap_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_RBMap_fromList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Std_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_RBMap_fromList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___at_Std_RBMap_fromList___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_fromList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at_Std_RBMap_fromList___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_fromList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_fromList___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_RBMap_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_RBNode_all___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_all(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_all___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_RBMap_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_all(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_RBMap_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_RBNode_any___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_any(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_any___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_RBMap_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_any(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Std_RBMap_size___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_size___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___at_Std_RBMap_size___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_RBMap_maxDepth___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_max___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_RBMap_maxDepth___rarg___closed__1;
x_3 = l_Std_RBNode_depth___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_maxDepth___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_RBMap_maxDepth___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_maxDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_maxDepth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_RBMap_min_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.Data.RBMap");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_min_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.RBMap.min!");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_min_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("map is empty");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_min_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_RBMap_min_x21___rarg___closed__1;
x_2 = l_Std_RBMap_min_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(333u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_RBMap_min_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_min___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Std_RBMap_min_x21___rarg___closed__4;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_min_x21___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_min_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_min_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_min_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_RBMap_max_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.RBMap.max!");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_max_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_RBMap_min_x21___rarg___closed__1;
x_2 = l_Std_RBMap_max_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(338u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_RBMap_min_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_max___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Std_RBMap_max_x21___rarg___closed__2;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_RBMap_max_x21___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_max_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_max_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBMap_max_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_RBMap_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.RBMap.find!");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("key is not in the map");
return x_1;
}
}
static lean_object* _init_l_Std_RBMap_find_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_RBMap_min_x21___rarg___closed__1;
x_2 = l_Std_RBMap_find_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(343u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_RBMap_find_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_RBMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBMap_find_x21___rarg___closed__3;
x_7 = lean_panic_fn(x_2, x_6);
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
LEAN_EXPORT lean_object* l_Std_RBMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_RBMap_find_x21___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_rbmapOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Std_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_rbmapOf___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___at_Std_rbmapOf___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_rbmapOf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at_Std_rbmapOf___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_rbmapOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_rbmapOf___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_RBMap(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Rbcolor_noConfusion___rarg___closed__1 = _init_l_Std_Rbcolor_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Std_Rbcolor_noConfusion___rarg___closed__1);
l_Std_RBMap_toList___rarg___closed__1 = _init_l_Std_RBMap_toList___rarg___closed__1();
lean_mark_persistent(l_Std_RBMap_toList___rarg___closed__1);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__1 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__1();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__1);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__2 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__2();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__2);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__3);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__4);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__5 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__5();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__5);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__6 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__6();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__6);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__7 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__7();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__7);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__8 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__8();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__8);
l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__9 = _init_l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__9();
lean_mark_persistent(l_repr___at_Std_RBMap_instReprRBMap___spec__1___rarg___closed__9);
l_Std_RBMap_instReprRBMap___rarg___closed__1 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__1();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__1);
l_Std_RBMap_instReprRBMap___rarg___closed__2 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__2();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__2);
l_Std_RBMap_instReprRBMap___rarg___closed__3 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__3();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__3);
l_Std_RBMap_instReprRBMap___rarg___closed__4 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__4();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__4);
l_Std_RBMap_instReprRBMap___rarg___closed__5 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__5();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__5);
l_Std_RBMap_instReprRBMap___rarg___closed__6 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__6();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__6);
l_Std_RBMap_instReprRBMap___rarg___closed__7 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__7();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__7);
l_Std_RBMap_instReprRBMap___rarg___closed__8 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__8();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__8);
l_Std_RBMap_instReprRBMap___rarg___closed__9 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__9();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__9);
l_Std_RBMap_instReprRBMap___rarg___closed__10 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__10();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__10);
l_Std_RBMap_instReprRBMap___rarg___closed__11 = _init_l_Std_RBMap_instReprRBMap___rarg___closed__11();
lean_mark_persistent(l_Std_RBMap_instReprRBMap___rarg___closed__11);
l_Std_RBMap_maxDepth___rarg___closed__1 = _init_l_Std_RBMap_maxDepth___rarg___closed__1();
lean_mark_persistent(l_Std_RBMap_maxDepth___rarg___closed__1);
l_Std_RBMap_min_x21___rarg___closed__1 = _init_l_Std_RBMap_min_x21___rarg___closed__1();
lean_mark_persistent(l_Std_RBMap_min_x21___rarg___closed__1);
l_Std_RBMap_min_x21___rarg___closed__2 = _init_l_Std_RBMap_min_x21___rarg___closed__2();
lean_mark_persistent(l_Std_RBMap_min_x21___rarg___closed__2);
l_Std_RBMap_min_x21___rarg___closed__3 = _init_l_Std_RBMap_min_x21___rarg___closed__3();
lean_mark_persistent(l_Std_RBMap_min_x21___rarg___closed__3);
l_Std_RBMap_min_x21___rarg___closed__4 = _init_l_Std_RBMap_min_x21___rarg___closed__4();
lean_mark_persistent(l_Std_RBMap_min_x21___rarg___closed__4);
l_Std_RBMap_max_x21___rarg___closed__1 = _init_l_Std_RBMap_max_x21___rarg___closed__1();
lean_mark_persistent(l_Std_RBMap_max_x21___rarg___closed__1);
l_Std_RBMap_max_x21___rarg___closed__2 = _init_l_Std_RBMap_max_x21___rarg___closed__2();
lean_mark_persistent(l_Std_RBMap_max_x21___rarg___closed__2);
l_Std_RBMap_find_x21___rarg___closed__1 = _init_l_Std_RBMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_Std_RBMap_find_x21___rarg___closed__1);
l_Std_RBMap_find_x21___rarg___closed__2 = _init_l_Std_RBMap_find_x21___rarg___closed__2();
lean_mark_persistent(l_Std_RBMap_find_x21___rarg___closed__2);
l_Std_RBMap_find_x21___rarg___closed__3 = _init_l_Std_RBMap_find_x21___rarg___closed__3();
lean_mark_persistent(l_Std_RBMap_find_x21___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
