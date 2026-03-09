// Lean compiler output
// Module: Lean.Data.RBMap
// Imports: public import Init.Data.Ord.Basic public import Init.Data.Nat.Linear public import Init.Data.Array.Basic import Init.WFTactics
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
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_RBNode_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_RBNode_toArray___redArg___closed__0 = (const lean_object*)&l_Lean_RBNode_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_RBMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_toList___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_RBMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_toArray___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_toArray___redArg___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_RBMap_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_RBMap_toArray___redArg___closed__1 = (const lean_object*)&l_Lean_RBMap_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_RBMap_instRepr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.rbmapOf "};
static const lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_RBMap_instRepr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_RBMap_instRepr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_RBMap_instRepr___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_RBMap_instRepr___redArg___lam__0___closed__1_value;
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__1 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__2 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__3 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__4 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__5 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__6 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__6_value;
static const lean_ctor_object l_Lean_RBMap_fromArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__0_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__1_value)}};
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__7 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__7_value;
static const lean_ctor_object l_Lean_RBMap_fromArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__7_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__2_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__3_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__4_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__5_value)}};
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__8 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__8_value;
static const lean_ctor_object l_Lean_RBMap_fromArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__8_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__6_value)}};
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__9 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__9_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_maxDepth___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_RBMap_maxDepth___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_maxDepth___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_maxDepth___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_RBMap_min_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.Data.RBMap"};
static const lean_object* l_Lean_RBMap_min_x21___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_min_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_RBMap_min_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.RBMap.min!"};
static const lean_object* l_Lean_RBMap_min_x21___redArg___closed__1 = (const lean_object*)&l_Lean_RBMap_min_x21___redArg___closed__1_value;
static const lean_string_object l_Lean_RBMap_min_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "map is empty"};
static const lean_object* l_Lean_RBMap_min_x21___redArg___closed__2 = (const lean_object*)&l_Lean_RBMap_min_x21___redArg___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_RBMap_min_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_RBMap_min_x21___redArg___closed__3;
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_RBMap_max_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Lean.RBMap.max!"};
static const lean_object* l_Lean_RBMap_max_x21___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_max_x21___redArg___closed__0_value;
static lean_once_cell_t l_Lean_RBMap_max_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_RBMap_max_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_RBMap_find_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.RBMap.find!"};
static const lean_object* l_Lean_RBMap_find_x21___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_find_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_RBMap_find_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_Lean_RBMap_find_x21___redArg___closed__1 = (const lean_object*)&l_Lean_RBMap_find_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_RBMap_find_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_RBMap_find_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBColor_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_RBColor_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBColor_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_RBColor_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBColor_red_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_RBColor_red_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBColor_black_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_RBColor_black_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_ctorIdx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_box(x_3);
x_9 = lean_apply_5(x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_ctorElim___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ctorElim___redArg(x_4, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_depth___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_min___redArg(x_1);
lean_dec(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_max___redArg(x_1);
lean_dec(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_forM___redArg(x_1, x_2, x_3);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___redArg(x_1, x_2, x_4, x_3);
return x_5;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
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
x_8 = lean_apply_2(x_1, x_5, x_6);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_10 = lean_unbox(x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_inc_ref(x_1);
x_11 = l_Lean_RBNode_all___redArg(x_1, x_4);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_all___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
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
x_8 = lean_apply_2(x_1, x_5, x_6);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc_ref(x_1);
x_10 = l_Lean_RBNode_any___redArg(x_1, x_4);
if (x_10 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_1);
return x_10;
}
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_1);
x_12 = lean_unbox(x_8);
return x_12;
}
}
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
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_any___redArg(x_3, x_4);
return x_5;
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
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
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
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isSingleton___redArg(x_3);
return x_4;
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
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
if (x_12 == 0)
{
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_13);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 3);
lean_inc(x_36);
lean_dec_ref(x_13);
x_17 = x_33;
x_18 = x_34;
x_19 = x_35;
x_20 = x_36;
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
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_16);
lean_inc_ref(x_13);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_16, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 3);
lean_inc(x_41);
lean_dec_ref(x_16);
x_17 = x_13;
x_18 = x_14;
x_19 = x_15;
x_20 = x_38;
x_21 = x_39;
x_22 = x_40;
x_23 = x_41;
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
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_16, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_16, 3);
lean_inc(x_46);
lean_dec_ref(x_16);
x_17 = x_13;
x_18 = x_14;
x_19 = x_15;
x_20 = x_43;
x_21 = x_44;
x_22 = x_45;
x_23 = x_46;
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
else
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
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
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
if (x_14 == 0)
{
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_15);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_3);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_15, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 3);
lean_inc(x_38);
lean_dec_ref(x_15);
x_19 = x_35;
x_20 = x_36;
x_21 = x_37;
x_22 = x_38;
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
if (lean_obj_tag(x_18) == 1)
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_18);
lean_inc_ref(x_15);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_3);
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 3);
lean_inc(x_43);
lean_dec_ref(x_18);
x_19 = x_15;
x_20 = x_16;
x_21 = x_17;
x_22 = x_40;
x_23 = x_41;
x_24 = x_42;
x_25 = x_43;
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
if (lean_obj_tag(x_18) == 1)
{
uint8_t x_44; 
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec_ref(x_3);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 3);
lean_inc(x_48);
lean_dec_ref(x_18);
x_19 = x_15;
x_20 = x_16;
x_21 = x_17;
x_22 = x_45;
x_23 = x_46;
x_24 = x_47;
x_25 = x_48;
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
else
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
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
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
if (x_12 == 0)
{
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_13);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_4);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 3);
lean_inc(x_36);
lean_dec_ref(x_13);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_33;
x_21 = x_34;
x_22 = x_35;
x_23 = x_36;
x_24 = x_14;
x_25 = x_15;
x_26 = x_16;
goto block_31;
}
else
{
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc_ref(x_16);
lean_inc_ref(x_13);
lean_inc(x_15);
lean_inc(x_14);
lean_dec_ref(x_4);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_16, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_16, 3);
lean_inc(x_41);
lean_dec_ref(x_16);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_13;
x_21 = x_14;
x_22 = x_15;
x_23 = x_38;
x_24 = x_39;
x_25 = x_40;
x_26 = x_41;
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
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec_ref(x_4);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_16, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_16, 3);
lean_inc(x_46);
lean_dec_ref(x_16);
x_17 = x_1;
x_18 = x_2;
x_19 = x_3;
x_20 = x_13;
x_21 = x_14;
x_22 = x_15;
x_23 = x_43;
x_24 = x_44;
x_25 = x_45;
x_26 = x_46;
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
else
{
x_5 = x_1;
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
goto block_11;
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
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
if (x_14 == 0)
{
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_15);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_6);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_15, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 3);
lean_inc(x_38);
lean_dec_ref(x_15);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_35;
x_23 = x_36;
x_24 = x_37;
x_25 = x_38;
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
goto block_33;
}
else
{
if (lean_obj_tag(x_18) == 1)
{
uint8_t x_39; 
x_39 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_18);
lean_inc_ref(x_15);
lean_inc(x_17);
lean_inc(x_16);
lean_dec_ref(x_6);
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 3);
lean_inc(x_43);
lean_dec_ref(x_18);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = x_40;
x_26 = x_41;
x_27 = x_42;
x_28 = x_43;
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
if (lean_obj_tag(x_18) == 1)
{
uint8_t x_44; 
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec_ref(x_6);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 3);
lean_inc(x_48);
lean_dec_ref(x_18);
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_15;
x_23 = x_16;
x_24 = x_17;
x_25 = x_45;
x_26 = x_46;
x_27 = x_47;
x_28 = x_48;
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
else
{
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = x_6;
goto block_13;
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
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
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
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_3);
return x_4;
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
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_2 == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
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
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isBlack___redArg(x_3);
return x_4;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_12 = x_2;
x_13 = x_28;
goto block_27;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc(x_3);
x_14 = lean_apply_2(x_1, x_3, x_9);
x_15 = lean_unbox(x_14);
switch (x_15) {
case 0:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_RBNode_ins___redArg(x_1, x_8, x_3, x_4);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_16);
x_17 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 3, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_7);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
case 1:
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 1, x_3);
x_20 = x_12;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_11);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___redArg(x_1, x_11, x_3, x_4);
if (x_13 == 0)
{
lean_ctor_set(x_12, 3, x_23);
x_24 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_9);
lean_ctor_set(x_26, 2, x_10);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_7);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_191; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_191 = !lean_is_exclusive(x_2);
if (x_191 == 0)
{
x_33 = x_2;
x_34 = x_191;
goto block_190;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_35; uint8_t x_36; 
lean_inc_ref(x_1);
lean_inc(x_30);
lean_inc(x_3);
x_35 = lean_apply_2(x_1, x_3, x_30);
x_36 = lean_unbox(x_35);
switch (x_36) {
case 0:
{
lean_object* x_37; 
x_37 = l_Lean_RBNode_ins___redArg(x_1, x_29, x_3, x_4);
if (lean_obj_tag(x_37) == 1)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 3);
lean_inc(x_42);
if (x_38 == 0)
{
if (lean_obj_tag(x_39) == 1)
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_37);
x_60 = lean_ctor_get(x_39, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_39, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_39, 3);
lean_inc(x_63);
lean_dec_ref(x_39);
x_43 = x_60;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_40;
x_48 = x_41;
x_49 = x_42;
x_50 = x_30;
x_51 = x_31;
x_52 = x_32;
goto block_58;
}
else
{
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_64; 
x_64 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_37);
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 3);
lean_inc(x_68);
lean_dec_ref(x_42);
x_43 = x_39;
x_44 = x_40;
x_45 = x_41;
x_46 = x_65;
x_47 = x_66;
x_48 = x_67;
x_49 = x_68;
x_50 = x_30;
x_51 = x_31;
x_52 = x_32;
goto block_58;
}
else
{
lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec_ref(x_39);
lean_dec(x_41);
lean_dec(x_40);
lean_del_object(x_33);
x_75 = !lean_is_exclusive(x_42);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_42, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_42, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_42, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_42, 0);
lean_dec(x_79);
x_69 = x_42;
x_70 = x_75;
goto block_74;
}
else
{
lean_dec(x_42);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
lean_ctor_set(x_69, 3, x_32);
lean_ctor_set(x_69, 2, x_31);
lean_ctor_set(x_69, 1, x_30);
lean_ctor_set(x_69, 0, x_37);
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_30);
lean_ctor_set(x_73, 2, x_31);
lean_ctor_set(x_73, 3, x_32);
x_71 = x_73;
goto block_72;
}
block_72:
{
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_7);
return x_71;
}
}
}
}
else
{
lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_del_object(x_33);
x_86 = !lean_is_exclusive(x_39);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_39, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_39, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_39, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_39, 0);
lean_dec(x_90);
x_80 = x_39;
x_81 = x_86;
goto block_85;
}
else
{
lean_dec(x_39);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 3, x_32);
lean_ctor_set(x_80, 2, x_31);
lean_ctor_set(x_80, 1, x_30);
lean_ctor_set(x_80, 0, x_37);
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_30);
lean_ctor_set(x_84, 2, x_31);
lean_ctor_set(x_84, 3, x_32);
x_82 = x_84;
goto block_83;
}
block_83:
{
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_7);
return x_82;
}
}
}
}
}
else
{
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_37);
x_92 = lean_ctor_get(x_42, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_42, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_42, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_42, 3);
lean_inc(x_95);
lean_dec_ref(x_42);
x_43 = x_39;
x_44 = x_40;
x_45 = x_41;
x_46 = x_92;
x_47 = x_93;
x_48 = x_94;
x_49 = x_95;
x_50 = x_30;
x_51 = x_31;
x_52 = x_32;
goto block_58;
}
else
{
lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_33);
x_102 = !lean_is_exclusive(x_42);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_42, 3);
lean_dec(x_103);
x_104 = lean_ctor_get(x_42, 2);
lean_dec(x_104);
x_105 = lean_ctor_get(x_42, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_42, 0);
lean_dec(x_106);
x_96 = x_42;
x_97 = x_102;
goto block_101;
}
else
{
lean_dec(x_42);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
lean_ctor_set(x_96, 3, x_32);
lean_ctor_set(x_96, 2, x_31);
lean_ctor_set(x_96, 1, x_30);
lean_ctor_set(x_96, 0, x_37);
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_100, 0, x_37);
lean_ctor_set(x_100, 1, x_30);
lean_ctor_set(x_100, 2, x_31);
lean_ctor_set(x_100, 3, x_32);
x_98 = x_100;
goto block_99;
}
block_99:
{
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_7);
return x_98;
}
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_33);
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_37);
lean_ctor_set(x_107, 1, x_30);
lean_ctor_set(x_107, 2, x_31);
lean_ctor_set(x_107, 3, x_32);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_7);
return x_107;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_33);
x_108 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_108, 0, x_37);
lean_ctor_set(x_108, 1, x_30);
lean_ctor_set(x_108, 2, x_31);
lean_ctor_set(x_108, 3, x_32);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_7);
return x_108;
}
block_58:
{
lean_object* x_53; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_46);
lean_ctor_set(x_33, 2, x_45);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_43);
x_53 = x_33;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_45);
lean_ctor_set(x_57, 3, x_46);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
x_53 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_7);
x_55 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_38);
return x_55;
}
}
}
else
{
lean_object* x_109; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_37);
x_109 = x_33;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_37);
lean_ctor_set(x_111, 1, x_30);
lean_ctor_set(x_111, 2, x_31);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_7);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
case 1:
{
lean_object* x_112; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
if (x_34 == 0)
{
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 1, x_3);
x_112 = x_33;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_29);
lean_ctor_set(x_114, 1, x_3);
lean_ctor_set(x_114, 2, x_4);
lean_ctor_set(x_114, 3, x_32);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
default: 
{
lean_object* x_115; 
x_115 = l_Lean_RBNode_ins___redArg(x_1, x_32, x_3, x_4);
if (lean_obj_tag(x_115) == 1)
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 1)
{
uint8_t x_137; 
x_137 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_115);
x_138 = lean_ctor_get(x_117, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_117, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_117, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_117, 3);
lean_inc(x_141);
lean_dec_ref(x_117);
x_121 = x_29;
x_122 = x_30;
x_123 = x_31;
x_124 = x_138;
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_136;
}
else
{
if (lean_obj_tag(x_120) == 1)
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_115);
x_143 = lean_ctor_get(x_120, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_120, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 3);
lean_inc(x_146);
lean_dec_ref(x_120);
x_121 = x_29;
x_122 = x_30;
x_123 = x_31;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_143;
x_128 = x_144;
x_129 = x_145;
x_130 = x_146;
goto block_136;
}
else
{
lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_dec_ref(x_117);
lean_dec(x_119);
lean_dec(x_118);
lean_del_object(x_33);
x_153 = !lean_is_exclusive(x_120);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_120, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_120, 2);
lean_dec(x_155);
x_156 = lean_ctor_get(x_120, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_120, 0);
lean_dec(x_157);
x_147 = x_120;
x_148 = x_153;
goto block_152;
}
else
{
lean_dec(x_120);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 3, x_115);
lean_ctor_set(x_147, 2, x_31);
lean_ctor_set(x_147, 1, x_30);
lean_ctor_set(x_147, 0, x_29);
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_29);
lean_ctor_set(x_151, 1, x_30);
lean_ctor_set(x_151, 2, x_31);
lean_ctor_set(x_151, 3, x_115);
x_149 = x_151;
goto block_150;
}
block_150:
{
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_7);
return x_149;
}
}
}
}
else
{
lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_del_object(x_33);
x_164 = !lean_is_exclusive(x_117);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_117, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_117, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_117, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_117, 0);
lean_dec(x_168);
x_158 = x_117;
x_159 = x_164;
goto block_163;
}
else
{
lean_dec(x_117);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
lean_ctor_set(x_158, 3, x_115);
lean_ctor_set(x_158, 2, x_31);
lean_ctor_set(x_158, 1, x_30);
lean_ctor_set(x_158, 0, x_29);
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_29);
lean_ctor_set(x_162, 1, x_30);
lean_ctor_set(x_162, 2, x_31);
lean_ctor_set(x_162, 3, x_115);
x_160 = x_162;
goto block_161;
}
block_161:
{
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_7);
return x_160;
}
}
}
}
}
else
{
if (lean_obj_tag(x_120) == 1)
{
uint8_t x_169; 
x_169 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_115);
x_170 = lean_ctor_get(x_120, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_120, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 3);
lean_inc(x_173);
lean_dec_ref(x_120);
x_121 = x_29;
x_122 = x_30;
x_123 = x_31;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_170;
x_128 = x_171;
x_129 = x_172;
x_130 = x_173;
goto block_136;
}
else
{
lean_object* x_174; uint8_t x_175; uint8_t x_180; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_del_object(x_33);
x_180 = !lean_is_exclusive(x_120);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_120, 3);
lean_dec(x_181);
x_182 = lean_ctor_get(x_120, 2);
lean_dec(x_182);
x_183 = lean_ctor_get(x_120, 1);
lean_dec(x_183);
x_184 = lean_ctor_get(x_120, 0);
lean_dec(x_184);
x_174 = x_120;
x_175 = x_180;
goto block_179;
}
else
{
lean_dec(x_120);
x_174 = lean_box(0);
x_175 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_176; 
if (x_175 == 0)
{
lean_ctor_set(x_174, 3, x_115);
lean_ctor_set(x_174, 2, x_31);
lean_ctor_set(x_174, 1, x_30);
lean_ctor_set(x_174, 0, x_29);
x_176 = x_174;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_29);
lean_ctor_set(x_178, 1, x_30);
lean_ctor_set(x_178, 2, x_31);
lean_ctor_set(x_178, 3, x_115);
x_176 = x_178;
goto block_177;
}
block_177:
{
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
}
}
}
else
{
lean_object* x_185; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_del_object(x_33);
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_29);
lean_ctor_set(x_185, 1, x_30);
lean_ctor_set(x_185, 2, x_31);
lean_ctor_set(x_185, 3, x_115);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_7);
return x_185;
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_del_object(x_33);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_29);
lean_ctor_set(x_186, 1, x_30);
lean_ctor_set(x_186, 2, x_31);
lean_ctor_set(x_186, 3, x_115);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_7);
return x_186;
}
block_136:
{
lean_object* x_131; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_124);
lean_ctor_set(x_33, 2, x_123);
lean_ctor_set(x_33, 1, x_122);
lean_ctor_set(x_33, 0, x_121);
x_131 = x_33;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_122);
lean_ctor_set(x_135, 2, x_123);
lean_ctor_set(x_135, 3, x_124);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_7);
x_131 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
else
{
lean_object* x_187; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_115);
x_187 = x_33;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_29);
lean_ctor_set(x_189, 1, x_30);
lean_ctor_set(x_189, 2, x_31);
lean_ctor_set(x_189, 3, x_115);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_7);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
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
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
x_6 = x_1;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
if (x_7 == 0)
{
x_9 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_5);
x_9 = x_11;
goto block_10;
}
block_10:
{
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
else
{
return x_1;
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
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
x_6 = x_1;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
if (x_7 == 0)
{
x_9 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_5);
x_9 = x_11;
goto block_10;
}
block_10:
{
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
else
{
return x_1;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_133; 
x_133 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_146; 
x_134 = lean_ctor_get(x_1, 0);
x_135 = lean_ctor_get(x_1, 1);
x_136 = lean_ctor_get(x_1, 2);
x_137 = lean_ctor_get(x_1, 3);
x_146 = !lean_is_exclusive(x_1);
if (x_146 == 0)
{
x_138 = x_1;
x_139 = x_146;
goto block_145;
}
else
{
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_1);
x_138 = lean_box(0);
x_139 = x_146;
goto block_145;
}
block_145:
{
uint8_t x_140; lean_object* x_141; 
x_140 = 1;
if (x_139 == 0)
{
x_141 = x_138;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_135);
lean_ctor_set(x_144, 2, x_136);
lean_ctor_set(x_144, 3, x_137);
x_141 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_142; 
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_140);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_2);
lean_ctor_set(x_142, 2, x_3);
lean_ctor_set(x_142, 3, x_4);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_133);
return x_142;
}
}
}
else
{
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_147; 
x_147 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_148) == 1)
{
uint8_t x_149; 
x_149 = lean_ctor_get_uint8(x_148, sizeof(void*)*4);
if (x_149 == 1)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_inc_ref(x_148);
x_150 = lean_ctor_get(x_4, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_4, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_4, 3);
lean_inc(x_152);
lean_dec_ref(x_4);
x_153 = lean_ctor_get(x_148, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_148, 2);
lean_inc(x_155);
x_156 = lean_ctor_get(x_148, 3);
lean_inc(x_156);
lean_dec_ref(x_148);
x_85 = x_1;
x_86 = x_2;
x_87 = x_3;
x_88 = x_153;
x_89 = x_154;
x_90 = x_155;
x_91 = x_156;
x_92 = x_150;
x_93 = x_151;
x_94 = x_152;
goto block_125;
}
else
{
x_126 = x_1;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
goto block_132;
}
}
else
{
x_126 = x_1;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
goto block_132;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_4, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_4, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_4, 3);
lean_inc(x_160);
lean_dec_ref(x_4);
x_28 = x_1;
x_29 = x_2;
x_30 = x_3;
x_31 = x_157;
x_32 = x_158;
x_33 = x_159;
x_34 = x_160;
goto block_52;
}
}
else
{
x_126 = x_1;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
goto block_132;
}
}
}
else
{
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_161; 
x_161 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_162) == 1)
{
uint8_t x_163; 
x_163 = lean_ctor_get_uint8(x_162, sizeof(void*)*4);
if (x_163 == 1)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_inc_ref(x_162);
x_164 = lean_ctor_get(x_4, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_4, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_4, 3);
lean_inc(x_166);
lean_dec_ref(x_4);
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 3);
lean_inc(x_170);
lean_dec_ref(x_162);
x_85 = x_1;
x_86 = x_2;
x_87 = x_3;
x_88 = x_167;
x_89 = x_168;
x_90 = x_169;
x_91 = x_170;
x_92 = x_164;
x_93 = x_165;
x_94 = x_166;
goto block_125;
}
else
{
x_126 = x_1;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
goto block_132;
}
}
else
{
x_126 = x_1;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
goto block_132;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_4, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_4, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_4, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_4, 3);
lean_inc(x_174);
lean_dec_ref(x_4);
x_28 = x_1;
x_29 = x_2;
x_30 = x_3;
x_31 = x_171;
x_32 = x_172;
x_33 = x_173;
x_34 = x_174;
goto block_52;
}
}
else
{
x_126 = x_1;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
goto block_132;
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
block_27:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = 0;
x_23 = 1;
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_23);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_23);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_22);
return x_26;
}
block_52:
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
if (lean_obj_tag(x_31) == 1)
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_31, sizeof(void*)*4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_31, 3);
lean_inc(x_41);
lean_dec_ref(x_31);
x_12 = x_28;
x_13 = x_29;
x_14 = x_30;
x_15 = x_38;
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_32;
x_20 = x_33;
x_21 = x_34;
goto block_27;
}
else
{
if (lean_obj_tag(x_34) == 1)
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_36);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_34, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_34, 3);
lean_inc(x_46);
lean_dec_ref(x_34);
x_12 = x_28;
x_13 = x_29;
x_14 = x_30;
x_15 = x_31;
x_16 = x_32;
x_17 = x_33;
x_18 = x_43;
x_19 = x_44;
x_20 = x_45;
x_21 = x_46;
goto block_27;
}
else
{
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec(x_33);
lean_dec(x_32);
x_5 = x_28;
x_6 = x_29;
x_7 = x_30;
x_8 = x_36;
goto block_11;
}
}
else
{
lean_dec_ref(x_31);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_5 = x_28;
x_6 = x_29;
x_7 = x_30;
x_8 = x_36;
goto block_11;
}
}
}
else
{
if (lean_obj_tag(x_34) == 1)
{
uint8_t x_47; 
x_47 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_36);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_34, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_34, 3);
lean_inc(x_51);
lean_dec_ref(x_34);
x_12 = x_28;
x_13 = x_29;
x_14 = x_30;
x_15 = x_31;
x_16 = x_32;
x_17 = x_33;
x_18 = x_48;
x_19 = x_49;
x_20 = x_50;
x_21 = x_51;
goto block_27;
}
else
{
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_5 = x_28;
x_6 = x_29;
x_7 = x_30;
x_8 = x_36;
goto block_11;
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_5 = x_28;
x_6 = x_29;
x_7 = x_30;
x_8 = x_36;
goto block_11;
}
}
}
block_72:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_57);
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_57);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_70, 2, x_63);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_56);
x_71 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_54);
lean_ctor_set(x_71, 2, x_53);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_56);
return x_71;
}
block_84:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_77);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_83, 2, x_73);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_76);
return x_83;
}
block_125:
{
uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_95 = 0;
x_96 = 1;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_85);
lean_ctor_set(x_97, 1, x_86);
lean_ctor_set(x_97, 2, x_87);
lean_ctor_set(x_97, 3, x_88);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = l_Lean_RBNode_setRed___redArg(x_94);
if (lean_obj_tag(x_98) == 1)
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*4);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 1)
{
uint8_t x_101; 
x_101 = lean_ctor_get_uint8(x_100, sizeof(void*)*4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 3);
lean_inc(x_104);
lean_dec_ref(x_98);
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_100, 3);
lean_inc(x_108);
lean_dec_ref(x_100);
x_53 = x_90;
x_54 = x_89;
x_55 = x_97;
x_56 = x_95;
x_57 = x_96;
x_58 = x_91;
x_59 = x_92;
x_60 = x_93;
x_61 = x_105;
x_62 = x_106;
x_63 = x_107;
x_64 = x_108;
x_65 = x_102;
x_66 = x_103;
x_67 = x_104;
goto block_72;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_98, 3);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 1)
{
uint8_t x_110; 
x_110 = lean_ctor_get_uint8(x_109, sizeof(void*)*4);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_98, 2);
lean_inc(x_112);
lean_dec_ref(x_98);
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 3);
lean_inc(x_116);
lean_dec_ref(x_109);
x_53 = x_90;
x_54 = x_89;
x_55 = x_97;
x_56 = x_95;
x_57 = x_96;
x_58 = x_91;
x_59 = x_92;
x_60 = x_93;
x_61 = x_100;
x_62 = x_111;
x_63 = x_112;
x_64 = x_113;
x_65 = x_114;
x_66 = x_115;
x_67 = x_116;
goto block_72;
}
else
{
lean_dec_ref(x_109);
lean_dec_ref(x_100);
x_73 = x_90;
x_74 = x_89;
x_75 = x_97;
x_76 = x_95;
x_77 = x_96;
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_98;
goto block_84;
}
}
else
{
lean_dec(x_109);
lean_dec_ref(x_100);
x_73 = x_90;
x_74 = x_89;
x_75 = x_97;
x_76 = x_95;
x_77 = x_96;
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_98;
goto block_84;
}
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_98, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 1)
{
uint8_t x_118; 
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_98, 2);
lean_inc(x_120);
lean_dec_ref(x_98);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 3);
lean_inc(x_124);
lean_dec_ref(x_117);
x_53 = x_90;
x_54 = x_89;
x_55 = x_97;
x_56 = x_95;
x_57 = x_96;
x_58 = x_91;
x_59 = x_92;
x_60 = x_93;
x_61 = x_100;
x_62 = x_119;
x_63 = x_120;
x_64 = x_121;
x_65 = x_122;
x_66 = x_123;
x_67 = x_124;
goto block_72;
}
else
{
lean_dec_ref(x_117);
lean_dec(x_100);
x_73 = x_90;
x_74 = x_89;
x_75 = x_97;
x_76 = x_95;
x_77 = x_96;
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_98;
goto block_84;
}
}
else
{
lean_dec(x_117);
lean_dec(x_100);
x_73 = x_90;
x_74 = x_89;
x_75 = x_97;
x_76 = x_95;
x_77 = x_96;
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_98;
goto block_84;
}
}
}
else
{
x_73 = x_90;
x_74 = x_89;
x_75 = x_97;
x_76 = x_95;
x_77 = x_96;
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_98;
goto block_84;
}
}
else
{
x_73 = x_90;
x_74 = x_89;
x_75 = x_97;
x_76 = x_95;
x_77 = x_96;
x_78 = x_91;
x_79 = x_92;
x_80 = x_93;
x_81 = x_98;
goto block_84;
}
}
block_132:
{
uint8_t x_130; lean_object* x_131; 
x_130 = 0;
x_131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 3, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_130);
return x_131;
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
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_162; 
x_162 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_175; 
x_163 = lean_ctor_get(x_4, 0);
x_164 = lean_ctor_get(x_4, 1);
x_165 = lean_ctor_get(x_4, 2);
x_166 = lean_ctor_get(x_4, 3);
x_175 = !lean_is_exclusive(x_4);
if (x_175 == 0)
{
x_167 = x_4;
x_168 = x_175;
goto block_174;
}
else
{
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_4);
x_167 = lean_box(0);
x_168 = x_175;
goto block_174;
}
block_174:
{
uint8_t x_169; lean_object* x_170; 
x_169 = 1;
if (x_168 == 0)
{
x_170 = x_167;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_165);
lean_ctor_set(x_173, 3, x_166);
x_170 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_171; 
lean_ctor_set_uint8(x_170, sizeof(void*)*4, x_169);
x_171 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_2);
lean_ctor_set(x_171, 2, x_3);
lean_ctor_set(x_171, 3, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_162);
return x_171;
}
}
}
else
{
goto block_161;
}
}
else
{
goto block_161;
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
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_4);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_26);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_28);
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
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_35);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_35);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_37);
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
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_54);
x_24 = x_52;
x_25 = x_53;
x_26 = x_54;
x_27 = x_56;
x_28 = x_55;
x_29 = x_61;
goto block_32;
}
block_161:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_63; 
x_63 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_64) == 1)
{
uint8_t x_65; 
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*4);
if (x_65 == 1)
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
if (lean_obj_tag(x_73) == 1)
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*4);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 1)
{
uint8_t x_76; 
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*4);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 3);
lean_inc(x_79);
lean_dec_ref(x_73);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 3);
lean_inc(x_83);
lean_dec_ref(x_75);
x_33 = x_72;
x_34 = x_70;
x_35 = x_65;
x_36 = x_71;
x_37 = x_63;
x_38 = x_80;
x_39 = x_81;
x_40 = x_82;
x_41 = x_83;
x_42 = x_77;
x_43 = x_78;
x_44 = x_79;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
goto block_51;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_73, 3);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 1)
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_84, sizeof(void*)*4);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_73, 2);
lean_inc(x_87);
lean_dec_ref(x_73);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 3);
lean_inc(x_91);
lean_dec_ref(x_84);
x_33 = x_72;
x_34 = x_70;
x_35 = x_65;
x_36 = x_71;
x_37 = x_63;
x_38 = x_75;
x_39 = x_86;
x_40 = x_87;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
goto block_51;
}
else
{
lean_dec_ref(x_84);
lean_dec_ref(x_75);
x_52 = x_72;
x_53 = x_70;
x_54 = x_65;
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
lean_dec(x_84);
lean_dec_ref(x_75);
x_52 = x_72;
x_53 = x_70;
x_54 = x_65;
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
lean_object* x_92; 
x_92 = lean_ctor_get(x_73, 3);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 1)
{
uint8_t x_93; 
x_93 = lean_ctor_get_uint8(x_92, sizeof(void*)*4);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_73, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_73, 2);
lean_inc(x_95);
lean_dec_ref(x_73);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 3);
lean_inc(x_99);
lean_dec_ref(x_92);
x_33 = x_72;
x_34 = x_70;
x_35 = x_65;
x_36 = x_71;
x_37 = x_63;
x_38 = x_75;
x_39 = x_94;
x_40 = x_95;
x_41 = x_96;
x_42 = x_97;
x_43 = x_98;
x_44 = x_99;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
goto block_51;
}
else
{
lean_dec_ref(x_92);
lean_dec(x_75);
x_52 = x_72;
x_53 = x_70;
x_54 = x_65;
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
lean_dec(x_92);
lean_dec(x_75);
x_52 = x_72;
x_53 = x_70;
x_54 = x_65;
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
x_52 = x_72;
x_53 = x_70;
x_54 = x_65;
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
x_52 = x_72;
x_53 = x_70;
x_54 = x_65;
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
goto block_7;
}
}
else
{
goto block_7;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_160; 
x_100 = lean_ctor_get(x_1, 0);
x_101 = lean_ctor_get(x_1, 1);
x_102 = lean_ctor_get(x_1, 2);
x_103 = lean_ctor_get(x_1, 3);
x_160 = !lean_is_exclusive(x_1);
if (x_160 == 0)
{
x_104 = x_1;
x_105 = x_160;
goto block_159;
}
else
{
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_1);
x_104 = lean_box(0);
x_105 = x_160;
goto block_159;
}
block_159:
{
uint8_t x_106; lean_object* x_107; 
x_106 = 0;
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
if (x_105 == 0)
{
x_107 = x_104;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_158, 0, x_100);
lean_ctor_set(x_158, 1, x_101);
lean_ctor_set(x_158, 2, x_102);
lean_ctor_set(x_158, 3, x_103);
x_107 = x_158;
goto block_157;
}
block_157:
{
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
if (lean_obj_tag(x_100) == 1)
{
uint8_t x_108; 
x_108 = lean_ctor_get_uint8(x_100, sizeof(void*)*4);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_107);
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_100, 3);
lean_inc(x_112);
lean_dec_ref(x_100);
x_8 = x_63;
x_9 = x_109;
x_10 = x_110;
x_11 = x_111;
x_12 = x_112;
x_13 = x_101;
x_14 = x_102;
x_15 = x_103;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
if (lean_obj_tag(x_103) == 1)
{
uint8_t x_113; 
x_113 = lean_ctor_get_uint8(x_103, sizeof(void*)*4);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_107);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_103, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_103, 3);
lean_inc(x_117);
lean_dec_ref(x_103);
x_8 = x_63;
x_9 = x_100;
x_10 = x_101;
x_11 = x_102;
x_12 = x_114;
x_13 = x_115;
x_14 = x_116;
x_15 = x_117;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
lean_object* x_118; uint8_t x_119; uint8_t x_124; 
lean_dec_ref(x_100);
lean_dec(x_102);
lean_dec(x_101);
x_124 = !lean_is_exclusive(x_103);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_103, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_103, 2);
lean_dec(x_126);
x_127 = lean_ctor_get(x_103, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_103, 0);
lean_dec(x_128);
x_118 = x_103;
x_119 = x_124;
goto block_123;
}
else
{
lean_dec(x_103);
x_118 = lean_box(0);
x_119 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_120; 
if (x_119 == 0)
{
lean_ctor_set(x_118, 3, x_4);
lean_ctor_set(x_118, 2, x_3);
lean_ctor_set(x_118, 1, x_2);
lean_ctor_set(x_118, 0, x_107);
x_120 = x_118;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_107);
lean_ctor_set(x_122, 1, x_2);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set(x_122, 3, x_4);
x_120 = x_122;
goto block_121;
}
block_121:
{
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_63);
return x_120;
}
}
}
}
else
{
lean_object* x_129; uint8_t x_130; uint8_t x_135; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
x_135 = !lean_is_exclusive(x_100);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_100, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_100, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_100, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_100, 0);
lean_dec(x_139);
x_129 = x_100;
x_130 = x_135;
goto block_134;
}
else
{
lean_dec(x_100);
x_129 = lean_box(0);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_130 == 0)
{
lean_ctor_set(x_129, 3, x_4);
lean_ctor_set(x_129, 2, x_3);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 0, x_107);
x_131 = x_129;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_107);
lean_ctor_set(x_133, 1, x_2);
lean_ctor_set(x_133, 2, x_3);
lean_ctor_set(x_133, 3, x_4);
x_131 = x_133;
goto block_132;
}
block_132:
{
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_63);
return x_131;
}
}
}
}
}
else
{
if (lean_obj_tag(x_103) == 1)
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_103, sizeof(void*)*4);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_107);
x_141 = lean_ctor_get(x_103, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_103, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_103, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_103, 3);
lean_inc(x_144);
lean_dec_ref(x_103);
x_8 = x_63;
x_9 = x_100;
x_10 = x_101;
x_11 = x_102;
x_12 = x_141;
x_13 = x_142;
x_14 = x_143;
x_15 = x_144;
x_16 = x_2;
x_17 = x_3;
x_18 = x_4;
goto block_23;
}
else
{
lean_object* x_145; uint8_t x_146; uint8_t x_151; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
x_151 = !lean_is_exclusive(x_103);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_103, 3);
lean_dec(x_152);
x_153 = lean_ctor_get(x_103, 2);
lean_dec(x_153);
x_154 = lean_ctor_get(x_103, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_103, 0);
lean_dec(x_155);
x_145 = x_103;
x_146 = x_151;
goto block_150;
}
else
{
lean_dec(x_103);
x_145 = lean_box(0);
x_146 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_147; 
if (x_146 == 0)
{
lean_ctor_set(x_145, 3, x_4);
lean_ctor_set(x_145, 2, x_3);
lean_ctor_set(x_145, 1, x_2);
lean_ctor_set(x_145, 0, x_107);
x_147 = x_145;
goto block_148;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_107);
lean_ctor_set(x_149, 1, x_2);
lean_ctor_set(x_149, 2, x_3);
lean_ctor_set(x_149, 3, x_4);
x_147 = x_149;
goto block_148;
}
block_148:
{
lean_ctor_set_uint8(x_147, sizeof(void*)*4, x_63);
return x_147;
}
}
}
}
else
{
lean_object* x_156; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_107);
lean_ctor_set(x_156, 1, x_2);
lean_ctor_set(x_156, 2, x_3);
lean_ctor_set(x_156, 3, x_4);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_63);
return x_156;
}
}
}
}
}
}
else
{
goto block_7;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBNode_size___redArg(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_box(x_6);
x_12 = lean_apply_5(x_3, x_11, x_7, x_8, x_9, x_10);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
if (x_8 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_55; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_2, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_2, 0);
lean_dec(x_59);
x_21 = x_2;
x_22 = x_55;
goto block_54;
}
else
{
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = x_55;
goto block_54;
}
block_54:
{
if (x_3 == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_45; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_1, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_1, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_1, 0);
lean_dec(x_49);
x_23 = x_1;
x_24 = x_45;
goto block_44;
}
else
{
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_25; 
x_25 = l_Lean_RBNode_appendTrees___redArg(x_7, x_9);
if (lean_obj_tag(x_25) == 1)
{
uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_43; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_ctor_get(x_25, 3);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
x_31 = x_25;
x_32 = x_43;
goto block_42;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_33; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 2, x_6);
lean_ctor_set(x_31, 1, x_5);
lean_ctor_set(x_31, 0, x_4);
x_33 = x_31;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_6);
lean_ctor_set(x_41, 3, x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_26);
x_33 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_34; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_30);
x_34 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_10);
lean_ctor_set(x_39, 2, x_11);
lean_ctor_set(x_39, 3, x_12);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_26);
if (x_24 == 0)
{
lean_ctor_set(x_23, 3, x_34);
lean_ctor_set(x_23, 2, x_29);
lean_ctor_set(x_23, 1, x_28);
lean_ctor_set(x_23, 0, x_33);
x_35 = x_23;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_26);
return x_35;
}
}
}
}
}
else
{
lean_del_object(x_23);
lean_del_object(x_21);
x_17 = x_25;
goto block_20;
}
}
else
{
lean_del_object(x_23);
lean_del_object(x_21);
x_17 = x_25;
goto block_20;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_RBNode_appendTrees___redArg(x_1, x_9);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_50);
x_51 = x_21;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_10);
lean_ctor_set(x_53, 2, x_11);
lean_ctor_set(x_53, 3, x_12);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_8);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; uint8_t x_94; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_94 = !lean_is_exclusive(x_1);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_1, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_1, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_1, 0);
lean_dec(x_98);
x_60 = x_1;
x_61 = x_94;
goto block_93;
}
else
{
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = x_94;
goto block_93;
}
block_93:
{
if (x_3 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_RBNode_appendTrees___redArg(x_7, x_2);
if (x_61 == 0)
{
lean_ctor_set(x_60, 3, x_62);
x_63 = x_60;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_5);
lean_ctor_set(x_65, 2, x_6);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_3);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; uint8_t x_67; uint8_t x_88; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_2, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_2, 2);
lean_dec(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_dec(x_91);
x_92 = lean_ctor_get(x_2, 0);
lean_dec(x_92);
x_66 = x_2;
x_67 = x_88;
goto block_87;
}
else
{
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_68; 
x_68 = l_Lean_RBNode_appendTrees___redArg(x_7, x_9);
if (lean_obj_tag(x_68) == 1)
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_68, sizeof(void*)*4);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_86; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
x_72 = lean_ctor_get(x_68, 2);
x_73 = lean_ctor_get(x_68, 3);
x_86 = !lean_is_exclusive(x_68);
if (x_86 == 0)
{
x_74 = x_68;
x_75 = x_86;
goto block_85;
}
else
{
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_74 = lean_box(0);
x_75 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 3, x_70);
lean_ctor_set(x_74, 2, x_6);
lean_ctor_set(x_74, 1, x_5);
lean_ctor_set(x_74, 0, x_4);
x_76 = x_74;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_5);
lean_ctor_set(x_84, 2, x_6);
lean_ctor_set(x_84, 3, x_70);
x_76 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_77; 
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_3);
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_73);
x_77 = x_66;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_10);
lean_ctor_set(x_82, 2, x_11);
lean_ctor_set(x_82, 3, x_12);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_3);
if (x_61 == 0)
{
lean_ctor_set(x_60, 3, x_77);
lean_ctor_set(x_60, 2, x_72);
lean_ctor_set(x_60, 1, x_71);
lean_ctor_set(x_60, 0, x_76);
x_78 = x_60;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_69);
return x_78;
}
}
}
}
}
else
{
lean_del_object(x_66);
lean_del_object(x_60);
x_13 = x_68;
goto block_16;
}
}
else
{
lean_del_object(x_66);
lean_del_object(x_60);
x_13 = x_68;
goto block_16;
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_3);
x_15 = l_Lean_RBNode_balLeft___redArg(x_4, x_5, x_6, x_14);
return x_15;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_3);
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_6);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_3);
return x_19;
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
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_apply_2(x_4, x_1, lean_box(0));
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
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
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_dec_ref(x_2);
x_26 = lean_apply_7(x_7, x_1, x_22, x_23, x_24, x_25, lean_box(0), lean_box(0));
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_5);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec_ref(x_1);
x_32 = lean_apply_7(x_8, x_28, x_29, x_30, x_31, x_2, lean_box(0), lean_box(0));
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 3);
lean_inc(x_40);
lean_dec_ref(x_2);
x_41 = lean_apply_8(x_6, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
return x_41;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_apply_1(x_6, x_5);
return x_12;
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_apply_2(x_7, x_4, lean_box(0));
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*4);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_9);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
lean_dec_ref(x_4);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 3);
lean_inc(x_23);
lean_dec_ref(x_5);
x_24 = lean_apply_8(x_8, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
lean_dec_ref(x_5);
x_29 = lean_apply_7(x_10, x_4, x_25, x_26, x_27, x_28, lean_box(0), lean_box(0));
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_8);
x_30 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 3);
lean_inc(x_34);
lean_dec_ref(x_4);
x_35 = lean_apply_7(x_11, x_31, x_32, x_33, x_34, x_5, lean_box(0), lean_box(0));
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 3);
lean_inc(x_39);
lean_dec_ref(x_4);
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_5, 3);
lean_inc(x_43);
lean_dec_ref(x_5);
x_44 = lean_apply_8(x_9, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_2(x_3, x_1, lean_box(0));
return x_10;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_apply_2(x_6, x_4, lean_box(0));
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_apply_2(x_6, x_4, lean_box(0));
return x_14;
}
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_30; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
x_8 = x_3;
x_9 = x_30;
goto block_29;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_10 = lean_apply_2(x_1, x_2, x_5);
x_11 = lean_unbox(x_10);
switch (x_11) {
case 0:
{
uint8_t x_12; 
x_12 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = l_Lean_RBNode_del___redArg(x_1, x_2, x_4);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_14);
x_15 = x_8;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_7);
x_15 = x_17;
goto block_16;
}
block_16:
{
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_13);
return x_15;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_del_object(x_8);
x_18 = l_Lean_RBNode_del___redArg(x_1, x_2, x_4);
x_19 = l_Lean_RBNode_balLeft___redArg(x_18, x_5, x_6, x_7);
return x_19;
}
}
case 1:
{
lean_object* x_20; 
lean_del_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_20;
}
default: 
{
uint8_t x_21; 
x_21 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = l_Lean_RBNode_del___redArg(x_1, x_2, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 3, x_23);
x_24 = x_8;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 2, x_6);
lean_ctor_set(x_26, 3, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_22);
return x_24;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_del_object(x_8);
x_27 = l_Lean_RBNode_del___redArg(x_1, x_2, x_7);
x_28 = l_Lean_RBNode_balRight___redArg(x_4, x_5, x_6, x_27);
return x_28;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_RBNode_mapM___redArg___lam__3(x_6, x_2, x_3, x_4, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_mapM___redArg(x_1, x_2, x_3);
return x_5;
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_18; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_9 = x_2;
x_10 = x_18;
goto block_17;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_11 = l_Lean_RBNode_map___redArg(x_1, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_2(x_1, x_6, x_7);
x_13 = l_Lean_RBNode_map___redArg(x_1, x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_13);
lean_ctor_set(x_9, 2, x_12);
lean_ctor_set(x_9, 0, x_11);
x_14 = x_9;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_4);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(x_1, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
x_3 = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(x_2, x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_toArray___redArg(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBMap_depth___redArg(x_1, x_2);
lean_dec(x_2);
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
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isSingleton___redArg(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(x_9, 0, x_5);
x_10 = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(x_1, x_9, x_3, x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBMap_instForInProdOfMonad(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
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
x_2 = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
x_3 = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
x_5 = x_2;
x_6 = x_20;
goto block_19;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_18; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
x_9 = x_4;
x_10 = x_18;
goto block_17;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_11);
x_12 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_5, 0);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
x_8 = x_5;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_21; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
x_12 = x_7;
x_13 = x_21;
goto block_20;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_14);
x_15 = x_8;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
x_5 = x_2;
x_6 = x_20;
goto block_19;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_18; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
x_9 = x_4;
x_10 = x_18;
goto block_17;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_8);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_11);
x_12 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_23; 
x_7 = lean_ctor_get(x_5, 0);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
x_8 = x_5;
x_9 = x_23;
goto block_22;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_21; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
x_12 = x_7;
x_13 = x_21;
goto block_20;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_14);
x_15 = x_8;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
x_5 = l_Lean_RBMap_toList___redArg(x_2);
x_6 = l_List_repr___redArg(x_1, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_3);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_2);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_findD___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_RBMap_contains___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_7 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_3;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_1, x_10, x_11, x_3);
return x_12;
}
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_8, x_1, x_13, x_14, x_3);
return x_15;
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
x_8 = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
if (x_9 == 0)
{
lean_dec_ref(x_10);
lean_dec_ref(x_3);
return x_5;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_8, x_10, x_3, x_12, x_13, x_5);
return x_14;
}
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_8, x_10, x_3, x_15, x_16, x_5);
return x_17;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBMap_all___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBMap_any___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(x_2, x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_size___redArg(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
x_3 = l_Lean_RBNode_depth___redArg(x_2, x_1);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBMap_maxDepth___redArg(x_4);
return x_5;
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
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(384u);
x_4 = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
x_5 = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
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
x_6 = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
x_7 = l_panic___redArg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_11 = x_8;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
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
x_9 = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
x_10 = l_panic___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_14 = x_11;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
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
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(389u);
x_4 = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
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
x_6 = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
x_7 = l_panic___redArg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_8, 0);
x_10 = lean_ctor_get(x_8, 1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_11 = x_8;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
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
x_9 = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
x_10 = l_panic___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_14 = x_11;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
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
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(395u);
x_4 = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
x_5 = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
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
x_6 = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
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
x_8 = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_12 = x_2;
x_13 = x_28;
goto block_27;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc(x_3);
x_14 = lean_apply_2(x_1, x_3, x_9);
x_15 = lean_unbox(x_14);
switch (x_15) {
case 0:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_8, x_3, x_4);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_16);
x_17 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 3, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_7);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
case 1:
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 1, x_3);
x_20 = x_12;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_11);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_11, x_3, x_4);
if (x_13 == 0)
{
lean_ctor_set(x_12, 3, x_23);
x_24 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_9);
lean_ctor_set(x_26, 2, x_10);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_7);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_191; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_191 = !lean_is_exclusive(x_2);
if (x_191 == 0)
{
x_33 = x_2;
x_34 = x_191;
goto block_190;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_35; uint8_t x_36; 
lean_inc_ref(x_1);
lean_inc(x_30);
lean_inc(x_3);
x_35 = lean_apply_2(x_1, x_3, x_30);
x_36 = lean_unbox(x_35);
switch (x_36) {
case 0:
{
lean_object* x_37; 
x_37 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_29, x_3, x_4);
if (lean_obj_tag(x_37) == 1)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 3);
lean_inc(x_42);
if (x_38 == 0)
{
if (lean_obj_tag(x_39) == 1)
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_37);
x_60 = lean_ctor_get(x_39, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_39, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_39, 3);
lean_inc(x_63);
lean_dec_ref(x_39);
x_43 = x_60;
x_44 = x_61;
x_45 = x_62;
x_46 = x_63;
x_47 = x_40;
x_48 = x_41;
x_49 = x_42;
x_50 = x_30;
x_51 = x_31;
x_52 = x_32;
goto block_58;
}
else
{
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_64; 
x_64 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_37);
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_42, 3);
lean_inc(x_68);
lean_dec_ref(x_42);
x_43 = x_39;
x_44 = x_40;
x_45 = x_41;
x_46 = x_65;
x_47 = x_66;
x_48 = x_67;
x_49 = x_68;
x_50 = x_30;
x_51 = x_31;
x_52 = x_32;
goto block_58;
}
else
{
lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec_ref(x_39);
lean_dec(x_41);
lean_dec(x_40);
lean_del_object(x_33);
x_75 = !lean_is_exclusive(x_42);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_42, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_42, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_42, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_42, 0);
lean_dec(x_79);
x_69 = x_42;
x_70 = x_75;
goto block_74;
}
else
{
lean_dec(x_42);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
lean_ctor_set(x_69, 3, x_32);
lean_ctor_set(x_69, 2, x_31);
lean_ctor_set(x_69, 1, x_30);
lean_ctor_set(x_69, 0, x_37);
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_30);
lean_ctor_set(x_73, 2, x_31);
lean_ctor_set(x_73, 3, x_32);
x_71 = x_73;
goto block_72;
}
block_72:
{
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_7);
return x_71;
}
}
}
}
else
{
lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_del_object(x_33);
x_86 = !lean_is_exclusive(x_39);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_39, 3);
lean_dec(x_87);
x_88 = lean_ctor_get(x_39, 2);
lean_dec(x_88);
x_89 = lean_ctor_get(x_39, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_39, 0);
lean_dec(x_90);
x_80 = x_39;
x_81 = x_86;
goto block_85;
}
else
{
lean_dec(x_39);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 3, x_32);
lean_ctor_set(x_80, 2, x_31);
lean_ctor_set(x_80, 1, x_30);
lean_ctor_set(x_80, 0, x_37);
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_37);
lean_ctor_set(x_84, 1, x_30);
lean_ctor_set(x_84, 2, x_31);
lean_ctor_set(x_84, 3, x_32);
x_82 = x_84;
goto block_83;
}
block_83:
{
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_7);
return x_82;
}
}
}
}
}
else
{
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_37);
x_92 = lean_ctor_get(x_42, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_42, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_42, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_42, 3);
lean_inc(x_95);
lean_dec_ref(x_42);
x_43 = x_39;
x_44 = x_40;
x_45 = x_41;
x_46 = x_92;
x_47 = x_93;
x_48 = x_94;
x_49 = x_95;
x_50 = x_30;
x_51 = x_31;
x_52 = x_32;
goto block_58;
}
else
{
lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_33);
x_102 = !lean_is_exclusive(x_42);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_42, 3);
lean_dec(x_103);
x_104 = lean_ctor_get(x_42, 2);
lean_dec(x_104);
x_105 = lean_ctor_get(x_42, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_42, 0);
lean_dec(x_106);
x_96 = x_42;
x_97 = x_102;
goto block_101;
}
else
{
lean_dec(x_42);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
lean_ctor_set(x_96, 3, x_32);
lean_ctor_set(x_96, 2, x_31);
lean_ctor_set(x_96, 1, x_30);
lean_ctor_set(x_96, 0, x_37);
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_100, 0, x_37);
lean_ctor_set(x_100, 1, x_30);
lean_ctor_set(x_100, 2, x_31);
lean_ctor_set(x_100, 3, x_32);
x_98 = x_100;
goto block_99;
}
block_99:
{
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_7);
return x_98;
}
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_33);
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_37);
lean_ctor_set(x_107, 1, x_30);
lean_ctor_set(x_107, 2, x_31);
lean_ctor_set(x_107, 3, x_32);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_7);
return x_107;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_33);
x_108 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_108, 0, x_37);
lean_ctor_set(x_108, 1, x_30);
lean_ctor_set(x_108, 2, x_31);
lean_ctor_set(x_108, 3, x_32);
lean_ctor_set_uint8(x_108, sizeof(void*)*4, x_7);
return x_108;
}
block_58:
{
lean_object* x_53; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_46);
lean_ctor_set(x_33, 2, x_45);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_43);
x_53 = x_33;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_45);
lean_ctor_set(x_57, 3, x_46);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
x_53 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_7);
x_55 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_38);
return x_55;
}
}
}
else
{
lean_object* x_109; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_37);
x_109 = x_33;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_37);
lean_ctor_set(x_111, 1, x_30);
lean_ctor_set(x_111, 2, x_31);
lean_ctor_set(x_111, 3, x_32);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_7);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
case 1:
{
lean_object* x_112; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
if (x_34 == 0)
{
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 1, x_3);
x_112 = x_33;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_29);
lean_ctor_set(x_114, 1, x_3);
lean_ctor_set(x_114, 2, x_4);
lean_ctor_set(x_114, 3, x_32);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
default: 
{
lean_object* x_115; 
x_115 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_32, x_3, x_4);
if (lean_obj_tag(x_115) == 1)
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 1)
{
uint8_t x_137; 
x_137 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_115);
x_138 = lean_ctor_get(x_117, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_117, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_117, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_117, 3);
lean_inc(x_141);
lean_dec_ref(x_117);
x_121 = x_29;
x_122 = x_30;
x_123 = x_31;
x_124 = x_138;
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_136;
}
else
{
if (lean_obj_tag(x_120) == 1)
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_115);
x_143 = lean_ctor_get(x_120, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_120, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 3);
lean_inc(x_146);
lean_dec_ref(x_120);
x_121 = x_29;
x_122 = x_30;
x_123 = x_31;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_143;
x_128 = x_144;
x_129 = x_145;
x_130 = x_146;
goto block_136;
}
else
{
lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_dec_ref(x_117);
lean_dec(x_119);
lean_dec(x_118);
lean_del_object(x_33);
x_153 = !lean_is_exclusive(x_120);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_120, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_120, 2);
lean_dec(x_155);
x_156 = lean_ctor_get(x_120, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_120, 0);
lean_dec(x_157);
x_147 = x_120;
x_148 = x_153;
goto block_152;
}
else
{
lean_dec(x_120);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
lean_ctor_set(x_147, 3, x_115);
lean_ctor_set(x_147, 2, x_31);
lean_ctor_set(x_147, 1, x_30);
lean_ctor_set(x_147, 0, x_29);
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_29);
lean_ctor_set(x_151, 1, x_30);
lean_ctor_set(x_151, 2, x_31);
lean_ctor_set(x_151, 3, x_115);
x_149 = x_151;
goto block_150;
}
block_150:
{
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_7);
return x_149;
}
}
}
}
else
{
lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_del_object(x_33);
x_164 = !lean_is_exclusive(x_117);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_117, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_117, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_117, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_117, 0);
lean_dec(x_168);
x_158 = x_117;
x_159 = x_164;
goto block_163;
}
else
{
lean_dec(x_117);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
lean_ctor_set(x_158, 3, x_115);
lean_ctor_set(x_158, 2, x_31);
lean_ctor_set(x_158, 1, x_30);
lean_ctor_set(x_158, 0, x_29);
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_29);
lean_ctor_set(x_162, 1, x_30);
lean_ctor_set(x_162, 2, x_31);
lean_ctor_set(x_162, 3, x_115);
x_160 = x_162;
goto block_161;
}
block_161:
{
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_7);
return x_160;
}
}
}
}
}
else
{
if (lean_obj_tag(x_120) == 1)
{
uint8_t x_169; 
x_169 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_115);
x_170 = lean_ctor_get(x_120, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_120, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 3);
lean_inc(x_173);
lean_dec_ref(x_120);
x_121 = x_29;
x_122 = x_30;
x_123 = x_31;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_170;
x_128 = x_171;
x_129 = x_172;
x_130 = x_173;
goto block_136;
}
else
{
lean_object* x_174; uint8_t x_175; uint8_t x_180; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_del_object(x_33);
x_180 = !lean_is_exclusive(x_120);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_120, 3);
lean_dec(x_181);
x_182 = lean_ctor_get(x_120, 2);
lean_dec(x_182);
x_183 = lean_ctor_get(x_120, 1);
lean_dec(x_183);
x_184 = lean_ctor_get(x_120, 0);
lean_dec(x_184);
x_174 = x_120;
x_175 = x_180;
goto block_179;
}
else
{
lean_dec(x_120);
x_174 = lean_box(0);
x_175 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_176; 
if (x_175 == 0)
{
lean_ctor_set(x_174, 3, x_115);
lean_ctor_set(x_174, 2, x_31);
lean_ctor_set(x_174, 1, x_30);
lean_ctor_set(x_174, 0, x_29);
x_176 = x_174;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_29);
lean_ctor_set(x_178, 1, x_30);
lean_ctor_set(x_178, 2, x_31);
lean_ctor_set(x_178, 3, x_115);
x_176 = x_178;
goto block_177;
}
block_177:
{
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
}
}
}
else
{
lean_object* x_185; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_del_object(x_33);
x_185 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_185, 0, x_29);
lean_ctor_set(x_185, 1, x_30);
lean_ctor_set(x_185, 2, x_31);
lean_ctor_set(x_185, 3, x_115);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_7);
return x_185;
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_del_object(x_33);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_29);
lean_ctor_set(x_186, 1, x_30);
lean_ctor_set(x_186, 2, x_31);
lean_ctor_set(x_186, 3, x_115);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_7);
return x_186;
}
block_136:
{
lean_object* x_131; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_124);
lean_ctor_set(x_33, 2, x_123);
lean_ctor_set(x_33, 1, x_122);
lean_ctor_set(x_33, 0, x_121);
x_131 = x_33;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_122);
lean_ctor_set(x_135, 2, x_123);
lean_ctor_set(x_135, 3, x_124);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_7);
x_131 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
else
{
lean_object* x_187; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 3, x_115);
x_187 = x_33;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_29);
lean_ctor_set(x_189, 1, x_30);
lean_ctor_set(x_189, 2, x_31);
lean_ctor_set(x_189, 3, x_115);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_7);
x_187 = x_189;
goto block_188;
}
block_188:
{
return x_187;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___redArg(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(x_1, x_2, x_3, x_5);
lean_inc(x_6);
lean_inc(x_9);
lean_inc_ref(x_1);
x_14 = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(x_1, x_9, x_6);
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
x_11 = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(x_1, x_9, x_6, x_10);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
lean_inc(x_7);
lean_inc(x_1);
lean_inc_ref(x_2);
x_11 = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(x_2, x_1, x_7);
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
x_15 = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_10, x_7, x_14);
x_4 = x_15;
x_5 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(x_4, x_1, x_2, x_5, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(x_1, x_2, x_3, x_5);
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
x_13 = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_9, x_6, x_7);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(x_2, x_1, x_4, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(x_1, x_2, x_3, x_5);
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
x_13 = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(x_2, x_9, x_6, x_12);
x_3 = x_13;
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(x_2, x_1, x_4, x_3);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(x_2, x_3, x_1);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_RBMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Ord_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_RBMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RBMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RBMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_RBMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_RBMap(builtin);
}
#ifdef __cplusplus
}
#endif
