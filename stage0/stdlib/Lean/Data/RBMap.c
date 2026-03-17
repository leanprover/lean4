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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__0 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__0_value;
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__1 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__1_value;
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__2 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__2_value;
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__3 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__3_value;
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__4 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__4_value;
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__5 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__5_value;
static const lean_closure_object l_Lean_RBMap_fromArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__6 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__6_value;
static const lean_ctor_object l_Lean_RBMap_fromArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__0_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__1_value)}};
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__7 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__7_value;
static const lean_ctor_object l_Lean_RBMap_fromArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__7_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__2_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__3_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__4_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__5_value)}};
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__8 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__8_value;
static const lean_ctor_object l_Lean_RBMap_fromArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__8_value),((lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__6_value)}};
static const lean_object* l_Lean_RBMap_fromArray___redArg___closed__9 = (const lean_object*)&l_Lean_RBMap_fromArray___redArg___closed__9_value;
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
static lean_once_cell_t l_Lean_RBMap_min_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_RBMap_min_x21___redArg___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_RBColor_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_RBColor_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Lean_RBColor_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_RBColor_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Lean_RBColor_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg(lean_object* v_red_27_){
_start:
{
lean_inc(v_red_27_);
return v_red_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg___boxed(lean_object* v_red_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_RBColor_red_elim___redArg(v_red_28_);
lean_dec(v_red_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_red_33_){
_start:
{
lean_inc(v_red_33_);
return v_red_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_red_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Lean_RBColor_red_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_red_37_);
lean_dec(v_red_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg(lean_object* v_black_40_){
_start:
{
lean_inc(v_black_40_);
return v_black_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg___boxed(lean_object* v_black_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_RBColor_black_elim___redArg(v_black_41_);
lean_dec(v_black_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_black_46_){
_start:
{
lean_inc(v_black_46_);
return v_black_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_black_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Lean_RBColor_black_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_black_50_);
lean_dec(v_black_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg(lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_unsigned_to_nat(0u);
return v___x_54_;
}
else
{
lean_object* v___x_55_; 
v___x_55_ = lean_unsigned_to_nat(1u);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg___boxed(lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_RBNode_ctorIdx___redArg(v_x_56_);
lean_dec(v_x_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx(lean_object* v_00_u03b1_58_, lean_object* v_00_u03b2_59_, lean_object* v_x_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_RBNode_ctorIdx___redArg(v_x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___boxed(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_RBNode_ctorIdx(v_00_u03b1_62_, v_00_u03b2_63_, v_x_64_);
lean_dec(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___redArg(lean_object* v_t_66_, lean_object* v_k_67_){
_start:
{
if (lean_obj_tag(v_t_66_) == 0)
{
return v_k_67_;
}
else
{
uint8_t v_color_68_; lean_object* v_lchild_69_; lean_object* v_key_70_; lean_object* v_val_71_; lean_object* v_rchild_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_color_68_ = lean_ctor_get_uint8(v_t_66_, sizeof(void*)*4);
v_lchild_69_ = lean_ctor_get(v_t_66_, 0);
lean_inc(v_lchild_69_);
v_key_70_ = lean_ctor_get(v_t_66_, 1);
lean_inc(v_key_70_);
v_val_71_ = lean_ctor_get(v_t_66_, 2);
lean_inc(v_val_71_);
v_rchild_72_ = lean_ctor_get(v_t_66_, 3);
lean_inc(v_rchild_72_);
lean_dec_ref(v_t_66_);
v___x_73_ = lean_box(v_color_68_);
v___x_74_ = lean_apply_5(v_k_67_, v___x_73_, v_lchild_69_, v_key_70_, v_val_71_, v_rchild_72_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_RBNode_ctorElim___redArg(v_t_79_, v_k_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___boxed(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_motive_85_, lean_object* v_ctorIdx_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_k_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_RBNode_ctorElim(v_00_u03b1_83_, v_00_u03b2_84_, v_motive_85_, v_ctorIdx_86_, v_t_87_, v_h_88_, v_k_89_);
lean_dec(v_ctorIdx_86_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim___redArg(lean_object* v_t_91_, lean_object* v_leaf_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_RBNode_ctorElim___redArg(v_t_91_, v_leaf_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_leaf_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_RBNode_ctorElim___redArg(v_t_97_, v_leaf_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim___redArg(lean_object* v_t_101_, lean_object* v_node_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_RBNode_ctorElim___redArg(v_t_101_, v_node_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim(lean_object* v_00_u03b1_104_, lean_object* v_00_u03b2_105_, lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_node_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_RBNode_ctorElim___redArg(v_t_107_, v_node_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object* v_f_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v___x_113_; 
lean_dec_ref(v_f_111_);
v___x_113_ = lean_unsigned_to_nat(0u);
return v___x_113_;
}
else
{
lean_object* v_lchild_114_; lean_object* v_rchild_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_lchild_114_ = lean_ctor_get(v_x_112_, 0);
v_rchild_115_ = lean_ctor_get(v_x_112_, 3);
lean_inc_ref(v_f_111_);
v___x_116_ = l_Lean_RBNode_depth___redArg(v_f_111_, v_lchild_114_);
lean_inc_ref(v_f_111_);
v___x_117_ = l_Lean_RBNode_depth___redArg(v_f_111_, v_rchild_115_);
v___x_118_ = lean_apply_2(v_f_111_, v___x_116_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object* v_f_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_RBNode_depth___redArg(v_f_121_, v_x_122_);
lean_dec(v_x_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_f_126_, lean_object* v_x_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_RBNode_depth___redArg(v_f_126_, v_x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_f_131_, lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_RBNode_depth(v_00_u03b1_129_, v_00_u03b2_130_, v_f_131_, v_x_132_);
lean_dec(v_x_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_135_; 
v___x_135_ = lean_box(0);
return v___x_135_;
}
else
{
lean_object* v_lchild_136_; 
v_lchild_136_ = lean_ctor_get(v_x_134_, 0);
if (lean_obj_tag(v_lchild_136_) == 0)
{
lean_object* v_key_137_; lean_object* v_val_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_key_137_ = lean_ctor_get(v_x_134_, 1);
v_val_138_ = lean_ctor_get(v_x_134_, 2);
lean_inc(v_val_138_);
lean_inc(v_key_137_);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_key_137_);
lean_ctor_set(v___x_139_, 1, v_val_138_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
else
{
v_x_134_ = v_lchild_136_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_RBNode_min___redArg(v_x_142_);
lean_dec(v_x_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_RBNode_min___redArg(v_x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_RBNode_min(v_00_u03b1_148_, v_00_u03b2_149_, v_x_150_);
lean_dec(v_x_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_rchild_154_; 
v_rchild_154_ = lean_ctor_get(v_x_152_, 3);
if (lean_obj_tag(v_rchild_154_) == 0)
{
lean_object* v_key_155_; lean_object* v_val_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_key_155_ = lean_ctor_get(v_x_152_, 1);
v_val_156_ = lean_ctor_get(v_x_152_, 2);
lean_inc(v_val_156_);
lean_inc(v_key_155_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_key_155_);
lean_ctor_set(v___x_157_, 1, v_val_156_);
v___x_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
else
{
v_x_152_ = v_rchild_154_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object* v_x_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_RBNode_max___redArg(v_x_160_);
lean_dec(v_x_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object* v_00_u03b1_162_, lean_object* v_00_u03b2_163_, lean_object* v_x_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_RBNode_max___redArg(v_x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_RBNode_max(v_00_u03b1_166_, v_00_u03b2_167_, v_x_168_);
lean_dec(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object* v_f_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_dec(v_f_170_);
return v_x_171_;
}
else
{
lean_object* v_lchild_173_; lean_object* v_key_174_; lean_object* v_val_175_; lean_object* v_rchild_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_lchild_173_ = lean_ctor_get(v_x_172_, 0);
lean_inc(v_lchild_173_);
v_key_174_ = lean_ctor_get(v_x_172_, 1);
lean_inc(v_key_174_);
v_val_175_ = lean_ctor_get(v_x_172_, 2);
lean_inc(v_val_175_);
v_rchild_176_ = lean_ctor_get(v_x_172_, 3);
lean_inc(v_rchild_176_);
lean_dec_ref(v_x_172_);
lean_inc(v_f_170_);
v___x_177_ = l_Lean_RBNode_fold___redArg(v_f_170_, v_x_171_, v_lchild_173_);
lean_inc(v_f_170_);
v___x_178_ = lean_apply_3(v_f_170_, v___x_177_, v_key_174_, v_val_175_);
v_x_171_ = v___x_178_;
v_x_172_ = v_rchild_176_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_00_u03c3_182_, lean_object* v_f_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_RBNode_fold___redArg(v_f_183_, v_x_184_, v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object* v_f_187_, lean_object* v_key_188_, lean_object* v_val_189_, lean_object* v_toBind_190_, lean_object* v___f_191_, lean_object* v_____r_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_apply_2(v_f_187_, v_key_188_, v_val_189_);
v___x_194_ = lean_apply_4(v_toBind_190_, lean_box(0), lean_box(0), v___x_193_, v___f_191_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object* v_inst_195_, lean_object* v_f_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v_toApplicative_198_; lean_object* v_toPure_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_toApplicative_198_ = lean_ctor_get(v_inst_195_, 0);
lean_inc_ref(v_toApplicative_198_);
lean_dec(v_f_196_);
lean_dec_ref(v_inst_195_);
v_toPure_199_ = lean_ctor_get(v_toApplicative_198_, 1);
lean_inc(v_toPure_199_);
lean_dec_ref(v_toApplicative_198_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_2(v_toPure_199_, lean_box(0), v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_toBind_202_; lean_object* v_lchild_203_; lean_object* v_key_204_; lean_object* v_val_205_; lean_object* v_rchild_206_; lean_object* v___f_207_; lean_object* v___f_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_toBind_202_ = lean_ctor_get(v_inst_195_, 1);
lean_inc(v_toBind_202_);
v_lchild_203_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_lchild_203_);
v_key_204_ = lean_ctor_get(v_x_197_, 1);
lean_inc(v_key_204_);
v_val_205_ = lean_ctor_get(v_x_197_, 2);
lean_inc(v_val_205_);
v_rchild_206_ = lean_ctor_get(v_x_197_, 3);
lean_inc(v_rchild_206_);
lean_dec_ref(v_x_197_);
lean_inc(v_f_196_);
lean_inc_ref(v_inst_195_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_207_, 0, v_inst_195_);
lean_closure_set(v___f_207_, 1, v_f_196_);
lean_closure_set(v___f_207_, 2, v_rchild_206_);
lean_inc(v_toBind_202_);
lean_inc(v_f_196_);
v___f_208_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_208_, 0, v_f_196_);
lean_closure_set(v___f_208_, 1, v_key_204_);
lean_closure_set(v___f_208_, 2, v_val_205_);
lean_closure_set(v___f_208_, 3, v_toBind_202_);
lean_closure_set(v___f_208_, 4, v___f_207_);
v___x_209_ = l_Lean_RBNode_forM___redArg(v_inst_195_, v_f_196_, v_lchild_203_);
v___x_210_ = lean_apply_4(v_toBind_202_, lean_box(0), lean_box(0), v___x_209_, v___f_208_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object* v_inst_211_, lean_object* v_f_212_, lean_object* v_rchild_213_, lean_object* v_____r_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_RBNode_forM___redArg(v_inst_211_, v_f_212_, v_rchild_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object* v_00_u03b1_216_, lean_object* v_00_u03b2_217_, lean_object* v_m_218_, lean_object* v_inst_219_, lean_object* v_f_220_, lean_object* v_x_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_RBNode_forM___redArg(v_inst_219_, v_f_220_, v_x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object* v_f_223_, lean_object* v_key_224_, lean_object* v_val_225_, lean_object* v_toBind_226_, lean_object* v___f_227_, lean_object* v_b_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_apply_3(v_f_223_, v_b_228_, v_key_224_, v_val_225_);
v___x_230_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_229_, v___f_227_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object* v_inst_231_, lean_object* v_f_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v_toApplicative_235_; lean_object* v_toPure_236_; lean_object* v___x_237_; 
v_toApplicative_235_ = lean_ctor_get(v_inst_231_, 0);
lean_inc_ref(v_toApplicative_235_);
lean_dec(v_f_232_);
lean_dec_ref(v_inst_231_);
v_toPure_236_ = lean_ctor_get(v_toApplicative_235_, 1);
lean_inc(v_toPure_236_);
lean_dec_ref(v_toApplicative_235_);
v___x_237_ = lean_apply_2(v_toPure_236_, lean_box(0), v_x_233_);
return v___x_237_;
}
else
{
lean_object* v_toBind_238_; lean_object* v_lchild_239_; lean_object* v_key_240_; lean_object* v_val_241_; lean_object* v_rchild_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_toBind_238_ = lean_ctor_get(v_inst_231_, 1);
lean_inc(v_toBind_238_);
v_lchild_239_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_lchild_239_);
v_key_240_ = lean_ctor_get(v_x_234_, 1);
lean_inc(v_key_240_);
v_val_241_ = lean_ctor_get(v_x_234_, 2);
lean_inc(v_val_241_);
v_rchild_242_ = lean_ctor_get(v_x_234_, 3);
lean_inc(v_rchild_242_);
lean_dec_ref(v_x_234_);
lean_inc(v_f_232_);
lean_inc_ref(v_inst_231_);
v___f_243_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_243_, 0, v_inst_231_);
lean_closure_set(v___f_243_, 1, v_f_232_);
lean_closure_set(v___f_243_, 2, v_rchild_242_);
lean_inc(v_toBind_238_);
lean_inc(v_f_232_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_244_, 0, v_f_232_);
lean_closure_set(v___f_244_, 1, v_key_240_);
lean_closure_set(v___f_244_, 2, v_val_241_);
lean_closure_set(v___f_244_, 3, v_toBind_238_);
lean_closure_set(v___f_244_, 4, v___f_243_);
v___x_245_ = l_Lean_RBNode_foldM___redArg(v_inst_231_, v_f_232_, v_x_233_, v_lchild_239_);
v___x_246_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v___x_245_, v___f_244_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object* v_inst_247_, lean_object* v_f_248_, lean_object* v_rchild_249_, lean_object* v_b_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_RBNode_foldM___redArg(v_inst_247_, v_f_248_, v_b_250_, v_rchild_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_00_u03c3_254_, lean_object* v_m_255_, lean_object* v_inst_256_, lean_object* v_f_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_RBNode_foldM___redArg(v_inst_256_, v_f_257_, v_x_258_, v_x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object* v_toPure_261_, lean_object* v_f_262_, lean_object* v_key_263_, lean_object* v_val_264_, lean_object* v_toBind_265_, lean_object* v___f_266_, lean_object* v_____do__lift_267_){
_start:
{
if (lean_obj_tag(v_____do__lift_267_) == 0)
{
lean_object* v___x_268_; 
lean_dec(v___f_266_);
lean_dec(v_toBind_265_);
lean_dec(v_val_264_);
lean_dec(v_key_263_);
lean_dec(v_f_262_);
v___x_268_ = lean_apply_2(v_toPure_261_, lean_box(0), v_____do__lift_267_);
return v___x_268_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_toPure_261_);
v_a_269_ = lean_ctor_get(v_____do__lift_267_, 0);
lean_inc(v_a_269_);
lean_dec_ref(v_____do__lift_267_);
v___x_270_ = lean_apply_3(v_f_262_, v_key_263_, v_val_264_, v_a_269_);
v___x_271_ = lean_apply_4(v_toBind_265_, lean_box(0), lean_box(0), v___x_270_, v___f_266_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object* v_inst_272_, lean_object* v_f_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
if (lean_obj_tag(v_a_274_) == 0)
{
lean_object* v_toApplicative_276_; lean_object* v_toPure_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_toApplicative_276_ = lean_ctor_get(v_inst_272_, 0);
lean_inc_ref(v_toApplicative_276_);
lean_dec(v_f_273_);
lean_dec_ref(v_inst_272_);
v_toPure_277_ = lean_ctor_get(v_toApplicative_276_, 1);
lean_inc(v_toPure_277_);
lean_dec_ref(v_toApplicative_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v_a_275_);
v___x_279_ = lean_apply_2(v_toPure_277_, lean_box(0), v___x_278_);
return v___x_279_;
}
else
{
lean_object* v_toApplicative_280_; lean_object* v_toBind_281_; lean_object* v_toPure_282_; lean_object* v_lchild_283_; lean_object* v_key_284_; lean_object* v_val_285_; lean_object* v_rchild_286_; lean_object* v___f_287_; lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_toApplicative_280_ = lean_ctor_get(v_inst_272_, 0);
v_toBind_281_ = lean_ctor_get(v_inst_272_, 1);
lean_inc(v_toBind_281_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_280_, 1);
v_lchild_283_ = lean_ctor_get(v_a_274_, 0);
lean_inc(v_lchild_283_);
v_key_284_ = lean_ctor_get(v_a_274_, 1);
lean_inc(v_key_284_);
v_val_285_ = lean_ctor_get(v_a_274_, 2);
lean_inc(v_val_285_);
v_rchild_286_ = lean_ctor_get(v_a_274_, 3);
lean_inc(v_rchild_286_);
lean_dec_ref(v_a_274_);
lean_inc(v_f_273_);
lean_inc_ref(v_inst_272_);
lean_inc(v_toPure_282_);
v___f_287_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0), 5, 4);
lean_closure_set(v___f_287_, 0, v_toPure_282_);
lean_closure_set(v___f_287_, 1, v_inst_272_);
lean_closure_set(v___f_287_, 2, v_f_273_);
lean_closure_set(v___f_287_, 3, v_rchild_286_);
lean_inc(v_toBind_281_);
lean_inc(v_f_273_);
lean_inc(v_toPure_282_);
v___f_288_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1), 7, 6);
lean_closure_set(v___f_288_, 0, v_toPure_282_);
lean_closure_set(v___f_288_, 1, v_f_273_);
lean_closure_set(v___f_288_, 2, v_key_284_);
lean_closure_set(v___f_288_, 3, v_val_285_);
lean_closure_set(v___f_288_, 4, v_toBind_281_);
lean_closure_set(v___f_288_, 5, v___f_287_);
v___x_289_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_272_, v_f_273_, v_lchild_283_, v_a_275_);
v___x_290_ = lean_apply_4(v_toBind_281_, lean_box(0), lean_box(0), v___x_289_, v___f_288_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object* v_toPure_291_, lean_object* v_inst_292_, lean_object* v_f_293_, lean_object* v_rchild_294_, lean_object* v_____do__lift_295_){
_start:
{
if (lean_obj_tag(v_____do__lift_295_) == 0)
{
lean_object* v___x_296_; 
lean_dec(v_rchild_294_);
lean_dec(v_f_293_);
lean_dec_ref(v_inst_292_);
v___x_296_ = lean_apply_2(v_toPure_291_, lean_box(0), v_____do__lift_295_);
return v___x_296_;
}
else
{
lean_object* v_a_297_; lean_object* v___x_298_; 
lean_dec(v_toPure_291_);
v_a_297_ = lean_ctor_get(v_____do__lift_295_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v_____do__lift_295_);
v___x_298_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_292_, v_f_293_, v_rchild_294_, v_a_297_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_00_u03c3_301_, lean_object* v_m_302_, lean_object* v_inst_303_, lean_object* v_f_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_303_, v_f_304_, v_a_305_, v_a_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object* v_toPure_308_, lean_object* v_____do__lift_309_){
_start:
{
lean_object* v_a_310_; lean_object* v___x_311_; 
v_a_310_ = lean_ctor_get(v_____do__lift_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref(v_____do__lift_309_);
v___x_311_ = lean_apply_2(v_toPure_308_, lean_box(0), v_a_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object* v_inst_312_, lean_object* v_as_313_, lean_object* v_init_314_, lean_object* v_f_315_){
_start:
{
lean_object* v_toApplicative_316_; lean_object* v_toBind_317_; lean_object* v_toPure_318_; lean_object* v___x_319_; lean_object* v___f_320_; lean_object* v___x_321_; 
v_toApplicative_316_ = lean_ctor_get(v_inst_312_, 0);
v_toBind_317_ = lean_ctor_get(v_inst_312_, 1);
lean_inc(v_toBind_317_);
v_toPure_318_ = lean_ctor_get(v_toApplicative_316_, 1);
lean_inc(v_toPure_318_);
v___x_319_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_312_, v_f_315_, v_as_313_, v_init_314_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_320_, 0, v_toPure_318_);
v___x_321_ = lean_apply_4(v_toBind_317_, lean_box(0), lean_box(0), v___x_319_, v___f_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_00_u03c3_324_, lean_object* v_m_325_, lean_object* v_inst_326_, lean_object* v_as_327_, lean_object* v_init_328_, lean_object* v_f_329_){
_start:
{
lean_object* v_toApplicative_330_; lean_object* v_toBind_331_; lean_object* v_toPure_332_; lean_object* v___x_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v_toApplicative_330_ = lean_ctor_get(v_inst_326_, 0);
v_toBind_331_ = lean_ctor_get(v_inst_326_, 1);
lean_inc(v_toBind_331_);
v_toPure_332_ = lean_ctor_get(v_toApplicative_330_, 1);
lean_inc(v_toPure_332_);
v___x_333_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_326_, v_f_329_, v_as_327_, v_init_328_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_334_, 0, v_toPure_332_);
v___x_335_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_333_, v___f_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object* v_f_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_dec(v_f_336_);
return v_x_337_;
}
else
{
lean_object* v_lchild_339_; lean_object* v_key_340_; lean_object* v_val_341_; lean_object* v_rchild_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_lchild_339_ = lean_ctor_get(v_x_338_, 0);
lean_inc(v_lchild_339_);
v_key_340_ = lean_ctor_get(v_x_338_, 1);
lean_inc(v_key_340_);
v_val_341_ = lean_ctor_get(v_x_338_, 2);
lean_inc(v_val_341_);
v_rchild_342_ = lean_ctor_get(v_x_338_, 3);
lean_inc(v_rchild_342_);
lean_dec_ref(v_x_338_);
lean_inc(v_f_336_);
v___x_343_ = l_Lean_RBNode_revFold___redArg(v_f_336_, v_x_337_, v_rchild_342_);
lean_inc(v_f_336_);
v___x_344_ = lean_apply_3(v_f_336_, v___x_343_, v_key_340_, v_val_341_);
v_x_337_ = v___x_344_;
v_x_338_ = v_lchild_339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_00_u03c3_348_, lean_object* v_f_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_RBNode_revFold___redArg(v_f_349_, v_x_350_, v_x_351_);
return v___x_352_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___redArg(lean_object* v_p_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
uint8_t v___x_355_; 
lean_dec_ref(v_p_353_);
v___x_355_ = 1;
return v___x_355_;
}
else
{
lean_object* v_lchild_356_; lean_object* v_key_357_; lean_object* v_val_358_; lean_object* v_rchild_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_lchild_356_ = lean_ctor_get(v_x_354_, 0);
lean_inc(v_lchild_356_);
v_key_357_ = lean_ctor_get(v_x_354_, 1);
lean_inc(v_key_357_);
v_val_358_ = lean_ctor_get(v_x_354_, 2);
lean_inc(v_val_358_);
v_rchild_359_ = lean_ctor_get(v_x_354_, 3);
lean_inc(v_rchild_359_);
lean_dec_ref(v_x_354_);
lean_inc_ref(v_p_353_);
v___x_360_ = lean_apply_2(v_p_353_, v_key_357_, v_val_358_);
v___x_361_ = lean_unbox(v___x_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
lean_dec(v_rchild_359_);
lean_dec(v_lchild_356_);
lean_dec_ref(v_p_353_);
v___x_362_ = lean_unbox(v___x_360_);
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
lean_inc_ref(v_p_353_);
v___x_363_ = l_Lean_RBNode_all___redArg(v_p_353_, v_lchild_356_);
if (v___x_363_ == 0)
{
lean_dec(v_rchild_359_);
lean_dec_ref(v_p_353_);
return v___x_363_;
}
else
{
v_x_354_ = v_rchild_359_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object* v_p_365_, lean_object* v_x_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Lean_RBNode_all___redArg(v_p_365_, v_x_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_p_371_, lean_object* v_x_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Lean_RBNode_all___redArg(v_p_371_, v_x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___boxed(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_p_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Lean_RBNode_all(v_00_u03b1_374_, v_00_u03b2_375_, v_p_376_, v_x_377_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any___redArg(lean_object* v_p_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v___x_382_; 
lean_dec_ref(v_p_380_);
v___x_382_ = 0;
return v___x_382_;
}
else
{
lean_object* v_lchild_383_; lean_object* v_key_384_; lean_object* v_val_385_; lean_object* v_rchild_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_lchild_383_ = lean_ctor_get(v_x_381_, 0);
lean_inc(v_lchild_383_);
v_key_384_ = lean_ctor_get(v_x_381_, 1);
lean_inc(v_key_384_);
v_val_385_ = lean_ctor_get(v_x_381_, 2);
lean_inc(v_val_385_);
v_rchild_386_ = lean_ctor_get(v_x_381_, 3);
lean_inc(v_rchild_386_);
lean_dec_ref(v_x_381_);
lean_inc_ref(v_p_380_);
v___x_387_ = lean_apply_2(v_p_380_, v_key_384_, v_val_385_);
v___x_388_ = lean_unbox(v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
lean_inc_ref(v_p_380_);
v___x_389_ = l_Lean_RBNode_any___redArg(v_p_380_, v_lchild_383_);
if (v___x_389_ == 0)
{
v_x_381_ = v_rchild_386_;
goto _start;
}
else
{
lean_dec(v_rchild_386_);
lean_dec_ref(v_p_380_);
return v___x_389_;
}
}
else
{
uint8_t v___x_391_; 
lean_dec(v_rchild_386_);
lean_dec(v_lchild_383_);
lean_dec_ref(v_p_380_);
v___x_391_ = lean_unbox(v___x_387_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object* v_p_392_, lean_object* v_x_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l_Lean_RBNode_any___redArg(v_p_392_, v_x_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_p_398_, lean_object* v_x_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_RBNode_any___redArg(v_p_398_, v_x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v_p_403_, lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_RBNode_any(v_00_u03b1_401_, v_00_u03b2_402_, v_p_403_, v_x_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object* v_k_407_, lean_object* v_v_408_){
_start:
{
uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = 0;
v___x_410_ = lean_box(0);
v___x_411_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_k_407_);
lean_ctor_set(v___x_411_, 2, v_v_408_);
lean_ctor_set(v___x_411_, 3, v___x_410_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*4, v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_k_414_, lean_object* v_v_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_RBNode_singleton___redArg(v_k_414_, v_v_415_);
return v___x_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 1)
{
lean_object* v_lchild_418_; 
v_lchild_418_ = lean_ctor_get(v_x_417_, 0);
if (lean_obj_tag(v_lchild_418_) == 0)
{
lean_object* v_rchild_419_; 
v_rchild_419_ = lean_ctor_get(v_x_417_, 3);
if (lean_obj_tag(v_rchild_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object* v_x_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_Lean_RBNode_isSingleton___redArg(v_x_424_);
lean_dec(v_x_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_x_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = l_Lean_RBNode_isSingleton___redArg(v_x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Lean_RBNode_isSingleton(v_00_u03b1_431_, v_00_u03b2_432_, v_x_433_);
lean_dec(v_x_433_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_a_441_; lean_object* v_kx_442_; lean_object* v_vx_443_; lean_object* v_b_444_; 
if (lean_obj_tag(v_x_436_) == 1)
{
uint8_t v_color_447_; lean_object* v_lchild_448_; lean_object* v_key_449_; lean_object* v_val_450_; lean_object* v_rchild_451_; lean_object* v_a_453_; lean_object* v_kx_454_; lean_object* v_vx_455_; lean_object* v_b_456_; lean_object* v_ky_457_; lean_object* v_vy_458_; lean_object* v_c_459_; lean_object* v_kz_460_; lean_object* v_vz_461_; lean_object* v_d_462_; 
v_color_447_ = lean_ctor_get_uint8(v_x_436_, sizeof(void*)*4);
v_lchild_448_ = lean_ctor_get(v_x_436_, 0);
v_key_449_ = lean_ctor_get(v_x_436_, 1);
v_val_450_ = lean_ctor_get(v_x_436_, 2);
v_rchild_451_ = lean_ctor_get(v_x_436_, 3);
if (v_color_447_ == 0)
{
if (lean_obj_tag(v_lchild_448_) == 1)
{
uint8_t v_color_467_; 
v_color_467_ = lean_ctor_get_uint8(v_lchild_448_, sizeof(void*)*4);
if (v_color_467_ == 0)
{
lean_object* v_lchild_468_; lean_object* v_key_469_; lean_object* v_val_470_; lean_object* v_rchild_471_; 
lean_inc_ref(v_lchild_448_);
lean_inc(v_rchild_451_);
lean_inc(v_val_450_);
lean_inc(v_key_449_);
lean_dec_ref(v_x_436_);
v_lchild_468_ = lean_ctor_get(v_lchild_448_, 0);
lean_inc(v_lchild_468_);
v_key_469_ = lean_ctor_get(v_lchild_448_, 1);
lean_inc(v_key_469_);
v_val_470_ = lean_ctor_get(v_lchild_448_, 2);
lean_inc(v_val_470_);
v_rchild_471_ = lean_ctor_get(v_lchild_448_, 3);
lean_inc(v_rchild_471_);
lean_dec_ref(v_lchild_448_);
v_a_453_ = v_lchild_468_;
v_kx_454_ = v_key_469_;
v_vx_455_ = v_val_470_;
v_b_456_ = v_rchild_471_;
v_ky_457_ = v_key_449_;
v_vy_458_ = v_val_450_;
v_c_459_ = v_rchild_451_;
v_kz_460_ = v_x_437_;
v_vz_461_ = v_x_438_;
v_d_462_ = v_x_439_;
goto v___jp_452_;
}
else
{
if (lean_obj_tag(v_rchild_451_) == 1)
{
uint8_t v_color_472_; 
v_color_472_ = lean_ctor_get_uint8(v_rchild_451_, sizeof(void*)*4);
if (v_color_472_ == 0)
{
lean_object* v_lchild_473_; lean_object* v_key_474_; lean_object* v_val_475_; lean_object* v_rchild_476_; 
lean_inc_ref(v_rchild_451_);
lean_inc_ref(v_lchild_448_);
lean_inc(v_val_450_);
lean_inc(v_key_449_);
lean_dec_ref(v_x_436_);
v_lchild_473_ = lean_ctor_get(v_rchild_451_, 0);
lean_inc(v_lchild_473_);
v_key_474_ = lean_ctor_get(v_rchild_451_, 1);
lean_inc(v_key_474_);
v_val_475_ = lean_ctor_get(v_rchild_451_, 2);
lean_inc(v_val_475_);
v_rchild_476_ = lean_ctor_get(v_rchild_451_, 3);
lean_inc(v_rchild_476_);
lean_dec_ref(v_rchild_451_);
v_a_453_ = v_lchild_448_;
v_kx_454_ = v_key_449_;
v_vx_455_ = v_val_450_;
v_b_456_ = v_lchild_473_;
v_ky_457_ = v_key_474_;
v_vy_458_ = v_val_475_;
v_c_459_ = v_rchild_476_;
v_kz_460_ = v_x_437_;
v_vz_461_ = v_x_438_;
v_d_462_ = v_x_439_;
goto v___jp_452_;
}
else
{
v_a_441_ = v_x_436_;
v_kx_442_ = v_x_437_;
v_vx_443_ = v_x_438_;
v_b_444_ = v_x_439_;
goto v___jp_440_;
}
}
else
{
v_a_441_ = v_x_436_;
v_kx_442_ = v_x_437_;
v_vx_443_ = v_x_438_;
v_b_444_ = v_x_439_;
goto v___jp_440_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_451_) == 1)
{
uint8_t v_color_477_; 
v_color_477_ = lean_ctor_get_uint8(v_rchild_451_, sizeof(void*)*4);
if (v_color_477_ == 0)
{
lean_object* v_lchild_478_; lean_object* v_key_479_; lean_object* v_val_480_; lean_object* v_rchild_481_; 
lean_inc_ref(v_rchild_451_);
lean_inc(v_val_450_);
lean_inc(v_key_449_);
lean_inc(v_lchild_448_);
lean_dec_ref(v_x_436_);
v_lchild_478_ = lean_ctor_get(v_rchild_451_, 0);
lean_inc(v_lchild_478_);
v_key_479_ = lean_ctor_get(v_rchild_451_, 1);
lean_inc(v_key_479_);
v_val_480_ = lean_ctor_get(v_rchild_451_, 2);
lean_inc(v_val_480_);
v_rchild_481_ = lean_ctor_get(v_rchild_451_, 3);
lean_inc(v_rchild_481_);
lean_dec_ref(v_rchild_451_);
v_a_453_ = v_lchild_448_;
v_kx_454_ = v_key_449_;
v_vx_455_ = v_val_450_;
v_b_456_ = v_lchild_478_;
v_ky_457_ = v_key_479_;
v_vy_458_ = v_val_480_;
v_c_459_ = v_rchild_481_;
v_kz_460_ = v_x_437_;
v_vz_461_ = v_x_438_;
v_d_462_ = v_x_439_;
goto v___jp_452_;
}
else
{
v_a_441_ = v_x_436_;
v_kx_442_ = v_x_437_;
v_vx_443_ = v_x_438_;
v_b_444_ = v_x_439_;
goto v___jp_440_;
}
}
else
{
v_a_441_ = v_x_436_;
v_kx_442_ = v_x_437_;
v_vx_443_ = v_x_438_;
v_b_444_ = v_x_439_;
goto v___jp_440_;
}
}
}
else
{
v_a_441_ = v_x_436_;
v_kx_442_ = v_x_437_;
v_vx_443_ = v_x_438_;
v_b_444_ = v_x_439_;
goto v___jp_440_;
}
v___jp_452_:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_463_ = 1;
v___x_464_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_464_, 0, v_a_453_);
lean_ctor_set(v___x_464_, 1, v_kx_454_);
lean_ctor_set(v___x_464_, 2, v_vx_455_);
lean_ctor_set(v___x_464_, 3, v_b_456_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*4, v___x_463_);
v___x_465_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_465_, 0, v_c_459_);
lean_ctor_set(v___x_465_, 1, v_kz_460_);
lean_ctor_set(v___x_465_, 2, v_vz_461_);
lean_ctor_set(v___x_465_, 3, v_d_462_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*4, v___x_463_);
v___x_466_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v_ky_457_);
lean_ctor_set(v___x_466_, 2, v_vy_458_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*4, v_color_447_);
return v___x_466_;
}
}
else
{
v_a_441_ = v_x_436_;
v_kx_442_ = v_x_437_;
v_vx_443_ = v_x_438_;
v_b_444_ = v_x_439_;
goto v___jp_440_;
}
v___jp_440_:
{
uint8_t v___x_445_; lean_object* v___x_446_; 
v___x_445_ = 1;
v___x_446_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_446_, 0, v_a_441_);
lean_ctor_set(v___x_446_, 1, v_kx_442_);
lean_ctor_set(v___x_446_, 2, v_vx_443_);
lean_ctor_set(v___x_446_, 3, v_b_444_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*4, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_a_489_; lean_object* v_kx_490_; lean_object* v_vx_491_; lean_object* v_b_492_; 
if (lean_obj_tag(v_x_484_) == 1)
{
uint8_t v_color_495_; lean_object* v_lchild_496_; lean_object* v_key_497_; lean_object* v_val_498_; lean_object* v_rchild_499_; lean_object* v_a_501_; lean_object* v_kx_502_; lean_object* v_vx_503_; lean_object* v_b_504_; lean_object* v_ky_505_; lean_object* v_vy_506_; lean_object* v_c_507_; lean_object* v_kz_508_; lean_object* v_vz_509_; lean_object* v_d_510_; 
v_color_495_ = lean_ctor_get_uint8(v_x_484_, sizeof(void*)*4);
v_lchild_496_ = lean_ctor_get(v_x_484_, 0);
v_key_497_ = lean_ctor_get(v_x_484_, 1);
v_val_498_ = lean_ctor_get(v_x_484_, 2);
v_rchild_499_ = lean_ctor_get(v_x_484_, 3);
if (v_color_495_ == 0)
{
if (lean_obj_tag(v_lchild_496_) == 1)
{
uint8_t v_color_515_; 
v_color_515_ = lean_ctor_get_uint8(v_lchild_496_, sizeof(void*)*4);
if (v_color_515_ == 0)
{
lean_object* v_lchild_516_; lean_object* v_key_517_; lean_object* v_val_518_; lean_object* v_rchild_519_; 
lean_inc_ref(v_lchild_496_);
lean_inc(v_rchild_499_);
lean_inc(v_val_498_);
lean_inc(v_key_497_);
lean_dec_ref(v_x_484_);
v_lchild_516_ = lean_ctor_get(v_lchild_496_, 0);
lean_inc(v_lchild_516_);
v_key_517_ = lean_ctor_get(v_lchild_496_, 1);
lean_inc(v_key_517_);
v_val_518_ = lean_ctor_get(v_lchild_496_, 2);
lean_inc(v_val_518_);
v_rchild_519_ = lean_ctor_get(v_lchild_496_, 3);
lean_inc(v_rchild_519_);
lean_dec_ref(v_lchild_496_);
v_a_501_ = v_lchild_516_;
v_kx_502_ = v_key_517_;
v_vx_503_ = v_val_518_;
v_b_504_ = v_rchild_519_;
v_ky_505_ = v_key_497_;
v_vy_506_ = v_val_498_;
v_c_507_ = v_rchild_499_;
v_kz_508_ = v_x_485_;
v_vz_509_ = v_x_486_;
v_d_510_ = v_x_487_;
goto v___jp_500_;
}
else
{
if (lean_obj_tag(v_rchild_499_) == 1)
{
uint8_t v_color_520_; 
v_color_520_ = lean_ctor_get_uint8(v_rchild_499_, sizeof(void*)*4);
if (v_color_520_ == 0)
{
lean_object* v_lchild_521_; lean_object* v_key_522_; lean_object* v_val_523_; lean_object* v_rchild_524_; 
lean_inc_ref(v_rchild_499_);
lean_inc_ref(v_lchild_496_);
lean_inc(v_val_498_);
lean_inc(v_key_497_);
lean_dec_ref(v_x_484_);
v_lchild_521_ = lean_ctor_get(v_rchild_499_, 0);
lean_inc(v_lchild_521_);
v_key_522_ = lean_ctor_get(v_rchild_499_, 1);
lean_inc(v_key_522_);
v_val_523_ = lean_ctor_get(v_rchild_499_, 2);
lean_inc(v_val_523_);
v_rchild_524_ = lean_ctor_get(v_rchild_499_, 3);
lean_inc(v_rchild_524_);
lean_dec_ref(v_rchild_499_);
v_a_501_ = v_lchild_496_;
v_kx_502_ = v_key_497_;
v_vx_503_ = v_val_498_;
v_b_504_ = v_lchild_521_;
v_ky_505_ = v_key_522_;
v_vy_506_ = v_val_523_;
v_c_507_ = v_rchild_524_;
v_kz_508_ = v_x_485_;
v_vz_509_ = v_x_486_;
v_d_510_ = v_x_487_;
goto v___jp_500_;
}
else
{
v_a_489_ = v_x_484_;
v_kx_490_ = v_x_485_;
v_vx_491_ = v_x_486_;
v_b_492_ = v_x_487_;
goto v___jp_488_;
}
}
else
{
v_a_489_ = v_x_484_;
v_kx_490_ = v_x_485_;
v_vx_491_ = v_x_486_;
v_b_492_ = v_x_487_;
goto v___jp_488_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_499_) == 1)
{
uint8_t v_color_525_; 
v_color_525_ = lean_ctor_get_uint8(v_rchild_499_, sizeof(void*)*4);
if (v_color_525_ == 0)
{
lean_object* v_lchild_526_; lean_object* v_key_527_; lean_object* v_val_528_; lean_object* v_rchild_529_; 
lean_inc_ref(v_rchild_499_);
lean_inc(v_val_498_);
lean_inc(v_key_497_);
lean_inc(v_lchild_496_);
lean_dec_ref(v_x_484_);
v_lchild_526_ = lean_ctor_get(v_rchild_499_, 0);
lean_inc(v_lchild_526_);
v_key_527_ = lean_ctor_get(v_rchild_499_, 1);
lean_inc(v_key_527_);
v_val_528_ = lean_ctor_get(v_rchild_499_, 2);
lean_inc(v_val_528_);
v_rchild_529_ = lean_ctor_get(v_rchild_499_, 3);
lean_inc(v_rchild_529_);
lean_dec_ref(v_rchild_499_);
v_a_501_ = v_lchild_496_;
v_kx_502_ = v_key_497_;
v_vx_503_ = v_val_498_;
v_b_504_ = v_lchild_526_;
v_ky_505_ = v_key_527_;
v_vy_506_ = v_val_528_;
v_c_507_ = v_rchild_529_;
v_kz_508_ = v_x_485_;
v_vz_509_ = v_x_486_;
v_d_510_ = v_x_487_;
goto v___jp_500_;
}
else
{
v_a_489_ = v_x_484_;
v_kx_490_ = v_x_485_;
v_vx_491_ = v_x_486_;
v_b_492_ = v_x_487_;
goto v___jp_488_;
}
}
else
{
v_a_489_ = v_x_484_;
v_kx_490_ = v_x_485_;
v_vx_491_ = v_x_486_;
v_b_492_ = v_x_487_;
goto v___jp_488_;
}
}
}
else
{
v_a_489_ = v_x_484_;
v_kx_490_ = v_x_485_;
v_vx_491_ = v_x_486_;
v_b_492_ = v_x_487_;
goto v___jp_488_;
}
v___jp_500_:
{
uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_511_ = 1;
v___x_512_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_512_, 0, v_a_501_);
lean_ctor_set(v___x_512_, 1, v_kx_502_);
lean_ctor_set(v___x_512_, 2, v_vx_503_);
lean_ctor_set(v___x_512_, 3, v_b_504_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*4, v___x_511_);
v___x_513_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_513_, 0, v_c_507_);
lean_ctor_set(v___x_513_, 1, v_kz_508_);
lean_ctor_set(v___x_513_, 2, v_vz_509_);
lean_ctor_set(v___x_513_, 3, v_d_510_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*4, v___x_511_);
v___x_514_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v_ky_505_);
lean_ctor_set(v___x_514_, 2, v_vy_506_);
lean_ctor_set(v___x_514_, 3, v___x_513_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*4, v_color_495_);
return v___x_514_;
}
}
else
{
v_a_489_ = v_x_484_;
v_kx_490_ = v_x_485_;
v_vx_491_ = v_x_486_;
v_b_492_ = v_x_487_;
goto v___jp_488_;
}
v___jp_488_:
{
uint8_t v___x_493_; lean_object* v___x_494_; 
v___x_493_ = 1;
v___x_494_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_494_, 0, v_a_489_);
lean_ctor_set(v___x_494_, 1, v_kx_490_);
lean_ctor_set(v___x_494_, 2, v_vx_491_);
lean_ctor_set(v___x_494_, 3, v_b_492_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*4, v___x_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_a_535_; lean_object* v_kx_536_; lean_object* v_vx_537_; lean_object* v_b_538_; 
if (lean_obj_tag(v_x_533_) == 1)
{
uint8_t v_color_541_; lean_object* v_lchild_542_; lean_object* v_key_543_; lean_object* v_val_544_; lean_object* v_rchild_545_; lean_object* v_a_547_; lean_object* v_kx_548_; lean_object* v_vx_549_; lean_object* v_b_550_; lean_object* v_ky_551_; lean_object* v_vy_552_; lean_object* v_c_553_; lean_object* v_kz_554_; lean_object* v_vz_555_; lean_object* v_d_556_; 
v_color_541_ = lean_ctor_get_uint8(v_x_533_, sizeof(void*)*4);
v_lchild_542_ = lean_ctor_get(v_x_533_, 0);
v_key_543_ = lean_ctor_get(v_x_533_, 1);
v_val_544_ = lean_ctor_get(v_x_533_, 2);
v_rchild_545_ = lean_ctor_get(v_x_533_, 3);
if (v_color_541_ == 0)
{
if (lean_obj_tag(v_lchild_542_) == 1)
{
uint8_t v_color_561_; 
v_color_561_ = lean_ctor_get_uint8(v_lchild_542_, sizeof(void*)*4);
if (v_color_561_ == 0)
{
lean_object* v_lchild_562_; lean_object* v_key_563_; lean_object* v_val_564_; lean_object* v_rchild_565_; 
lean_inc_ref(v_lchild_542_);
lean_inc(v_rchild_545_);
lean_inc(v_val_544_);
lean_inc(v_key_543_);
lean_dec_ref(v_x_533_);
v_lchild_562_ = lean_ctor_get(v_lchild_542_, 0);
lean_inc(v_lchild_562_);
v_key_563_ = lean_ctor_get(v_lchild_542_, 1);
lean_inc(v_key_563_);
v_val_564_ = lean_ctor_get(v_lchild_542_, 2);
lean_inc(v_val_564_);
v_rchild_565_ = lean_ctor_get(v_lchild_542_, 3);
lean_inc(v_rchild_565_);
lean_dec_ref(v_lchild_542_);
v_a_547_ = v_x_530_;
v_kx_548_ = v_x_531_;
v_vx_549_ = v_x_532_;
v_b_550_ = v_lchild_562_;
v_ky_551_ = v_key_563_;
v_vy_552_ = v_val_564_;
v_c_553_ = v_rchild_565_;
v_kz_554_ = v_key_543_;
v_vz_555_ = v_val_544_;
v_d_556_ = v_rchild_545_;
goto v___jp_546_;
}
else
{
if (lean_obj_tag(v_rchild_545_) == 1)
{
uint8_t v_color_566_; 
v_color_566_ = lean_ctor_get_uint8(v_rchild_545_, sizeof(void*)*4);
if (v_color_566_ == 0)
{
lean_object* v_lchild_567_; lean_object* v_key_568_; lean_object* v_val_569_; lean_object* v_rchild_570_; 
lean_inc_ref(v_rchild_545_);
lean_inc_ref(v_lchild_542_);
lean_inc(v_val_544_);
lean_inc(v_key_543_);
lean_dec_ref(v_x_533_);
v_lchild_567_ = lean_ctor_get(v_rchild_545_, 0);
lean_inc(v_lchild_567_);
v_key_568_ = lean_ctor_get(v_rchild_545_, 1);
lean_inc(v_key_568_);
v_val_569_ = lean_ctor_get(v_rchild_545_, 2);
lean_inc(v_val_569_);
v_rchild_570_ = lean_ctor_get(v_rchild_545_, 3);
lean_inc(v_rchild_570_);
lean_dec_ref(v_rchild_545_);
v_a_547_ = v_x_530_;
v_kx_548_ = v_x_531_;
v_vx_549_ = v_x_532_;
v_b_550_ = v_lchild_542_;
v_ky_551_ = v_key_543_;
v_vy_552_ = v_val_544_;
v_c_553_ = v_lchild_567_;
v_kz_554_ = v_key_568_;
v_vz_555_ = v_val_569_;
v_d_556_ = v_rchild_570_;
goto v___jp_546_;
}
else
{
v_a_535_ = v_x_530_;
v_kx_536_ = v_x_531_;
v_vx_537_ = v_x_532_;
v_b_538_ = v_x_533_;
goto v___jp_534_;
}
}
else
{
v_a_535_ = v_x_530_;
v_kx_536_ = v_x_531_;
v_vx_537_ = v_x_532_;
v_b_538_ = v_x_533_;
goto v___jp_534_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_545_) == 1)
{
uint8_t v_color_571_; 
v_color_571_ = lean_ctor_get_uint8(v_rchild_545_, sizeof(void*)*4);
if (v_color_571_ == 0)
{
lean_object* v_lchild_572_; lean_object* v_key_573_; lean_object* v_val_574_; lean_object* v_rchild_575_; 
lean_inc_ref(v_rchild_545_);
lean_inc(v_val_544_);
lean_inc(v_key_543_);
lean_inc(v_lchild_542_);
lean_dec_ref(v_x_533_);
v_lchild_572_ = lean_ctor_get(v_rchild_545_, 0);
lean_inc(v_lchild_572_);
v_key_573_ = lean_ctor_get(v_rchild_545_, 1);
lean_inc(v_key_573_);
v_val_574_ = lean_ctor_get(v_rchild_545_, 2);
lean_inc(v_val_574_);
v_rchild_575_ = lean_ctor_get(v_rchild_545_, 3);
lean_inc(v_rchild_575_);
lean_dec_ref(v_rchild_545_);
v_a_547_ = v_x_530_;
v_kx_548_ = v_x_531_;
v_vx_549_ = v_x_532_;
v_b_550_ = v_lchild_542_;
v_ky_551_ = v_key_543_;
v_vy_552_ = v_val_544_;
v_c_553_ = v_lchild_572_;
v_kz_554_ = v_key_573_;
v_vz_555_ = v_val_574_;
v_d_556_ = v_rchild_575_;
goto v___jp_546_;
}
else
{
v_a_535_ = v_x_530_;
v_kx_536_ = v_x_531_;
v_vx_537_ = v_x_532_;
v_b_538_ = v_x_533_;
goto v___jp_534_;
}
}
else
{
v_a_535_ = v_x_530_;
v_kx_536_ = v_x_531_;
v_vx_537_ = v_x_532_;
v_b_538_ = v_x_533_;
goto v___jp_534_;
}
}
}
else
{
v_a_535_ = v_x_530_;
v_kx_536_ = v_x_531_;
v_vx_537_ = v_x_532_;
v_b_538_ = v_x_533_;
goto v___jp_534_;
}
v___jp_546_:
{
uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = 1;
v___x_558_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_558_, 0, v_a_547_);
lean_ctor_set(v___x_558_, 1, v_kx_548_);
lean_ctor_set(v___x_558_, 2, v_vx_549_);
lean_ctor_set(v___x_558_, 3, v_b_550_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*4, v___x_557_);
v___x_559_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_559_, 0, v_c_553_);
lean_ctor_set(v___x_559_, 1, v_kz_554_);
lean_ctor_set(v___x_559_, 2, v_vz_555_);
lean_ctor_set(v___x_559_, 3, v_d_556_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*4, v___x_557_);
v___x_560_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v_ky_551_);
lean_ctor_set(v___x_560_, 2, v_vy_552_);
lean_ctor_set(v___x_560_, 3, v___x_559_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*4, v_color_541_);
return v___x_560_;
}
}
else
{
v_a_535_ = v_x_530_;
v_kx_536_ = v_x_531_;
v_vx_537_ = v_x_532_;
v_b_538_ = v_x_533_;
goto v___jp_534_;
}
v___jp_534_:
{
uint8_t v___x_539_; lean_object* v___x_540_; 
v___x_539_ = 1;
v___x_540_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_540_, 0, v_a_535_);
lean_ctor_set(v___x_540_, 1, v_kx_536_);
lean_ctor_set(v___x_540_, 2, v_vx_537_);
lean_ctor_set(v___x_540_, 3, v_b_538_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*4, v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object* v_00_u03b1_576_, lean_object* v_00_u03b2_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_a_583_; lean_object* v_kx_584_; lean_object* v_vx_585_; lean_object* v_b_586_; 
if (lean_obj_tag(v_x_581_) == 1)
{
uint8_t v_color_589_; lean_object* v_lchild_590_; lean_object* v_key_591_; lean_object* v_val_592_; lean_object* v_rchild_593_; lean_object* v_a_595_; lean_object* v_kx_596_; lean_object* v_vx_597_; lean_object* v_b_598_; lean_object* v_ky_599_; lean_object* v_vy_600_; lean_object* v_c_601_; lean_object* v_kz_602_; lean_object* v_vz_603_; lean_object* v_d_604_; 
v_color_589_ = lean_ctor_get_uint8(v_x_581_, sizeof(void*)*4);
v_lchild_590_ = lean_ctor_get(v_x_581_, 0);
v_key_591_ = lean_ctor_get(v_x_581_, 1);
v_val_592_ = lean_ctor_get(v_x_581_, 2);
v_rchild_593_ = lean_ctor_get(v_x_581_, 3);
if (v_color_589_ == 0)
{
if (lean_obj_tag(v_lchild_590_) == 1)
{
uint8_t v_color_609_; 
v_color_609_ = lean_ctor_get_uint8(v_lchild_590_, sizeof(void*)*4);
if (v_color_609_ == 0)
{
lean_object* v_lchild_610_; lean_object* v_key_611_; lean_object* v_val_612_; lean_object* v_rchild_613_; 
lean_inc_ref(v_lchild_590_);
lean_inc(v_rchild_593_);
lean_inc(v_val_592_);
lean_inc(v_key_591_);
lean_dec_ref(v_x_581_);
v_lchild_610_ = lean_ctor_get(v_lchild_590_, 0);
lean_inc(v_lchild_610_);
v_key_611_ = lean_ctor_get(v_lchild_590_, 1);
lean_inc(v_key_611_);
v_val_612_ = lean_ctor_get(v_lchild_590_, 2);
lean_inc(v_val_612_);
v_rchild_613_ = lean_ctor_get(v_lchild_590_, 3);
lean_inc(v_rchild_613_);
lean_dec_ref(v_lchild_590_);
v_a_595_ = v_x_578_;
v_kx_596_ = v_x_579_;
v_vx_597_ = v_x_580_;
v_b_598_ = v_lchild_610_;
v_ky_599_ = v_key_611_;
v_vy_600_ = v_val_612_;
v_c_601_ = v_rchild_613_;
v_kz_602_ = v_key_591_;
v_vz_603_ = v_val_592_;
v_d_604_ = v_rchild_593_;
goto v___jp_594_;
}
else
{
if (lean_obj_tag(v_rchild_593_) == 1)
{
uint8_t v_color_614_; 
v_color_614_ = lean_ctor_get_uint8(v_rchild_593_, sizeof(void*)*4);
if (v_color_614_ == 0)
{
lean_object* v_lchild_615_; lean_object* v_key_616_; lean_object* v_val_617_; lean_object* v_rchild_618_; 
lean_inc_ref(v_rchild_593_);
lean_inc_ref(v_lchild_590_);
lean_inc(v_val_592_);
lean_inc(v_key_591_);
lean_dec_ref(v_x_581_);
v_lchild_615_ = lean_ctor_get(v_rchild_593_, 0);
lean_inc(v_lchild_615_);
v_key_616_ = lean_ctor_get(v_rchild_593_, 1);
lean_inc(v_key_616_);
v_val_617_ = lean_ctor_get(v_rchild_593_, 2);
lean_inc(v_val_617_);
v_rchild_618_ = lean_ctor_get(v_rchild_593_, 3);
lean_inc(v_rchild_618_);
lean_dec_ref(v_rchild_593_);
v_a_595_ = v_x_578_;
v_kx_596_ = v_x_579_;
v_vx_597_ = v_x_580_;
v_b_598_ = v_lchild_590_;
v_ky_599_ = v_key_591_;
v_vy_600_ = v_val_592_;
v_c_601_ = v_lchild_615_;
v_kz_602_ = v_key_616_;
v_vz_603_ = v_val_617_;
v_d_604_ = v_rchild_618_;
goto v___jp_594_;
}
else
{
v_a_583_ = v_x_578_;
v_kx_584_ = v_x_579_;
v_vx_585_ = v_x_580_;
v_b_586_ = v_x_581_;
goto v___jp_582_;
}
}
else
{
v_a_583_ = v_x_578_;
v_kx_584_ = v_x_579_;
v_vx_585_ = v_x_580_;
v_b_586_ = v_x_581_;
goto v___jp_582_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_593_) == 1)
{
uint8_t v_color_619_; 
v_color_619_ = lean_ctor_get_uint8(v_rchild_593_, sizeof(void*)*4);
if (v_color_619_ == 0)
{
lean_object* v_lchild_620_; lean_object* v_key_621_; lean_object* v_val_622_; lean_object* v_rchild_623_; 
lean_inc_ref(v_rchild_593_);
lean_inc(v_val_592_);
lean_inc(v_key_591_);
lean_inc(v_lchild_590_);
lean_dec_ref(v_x_581_);
v_lchild_620_ = lean_ctor_get(v_rchild_593_, 0);
lean_inc(v_lchild_620_);
v_key_621_ = lean_ctor_get(v_rchild_593_, 1);
lean_inc(v_key_621_);
v_val_622_ = lean_ctor_get(v_rchild_593_, 2);
lean_inc(v_val_622_);
v_rchild_623_ = lean_ctor_get(v_rchild_593_, 3);
lean_inc(v_rchild_623_);
lean_dec_ref(v_rchild_593_);
v_a_595_ = v_x_578_;
v_kx_596_ = v_x_579_;
v_vx_597_ = v_x_580_;
v_b_598_ = v_lchild_590_;
v_ky_599_ = v_key_591_;
v_vy_600_ = v_val_592_;
v_c_601_ = v_lchild_620_;
v_kz_602_ = v_key_621_;
v_vz_603_ = v_val_622_;
v_d_604_ = v_rchild_623_;
goto v___jp_594_;
}
else
{
v_a_583_ = v_x_578_;
v_kx_584_ = v_x_579_;
v_vx_585_ = v_x_580_;
v_b_586_ = v_x_581_;
goto v___jp_582_;
}
}
else
{
v_a_583_ = v_x_578_;
v_kx_584_ = v_x_579_;
v_vx_585_ = v_x_580_;
v_b_586_ = v_x_581_;
goto v___jp_582_;
}
}
}
else
{
v_a_583_ = v_x_578_;
v_kx_584_ = v_x_579_;
v_vx_585_ = v_x_580_;
v_b_586_ = v_x_581_;
goto v___jp_582_;
}
v___jp_594_:
{
uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = 1;
v___x_606_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_606_, 0, v_a_595_);
lean_ctor_set(v___x_606_, 1, v_kx_596_);
lean_ctor_set(v___x_606_, 2, v_vx_597_);
lean_ctor_set(v___x_606_, 3, v_b_598_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*4, v___x_605_);
v___x_607_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_607_, 0, v_c_601_);
lean_ctor_set(v___x_607_, 1, v_kz_602_);
lean_ctor_set(v___x_607_, 2, v_vz_603_);
lean_ctor_set(v___x_607_, 3, v_d_604_);
lean_ctor_set_uint8(v___x_607_, sizeof(void*)*4, v___x_605_);
v___x_608_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v_ky_599_);
lean_ctor_set(v___x_608_, 2, v_vy_600_);
lean_ctor_set(v___x_608_, 3, v___x_607_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*4, v_color_589_);
return v___x_608_;
}
}
else
{
v_a_583_ = v_x_578_;
v_kx_584_ = v_x_579_;
v_vx_585_ = v_x_580_;
v_b_586_ = v_x_581_;
goto v___jp_582_;
}
v___jp_582_:
{
uint8_t v___x_587_; lean_object* v___x_588_; 
v___x_587_ = 1;
v___x_588_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_588_, 0, v_a_583_);
lean_ctor_set(v___x_588_, 1, v_kx_584_);
lean_ctor_set(v___x_588_, 2, v_vx_585_);
lean_ctor_set(v___x_588_, 3, v_b_586_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*4, v___x_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___redArg(lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 1)
{
uint8_t v_color_625_; 
v_color_625_ = lean_ctor_get_uint8(v_x_624_, sizeof(void*)*4);
if (v_color_625_ == 0)
{
uint8_t v___x_626_; 
v___x_626_ = 1;
return v___x_626_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object* v_x_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l_Lean_RBNode_isRed___redArg(v_x_629_);
lean_dec(v_x_629_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_x_634_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_RBNode_isRed___redArg(v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_Lean_RBNode_isRed(v_00_u03b1_636_, v_00_u03b2_637_, v_x_638_);
lean_dec(v_x_638_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___redArg(lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 1)
{
uint8_t v_color_642_; 
v_color_642_ = lean_ctor_get_uint8(v_x_641_, sizeof(void*)*4);
if (v_color_642_ == 1)
{
uint8_t v___x_643_; 
v___x_643_ = 1;
return v___x_643_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = 0;
return v___x_644_;
}
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 0;
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object* v_x_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Lean_RBNode_isBlack___redArg(v_x_646_);
lean_dec(v_x_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_x_651_){
_start:
{
uint8_t v___x_652_; 
v___x_652_ = l_Lean_RBNode_isBlack___redArg(v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_x_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_RBNode_isBlack(v_00_u03b1_653_, v_00_u03b2_654_, v_x_655_);
lean_dec(v_x_655_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object* v_cmp_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
uint8_t v___x_662_; lean_object* v___x_663_; 
lean_dec_ref(v_cmp_658_);
v___x_662_ = 0;
v___x_663_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_663_, 0, v_x_659_);
lean_ctor_set(v___x_663_, 1, v_x_660_);
lean_ctor_set(v___x_663_, 2, v_x_661_);
lean_ctor_set(v___x_663_, 3, v_x_659_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*4, v___x_662_);
return v___x_663_;
}
else
{
uint8_t v_color_664_; 
v_color_664_ = lean_ctor_get_uint8(v_x_659_, sizeof(void*)*4);
if (v_color_664_ == 0)
{
lean_object* v_lchild_665_; lean_object* v_key_666_; lean_object* v_val_667_; lean_object* v_rchild_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_685_; 
v_lchild_665_ = lean_ctor_get(v_x_659_, 0);
v_key_666_ = lean_ctor_get(v_x_659_, 1);
v_val_667_ = lean_ctor_get(v_x_659_, 2);
v_rchild_668_ = lean_ctor_get(v_x_659_, 3);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_685_ == 0)
{
v___x_670_ = v_x_659_;
v_isShared_671_ = v_isSharedCheck_685_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_rchild_668_);
lean_inc(v_val_667_);
lean_inc(v_key_666_);
lean_inc(v_lchild_665_);
lean_dec(v_x_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_685_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
lean_inc_ref(v_cmp_658_);
lean_inc(v_key_666_);
lean_inc(v_x_660_);
v___x_672_ = lean_apply_2(v_cmp_658_, v_x_660_, v_key_666_);
v___x_673_ = lean_unbox(v___x_672_);
switch(v___x_673_)
{
case 0:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = l_Lean_RBNode_ins___redArg(v_cmp_658_, v_lchild_665_, v_x_660_, v_x_661_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_674_);
v___x_676_ = v___x_670_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_key_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_val_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_rchild_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*4, v_color_664_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
case 1:
{
lean_object* v___x_679_; 
lean_dec(v_val_667_);
lean_dec(v_key_666_);
lean_dec_ref(v_cmp_658_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 2, v_x_661_);
lean_ctor_set(v___x_670_, 1, v_x_660_);
v___x_679_ = v___x_670_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_lchild_665_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_x_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_rchild_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*4, v_color_664_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
default: 
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_RBNode_ins___redArg(v_cmp_658_, v_rchild_668_, v_x_660_, v_x_661_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 3, v___x_681_);
v___x_683_ = v___x_670_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_lchild_665_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_key_666_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_val_667_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v___x_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_684_, sizeof(void*)*4, v_color_664_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
else
{
lean_object* v_lchild_686_; lean_object* v_key_687_; lean_object* v_val_688_; lean_object* v_rchild_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_848_; 
v_lchild_686_ = lean_ctor_get(v_x_659_, 0);
v_key_687_ = lean_ctor_get(v_x_659_, 1);
v_val_688_ = lean_ctor_get(v_x_659_, 2);
v_rchild_689_ = lean_ctor_get(v_x_659_, 3);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_848_ == 0)
{
v___x_691_ = v_x_659_;
v_isShared_692_ = v_isSharedCheck_848_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_rchild_689_);
lean_inc(v_val_688_);
lean_inc(v_key_687_);
lean_inc(v_lchild_686_);
lean_dec(v_x_659_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_848_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
lean_inc_ref(v_cmp_658_);
lean_inc(v_key_687_);
lean_inc(v_x_660_);
v___x_693_ = lean_apply_2(v_cmp_658_, v_x_660_, v_key_687_);
v___x_694_ = lean_unbox(v___x_693_);
switch(v___x_694_)
{
case 0:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_RBNode_ins___redArg(v_cmp_658_, v_lchild_686_, v_x_660_, v_x_661_);
if (lean_obj_tag(v___x_695_) == 1)
{
uint8_t v_color_696_; lean_object* v_lchild_697_; lean_object* v_key_698_; lean_object* v_val_699_; lean_object* v_rchild_700_; lean_object* v_a_702_; lean_object* v_kx_703_; lean_object* v_vx_704_; lean_object* v_b_705_; lean_object* v_ky_706_; lean_object* v_vy_707_; lean_object* v_c_708_; lean_object* v_kz_709_; lean_object* v_vz_710_; lean_object* v_d_711_; 
v_color_696_ = lean_ctor_get_uint8(v___x_695_, sizeof(void*)*4);
v_lchild_697_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_lchild_697_);
v_key_698_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_key_698_);
v_val_699_ = lean_ctor_get(v___x_695_, 2);
lean_inc(v_val_699_);
v_rchild_700_ = lean_ctor_get(v___x_695_, 3);
lean_inc(v_rchild_700_);
if (v_color_696_ == 0)
{
if (lean_obj_tag(v_lchild_697_) == 1)
{
uint8_t v_color_717_; 
v_color_717_ = lean_ctor_get_uint8(v_lchild_697_, sizeof(void*)*4);
if (v_color_717_ == 0)
{
lean_object* v_lchild_718_; lean_object* v_key_719_; lean_object* v_val_720_; lean_object* v_rchild_721_; 
lean_dec_ref(v___x_695_);
v_lchild_718_ = lean_ctor_get(v_lchild_697_, 0);
lean_inc(v_lchild_718_);
v_key_719_ = lean_ctor_get(v_lchild_697_, 1);
lean_inc(v_key_719_);
v_val_720_ = lean_ctor_get(v_lchild_697_, 2);
lean_inc(v_val_720_);
v_rchild_721_ = lean_ctor_get(v_lchild_697_, 3);
lean_inc(v_rchild_721_);
lean_dec_ref(v_lchild_697_);
v_a_702_ = v_lchild_718_;
v_kx_703_ = v_key_719_;
v_vx_704_ = v_val_720_;
v_b_705_ = v_rchild_721_;
v_ky_706_ = v_key_698_;
v_vy_707_ = v_val_699_;
v_c_708_ = v_rchild_700_;
v_kz_709_ = v_key_687_;
v_vz_710_ = v_val_688_;
v_d_711_ = v_rchild_689_;
goto v___jp_701_;
}
else
{
if (lean_obj_tag(v_rchild_700_) == 1)
{
uint8_t v_color_722_; 
v_color_722_ = lean_ctor_get_uint8(v_rchild_700_, sizeof(void*)*4);
if (v_color_722_ == 0)
{
lean_object* v_lchild_723_; lean_object* v_key_724_; lean_object* v_val_725_; lean_object* v_rchild_726_; 
lean_dec_ref(v___x_695_);
v_lchild_723_ = lean_ctor_get(v_rchild_700_, 0);
lean_inc(v_lchild_723_);
v_key_724_ = lean_ctor_get(v_rchild_700_, 1);
lean_inc(v_key_724_);
v_val_725_ = lean_ctor_get(v_rchild_700_, 2);
lean_inc(v_val_725_);
v_rchild_726_ = lean_ctor_get(v_rchild_700_, 3);
lean_inc(v_rchild_726_);
lean_dec_ref(v_rchild_700_);
v_a_702_ = v_lchild_697_;
v_kx_703_ = v_key_698_;
v_vx_704_ = v_val_699_;
v_b_705_ = v_lchild_723_;
v_ky_706_ = v_key_724_;
v_vy_707_ = v_val_725_;
v_c_708_ = v_rchild_726_;
v_kz_709_ = v_key_687_;
v_vz_710_ = v_val_688_;
v_d_711_ = v_rchild_689_;
goto v___jp_701_;
}
else
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_lchild_697_);
lean_dec(v_val_699_);
lean_dec(v_key_698_);
lean_del_object(v___x_691_);
v_isSharedCheck_733_ = !lean_is_exclusive(v_rchild_700_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; 
v_unused_734_ = lean_ctor_get(v_rchild_700_, 3);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_rchild_700_, 2);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_rchild_700_, 1);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_rchild_700_, 0);
lean_dec(v_unused_737_);
v___x_728_ = v_rchild_700_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_dec(v_rchild_700_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 3, v_rchild_689_);
lean_ctor_set(v___x_728_, 2, v_val_688_);
lean_ctor_set(v___x_728_, 1, v_key_687_);
lean_ctor_set(v___x_728_, 0, v___x_695_);
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_rchild_689_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*4, v_color_664_);
return v___x_731_;
}
}
}
}
else
{
lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_rchild_700_);
lean_dec(v_val_699_);
lean_dec(v_key_698_);
lean_del_object(v___x_691_);
v_isSharedCheck_744_ = !lean_is_exclusive(v_lchild_697_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; lean_object* v_unused_746_; lean_object* v_unused_747_; lean_object* v_unused_748_; 
v_unused_745_ = lean_ctor_get(v_lchild_697_, 3);
lean_dec(v_unused_745_);
v_unused_746_ = lean_ctor_get(v_lchild_697_, 2);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_lchild_697_, 1);
lean_dec(v_unused_747_);
v_unused_748_ = lean_ctor_get(v_lchild_697_, 0);
lean_dec(v_unused_748_);
v___x_739_ = v_lchild_697_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_dec(v_lchild_697_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 3, v_rchild_689_);
lean_ctor_set(v___x_739_, 2, v_val_688_);
lean_ctor_set(v___x_739_, 1, v_key_687_);
lean_ctor_set(v___x_739_, 0, v___x_695_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_rchild_689_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*4, v_color_664_);
return v___x_742_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_700_) == 1)
{
uint8_t v_color_749_; 
v_color_749_ = lean_ctor_get_uint8(v_rchild_700_, sizeof(void*)*4);
if (v_color_749_ == 0)
{
lean_object* v_lchild_750_; lean_object* v_key_751_; lean_object* v_val_752_; lean_object* v_rchild_753_; 
lean_dec_ref(v___x_695_);
v_lchild_750_ = lean_ctor_get(v_rchild_700_, 0);
lean_inc(v_lchild_750_);
v_key_751_ = lean_ctor_get(v_rchild_700_, 1);
lean_inc(v_key_751_);
v_val_752_ = lean_ctor_get(v_rchild_700_, 2);
lean_inc(v_val_752_);
v_rchild_753_ = lean_ctor_get(v_rchild_700_, 3);
lean_inc(v_rchild_753_);
lean_dec_ref(v_rchild_700_);
v_a_702_ = v_lchild_697_;
v_kx_703_ = v_key_698_;
v_vx_704_ = v_val_699_;
v_b_705_ = v_lchild_750_;
v_ky_706_ = v_key_751_;
v_vy_707_ = v_val_752_;
v_c_708_ = v_rchild_753_;
v_kz_709_ = v_key_687_;
v_vz_710_ = v_val_688_;
v_d_711_ = v_rchild_689_;
goto v___jp_701_;
}
else
{
lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v_val_699_);
lean_dec(v_key_698_);
lean_dec(v_lchild_697_);
lean_del_object(v___x_691_);
v_isSharedCheck_760_ = !lean_is_exclusive(v_rchild_700_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_761_ = lean_ctor_get(v_rchild_700_, 3);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_rchild_700_, 2);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_rchild_700_, 1);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_rchild_700_, 0);
lean_dec(v_unused_764_);
v___x_755_ = v_rchild_700_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_dec(v_rchild_700_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 3, v_rchild_689_);
lean_ctor_set(v___x_755_, 2, v_val_688_);
lean_ctor_set(v___x_755_, 1, v_key_687_);
lean_ctor_set(v___x_755_, 0, v___x_695_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_rchild_689_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_ctor_set_uint8(v___x_758_, sizeof(void*)*4, v_color_664_);
return v___x_758_;
}
}
}
}
else
{
lean_object* v___x_765_; 
lean_dec(v_rchild_700_);
lean_dec(v_val_699_);
lean_dec(v_key_698_);
lean_dec(v_lchild_697_);
lean_del_object(v___x_691_);
v___x_765_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_765_, 0, v___x_695_);
lean_ctor_set(v___x_765_, 1, v_key_687_);
lean_ctor_set(v___x_765_, 2, v_val_688_);
lean_ctor_set(v___x_765_, 3, v_rchild_689_);
lean_ctor_set_uint8(v___x_765_, sizeof(void*)*4, v_color_664_);
return v___x_765_;
}
}
}
else
{
lean_object* v___x_766_; 
lean_dec(v_rchild_700_);
lean_dec(v_val_699_);
lean_dec(v_key_698_);
lean_dec(v_lchild_697_);
lean_del_object(v___x_691_);
v___x_766_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_766_, 0, v___x_695_);
lean_ctor_set(v___x_766_, 1, v_key_687_);
lean_ctor_set(v___x_766_, 2, v_val_688_);
lean_ctor_set(v___x_766_, 3, v_rchild_689_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*4, v_color_664_);
return v___x_766_;
}
v___jp_701_:
{
lean_object* v___x_713_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 3, v_b_705_);
lean_ctor_set(v___x_691_, 2, v_vx_704_);
lean_ctor_set(v___x_691_, 1, v_kx_703_);
lean_ctor_set(v___x_691_, 0, v_a_702_);
v___x_713_ = v___x_691_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_702_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_kx_703_);
lean_ctor_set(v_reuseFailAlloc_716_, 2, v_vx_704_);
lean_ctor_set(v_reuseFailAlloc_716_, 3, v_b_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_716_, sizeof(void*)*4, v_color_664_);
v___x_713_ = v_reuseFailAlloc_716_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_714_, 0, v_c_708_);
lean_ctor_set(v___x_714_, 1, v_kz_709_);
lean_ctor_set(v___x_714_, 2, v_vz_710_);
lean_ctor_set(v___x_714_, 3, v_d_711_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*4, v_color_664_);
v___x_715_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v_ky_706_);
lean_ctor_set(v___x_715_, 2, v_vy_707_);
lean_ctor_set(v___x_715_, 3, v___x_714_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*4, v_color_696_);
return v___x_715_;
}
}
}
else
{
lean_object* v___x_768_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_695_);
v___x_768_ = v___x_691_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_rchild_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_769_, sizeof(void*)*4, v_color_664_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
case 1:
{
lean_object* v___x_771_; 
lean_dec(v_val_688_);
lean_dec(v_key_687_);
lean_dec_ref(v_cmp_658_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 2, v_x_661_);
lean_ctor_set(v___x_691_, 1, v_x_660_);
v___x_771_ = v___x_691_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_lchild_686_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_x_660_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_x_661_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_rchild_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_772_, sizeof(void*)*4, v_color_664_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
default: 
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_RBNode_ins___redArg(v_cmp_658_, v_rchild_689_, v_x_660_, v_x_661_);
if (lean_obj_tag(v___x_773_) == 1)
{
uint8_t v_color_774_; lean_object* v_lchild_775_; lean_object* v_key_776_; lean_object* v_val_777_; lean_object* v_rchild_778_; lean_object* v_a_780_; lean_object* v_kx_781_; lean_object* v_vx_782_; lean_object* v_b_783_; lean_object* v_ky_784_; lean_object* v_vy_785_; lean_object* v_c_786_; lean_object* v_kz_787_; lean_object* v_vz_788_; lean_object* v_d_789_; 
v_color_774_ = lean_ctor_get_uint8(v___x_773_, sizeof(void*)*4);
v_lchild_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_lchild_775_);
v_key_776_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_key_776_);
v_val_777_ = lean_ctor_get(v___x_773_, 2);
lean_inc(v_val_777_);
v_rchild_778_ = lean_ctor_get(v___x_773_, 3);
lean_inc(v_rchild_778_);
if (v_color_774_ == 0)
{
if (lean_obj_tag(v_lchild_775_) == 1)
{
uint8_t v_color_795_; 
v_color_795_ = lean_ctor_get_uint8(v_lchild_775_, sizeof(void*)*4);
if (v_color_795_ == 0)
{
lean_object* v_lchild_796_; lean_object* v_key_797_; lean_object* v_val_798_; lean_object* v_rchild_799_; 
lean_dec_ref(v___x_773_);
v_lchild_796_ = lean_ctor_get(v_lchild_775_, 0);
lean_inc(v_lchild_796_);
v_key_797_ = lean_ctor_get(v_lchild_775_, 1);
lean_inc(v_key_797_);
v_val_798_ = lean_ctor_get(v_lchild_775_, 2);
lean_inc(v_val_798_);
v_rchild_799_ = lean_ctor_get(v_lchild_775_, 3);
lean_inc(v_rchild_799_);
lean_dec_ref(v_lchild_775_);
v_a_780_ = v_lchild_686_;
v_kx_781_ = v_key_687_;
v_vx_782_ = v_val_688_;
v_b_783_ = v_lchild_796_;
v_ky_784_ = v_key_797_;
v_vy_785_ = v_val_798_;
v_c_786_ = v_rchild_799_;
v_kz_787_ = v_key_776_;
v_vz_788_ = v_val_777_;
v_d_789_ = v_rchild_778_;
goto v___jp_779_;
}
else
{
if (lean_obj_tag(v_rchild_778_) == 1)
{
uint8_t v_color_800_; 
v_color_800_ = lean_ctor_get_uint8(v_rchild_778_, sizeof(void*)*4);
if (v_color_800_ == 0)
{
lean_object* v_lchild_801_; lean_object* v_key_802_; lean_object* v_val_803_; lean_object* v_rchild_804_; 
lean_dec_ref(v___x_773_);
v_lchild_801_ = lean_ctor_get(v_rchild_778_, 0);
lean_inc(v_lchild_801_);
v_key_802_ = lean_ctor_get(v_rchild_778_, 1);
lean_inc(v_key_802_);
v_val_803_ = lean_ctor_get(v_rchild_778_, 2);
lean_inc(v_val_803_);
v_rchild_804_ = lean_ctor_get(v_rchild_778_, 3);
lean_inc(v_rchild_804_);
lean_dec_ref(v_rchild_778_);
v_a_780_ = v_lchild_686_;
v_kx_781_ = v_key_687_;
v_vx_782_ = v_val_688_;
v_b_783_ = v_lchild_775_;
v_ky_784_ = v_key_776_;
v_vy_785_ = v_val_777_;
v_c_786_ = v_lchild_801_;
v_kz_787_ = v_key_802_;
v_vz_788_ = v_val_803_;
v_d_789_ = v_rchild_804_;
goto v___jp_779_;
}
else
{
lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_lchild_775_);
lean_dec(v_val_777_);
lean_dec(v_key_776_);
lean_del_object(v___x_691_);
v_isSharedCheck_811_ = !lean_is_exclusive(v_rchild_778_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; lean_object* v_unused_815_; 
v_unused_812_ = lean_ctor_get(v_rchild_778_, 3);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_rchild_778_, 2);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_rchild_778_, 1);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_rchild_778_, 0);
lean_dec(v_unused_815_);
v___x_806_ = v_rchild_778_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_dec(v_rchild_778_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 3, v___x_773_);
lean_ctor_set(v___x_806_, 2, v_val_688_);
lean_ctor_set(v___x_806_, 1, v_key_687_);
lean_ctor_set(v___x_806_, 0, v_lchild_686_);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_lchild_686_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v___x_773_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*4, v_color_664_);
return v___x_809_;
}
}
}
}
else
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_rchild_778_);
lean_dec(v_val_777_);
lean_dec(v_key_776_);
lean_del_object(v___x_691_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_lchild_775_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_823_ = lean_ctor_get(v_lchild_775_, 3);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_lchild_775_, 2);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_lchild_775_, 1);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_lchild_775_, 0);
lean_dec(v_unused_826_);
v___x_817_ = v_lchild_775_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_lchild_775_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 3, v___x_773_);
lean_ctor_set(v___x_817_, 2, v_val_688_);
lean_ctor_set(v___x_817_, 1, v_key_687_);
lean_ctor_set(v___x_817_, 0, v_lchild_686_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_lchild_686_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v___x_773_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_ctor_set_uint8(v___x_820_, sizeof(void*)*4, v_color_664_);
return v___x_820_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_778_) == 1)
{
uint8_t v_color_827_; 
v_color_827_ = lean_ctor_get_uint8(v_rchild_778_, sizeof(void*)*4);
if (v_color_827_ == 0)
{
lean_object* v_lchild_828_; lean_object* v_key_829_; lean_object* v_val_830_; lean_object* v_rchild_831_; 
lean_dec_ref(v___x_773_);
v_lchild_828_ = lean_ctor_get(v_rchild_778_, 0);
lean_inc(v_lchild_828_);
v_key_829_ = lean_ctor_get(v_rchild_778_, 1);
lean_inc(v_key_829_);
v_val_830_ = lean_ctor_get(v_rchild_778_, 2);
lean_inc(v_val_830_);
v_rchild_831_ = lean_ctor_get(v_rchild_778_, 3);
lean_inc(v_rchild_831_);
lean_dec_ref(v_rchild_778_);
v_a_780_ = v_lchild_686_;
v_kx_781_ = v_key_687_;
v_vx_782_ = v_val_688_;
v_b_783_ = v_lchild_775_;
v_ky_784_ = v_key_776_;
v_vy_785_ = v_val_777_;
v_c_786_ = v_lchild_828_;
v_kz_787_ = v_key_829_;
v_vz_788_ = v_val_830_;
v_d_789_ = v_rchild_831_;
goto v___jp_779_;
}
else
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_val_777_);
lean_dec(v_key_776_);
lean_dec(v_lchild_775_);
lean_del_object(v___x_691_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_rchild_778_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_839_ = lean_ctor_get(v_rchild_778_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_rchild_778_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_rchild_778_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_rchild_778_, 0);
lean_dec(v_unused_842_);
v___x_833_ = v_rchild_778_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_dec(v_rchild_778_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 3, v___x_773_);
lean_ctor_set(v___x_833_, 2, v_val_688_);
lean_ctor_set(v___x_833_, 1, v_key_687_);
lean_ctor_set(v___x_833_, 0, v_lchild_686_);
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_lchild_686_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v___x_773_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*4, v_color_664_);
return v___x_836_;
}
}
}
}
else
{
lean_object* v___x_843_; 
lean_dec(v_rchild_778_);
lean_dec(v_val_777_);
lean_dec(v_key_776_);
lean_dec(v_lchild_775_);
lean_del_object(v___x_691_);
v___x_843_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_843_, 0, v_lchild_686_);
lean_ctor_set(v___x_843_, 1, v_key_687_);
lean_ctor_set(v___x_843_, 2, v_val_688_);
lean_ctor_set(v___x_843_, 3, v___x_773_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*4, v_color_664_);
return v___x_843_;
}
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v_rchild_778_);
lean_dec(v_val_777_);
lean_dec(v_key_776_);
lean_dec(v_lchild_775_);
lean_del_object(v___x_691_);
v___x_844_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_844_, 0, v_lchild_686_);
lean_ctor_set(v___x_844_, 1, v_key_687_);
lean_ctor_set(v___x_844_, 2, v_val_688_);
lean_ctor_set(v___x_844_, 3, v___x_773_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*4, v_color_664_);
return v___x_844_;
}
v___jp_779_:
{
lean_object* v___x_791_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 3, v_b_783_);
lean_ctor_set(v___x_691_, 2, v_vx_782_);
lean_ctor_set(v___x_691_, 1, v_kx_781_);
lean_ctor_set(v___x_691_, 0, v_a_780_);
v___x_791_ = v___x_691_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_kx_781_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_vx_782_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_b_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_794_, sizeof(void*)*4, v_color_664_);
v___x_791_ = v_reuseFailAlloc_794_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_792_, 0, v_c_786_);
lean_ctor_set(v___x_792_, 1, v_kz_787_);
lean_ctor_set(v___x_792_, 2, v_vz_788_);
lean_ctor_set(v___x_792_, 3, v_d_789_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*4, v_color_664_);
v___x_793_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v_ky_784_);
lean_ctor_set(v___x_793_, 2, v_vy_785_);
lean_ctor_set(v___x_793_, 3, v___x_792_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*4, v_color_774_);
return v___x_793_;
}
}
}
else
{
lean_object* v___x_846_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 3, v___x_773_);
v___x_846_ = v___x_691_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_lchild_686_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_val_688_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v___x_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_847_, sizeof(void*)*4, v_color_664_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object* v_00_u03b1_849_, lean_object* v_00_u03b2_850_, lean_object* v_cmp_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_RBNode_ins___redArg(v_cmp_851_, v_x_852_, v_x_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 1)
{
lean_object* v_lchild_857_; lean_object* v_key_858_; lean_object* v_val_859_; lean_object* v_rchild_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
v_lchild_857_ = lean_ctor_get(v_x_856_, 0);
v_key_858_ = lean_ctor_get(v_x_856_, 1);
v_val_859_ = lean_ctor_get(v_x_856_, 2);
v_rchild_860_ = lean_ctor_get(v_x_856_, 3);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_856_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v_x_856_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_rchild_860_);
lean_inc(v_val_859_);
lean_inc(v_key_858_);
lean_inc(v_lchild_857_);
lean_dec(v_x_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
uint8_t v___x_864_; lean_object* v___x_866_; 
v___x_864_ = 1;
if (v_isShared_863_ == 0)
{
v___x_866_ = v___x_862_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_lchild_857_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_key_858_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_val_859_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_rchild_860_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*4, v___x_864_);
return v___x_866_;
}
}
}
else
{
return v_x_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_RBNode_setBlack___redArg(v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object* v_cmp_873_, lean_object* v_t_874_, lean_object* v_k_875_, lean_object* v_v_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_RBNode_isRed___redArg(v_t_874_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_RBNode_ins___redArg(v_cmp_873_, v_t_874_, v_k_875_, v_v_876_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = l_Lean_RBNode_ins___redArg(v_cmp_873_, v_t_874_, v_k_875_, v_v_876_);
v___x_880_ = l_Lean_RBNode_setBlack___redArg(v___x_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_cmp_883_, lean_object* v_t_884_, lean_object* v_k_885_, lean_object* v_v_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_RBNode_insert___redArg(v_cmp_883_, v_t_884_, v_k_885_, v_v_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_888_) == 1)
{
lean_object* v_lchild_889_; lean_object* v_key_890_; lean_object* v_val_891_; lean_object* v_rchild_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v_lchild_889_ = lean_ctor_get(v_x_888_, 0);
v_key_890_ = lean_ctor_get(v_x_888_, 1);
v_val_891_ = lean_ctor_get(v_x_888_, 2);
v_rchild_892_ = lean_ctor_get(v_x_888_, 3);
v_isSharedCheck_900_ = !lean_is_exclusive(v_x_888_);
if (v_isSharedCheck_900_ == 0)
{
v___x_894_ = v_x_888_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_rchild_892_);
lean_inc(v_val_891_);
lean_inc(v_key_890_);
lean_inc(v_lchild_889_);
lean_dec(v_x_888_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
uint8_t v___x_896_; lean_object* v___x_898_; 
v___x_896_ = 0;
if (v_isShared_895_ == 0)
{
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_lchild_889_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_key_890_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_val_891_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_rchild_892_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*4, v___x_896_);
return v___x_898_;
}
}
}
else
{
return v_x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_x_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_RBNode_setRed___redArg(v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_a_910_; lean_object* v_kx_911_; lean_object* v_vx_912_; lean_object* v_b_913_; lean_object* v_a_917_; lean_object* v_kx_918_; lean_object* v_vx_919_; lean_object* v_b_920_; lean_object* v_ky_921_; lean_object* v_vy_922_; lean_object* v_c_923_; lean_object* v_kz_924_; lean_object* v_vz_925_; lean_object* v_d_926_; lean_object* v_l_933_; lean_object* v_k_934_; lean_object* v_v_935_; lean_object* v_a_936_; lean_object* v_ky_937_; lean_object* v_vy_938_; lean_object* v_b_939_; uint8_t v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v_a_963_; lean_object* v_kx_964_; lean_object* v_vx_965_; lean_object* v_b_966_; lean_object* v_ky_967_; lean_object* v_vy_968_; lean_object* v_c_969_; lean_object* v_kz_970_; lean_object* v_vz_971_; lean_object* v_d_972_; uint8_t v___y_978_; lean_object* v___y_979_; uint8_t v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v_a_983_; lean_object* v_kx_984_; lean_object* v_vx_985_; lean_object* v_b_986_; lean_object* v_l_990_; lean_object* v_k_991_; lean_object* v_v_992_; lean_object* v_a_993_; lean_object* v_ky_994_; lean_object* v_vy_995_; lean_object* v_b_996_; lean_object* v_kz_997_; lean_object* v_vz_998_; lean_object* v_c_999_; lean_object* v_l_1031_; lean_object* v_k_1032_; lean_object* v_v_1033_; lean_object* v_r_1034_; 
if (lean_obj_tag(v_x_905_) == 1)
{
uint8_t v_color_1037_; 
v_color_1037_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*4);
if (v_color_1037_ == 0)
{
lean_object* v_lchild_1038_; lean_object* v_key_1039_; lean_object* v_val_1040_; lean_object* v_rchild_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1050_; 
v_lchild_1038_ = lean_ctor_get(v_x_905_, 0);
v_key_1039_ = lean_ctor_get(v_x_905_, 1);
v_val_1040_ = lean_ctor_get(v_x_905_, 2);
v_rchild_1041_ = lean_ctor_get(v_x_905_, 3);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_905_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1043_ = v_x_905_;
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_rchild_1041_);
lean_inc(v_val_1040_);
lean_inc(v_key_1039_);
lean_inc(v_lchild_1038_);
lean_dec(v_x_905_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
uint8_t v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = 1;
if (v_isShared_1044_ == 0)
{
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_lchild_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_key_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_val_1040_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_rchild_1041_);
v___x_1047_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; 
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*4, v___x_1045_);
v___x_1048_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_x_906_);
lean_ctor_set(v___x_1048_, 2, v_x_907_);
lean_ctor_set(v___x_1048_, 3, v_x_908_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*4, v_color_1037_);
return v___x_1048_;
}
}
}
else
{
if (lean_obj_tag(v_x_908_) == 1)
{
uint8_t v_color_1051_; 
v_color_1051_ = lean_ctor_get_uint8(v_x_908_, sizeof(void*)*4);
if (v_color_1051_ == 0)
{
lean_object* v_lchild_1052_; 
v_lchild_1052_ = lean_ctor_get(v_x_908_, 0);
if (lean_obj_tag(v_lchild_1052_) == 1)
{
uint8_t v_color_1053_; 
v_color_1053_ = lean_ctor_get_uint8(v_lchild_1052_, sizeof(void*)*4);
if (v_color_1053_ == 1)
{
lean_object* v_key_1054_; lean_object* v_val_1055_; lean_object* v_rchild_1056_; lean_object* v_lchild_1057_; lean_object* v_key_1058_; lean_object* v_val_1059_; lean_object* v_rchild_1060_; 
lean_inc_ref(v_lchild_1052_);
v_key_1054_ = lean_ctor_get(v_x_908_, 1);
lean_inc(v_key_1054_);
v_val_1055_ = lean_ctor_get(v_x_908_, 2);
lean_inc(v_val_1055_);
v_rchild_1056_ = lean_ctor_get(v_x_908_, 3);
lean_inc(v_rchild_1056_);
lean_dec_ref(v_x_908_);
v_lchild_1057_ = lean_ctor_get(v_lchild_1052_, 0);
lean_inc(v_lchild_1057_);
v_key_1058_ = lean_ctor_get(v_lchild_1052_, 1);
lean_inc(v_key_1058_);
v_val_1059_ = lean_ctor_get(v_lchild_1052_, 2);
lean_inc(v_val_1059_);
v_rchild_1060_ = lean_ctor_get(v_lchild_1052_, 3);
lean_inc(v_rchild_1060_);
lean_dec_ref(v_lchild_1052_);
v_l_990_ = v_x_905_;
v_k_991_ = v_x_906_;
v_v_992_ = v_x_907_;
v_a_993_ = v_lchild_1057_;
v_ky_994_ = v_key_1058_;
v_vy_995_ = v_val_1059_;
v_b_996_ = v_rchild_1060_;
v_kz_997_ = v_key_1054_;
v_vz_998_ = v_val_1055_;
v_c_999_ = v_rchild_1056_;
goto v___jp_989_;
}
else
{
v_l_1031_ = v_x_905_;
v_k_1032_ = v_x_906_;
v_v_1033_ = v_x_907_;
v_r_1034_ = v_x_908_;
goto v___jp_1030_;
}
}
else
{
v_l_1031_ = v_x_905_;
v_k_1032_ = v_x_906_;
v_v_1033_ = v_x_907_;
v_r_1034_ = v_x_908_;
goto v___jp_1030_;
}
}
else
{
lean_object* v_lchild_1061_; lean_object* v_key_1062_; lean_object* v_val_1063_; lean_object* v_rchild_1064_; 
v_lchild_1061_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_lchild_1061_);
v_key_1062_ = lean_ctor_get(v_x_908_, 1);
lean_inc(v_key_1062_);
v_val_1063_ = lean_ctor_get(v_x_908_, 2);
lean_inc(v_val_1063_);
v_rchild_1064_ = lean_ctor_get(v_x_908_, 3);
lean_inc(v_rchild_1064_);
lean_dec_ref(v_x_908_);
v_l_933_ = v_x_905_;
v_k_934_ = v_x_906_;
v_v_935_ = v_x_907_;
v_a_936_ = v_lchild_1061_;
v_ky_937_ = v_key_1062_;
v_vy_938_ = v_val_1063_;
v_b_939_ = v_rchild_1064_;
goto v___jp_932_;
}
}
else
{
v_l_1031_ = v_x_905_;
v_k_1032_ = v_x_906_;
v_v_1033_ = v_x_907_;
v_r_1034_ = v_x_908_;
goto v___jp_1030_;
}
}
}
else
{
if (lean_obj_tag(v_x_908_) == 1)
{
uint8_t v_color_1065_; 
v_color_1065_ = lean_ctor_get_uint8(v_x_908_, sizeof(void*)*4);
if (v_color_1065_ == 0)
{
lean_object* v_lchild_1066_; 
v_lchild_1066_ = lean_ctor_get(v_x_908_, 0);
if (lean_obj_tag(v_lchild_1066_) == 1)
{
uint8_t v_color_1067_; 
v_color_1067_ = lean_ctor_get_uint8(v_lchild_1066_, sizeof(void*)*4);
if (v_color_1067_ == 1)
{
lean_object* v_key_1068_; lean_object* v_val_1069_; lean_object* v_rchild_1070_; lean_object* v_lchild_1071_; lean_object* v_key_1072_; lean_object* v_val_1073_; lean_object* v_rchild_1074_; 
lean_inc_ref(v_lchild_1066_);
v_key_1068_ = lean_ctor_get(v_x_908_, 1);
lean_inc(v_key_1068_);
v_val_1069_ = lean_ctor_get(v_x_908_, 2);
lean_inc(v_val_1069_);
v_rchild_1070_ = lean_ctor_get(v_x_908_, 3);
lean_inc(v_rchild_1070_);
lean_dec_ref(v_x_908_);
v_lchild_1071_ = lean_ctor_get(v_lchild_1066_, 0);
lean_inc(v_lchild_1071_);
v_key_1072_ = lean_ctor_get(v_lchild_1066_, 1);
lean_inc(v_key_1072_);
v_val_1073_ = lean_ctor_get(v_lchild_1066_, 2);
lean_inc(v_val_1073_);
v_rchild_1074_ = lean_ctor_get(v_lchild_1066_, 3);
lean_inc(v_rchild_1074_);
lean_dec_ref(v_lchild_1066_);
v_l_990_ = v_x_905_;
v_k_991_ = v_x_906_;
v_v_992_ = v_x_907_;
v_a_993_ = v_lchild_1071_;
v_ky_994_ = v_key_1072_;
v_vy_995_ = v_val_1073_;
v_b_996_ = v_rchild_1074_;
v_kz_997_ = v_key_1068_;
v_vz_998_ = v_val_1069_;
v_c_999_ = v_rchild_1070_;
goto v___jp_989_;
}
else
{
v_l_1031_ = v_x_905_;
v_k_1032_ = v_x_906_;
v_v_1033_ = v_x_907_;
v_r_1034_ = v_x_908_;
goto v___jp_1030_;
}
}
else
{
v_l_1031_ = v_x_905_;
v_k_1032_ = v_x_906_;
v_v_1033_ = v_x_907_;
v_r_1034_ = v_x_908_;
goto v___jp_1030_;
}
}
else
{
lean_object* v_lchild_1075_; lean_object* v_key_1076_; lean_object* v_val_1077_; lean_object* v_rchild_1078_; 
v_lchild_1075_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_lchild_1075_);
v_key_1076_ = lean_ctor_get(v_x_908_, 1);
lean_inc(v_key_1076_);
v_val_1077_ = lean_ctor_get(v_x_908_, 2);
lean_inc(v_val_1077_);
v_rchild_1078_ = lean_ctor_get(v_x_908_, 3);
lean_inc(v_rchild_1078_);
lean_dec_ref(v_x_908_);
v_l_933_ = v_x_905_;
v_k_934_ = v_x_906_;
v_v_935_ = v_x_907_;
v_a_936_ = v_lchild_1075_;
v_ky_937_ = v_key_1076_;
v_vy_938_ = v_val_1077_;
v_b_939_ = v_rchild_1078_;
goto v___jp_932_;
}
}
else
{
v_l_1031_ = v_x_905_;
v_k_1032_ = v_x_906_;
v_v_1033_ = v_x_907_;
v_r_1034_ = v_x_908_;
goto v___jp_1030_;
}
}
v___jp_909_:
{
uint8_t v___x_914_; lean_object* v___x_915_; 
v___x_914_ = 1;
v___x_915_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_915_, 0, v_a_910_);
lean_ctor_set(v___x_915_, 1, v_kx_911_);
lean_ctor_set(v___x_915_, 2, v_vx_912_);
lean_ctor_set(v___x_915_, 3, v_b_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*4, v___x_914_);
return v___x_915_;
}
v___jp_916_:
{
uint8_t v___x_927_; uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_927_ = 0;
v___x_928_ = 1;
v___x_929_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_929_, 0, v_a_917_);
lean_ctor_set(v___x_929_, 1, v_kx_918_);
lean_ctor_set(v___x_929_, 2, v_vx_919_);
lean_ctor_set(v___x_929_, 3, v_b_920_);
lean_ctor_set_uint8(v___x_929_, sizeof(void*)*4, v___x_928_);
v___x_930_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_930_, 0, v_c_923_);
lean_ctor_set(v___x_930_, 1, v_kz_924_);
lean_ctor_set(v___x_930_, 2, v_vz_925_);
lean_ctor_set(v___x_930_, 3, v_d_926_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*4, v___x_928_);
v___x_931_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v_ky_921_);
lean_ctor_set(v___x_931_, 2, v_vy_922_);
lean_ctor_set(v___x_931_, 3, v___x_930_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*4, v___x_927_);
return v___x_931_;
}
v___jp_932_:
{
uint8_t v___x_940_; lean_object* v___x_941_; 
v___x_940_ = 0;
lean_inc(v_b_939_);
lean_inc(v_vy_938_);
lean_inc(v_ky_937_);
lean_inc(v_a_936_);
v___x_941_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_941_, 0, v_a_936_);
lean_ctor_set(v___x_941_, 1, v_ky_937_);
lean_ctor_set(v___x_941_, 2, v_vy_938_);
lean_ctor_set(v___x_941_, 3, v_b_939_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*4, v___x_940_);
if (lean_obj_tag(v_a_936_) == 1)
{
uint8_t v_color_942_; 
v_color_942_ = lean_ctor_get_uint8(v_a_936_, sizeof(void*)*4);
if (v_color_942_ == 0)
{
lean_object* v_lchild_943_; lean_object* v_key_944_; lean_object* v_val_945_; lean_object* v_rchild_946_; 
lean_dec_ref(v___x_941_);
v_lchild_943_ = lean_ctor_get(v_a_936_, 0);
lean_inc(v_lchild_943_);
v_key_944_ = lean_ctor_get(v_a_936_, 1);
lean_inc(v_key_944_);
v_val_945_ = lean_ctor_get(v_a_936_, 2);
lean_inc(v_val_945_);
v_rchild_946_ = lean_ctor_get(v_a_936_, 3);
lean_inc(v_rchild_946_);
lean_dec_ref(v_a_936_);
v_a_917_ = v_l_933_;
v_kx_918_ = v_k_934_;
v_vx_919_ = v_v_935_;
v_b_920_ = v_lchild_943_;
v_ky_921_ = v_key_944_;
v_vy_922_ = v_val_945_;
v_c_923_ = v_rchild_946_;
v_kz_924_ = v_ky_937_;
v_vz_925_ = v_vy_938_;
v_d_926_ = v_b_939_;
goto v___jp_916_;
}
else
{
if (lean_obj_tag(v_b_939_) == 1)
{
uint8_t v_color_947_; 
v_color_947_ = lean_ctor_get_uint8(v_b_939_, sizeof(void*)*4);
if (v_color_947_ == 0)
{
lean_object* v_lchild_948_; lean_object* v_key_949_; lean_object* v_val_950_; lean_object* v_rchild_951_; 
lean_dec_ref(v___x_941_);
v_lchild_948_ = lean_ctor_get(v_b_939_, 0);
lean_inc(v_lchild_948_);
v_key_949_ = lean_ctor_get(v_b_939_, 1);
lean_inc(v_key_949_);
v_val_950_ = lean_ctor_get(v_b_939_, 2);
lean_inc(v_val_950_);
v_rchild_951_ = lean_ctor_get(v_b_939_, 3);
lean_inc(v_rchild_951_);
lean_dec_ref(v_b_939_);
v_a_917_ = v_l_933_;
v_kx_918_ = v_k_934_;
v_vx_919_ = v_v_935_;
v_b_920_ = v_a_936_;
v_ky_921_ = v_ky_937_;
v_vy_922_ = v_vy_938_;
v_c_923_ = v_lchild_948_;
v_kz_924_ = v_key_949_;
v_vz_925_ = v_val_950_;
v_d_926_ = v_rchild_951_;
goto v___jp_916_;
}
else
{
lean_dec_ref(v_b_939_);
lean_dec_ref(v_a_936_);
lean_dec(v_vy_938_);
lean_dec(v_ky_937_);
v_a_910_ = v_l_933_;
v_kx_911_ = v_k_934_;
v_vx_912_ = v_v_935_;
v_b_913_ = v___x_941_;
goto v___jp_909_;
}
}
else
{
lean_dec_ref(v_a_936_);
lean_dec(v_b_939_);
lean_dec(v_vy_938_);
lean_dec(v_ky_937_);
v_a_910_ = v_l_933_;
v_kx_911_ = v_k_934_;
v_vx_912_ = v_v_935_;
v_b_913_ = v___x_941_;
goto v___jp_909_;
}
}
}
else
{
if (lean_obj_tag(v_b_939_) == 1)
{
uint8_t v_color_952_; 
v_color_952_ = lean_ctor_get_uint8(v_b_939_, sizeof(void*)*4);
if (v_color_952_ == 0)
{
lean_object* v_lchild_953_; lean_object* v_key_954_; lean_object* v_val_955_; lean_object* v_rchild_956_; 
lean_dec_ref(v___x_941_);
v_lchild_953_ = lean_ctor_get(v_b_939_, 0);
lean_inc(v_lchild_953_);
v_key_954_ = lean_ctor_get(v_b_939_, 1);
lean_inc(v_key_954_);
v_val_955_ = lean_ctor_get(v_b_939_, 2);
lean_inc(v_val_955_);
v_rchild_956_ = lean_ctor_get(v_b_939_, 3);
lean_inc(v_rchild_956_);
lean_dec_ref(v_b_939_);
v_a_917_ = v_l_933_;
v_kx_918_ = v_k_934_;
v_vx_919_ = v_v_935_;
v_b_920_ = v_a_936_;
v_ky_921_ = v_ky_937_;
v_vy_922_ = v_vy_938_;
v_c_923_ = v_lchild_953_;
v_kz_924_ = v_key_954_;
v_vz_925_ = v_val_955_;
v_d_926_ = v_rchild_956_;
goto v___jp_916_;
}
else
{
lean_dec_ref(v_b_939_);
lean_dec(v_vy_938_);
lean_dec(v_ky_937_);
lean_dec(v_a_936_);
v_a_910_ = v_l_933_;
v_kx_911_ = v_k_934_;
v_vx_912_ = v_v_935_;
v_b_913_ = v___x_941_;
goto v___jp_909_;
}
}
else
{
lean_dec(v_b_939_);
lean_dec(v_vy_938_);
lean_dec(v_ky_937_);
lean_dec(v_a_936_);
v_a_910_ = v_l_933_;
v_kx_911_ = v_k_934_;
v_vx_912_ = v_v_935_;
v_b_913_ = v___x_941_;
goto v___jp_909_;
}
}
}
v___jp_957_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_973_, 0, v_a_963_);
lean_ctor_set(v___x_973_, 1, v_kx_964_);
lean_ctor_set(v___x_973_, 2, v_vx_965_);
lean_ctor_set(v___x_973_, 3, v_b_966_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*4, v___y_958_);
v___x_974_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_974_, 0, v_c_969_);
lean_ctor_set(v___x_974_, 1, v_kz_970_);
lean_ctor_set(v___x_974_, 2, v_vz_971_);
lean_ctor_set(v___x_974_, 3, v_d_972_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*4, v___y_958_);
v___x_975_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v_ky_967_);
lean_ctor_set(v___x_975_, 2, v_vy_968_);
lean_ctor_set(v___x_975_, 3, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*4, v___y_960_);
v___x_976_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_976_, 0, v___y_959_);
lean_ctor_set(v___x_976_, 1, v___y_962_);
lean_ctor_set(v___x_976_, 2, v___y_961_);
lean_ctor_set(v___x_976_, 3, v___x_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*4, v___y_960_);
return v___x_976_;
}
v___jp_977_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_987_, 0, v_a_983_);
lean_ctor_set(v___x_987_, 1, v_kx_984_);
lean_ctor_set(v___x_987_, 2, v_vx_985_);
lean_ctor_set(v___x_987_, 3, v_b_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*4, v___y_978_);
v___x_988_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_988_, 0, v___y_979_);
lean_ctor_set(v___x_988_, 1, v___y_982_);
lean_ctor_set(v___x_988_, 2, v___y_981_);
lean_ctor_set(v___x_988_, 3, v___x_987_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*4, v___y_980_);
return v___x_988_;
}
v___jp_989_:
{
uint8_t v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = 0;
v___x_1001_ = 1;
v___x_1002_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1002_, 0, v_l_990_);
lean_ctor_set(v___x_1002_, 1, v_k_991_);
lean_ctor_set(v___x_1002_, 2, v_v_992_);
lean_ctor_set(v___x_1002_, 3, v_a_993_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*4, v___x_1001_);
v___x_1003_ = l_Lean_RBNode_setRed___redArg(v_c_999_);
if (lean_obj_tag(v___x_1003_) == 1)
{
uint8_t v_color_1004_; 
v_color_1004_ = lean_ctor_get_uint8(v___x_1003_, sizeof(void*)*4);
if (v_color_1004_ == 0)
{
lean_object* v_lchild_1005_; 
v_lchild_1005_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_lchild_1005_);
if (lean_obj_tag(v_lchild_1005_) == 1)
{
uint8_t v_color_1006_; 
v_color_1006_ = lean_ctor_get_uint8(v_lchild_1005_, sizeof(void*)*4);
if (v_color_1006_ == 0)
{
lean_object* v_key_1007_; lean_object* v_val_1008_; lean_object* v_rchild_1009_; lean_object* v_lchild_1010_; lean_object* v_key_1011_; lean_object* v_val_1012_; lean_object* v_rchild_1013_; 
v_key_1007_ = lean_ctor_get(v___x_1003_, 1);
lean_inc(v_key_1007_);
v_val_1008_ = lean_ctor_get(v___x_1003_, 2);
lean_inc(v_val_1008_);
v_rchild_1009_ = lean_ctor_get(v___x_1003_, 3);
lean_inc(v_rchild_1009_);
lean_dec_ref(v___x_1003_);
v_lchild_1010_ = lean_ctor_get(v_lchild_1005_, 0);
lean_inc(v_lchild_1010_);
v_key_1011_ = lean_ctor_get(v_lchild_1005_, 1);
lean_inc(v_key_1011_);
v_val_1012_ = lean_ctor_get(v_lchild_1005_, 2);
lean_inc(v_val_1012_);
v_rchild_1013_ = lean_ctor_get(v_lchild_1005_, 3);
lean_inc(v_rchild_1013_);
lean_dec_ref(v_lchild_1005_);
v___y_958_ = v___x_1001_;
v___y_959_ = v___x_1002_;
v___y_960_ = v___x_1000_;
v___y_961_ = v_vy_995_;
v___y_962_ = v_ky_994_;
v_a_963_ = v_b_996_;
v_kx_964_ = v_kz_997_;
v_vx_965_ = v_vz_998_;
v_b_966_ = v_lchild_1010_;
v_ky_967_ = v_key_1011_;
v_vy_968_ = v_val_1012_;
v_c_969_ = v_rchild_1013_;
v_kz_970_ = v_key_1007_;
v_vz_971_ = v_val_1008_;
v_d_972_ = v_rchild_1009_;
goto v___jp_957_;
}
else
{
lean_object* v_rchild_1014_; 
v_rchild_1014_ = lean_ctor_get(v___x_1003_, 3);
lean_inc(v_rchild_1014_);
if (lean_obj_tag(v_rchild_1014_) == 1)
{
uint8_t v_color_1015_; 
v_color_1015_ = lean_ctor_get_uint8(v_rchild_1014_, sizeof(void*)*4);
if (v_color_1015_ == 0)
{
lean_object* v_key_1016_; lean_object* v_val_1017_; lean_object* v_lchild_1018_; lean_object* v_key_1019_; lean_object* v_val_1020_; lean_object* v_rchild_1021_; 
v_key_1016_ = lean_ctor_get(v___x_1003_, 1);
lean_inc(v_key_1016_);
v_val_1017_ = lean_ctor_get(v___x_1003_, 2);
lean_inc(v_val_1017_);
lean_dec_ref(v___x_1003_);
v_lchild_1018_ = lean_ctor_get(v_rchild_1014_, 0);
lean_inc(v_lchild_1018_);
v_key_1019_ = lean_ctor_get(v_rchild_1014_, 1);
lean_inc(v_key_1019_);
v_val_1020_ = lean_ctor_get(v_rchild_1014_, 2);
lean_inc(v_val_1020_);
v_rchild_1021_ = lean_ctor_get(v_rchild_1014_, 3);
lean_inc(v_rchild_1021_);
lean_dec_ref(v_rchild_1014_);
v___y_958_ = v___x_1001_;
v___y_959_ = v___x_1002_;
v___y_960_ = v___x_1000_;
v___y_961_ = v_vy_995_;
v___y_962_ = v_ky_994_;
v_a_963_ = v_b_996_;
v_kx_964_ = v_kz_997_;
v_vx_965_ = v_vz_998_;
v_b_966_ = v_lchild_1005_;
v_ky_967_ = v_key_1016_;
v_vy_968_ = v_val_1017_;
v_c_969_ = v_lchild_1018_;
v_kz_970_ = v_key_1019_;
v_vz_971_ = v_val_1020_;
v_d_972_ = v_rchild_1021_;
goto v___jp_957_;
}
else
{
lean_dec_ref(v_rchild_1014_);
lean_dec_ref(v_lchild_1005_);
v___y_978_ = v___x_1001_;
v___y_979_ = v___x_1002_;
v___y_980_ = v___x_1000_;
v___y_981_ = v_vy_995_;
v___y_982_ = v_ky_994_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
else
{
lean_dec(v_rchild_1014_);
lean_dec_ref(v_lchild_1005_);
v___y_978_ = v___x_1001_;
v___y_979_ = v___x_1002_;
v___y_980_ = v___x_1000_;
v___y_981_ = v_vy_995_;
v___y_982_ = v_ky_994_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
}
else
{
lean_object* v_rchild_1022_; 
v_rchild_1022_ = lean_ctor_get(v___x_1003_, 3);
lean_inc(v_rchild_1022_);
if (lean_obj_tag(v_rchild_1022_) == 1)
{
uint8_t v_color_1023_; 
v_color_1023_ = lean_ctor_get_uint8(v_rchild_1022_, sizeof(void*)*4);
if (v_color_1023_ == 0)
{
lean_object* v_key_1024_; lean_object* v_val_1025_; lean_object* v_lchild_1026_; lean_object* v_key_1027_; lean_object* v_val_1028_; lean_object* v_rchild_1029_; 
v_key_1024_ = lean_ctor_get(v___x_1003_, 1);
lean_inc(v_key_1024_);
v_val_1025_ = lean_ctor_get(v___x_1003_, 2);
lean_inc(v_val_1025_);
lean_dec_ref(v___x_1003_);
v_lchild_1026_ = lean_ctor_get(v_rchild_1022_, 0);
lean_inc(v_lchild_1026_);
v_key_1027_ = lean_ctor_get(v_rchild_1022_, 1);
lean_inc(v_key_1027_);
v_val_1028_ = lean_ctor_get(v_rchild_1022_, 2);
lean_inc(v_val_1028_);
v_rchild_1029_ = lean_ctor_get(v_rchild_1022_, 3);
lean_inc(v_rchild_1029_);
lean_dec_ref(v_rchild_1022_);
v___y_958_ = v___x_1001_;
v___y_959_ = v___x_1002_;
v___y_960_ = v___x_1000_;
v___y_961_ = v_vy_995_;
v___y_962_ = v_ky_994_;
v_a_963_ = v_b_996_;
v_kx_964_ = v_kz_997_;
v_vx_965_ = v_vz_998_;
v_b_966_ = v_lchild_1005_;
v_ky_967_ = v_key_1024_;
v_vy_968_ = v_val_1025_;
v_c_969_ = v_lchild_1026_;
v_kz_970_ = v_key_1027_;
v_vz_971_ = v_val_1028_;
v_d_972_ = v_rchild_1029_;
goto v___jp_957_;
}
else
{
lean_dec_ref(v_rchild_1022_);
lean_dec(v_lchild_1005_);
v___y_978_ = v___x_1001_;
v___y_979_ = v___x_1002_;
v___y_980_ = v___x_1000_;
v___y_981_ = v_vy_995_;
v___y_982_ = v_ky_994_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
else
{
lean_dec(v_rchild_1022_);
lean_dec(v_lchild_1005_);
v___y_978_ = v___x_1001_;
v___y_979_ = v___x_1002_;
v___y_980_ = v___x_1000_;
v___y_981_ = v_vy_995_;
v___y_982_ = v_ky_994_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
}
else
{
v___y_978_ = v___x_1001_;
v___y_979_ = v___x_1002_;
v___y_980_ = v___x_1000_;
v___y_981_ = v_vy_995_;
v___y_982_ = v_ky_994_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
else
{
v___y_978_ = v___x_1001_;
v___y_979_ = v___x_1002_;
v___y_980_ = v___x_1000_;
v___y_981_ = v_vy_995_;
v___y_982_ = v_ky_994_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
v___jp_1030_:
{
uint8_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = 0;
v___x_1036_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1036_, 0, v_l_1031_);
lean_ctor_set(v___x_1036_, 1, v_k_1032_);
lean_ctor_set(v___x_1036_, 2, v_v_1033_);
lean_ctor_set(v___x_1036_, 3, v_r_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*4, v___x_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_RBNode_balLeft___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object* v_l_1086_, lean_object* v_k_1087_, lean_object* v_v_1088_, lean_object* v_r_1089_){
_start:
{
uint8_t v___y_1094_; lean_object* v_a_1095_; lean_object* v_kx_1096_; lean_object* v_vx_1097_; lean_object* v_b_1098_; lean_object* v_ky_1099_; lean_object* v_vy_1100_; lean_object* v_c_1101_; lean_object* v_kz_1102_; lean_object* v_vz_1103_; lean_object* v_d_1104_; lean_object* v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1123_; lean_object* v_a_1124_; lean_object* v_kx_1125_; lean_object* v_vx_1126_; lean_object* v_b_1127_; lean_object* v_ky_1128_; lean_object* v_vy_1129_; lean_object* v_c_1130_; lean_object* v_kz_1131_; lean_object* v_vz_1132_; lean_object* v_d_1133_; lean_object* v___y_1138_; uint8_t v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v_a_1143_; lean_object* v_kx_1144_; lean_object* v_vx_1145_; lean_object* v_b_1146_; 
if (lean_obj_tag(v_r_1089_) == 1)
{
uint8_t v_color_1247_; 
v_color_1247_ = lean_ctor_get_uint8(v_r_1089_, sizeof(void*)*4);
if (v_color_1247_ == 0)
{
lean_object* v_lchild_1248_; lean_object* v_key_1249_; lean_object* v_val_1250_; lean_object* v_rchild_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1260_; 
v_lchild_1248_ = lean_ctor_get(v_r_1089_, 0);
v_key_1249_ = lean_ctor_get(v_r_1089_, 1);
v_val_1250_ = lean_ctor_get(v_r_1089_, 2);
v_rchild_1251_ = lean_ctor_get(v_r_1089_, 3);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_r_1089_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1253_ = v_r_1089_;
v_isShared_1254_ = v_isSharedCheck_1260_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_rchild_1251_);
lean_inc(v_val_1250_);
lean_inc(v_key_1249_);
lean_inc(v_lchild_1248_);
lean_dec(v_r_1089_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1260_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
uint8_t v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = 1;
if (v_isShared_1254_ == 0)
{
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_lchild_1248_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_key_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_val_1250_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_rchild_1251_);
v___x_1257_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; 
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*4, v___x_1255_);
v___x_1258_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1258_, 0, v_l_1086_);
lean_ctor_set(v___x_1258_, 1, v_k_1087_);
lean_ctor_set(v___x_1258_, 2, v_v_1088_);
lean_ctor_set(v___x_1258_, 3, v___x_1257_);
lean_ctor_set_uint8(v___x_1258_, sizeof(void*)*4, v_color_1247_);
return v___x_1258_;
}
}
}
else
{
goto v___jp_1148_;
}
}
else
{
goto v___jp_1148_;
}
v___jp_1090_:
{
uint8_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = 0;
v___x_1092_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1092_, 0, v_l_1086_);
lean_ctor_set(v___x_1092_, 1, v_k_1087_);
lean_ctor_set(v___x_1092_, 2, v_v_1088_);
lean_ctor_set(v___x_1092_, 3, v_r_1089_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*4, v___x_1091_);
return v___x_1092_;
}
v___jp_1093_:
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1105_ = 0;
v___x_1106_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1106_, 0, v_a_1095_);
lean_ctor_set(v___x_1106_, 1, v_kx_1096_);
lean_ctor_set(v___x_1106_, 2, v_vx_1097_);
lean_ctor_set(v___x_1106_, 3, v_b_1098_);
lean_ctor_set_uint8(v___x_1106_, sizeof(void*)*4, v___y_1094_);
v___x_1107_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1107_, 0, v_c_1101_);
lean_ctor_set(v___x_1107_, 1, v_kz_1102_);
lean_ctor_set(v___x_1107_, 2, v_vz_1103_);
lean_ctor_set(v___x_1107_, 3, v_d_1104_);
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*4, v___y_1094_);
v___x_1108_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v_ky_1099_);
lean_ctor_set(v___x_1108_, 2, v_vy_1100_);
lean_ctor_set(v___x_1108_, 3, v___x_1107_);
lean_ctor_set_uint8(v___x_1108_, sizeof(void*)*4, v___x_1105_);
return v___x_1108_;
}
v___jp_1109_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1116_, 0, v___y_1114_);
lean_ctor_set(v___x_1116_, 1, v_k_1087_);
lean_ctor_set(v___x_1116_, 2, v_v_1088_);
lean_ctor_set(v___x_1116_, 3, v_r_1089_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*4, v___y_1111_);
v___x_1117_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1117_, 0, v___y_1115_);
lean_ctor_set(v___x_1117_, 1, v___y_1112_);
lean_ctor_set(v___x_1117_, 2, v___y_1110_);
lean_ctor_set(v___x_1117_, 3, v___x_1116_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*4, v___y_1113_);
return v___x_1117_;
}
v___jp_1118_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1134_, 0, v_a_1124_);
lean_ctor_set(v___x_1134_, 1, v_kx_1125_);
lean_ctor_set(v___x_1134_, 2, v_vx_1126_);
lean_ctor_set(v___x_1134_, 3, v_b_1127_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*4, v___y_1120_);
v___x_1135_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1135_, 0, v_c_1130_);
lean_ctor_set(v___x_1135_, 1, v_kz_1131_);
lean_ctor_set(v___x_1135_, 2, v_vz_1132_);
lean_ctor_set(v___x_1135_, 3, v_d_1133_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*4, v___y_1120_);
v___x_1136_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v_ky_1128_);
lean_ctor_set(v___x_1136_, 2, v_vy_1129_);
lean_ctor_set(v___x_1136_, 3, v___x_1135_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*4, v___y_1122_);
v___y_1110_ = v___y_1119_;
v___y_1111_ = v___y_1120_;
v___y_1112_ = v___y_1121_;
v___y_1113_ = v___y_1122_;
v___y_1114_ = v___y_1123_;
v___y_1115_ = v___x_1136_;
goto v___jp_1109_;
}
v___jp_1137_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1147_, 0, v_a_1143_);
lean_ctor_set(v___x_1147_, 1, v_kx_1144_);
lean_ctor_set(v___x_1147_, 2, v_vx_1145_);
lean_ctor_set(v___x_1147_, 3, v_b_1146_);
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*4, v___y_1139_);
v___y_1110_ = v___y_1138_;
v___y_1111_ = v___y_1139_;
v___y_1112_ = v___y_1140_;
v___y_1113_ = v___y_1141_;
v___y_1114_ = v___y_1142_;
v___y_1115_ = v___x_1147_;
goto v___jp_1109_;
}
v___jp_1148_:
{
if (lean_obj_tag(v_l_1086_) == 1)
{
uint8_t v_color_1149_; 
v_color_1149_ = lean_ctor_get_uint8(v_l_1086_, sizeof(void*)*4);
if (v_color_1149_ == 0)
{
lean_object* v_rchild_1150_; 
v_rchild_1150_ = lean_ctor_get(v_l_1086_, 3);
if (lean_obj_tag(v_rchild_1150_) == 1)
{
uint8_t v_color_1151_; 
v_color_1151_ = lean_ctor_get_uint8(v_rchild_1150_, sizeof(void*)*4);
if (v_color_1151_ == 1)
{
lean_object* v_lchild_1152_; lean_object* v_key_1153_; lean_object* v_val_1154_; lean_object* v_lchild_1155_; lean_object* v_key_1156_; lean_object* v_val_1157_; lean_object* v_rchild_1158_; lean_object* v___x_1159_; 
lean_inc_ref(v_rchild_1150_);
v_lchild_1152_ = lean_ctor_get(v_l_1086_, 0);
lean_inc(v_lchild_1152_);
v_key_1153_ = lean_ctor_get(v_l_1086_, 1);
lean_inc(v_key_1153_);
v_val_1154_ = lean_ctor_get(v_l_1086_, 2);
lean_inc(v_val_1154_);
lean_dec_ref(v_l_1086_);
v_lchild_1155_ = lean_ctor_get(v_rchild_1150_, 0);
lean_inc(v_lchild_1155_);
v_key_1156_ = lean_ctor_get(v_rchild_1150_, 1);
lean_inc(v_key_1156_);
v_val_1157_ = lean_ctor_get(v_rchild_1150_, 2);
lean_inc(v_val_1157_);
v_rchild_1158_ = lean_ctor_get(v_rchild_1150_, 3);
lean_inc(v_rchild_1158_);
lean_dec_ref(v_rchild_1150_);
v___x_1159_ = l_Lean_RBNode_setRed___redArg(v_lchild_1152_);
if (lean_obj_tag(v___x_1159_) == 1)
{
uint8_t v_color_1160_; 
v_color_1160_ = lean_ctor_get_uint8(v___x_1159_, sizeof(void*)*4);
if (v_color_1160_ == 0)
{
lean_object* v_lchild_1161_; 
v_lchild_1161_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_lchild_1161_);
if (lean_obj_tag(v_lchild_1161_) == 1)
{
uint8_t v_color_1162_; 
v_color_1162_ = lean_ctor_get_uint8(v_lchild_1161_, sizeof(void*)*4);
if (v_color_1162_ == 0)
{
lean_object* v_key_1163_; lean_object* v_val_1164_; lean_object* v_rchild_1165_; lean_object* v_lchild_1166_; lean_object* v_key_1167_; lean_object* v_val_1168_; lean_object* v_rchild_1169_; 
v_key_1163_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_key_1163_);
v_val_1164_ = lean_ctor_get(v___x_1159_, 2);
lean_inc(v_val_1164_);
v_rchild_1165_ = lean_ctor_get(v___x_1159_, 3);
lean_inc(v_rchild_1165_);
lean_dec_ref(v___x_1159_);
v_lchild_1166_ = lean_ctor_get(v_lchild_1161_, 0);
lean_inc(v_lchild_1166_);
v_key_1167_ = lean_ctor_get(v_lchild_1161_, 1);
lean_inc(v_key_1167_);
v_val_1168_ = lean_ctor_get(v_lchild_1161_, 2);
lean_inc(v_val_1168_);
v_rchild_1169_ = lean_ctor_get(v_lchild_1161_, 3);
lean_inc(v_rchild_1169_);
lean_dec_ref(v_lchild_1161_);
v___y_1119_ = v_val_1157_;
v___y_1120_ = v_color_1151_;
v___y_1121_ = v_key_1156_;
v___y_1122_ = v_color_1149_;
v___y_1123_ = v_rchild_1158_;
v_a_1124_ = v_lchild_1166_;
v_kx_1125_ = v_key_1167_;
v_vx_1126_ = v_val_1168_;
v_b_1127_ = v_rchild_1169_;
v_ky_1128_ = v_key_1163_;
v_vy_1129_ = v_val_1164_;
v_c_1130_ = v_rchild_1165_;
v_kz_1131_ = v_key_1153_;
v_vz_1132_ = v_val_1154_;
v_d_1133_ = v_lchild_1155_;
goto v___jp_1118_;
}
else
{
lean_object* v_rchild_1170_; 
v_rchild_1170_ = lean_ctor_get(v___x_1159_, 3);
lean_inc(v_rchild_1170_);
if (lean_obj_tag(v_rchild_1170_) == 1)
{
uint8_t v_color_1171_; 
v_color_1171_ = lean_ctor_get_uint8(v_rchild_1170_, sizeof(void*)*4);
if (v_color_1171_ == 0)
{
lean_object* v_key_1172_; lean_object* v_val_1173_; lean_object* v_lchild_1174_; lean_object* v_key_1175_; lean_object* v_val_1176_; lean_object* v_rchild_1177_; 
v_key_1172_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_key_1172_);
v_val_1173_ = lean_ctor_get(v___x_1159_, 2);
lean_inc(v_val_1173_);
lean_dec_ref(v___x_1159_);
v_lchild_1174_ = lean_ctor_get(v_rchild_1170_, 0);
lean_inc(v_lchild_1174_);
v_key_1175_ = lean_ctor_get(v_rchild_1170_, 1);
lean_inc(v_key_1175_);
v_val_1176_ = lean_ctor_get(v_rchild_1170_, 2);
lean_inc(v_val_1176_);
v_rchild_1177_ = lean_ctor_get(v_rchild_1170_, 3);
lean_inc(v_rchild_1177_);
lean_dec_ref(v_rchild_1170_);
v___y_1119_ = v_val_1157_;
v___y_1120_ = v_color_1151_;
v___y_1121_ = v_key_1156_;
v___y_1122_ = v_color_1149_;
v___y_1123_ = v_rchild_1158_;
v_a_1124_ = v_lchild_1161_;
v_kx_1125_ = v_key_1172_;
v_vx_1126_ = v_val_1173_;
v_b_1127_ = v_lchild_1174_;
v_ky_1128_ = v_key_1175_;
v_vy_1129_ = v_val_1176_;
v_c_1130_ = v_rchild_1177_;
v_kz_1131_ = v_key_1153_;
v_vz_1132_ = v_val_1154_;
v_d_1133_ = v_lchild_1155_;
goto v___jp_1118_;
}
else
{
lean_dec_ref(v_rchild_1170_);
lean_dec_ref(v_lchild_1161_);
v___y_1138_ = v_val_1157_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_key_1156_;
v___y_1141_ = v_color_1149_;
v___y_1142_ = v_rchild_1158_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
else
{
lean_dec(v_rchild_1170_);
lean_dec_ref(v_lchild_1161_);
v___y_1138_ = v_val_1157_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_key_1156_;
v___y_1141_ = v_color_1149_;
v___y_1142_ = v_rchild_1158_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
}
else
{
lean_object* v_rchild_1178_; 
v_rchild_1178_ = lean_ctor_get(v___x_1159_, 3);
lean_inc(v_rchild_1178_);
if (lean_obj_tag(v_rchild_1178_) == 1)
{
uint8_t v_color_1179_; 
v_color_1179_ = lean_ctor_get_uint8(v_rchild_1178_, sizeof(void*)*4);
if (v_color_1179_ == 0)
{
lean_object* v_key_1180_; lean_object* v_val_1181_; lean_object* v_lchild_1182_; lean_object* v_key_1183_; lean_object* v_val_1184_; lean_object* v_rchild_1185_; 
v_key_1180_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_key_1180_);
v_val_1181_ = lean_ctor_get(v___x_1159_, 2);
lean_inc(v_val_1181_);
lean_dec_ref(v___x_1159_);
v_lchild_1182_ = lean_ctor_get(v_rchild_1178_, 0);
lean_inc(v_lchild_1182_);
v_key_1183_ = lean_ctor_get(v_rchild_1178_, 1);
lean_inc(v_key_1183_);
v_val_1184_ = lean_ctor_get(v_rchild_1178_, 2);
lean_inc(v_val_1184_);
v_rchild_1185_ = lean_ctor_get(v_rchild_1178_, 3);
lean_inc(v_rchild_1185_);
lean_dec_ref(v_rchild_1178_);
v___y_1119_ = v_val_1157_;
v___y_1120_ = v_color_1151_;
v___y_1121_ = v_key_1156_;
v___y_1122_ = v_color_1149_;
v___y_1123_ = v_rchild_1158_;
v_a_1124_ = v_lchild_1161_;
v_kx_1125_ = v_key_1180_;
v_vx_1126_ = v_val_1181_;
v_b_1127_ = v_lchild_1182_;
v_ky_1128_ = v_key_1183_;
v_vy_1129_ = v_val_1184_;
v_c_1130_ = v_rchild_1185_;
v_kz_1131_ = v_key_1153_;
v_vz_1132_ = v_val_1154_;
v_d_1133_ = v_lchild_1155_;
goto v___jp_1118_;
}
else
{
lean_dec_ref(v_rchild_1178_);
lean_dec(v_lchild_1161_);
v___y_1138_ = v_val_1157_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_key_1156_;
v___y_1141_ = v_color_1149_;
v___y_1142_ = v_rchild_1158_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
else
{
lean_dec(v_rchild_1178_);
lean_dec(v_lchild_1161_);
v___y_1138_ = v_val_1157_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_key_1156_;
v___y_1141_ = v_color_1149_;
v___y_1142_ = v_rchild_1158_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
}
else
{
v___y_1138_ = v_val_1157_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_key_1156_;
v___y_1141_ = v_color_1149_;
v___y_1142_ = v_rchild_1158_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
else
{
v___y_1138_ = v_val_1157_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_key_1156_;
v___y_1141_ = v_color_1149_;
v___y_1142_ = v_rchild_1158_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
else
{
goto v___jp_1090_;
}
}
else
{
goto v___jp_1090_;
}
}
else
{
lean_object* v_lchild_1186_; lean_object* v_key_1187_; lean_object* v_val_1188_; lean_object* v_rchild_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1246_; 
v_lchild_1186_ = lean_ctor_get(v_l_1086_, 0);
v_key_1187_ = lean_ctor_get(v_l_1086_, 1);
v_val_1188_ = lean_ctor_get(v_l_1086_, 2);
v_rchild_1189_ = lean_ctor_get(v_l_1086_, 3);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_l_1086_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1191_ = v_l_1086_;
v_isShared_1192_ = v_isSharedCheck_1246_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_rchild_1189_);
lean_inc(v_val_1188_);
lean_inc(v_key_1187_);
lean_inc(v_lchild_1186_);
lean_dec(v_l_1086_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1246_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = 0;
lean_inc(v_rchild_1189_);
lean_inc(v_val_1188_);
lean_inc(v_key_1187_);
lean_inc(v_lchild_1186_);
if (v_isShared_1192_ == 0)
{
v___x_1195_ = v___x_1191_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_lchild_1186_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_key_1187_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_val_1188_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_rchild_1189_);
v___x_1195_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*4, v___x_1193_);
if (lean_obj_tag(v_lchild_1186_) == 1)
{
uint8_t v_color_1196_; 
v_color_1196_ = lean_ctor_get_uint8(v_lchild_1186_, sizeof(void*)*4);
if (v_color_1196_ == 0)
{
lean_object* v_lchild_1197_; lean_object* v_key_1198_; lean_object* v_val_1199_; lean_object* v_rchild_1200_; 
lean_dec_ref(v___x_1195_);
v_lchild_1197_ = lean_ctor_get(v_lchild_1186_, 0);
lean_inc(v_lchild_1197_);
v_key_1198_ = lean_ctor_get(v_lchild_1186_, 1);
lean_inc(v_key_1198_);
v_val_1199_ = lean_ctor_get(v_lchild_1186_, 2);
lean_inc(v_val_1199_);
v_rchild_1200_ = lean_ctor_get(v_lchild_1186_, 3);
lean_inc(v_rchild_1200_);
lean_dec_ref(v_lchild_1186_);
v___y_1094_ = v_color_1149_;
v_a_1095_ = v_lchild_1197_;
v_kx_1096_ = v_key_1198_;
v_vx_1097_ = v_val_1199_;
v_b_1098_ = v_rchild_1200_;
v_ky_1099_ = v_key_1187_;
v_vy_1100_ = v_val_1188_;
v_c_1101_ = v_rchild_1189_;
v_kz_1102_ = v_k_1087_;
v_vz_1103_ = v_v_1088_;
v_d_1104_ = v_r_1089_;
goto v___jp_1093_;
}
else
{
if (lean_obj_tag(v_rchild_1189_) == 1)
{
uint8_t v_color_1201_; 
v_color_1201_ = lean_ctor_get_uint8(v_rchild_1189_, sizeof(void*)*4);
if (v_color_1201_ == 0)
{
lean_object* v_lchild_1202_; lean_object* v_key_1203_; lean_object* v_val_1204_; lean_object* v_rchild_1205_; 
lean_dec_ref(v___x_1195_);
v_lchild_1202_ = lean_ctor_get(v_rchild_1189_, 0);
lean_inc(v_lchild_1202_);
v_key_1203_ = lean_ctor_get(v_rchild_1189_, 1);
lean_inc(v_key_1203_);
v_val_1204_ = lean_ctor_get(v_rchild_1189_, 2);
lean_inc(v_val_1204_);
v_rchild_1205_ = lean_ctor_get(v_rchild_1189_, 3);
lean_inc(v_rchild_1205_);
lean_dec_ref(v_rchild_1189_);
v___y_1094_ = v_color_1149_;
v_a_1095_ = v_lchild_1186_;
v_kx_1096_ = v_key_1187_;
v_vx_1097_ = v_val_1188_;
v_b_1098_ = v_lchild_1202_;
v_ky_1099_ = v_key_1203_;
v_vy_1100_ = v_val_1204_;
v_c_1101_ = v_rchild_1205_;
v_kz_1102_ = v_k_1087_;
v_vz_1103_ = v_v_1088_;
v_d_1104_ = v_r_1089_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v_lchild_1186_);
lean_dec(v_val_1188_);
lean_dec(v_key_1187_);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_rchild_1189_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; lean_object* v_unused_1214_; lean_object* v_unused_1215_; lean_object* v_unused_1216_; 
v_unused_1213_ = lean_ctor_get(v_rchild_1189_, 3);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_rchild_1189_, 2);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_rchild_1189_, 1);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_rchild_1189_, 0);
lean_dec(v_unused_1216_);
v___x_1207_ = v_rchild_1189_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_dec(v_rchild_1189_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 3, v_r_1089_);
lean_ctor_set(v___x_1207_, 2, v_v_1088_);
lean_ctor_set(v___x_1207_, 1, v_k_1087_);
lean_ctor_set(v___x_1207_, 0, v___x_1195_);
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_r_1089_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*4, v_color_1149_);
return v___x_1210_;
}
}
}
}
else
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_rchild_1189_);
lean_dec(v_val_1188_);
lean_dec(v_key_1187_);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_lchild_1186_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1224_ = lean_ctor_get(v_lchild_1186_, 3);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_lchild_1186_, 2);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_lchild_1186_, 1);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_lchild_1186_, 0);
lean_dec(v_unused_1227_);
v___x_1218_ = v_lchild_1186_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v_lchild_1186_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 3, v_r_1089_);
lean_ctor_set(v___x_1218_, 2, v_v_1088_);
lean_ctor_set(v___x_1218_, 1, v_k_1087_);
lean_ctor_set(v___x_1218_, 0, v___x_1195_);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_r_1089_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*4, v_color_1149_);
return v___x_1221_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_1189_) == 1)
{
uint8_t v_color_1228_; 
v_color_1228_ = lean_ctor_get_uint8(v_rchild_1189_, sizeof(void*)*4);
if (v_color_1228_ == 0)
{
lean_object* v_lchild_1229_; lean_object* v_key_1230_; lean_object* v_val_1231_; lean_object* v_rchild_1232_; 
lean_dec_ref(v___x_1195_);
v_lchild_1229_ = lean_ctor_get(v_rchild_1189_, 0);
lean_inc(v_lchild_1229_);
v_key_1230_ = lean_ctor_get(v_rchild_1189_, 1);
lean_inc(v_key_1230_);
v_val_1231_ = lean_ctor_get(v_rchild_1189_, 2);
lean_inc(v_val_1231_);
v_rchild_1232_ = lean_ctor_get(v_rchild_1189_, 3);
lean_inc(v_rchild_1232_);
lean_dec_ref(v_rchild_1189_);
v___y_1094_ = v_color_1149_;
v_a_1095_ = v_lchild_1186_;
v_kx_1096_ = v_key_1187_;
v_vx_1097_ = v_val_1188_;
v_b_1098_ = v_lchild_1229_;
v_ky_1099_ = v_key_1230_;
v_vy_1100_ = v_val_1231_;
v_c_1101_ = v_rchild_1232_;
v_kz_1102_ = v_k_1087_;
v_vz_1103_ = v_v_1088_;
v_d_1104_ = v_r_1089_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_val_1188_);
lean_dec(v_key_1187_);
lean_dec(v_lchild_1186_);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_rchild_1189_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; lean_object* v_unused_1241_; lean_object* v_unused_1242_; lean_object* v_unused_1243_; 
v_unused_1240_ = lean_ctor_get(v_rchild_1189_, 3);
lean_dec(v_unused_1240_);
v_unused_1241_ = lean_ctor_get(v_rchild_1189_, 2);
lean_dec(v_unused_1241_);
v_unused_1242_ = lean_ctor_get(v_rchild_1189_, 1);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_rchild_1189_, 0);
lean_dec(v_unused_1243_);
v___x_1234_ = v_rchild_1189_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v_rchild_1189_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 3, v_r_1089_);
lean_ctor_set(v___x_1234_, 2, v_v_1088_);
lean_ctor_set(v___x_1234_, 1, v_k_1087_);
lean_ctor_set(v___x_1234_, 0, v___x_1195_);
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_k_1087_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_v_1088_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_r_1089_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*4, v_color_1149_);
return v___x_1237_;
}
}
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v_rchild_1189_);
lean_dec(v_val_1188_);
lean_dec(v_key_1187_);
lean_dec(v_lchild_1186_);
v___x_1244_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1244_, 0, v___x_1195_);
lean_ctor_set(v___x_1244_, 1, v_k_1087_);
lean_ctor_set(v___x_1244_, 2, v_v_1088_);
lean_ctor_set(v___x_1244_, 3, v_r_1089_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*4, v_color_1149_);
return v___x_1244_;
}
}
}
}
}
}
else
{
goto v___jp_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_l_1263_, lean_object* v_k_1264_, lean_object* v_v_1265_, lean_object* v_r_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_RBNode_balRight___redArg(v_l_1263_, v_k_1264_, v_v_1265_, v_r_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_unsigned_to_nat(0u);
return v___x_1269_;
}
else
{
lean_object* v_lchild_1270_; lean_object* v_rchild_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_lchild_1270_ = lean_ctor_get(v_x_1268_, 0);
v_rchild_1271_ = lean_ctor_get(v_x_1268_, 3);
v___x_1272_ = l_Lean_RBNode_size___redArg(v_lchild_1270_);
v___x_1273_ = l_Lean_RBNode_size___redArg(v_rchild_1271_);
v___x_1274_ = lean_nat_add(v___x_1272_, v___x_1273_);
lean_dec(v___x_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_unsigned_to_nat(1u);
v___x_1276_ = lean_nat_add(v___x_1274_, v___x_1275_);
lean_dec(v___x_1274_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object* v_x_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_RBNode_size___redArg(v_x_1277_);
lean_dec(v_x_1277_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object* v_00_u03b1_1279_, lean_object* v_00_u03b2_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_RBNode_size___redArg(v_x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_RBNode_size(v_00_u03b1_1283_, v_00_u03b2_1284_, v_x_1285_);
lean_dec(v_x_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(lean_object* v_x_1287_, lean_object* v_h__1_1288_, lean_object* v_h__2_1289_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v_h__2_1289_);
v___x_1290_ = lean_box(0);
v___x_1291_ = lean_apply_1(v_h__1_1288_, v___x_1290_);
return v___x_1291_;
}
else
{
uint8_t v_color_1292_; lean_object* v_lchild_1293_; lean_object* v_key_1294_; lean_object* v_val_1295_; lean_object* v_rchild_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec(v_h__1_1288_);
v_color_1292_ = lean_ctor_get_uint8(v_x_1287_, sizeof(void*)*4);
v_lchild_1293_ = lean_ctor_get(v_x_1287_, 0);
lean_inc(v_lchild_1293_);
v_key_1294_ = lean_ctor_get(v_x_1287_, 1);
lean_inc(v_key_1294_);
v_val_1295_ = lean_ctor_get(v_x_1287_, 2);
lean_inc(v_val_1295_);
v_rchild_1296_ = lean_ctor_get(v_x_1287_, 3);
lean_inc(v_rchild_1296_);
lean_dec_ref(v_x_1287_);
v___x_1297_ = lean_box(v_color_1292_);
v___x_1298_ = lean_apply_5(v_h__2_1289_, v___x_1297_, v_lchild_1293_, v_key_1294_, v_val_1295_, v_rchild_1296_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_motive_1301_, lean_object* v_x_1302_, lean_object* v_h__1_1303_, lean_object* v_h__2_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(v_x_1302_, v_h__1_1303_, v_h__2_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1306_) == 0)
{
return v_x_1307_;
}
else
{
if (lean_obj_tag(v_x_1307_) == 0)
{
return v_x_1306_;
}
else
{
uint8_t v_color_1308_; lean_object* v_lchild_1309_; lean_object* v_key_1310_; lean_object* v_val_1311_; lean_object* v_rchild_1312_; uint8_t v_color_1313_; lean_object* v_lchild_1314_; lean_object* v_key_1315_; lean_object* v_val_1316_; lean_object* v_rchild_1317_; lean_object* v_bc_1319_; lean_object* v_bc_1323_; 
v_color_1308_ = lean_ctor_get_uint8(v_x_1306_, sizeof(void*)*4);
v_lchild_1309_ = lean_ctor_get(v_x_1306_, 0);
v_key_1310_ = lean_ctor_get(v_x_1306_, 1);
v_val_1311_ = lean_ctor_get(v_x_1306_, 2);
v_rchild_1312_ = lean_ctor_get(v_x_1306_, 3);
v_color_1313_ = lean_ctor_get_uint8(v_x_1307_, sizeof(void*)*4);
v_lchild_1314_ = lean_ctor_get(v_x_1307_, 0);
v_key_1315_ = lean_ctor_get(v_x_1307_, 1);
v_val_1316_ = lean_ctor_get(v_x_1307_, 2);
v_rchild_1317_ = lean_ctor_get(v_x_1307_, 3);
if (v_color_1313_ == 0)
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1360_; 
lean_inc(v_rchild_1317_);
lean_inc(v_val_1316_);
lean_inc(v_key_1315_);
lean_inc(v_lchild_1314_);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_x_1307_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; lean_object* v_unused_1364_; 
v_unused_1361_ = lean_ctor_get(v_x_1307_, 3);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_x_1307_, 2);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_x_1307_, 1);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_x_1307_, 0);
lean_dec(v_unused_1364_);
v___x_1327_ = v_x_1307_;
v_isShared_1328_ = v_isSharedCheck_1360_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_x_1307_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1360_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
if (v_color_1308_ == 0)
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1351_; 
lean_inc(v_rchild_1312_);
lean_inc(v_val_1311_);
lean_inc(v_key_1310_);
lean_inc(v_lchild_1309_);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; 
v_unused_1352_ = lean_ctor_get(v_x_1306_, 3);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_x_1306_, 2);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_x_1306_, 1);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_x_1306_, 0);
lean_dec(v_unused_1355_);
v___x_1330_ = v_x_1306_;
v_isShared_1331_ = v_isSharedCheck_1351_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v_x_1306_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1351_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1312_, v_lchild_1314_);
if (lean_obj_tag(v___x_1332_) == 1)
{
uint8_t v_color_1333_; 
v_color_1333_ = lean_ctor_get_uint8(v___x_1332_, sizeof(void*)*4);
if (v_color_1333_ == 0)
{
lean_object* v_lchild_1334_; lean_object* v_key_1335_; lean_object* v_val_1336_; lean_object* v_rchild_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1350_; 
v_lchild_1334_ = lean_ctor_get(v___x_1332_, 0);
v_key_1335_ = lean_ctor_get(v___x_1332_, 1);
v_val_1336_ = lean_ctor_get(v___x_1332_, 2);
v_rchild_1337_ = lean_ctor_get(v___x_1332_, 3);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1339_ = v___x_1332_;
v_isShared_1340_ = v_isSharedCheck_1350_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_rchild_1337_);
lean_inc(v_val_1336_);
lean_inc(v_key_1335_);
lean_inc(v_lchild_1334_);
lean_dec(v___x_1332_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1350_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 3, v_lchild_1334_);
lean_ctor_set(v___x_1339_, 2, v_val_1311_);
lean_ctor_set(v___x_1339_, 1, v_key_1310_);
lean_ctor_set(v___x_1339_, 0, v_lchild_1309_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_lchild_1309_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_key_1310_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_val_1311_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_lchild_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*4, v_color_1333_);
v___x_1342_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_rchild_1337_);
v___x_1344_ = v___x_1327_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_rchild_1337_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_key_1315_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_val_1316_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_rchild_1317_);
v___x_1344_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*4, v_color_1333_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 3, v___x_1344_);
lean_ctor_set(v___x_1330_, 2, v_val_1336_);
lean_ctor_set(v___x_1330_, 1, v_key_1335_);
lean_ctor_set(v___x_1330_, 0, v___x_1342_);
v___x_1346_ = v___x_1330_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_key_1335_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_val_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*4, v_color_1333_);
return v___x_1346_;
}
}
}
}
}
else
{
lean_del_object(v___x_1330_);
lean_del_object(v___x_1327_);
v_bc_1323_ = v___x_1332_;
goto v___jp_1322_;
}
}
else
{
lean_del_object(v___x_1330_);
lean_del_object(v___x_1327_);
v_bc_1323_ = v___x_1332_;
goto v___jp_1322_;
}
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l_Lean_RBNode_appendTrees___redArg(v_x_1306_, v_lchild_1314_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1356_);
v___x_1358_ = v___x_1327_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_key_1315_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_val_1316_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_rchild_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1359_, sizeof(void*)*4, v_color_1313_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
else
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1399_; 
lean_inc(v_rchild_1312_);
lean_inc(v_val_1311_);
lean_inc(v_key_1310_);
lean_inc(v_lchild_1309_);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1400_ = lean_ctor_get(v_x_1306_, 3);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_x_1306_, 2);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_x_1306_, 1);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_x_1306_, 0);
lean_dec(v_unused_1403_);
v___x_1366_ = v_x_1306_;
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v_x_1306_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1399_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
if (v_color_1308_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1312_, v_x_1307_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 3, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_lchild_1309_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_key_1310_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_val_1311_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v___x_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*4, v_color_1308_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1394_; 
lean_inc(v_rchild_1317_);
lean_inc(v_val_1316_);
lean_inc(v_key_1315_);
lean_inc(v_lchild_1314_);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_x_1307_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; lean_object* v_unused_1396_; lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1395_ = lean_ctor_get(v_x_1307_, 3);
lean_dec(v_unused_1395_);
v_unused_1396_ = lean_ctor_get(v_x_1307_, 2);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_x_1307_, 1);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_x_1307_, 0);
lean_dec(v_unused_1398_);
v___x_1373_ = v_x_1307_;
v_isShared_1374_ = v_isSharedCheck_1394_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v_x_1307_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1394_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1312_, v_lchild_1314_);
if (lean_obj_tag(v___x_1375_) == 1)
{
uint8_t v_color_1376_; 
v_color_1376_ = lean_ctor_get_uint8(v___x_1375_, sizeof(void*)*4);
if (v_color_1376_ == 0)
{
lean_object* v_lchild_1377_; lean_object* v_key_1378_; lean_object* v_val_1379_; lean_object* v_rchild_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1393_; 
v_lchild_1377_ = lean_ctor_get(v___x_1375_, 0);
v_key_1378_ = lean_ctor_get(v___x_1375_, 1);
v_val_1379_ = lean_ctor_get(v___x_1375_, 2);
v_rchild_1380_ = lean_ctor_get(v___x_1375_, 3);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1382_ = v___x_1375_;
v_isShared_1383_ = v_isSharedCheck_1393_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_rchild_1380_);
lean_inc(v_val_1379_);
lean_inc(v_key_1378_);
lean_inc(v_lchild_1377_);
lean_dec(v___x_1375_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1393_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 3, v_lchild_1377_);
lean_ctor_set(v___x_1382_, 2, v_val_1311_);
lean_ctor_set(v___x_1382_, 1, v_key_1310_);
lean_ctor_set(v___x_1382_, 0, v_lchild_1309_);
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_lchild_1309_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_key_1310_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_val_1311_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_lchild_1377_);
v___x_1385_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*4, v_color_1308_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_rchild_1380_);
v___x_1387_ = v___x_1373_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_rchild_1380_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_key_1315_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_val_1316_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_rchild_1317_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*4, v_color_1308_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 3, v___x_1387_);
lean_ctor_set(v___x_1366_, 2, v_val_1379_);
lean_ctor_set(v___x_1366_, 1, v_key_1378_);
lean_ctor_set(v___x_1366_, 0, v___x_1385_);
v___x_1389_ = v___x_1366_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_key_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_val_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*4, v_color_1376_);
return v___x_1389_;
}
}
}
}
}
else
{
lean_del_object(v___x_1373_);
lean_del_object(v___x_1366_);
v_bc_1319_ = v___x_1375_;
goto v___jp_1318_;
}
}
else
{
lean_del_object(v___x_1373_);
lean_del_object(v___x_1366_);
v_bc_1319_ = v___x_1375_;
goto v___jp_1318_;
}
}
}
}
}
v___jp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1320_, 0, v_bc_1319_);
lean_ctor_set(v___x_1320_, 1, v_key_1315_);
lean_ctor_set(v___x_1320_, 2, v_val_1316_);
lean_ctor_set(v___x_1320_, 3, v_rchild_1317_);
lean_ctor_set_uint8(v___x_1320_, sizeof(void*)*4, v_color_1308_);
v___x_1321_ = l_Lean_RBNode_balLeft___redArg(v_lchild_1309_, v_key_1310_, v_val_1311_, v___x_1320_);
return v___x_1321_;
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1324_, 0, v_bc_1323_);
lean_ctor_set(v___x_1324_, 1, v_key_1315_);
lean_ctor_set(v___x_1324_, 2, v_val_1316_);
lean_ctor_set(v___x_1324_, 3, v_rchild_1317_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*4, v_color_1308_);
v___x_1325_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1325_, 0, v_lchild_1309_);
lean_ctor_set(v___x_1325_, 1, v_key_1310_);
lean_ctor_set(v___x_1325_, 2, v_val_1311_);
lean_ctor_set(v___x_1325_, 3, v___x_1324_);
lean_ctor_set_uint8(v___x_1325_, sizeof(void*)*4, v_color_1308_);
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* v_00_u03b1_1404_, lean_object* v_00_u03b2_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_RBNode_appendTrees___redArg(v_x_1406_, v_x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v_h__1_1411_, lean_object* v_h__2_1412_, lean_object* v_h__3_1413_, lean_object* v_h__4_1414_, lean_object* v_h__5_1415_, lean_object* v_h__6_1416_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v___x_1417_; 
lean_dec(v_h__6_1416_);
lean_dec(v_h__5_1415_);
lean_dec(v_h__4_1414_);
lean_dec(v_h__3_1413_);
lean_dec(v_h__2_1412_);
v___x_1417_ = lean_apply_1(v_h__1_1411_, v_x_1410_);
return v___x_1417_;
}
else
{
lean_dec(v_h__1_1411_);
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_h__6_1416_);
lean_dec(v_h__5_1415_);
lean_dec(v_h__4_1414_);
lean_dec(v_h__3_1413_);
v___x_1418_ = lean_apply_2(v_h__2_1412_, v_x_1409_, lean_box(0));
return v___x_1418_;
}
else
{
uint8_t v_color_1419_; 
lean_dec(v_h__2_1412_);
v_color_1419_ = lean_ctor_get_uint8(v_x_1410_, sizeof(void*)*4);
if (v_color_1419_ == 0)
{
uint8_t v_color_1420_; 
lean_dec(v_h__6_1416_);
lean_dec(v_h__4_1414_);
v_color_1420_ = lean_ctor_get_uint8(v_x_1409_, sizeof(void*)*4);
if (v_color_1420_ == 0)
{
lean_object* v_lchild_1421_; lean_object* v_key_1422_; lean_object* v_val_1423_; lean_object* v_rchild_1424_; lean_object* v_lchild_1425_; lean_object* v_key_1426_; lean_object* v_val_1427_; lean_object* v_rchild_1428_; lean_object* v___x_1429_; 
lean_dec(v_h__5_1415_);
v_lchild_1421_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_lchild_1421_);
v_key_1422_ = lean_ctor_get(v_x_1409_, 1);
lean_inc(v_key_1422_);
v_val_1423_ = lean_ctor_get(v_x_1409_, 2);
lean_inc(v_val_1423_);
v_rchild_1424_ = lean_ctor_get(v_x_1409_, 3);
lean_inc(v_rchild_1424_);
lean_dec_ref(v_x_1409_);
v_lchild_1425_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_lchild_1425_);
v_key_1426_ = lean_ctor_get(v_x_1410_, 1);
lean_inc(v_key_1426_);
v_val_1427_ = lean_ctor_get(v_x_1410_, 2);
lean_inc(v_val_1427_);
v_rchild_1428_ = lean_ctor_get(v_x_1410_, 3);
lean_inc(v_rchild_1428_);
lean_dec_ref(v_x_1410_);
v___x_1429_ = lean_apply_8(v_h__3_1413_, v_lchild_1421_, v_key_1422_, v_val_1423_, v_rchild_1424_, v_lchild_1425_, v_key_1426_, v_val_1427_, v_rchild_1428_);
return v___x_1429_;
}
else
{
lean_object* v_lchild_1430_; lean_object* v_key_1431_; lean_object* v_val_1432_; lean_object* v_rchild_1433_; lean_object* v___x_1434_; 
lean_dec(v_h__3_1413_);
v_lchild_1430_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_lchild_1430_);
v_key_1431_ = lean_ctor_get(v_x_1410_, 1);
lean_inc(v_key_1431_);
v_val_1432_ = lean_ctor_get(v_x_1410_, 2);
lean_inc(v_val_1432_);
v_rchild_1433_ = lean_ctor_get(v_x_1410_, 3);
lean_inc(v_rchild_1433_);
lean_dec_ref(v_x_1410_);
v___x_1434_ = lean_apply_7(v_h__5_1415_, v_x_1409_, v_lchild_1430_, v_key_1431_, v_val_1432_, v_rchild_1433_, lean_box(0), lean_box(0));
return v___x_1434_;
}
}
else
{
uint8_t v_color_1435_; 
lean_dec(v_h__5_1415_);
lean_dec(v_h__3_1413_);
v_color_1435_ = lean_ctor_get_uint8(v_x_1409_, sizeof(void*)*4);
if (v_color_1435_ == 0)
{
lean_object* v_lchild_1436_; lean_object* v_key_1437_; lean_object* v_val_1438_; lean_object* v_rchild_1439_; lean_object* v___x_1440_; 
lean_dec(v_h__4_1414_);
v_lchild_1436_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_lchild_1436_);
v_key_1437_ = lean_ctor_get(v_x_1409_, 1);
lean_inc(v_key_1437_);
v_val_1438_ = lean_ctor_get(v_x_1409_, 2);
lean_inc(v_val_1438_);
v_rchild_1439_ = lean_ctor_get(v_x_1409_, 3);
lean_inc(v_rchild_1439_);
lean_dec_ref(v_x_1409_);
v___x_1440_ = lean_apply_7(v_h__6_1416_, v_lchild_1436_, v_key_1437_, v_val_1438_, v_rchild_1439_, v_x_1410_, lean_box(0), lean_box(0));
return v___x_1440_;
}
else
{
lean_object* v_lchild_1441_; lean_object* v_key_1442_; lean_object* v_val_1443_; lean_object* v_rchild_1444_; lean_object* v_lchild_1445_; lean_object* v_key_1446_; lean_object* v_val_1447_; lean_object* v_rchild_1448_; lean_object* v___x_1449_; 
lean_dec(v_h__6_1416_);
v_lchild_1441_ = lean_ctor_get(v_x_1409_, 0);
lean_inc(v_lchild_1441_);
v_key_1442_ = lean_ctor_get(v_x_1409_, 1);
lean_inc(v_key_1442_);
v_val_1443_ = lean_ctor_get(v_x_1409_, 2);
lean_inc(v_val_1443_);
v_rchild_1444_ = lean_ctor_get(v_x_1409_, 3);
lean_inc(v_rchild_1444_);
lean_dec_ref(v_x_1409_);
v_lchild_1445_ = lean_ctor_get(v_x_1410_, 0);
lean_inc(v_lchild_1445_);
v_key_1446_ = lean_ctor_get(v_x_1410_, 1);
lean_inc(v_key_1446_);
v_val_1447_ = lean_ctor_get(v_x_1410_, 2);
lean_inc(v_val_1447_);
v_rchild_1448_ = lean_ctor_get(v_x_1410_, 3);
lean_inc(v_rchild_1448_);
lean_dec_ref(v_x_1410_);
v___x_1449_ = lean_apply_8(v_h__4_1414_, v_lchild_1441_, v_key_1442_, v_val_1443_, v_rchild_1444_, v_lchild_1445_, v_key_1446_, v_val_1447_, v_rchild_1448_);
return v___x_1449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_motive_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_h__1_1455_, lean_object* v_h__2_1456_, lean_object* v_h__3_1457_, lean_object* v_h__4_1458_, lean_object* v_h__5_1459_, lean_object* v_h__6_1460_){
_start:
{
if (lean_obj_tag(v_x_1453_) == 0)
{
lean_object* v___x_1461_; 
lean_dec(v_h__6_1460_);
lean_dec(v_h__5_1459_);
lean_dec(v_h__4_1458_);
lean_dec(v_h__3_1457_);
lean_dec(v_h__2_1456_);
v___x_1461_ = lean_apply_1(v_h__1_1455_, v_x_1454_);
return v___x_1461_;
}
else
{
lean_dec(v_h__1_1455_);
if (lean_obj_tag(v_x_1454_) == 0)
{
lean_object* v___x_1462_; 
lean_dec(v_h__6_1460_);
lean_dec(v_h__5_1459_);
lean_dec(v_h__4_1458_);
lean_dec(v_h__3_1457_);
v___x_1462_ = lean_apply_2(v_h__2_1456_, v_x_1453_, lean_box(0));
return v___x_1462_;
}
else
{
uint8_t v_color_1463_; 
lean_dec(v_h__2_1456_);
v_color_1463_ = lean_ctor_get_uint8(v_x_1454_, sizeof(void*)*4);
if (v_color_1463_ == 0)
{
uint8_t v_color_1464_; 
lean_dec(v_h__6_1460_);
lean_dec(v_h__4_1458_);
v_color_1464_ = lean_ctor_get_uint8(v_x_1453_, sizeof(void*)*4);
if (v_color_1464_ == 0)
{
lean_object* v_lchild_1465_; lean_object* v_key_1466_; lean_object* v_val_1467_; lean_object* v_rchild_1468_; lean_object* v_lchild_1469_; lean_object* v_key_1470_; lean_object* v_val_1471_; lean_object* v_rchild_1472_; lean_object* v___x_1473_; 
lean_dec(v_h__5_1459_);
v_lchild_1465_ = lean_ctor_get(v_x_1453_, 0);
lean_inc(v_lchild_1465_);
v_key_1466_ = lean_ctor_get(v_x_1453_, 1);
lean_inc(v_key_1466_);
v_val_1467_ = lean_ctor_get(v_x_1453_, 2);
lean_inc(v_val_1467_);
v_rchild_1468_ = lean_ctor_get(v_x_1453_, 3);
lean_inc(v_rchild_1468_);
lean_dec_ref(v_x_1453_);
v_lchild_1469_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_lchild_1469_);
v_key_1470_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_key_1470_);
v_val_1471_ = lean_ctor_get(v_x_1454_, 2);
lean_inc(v_val_1471_);
v_rchild_1472_ = lean_ctor_get(v_x_1454_, 3);
lean_inc(v_rchild_1472_);
lean_dec_ref(v_x_1454_);
v___x_1473_ = lean_apply_8(v_h__3_1457_, v_lchild_1465_, v_key_1466_, v_val_1467_, v_rchild_1468_, v_lchild_1469_, v_key_1470_, v_val_1471_, v_rchild_1472_);
return v___x_1473_;
}
else
{
lean_object* v_lchild_1474_; lean_object* v_key_1475_; lean_object* v_val_1476_; lean_object* v_rchild_1477_; lean_object* v___x_1478_; 
lean_dec(v_h__3_1457_);
v_lchild_1474_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_lchild_1474_);
v_key_1475_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_key_1475_);
v_val_1476_ = lean_ctor_get(v_x_1454_, 2);
lean_inc(v_val_1476_);
v_rchild_1477_ = lean_ctor_get(v_x_1454_, 3);
lean_inc(v_rchild_1477_);
lean_dec_ref(v_x_1454_);
v___x_1478_ = lean_apply_7(v_h__5_1459_, v_x_1453_, v_lchild_1474_, v_key_1475_, v_val_1476_, v_rchild_1477_, lean_box(0), lean_box(0));
return v___x_1478_;
}
}
else
{
uint8_t v_color_1479_; 
lean_dec(v_h__5_1459_);
lean_dec(v_h__3_1457_);
v_color_1479_ = lean_ctor_get_uint8(v_x_1453_, sizeof(void*)*4);
if (v_color_1479_ == 0)
{
lean_object* v_lchild_1480_; lean_object* v_key_1481_; lean_object* v_val_1482_; lean_object* v_rchild_1483_; lean_object* v___x_1484_; 
lean_dec(v_h__4_1458_);
v_lchild_1480_ = lean_ctor_get(v_x_1453_, 0);
lean_inc(v_lchild_1480_);
v_key_1481_ = lean_ctor_get(v_x_1453_, 1);
lean_inc(v_key_1481_);
v_val_1482_ = lean_ctor_get(v_x_1453_, 2);
lean_inc(v_val_1482_);
v_rchild_1483_ = lean_ctor_get(v_x_1453_, 3);
lean_inc(v_rchild_1483_);
lean_dec_ref(v_x_1453_);
v___x_1484_ = lean_apply_7(v_h__6_1460_, v_lchild_1480_, v_key_1481_, v_val_1482_, v_rchild_1483_, v_x_1454_, lean_box(0), lean_box(0));
return v___x_1484_;
}
else
{
lean_object* v_lchild_1485_; lean_object* v_key_1486_; lean_object* v_val_1487_; lean_object* v_rchild_1488_; lean_object* v_lchild_1489_; lean_object* v_key_1490_; lean_object* v_val_1491_; lean_object* v_rchild_1492_; lean_object* v___x_1493_; 
lean_dec(v_h__6_1460_);
v_lchild_1485_ = lean_ctor_get(v_x_1453_, 0);
lean_inc(v_lchild_1485_);
v_key_1486_ = lean_ctor_get(v_x_1453_, 1);
lean_inc(v_key_1486_);
v_val_1487_ = lean_ctor_get(v_x_1453_, 2);
lean_inc(v_val_1487_);
v_rchild_1488_ = lean_ctor_get(v_x_1453_, 3);
lean_inc(v_rchild_1488_);
lean_dec_ref(v_x_1453_);
v_lchild_1489_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_lchild_1489_);
v_key_1490_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_key_1490_);
v_val_1491_ = lean_ctor_get(v_x_1454_, 2);
lean_inc(v_val_1491_);
v_rchild_1492_ = lean_ctor_get(v_x_1454_, 3);
lean_inc(v_rchild_1492_);
lean_dec_ref(v_x_1454_);
v___x_1493_ = lean_apply_8(v_h__4_1458_, v_lchild_1485_, v_key_1486_, v_val_1487_, v_rchild_1488_, v_lchild_1489_, v_key_1490_, v_val_1491_, v_rchild_1492_);
return v___x_1493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* v_x_1494_, lean_object* v_h__1_1495_, lean_object* v_h__2_1496_){
_start:
{
if (lean_obj_tag(v_x_1494_) == 1)
{
uint8_t v_color_1497_; 
v_color_1497_ = lean_ctor_get_uint8(v_x_1494_, sizeof(void*)*4);
if (v_color_1497_ == 0)
{
lean_object* v_lchild_1498_; lean_object* v_key_1499_; lean_object* v_val_1500_; lean_object* v_rchild_1501_; lean_object* v___x_1502_; 
lean_dec(v_h__2_1496_);
v_lchild_1498_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_lchild_1498_);
v_key_1499_ = lean_ctor_get(v_x_1494_, 1);
lean_inc(v_key_1499_);
v_val_1500_ = lean_ctor_get(v_x_1494_, 2);
lean_inc(v_val_1500_);
v_rchild_1501_ = lean_ctor_get(v_x_1494_, 3);
lean_inc(v_rchild_1501_);
lean_dec_ref(v_x_1494_);
v___x_1502_ = lean_apply_4(v_h__1_1495_, v_lchild_1498_, v_key_1499_, v_val_1500_, v_rchild_1501_);
return v___x_1502_;
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_h__1_1495_);
v___x_1503_ = lean_apply_2(v_h__2_1496_, v_x_1494_, lean_box(0));
return v___x_1503_;
}
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_h__1_1495_);
v___x_1504_ = lean_apply_2(v_h__2_1496_, v_x_1494_, lean_box(0));
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_motive_1507_, lean_object* v_x_1508_, lean_object* v_h__1_1509_, lean_object* v_h__2_1510_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 1)
{
uint8_t v_color_1511_; 
v_color_1511_ = lean_ctor_get_uint8(v_x_1508_, sizeof(void*)*4);
if (v_color_1511_ == 0)
{
lean_object* v_lchild_1512_; lean_object* v_key_1513_; lean_object* v_val_1514_; lean_object* v_rchild_1515_; lean_object* v___x_1516_; 
lean_dec(v_h__2_1510_);
v_lchild_1512_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_lchild_1512_);
v_key_1513_ = lean_ctor_get(v_x_1508_, 1);
lean_inc(v_key_1513_);
v_val_1514_ = lean_ctor_get(v_x_1508_, 2);
lean_inc(v_val_1514_);
v_rchild_1515_ = lean_ctor_get(v_x_1508_, 3);
lean_inc(v_rchild_1515_);
lean_dec_ref(v_x_1508_);
v___x_1516_ = lean_apply_4(v_h__1_1509_, v_lchild_1512_, v_key_1513_, v_val_1514_, v_rchild_1515_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; 
lean_dec(v_h__1_1509_);
v___x_1517_ = lean_apply_2(v_h__2_1510_, v_x_1508_, lean_box(0));
return v___x_1517_;
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_h__1_1509_);
v___x_1518_ = lean_apply_2(v_h__2_1510_, v_x_1508_, lean_box(0));
return v___x_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* v_cmp_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_dec(v_x_1520_);
lean_dec_ref(v_cmp_1519_);
return v_x_1521_;
}
else
{
lean_object* v_lchild_1522_; lean_object* v_key_1523_; lean_object* v_val_1524_; lean_object* v_rchild_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1548_; 
v_lchild_1522_ = lean_ctor_get(v_x_1521_, 0);
v_key_1523_ = lean_ctor_get(v_x_1521_, 1);
v_val_1524_ = lean_ctor_get(v_x_1521_, 2);
v_rchild_1525_ = lean_ctor_get(v_x_1521_, 3);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1527_ = v_x_1521_;
v_isShared_1528_ = v_isSharedCheck_1548_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_rchild_1525_);
lean_inc(v_val_1524_);
lean_inc(v_key_1523_);
lean_inc(v_lchild_1522_);
lean_dec(v_x_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1548_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
lean_inc_ref(v_cmp_1519_);
lean_inc(v_key_1523_);
lean_inc(v_x_1520_);
v___x_1529_ = lean_apply_2(v_cmp_1519_, v_x_1520_, v_key_1523_);
v___x_1530_ = lean_unbox(v___x_1529_);
switch(v___x_1530_)
{
case 0:
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1522_);
if (v___x_1531_ == 0)
{
uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = 0;
v___x_1533_ = l_Lean_RBNode_del___redArg(v_cmp_1519_, v_x_1520_, v_lchild_1522_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1533_);
v___x_1535_ = v___x_1527_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_key_1523_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_val_1524_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_rchild_1525_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*4, v___x_1532_);
return v___x_1535_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_del_object(v___x_1527_);
v___x_1537_ = l_Lean_RBNode_del___redArg(v_cmp_1519_, v_x_1520_, v_lchild_1522_);
v___x_1538_ = l_Lean_RBNode_balLeft___redArg(v___x_1537_, v_key_1523_, v_val_1524_, v_rchild_1525_);
return v___x_1538_;
}
}
case 1:
{
lean_object* v___x_1539_; 
lean_del_object(v___x_1527_);
lean_dec(v_val_1524_);
lean_dec(v_key_1523_);
lean_dec(v_x_1520_);
lean_dec_ref(v_cmp_1519_);
v___x_1539_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_1522_, v_rchild_1525_);
return v___x_1539_;
}
default: 
{
uint8_t v___x_1540_; 
v___x_1540_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1525_);
if (v___x_1540_ == 0)
{
uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1541_ = 0;
v___x_1542_ = l_Lean_RBNode_del___redArg(v_cmp_1519_, v_x_1520_, v_rchild_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 3, v___x_1542_);
v___x_1544_ = v___x_1527_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_lchild_1522_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_key_1523_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_val_1524_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*4, v___x_1541_);
return v___x_1544_;
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_del_object(v___x_1527_);
v___x_1546_ = l_Lean_RBNode_del___redArg(v_cmp_1519_, v_x_1520_, v_rchild_1525_);
v___x_1547_ = l_Lean_RBNode_balRight___redArg(v_lchild_1522_, v_key_1523_, v_val_1524_, v___x_1546_);
return v___x_1547_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_cmp_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_RBNode_del___redArg(v_cmp_1551_, v_x_1552_, v_x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* v_cmp_1555_, lean_object* v_x_1556_, lean_object* v_t_1557_){
_start:
{
lean_object* v_t_1558_; lean_object* v___x_1559_; 
v_t_1558_ = l_Lean_RBNode_del___redArg(v_cmp_1555_, v_x_1556_, v_t_1557_);
v___x_1559_ = l_Lean_RBNode_setBlack___redArg(v_t_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* v_00_u03b1_1560_, lean_object* v_00_u03b2_1561_, lean_object* v_cmp_1562_, lean_object* v_x_1563_, lean_object* v_t_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_RBNode_erase___redArg(v_cmp_1562_, v_x_1563_, v_t_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* v_cmp_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1567_) == 0)
{
lean_object* v___x_1569_; 
lean_dec(v_x_1568_);
lean_dec_ref(v_cmp_1566_);
v___x_1569_ = lean_box(0);
return v___x_1569_;
}
else
{
lean_object* v_lchild_1570_; lean_object* v_key_1571_; lean_object* v_val_1572_; lean_object* v_rchild_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_lchild_1570_ = lean_ctor_get(v_x_1567_, 0);
lean_inc(v_lchild_1570_);
v_key_1571_ = lean_ctor_get(v_x_1567_, 1);
lean_inc(v_key_1571_);
v_val_1572_ = lean_ctor_get(v_x_1567_, 2);
lean_inc(v_val_1572_);
v_rchild_1573_ = lean_ctor_get(v_x_1567_, 3);
lean_inc(v_rchild_1573_);
lean_dec_ref(v_x_1567_);
lean_inc_ref(v_cmp_1566_);
lean_inc(v_key_1571_);
lean_inc(v_x_1568_);
v___x_1574_ = lean_apply_2(v_cmp_1566_, v_x_1568_, v_key_1571_);
v___x_1575_ = lean_unbox(v___x_1574_);
switch(v___x_1575_)
{
case 0:
{
lean_dec(v_rchild_1573_);
lean_dec(v_val_1572_);
lean_dec(v_key_1571_);
v_x_1567_ = v_lchild_1570_;
goto _start;
}
case 1:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v_rchild_1573_);
lean_dec(v_lchild_1570_);
lean_dec(v_x_1568_);
lean_dec_ref(v_cmp_1566_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_key_1571_);
lean_ctor_set(v___x_1577_, 1, v_val_1572_);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
default: 
{
lean_dec(v_val_1572_);
lean_dec(v_key_1571_);
lean_dec(v_lchild_1570_);
v_x_1567_ = v_rchild_1573_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_cmp_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_RBNode_findCore___redArg(v_cmp_1582_, v_x_1583_, v_x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* v_cmp_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 0)
{
lean_object* v___x_1589_; 
lean_dec(v_x_1588_);
lean_dec_ref(v_cmp_1586_);
v___x_1589_ = lean_box(0);
return v___x_1589_;
}
else
{
lean_object* v_lchild_1590_; lean_object* v_key_1591_; lean_object* v_val_1592_; lean_object* v_rchild_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_lchild_1590_ = lean_ctor_get(v_x_1587_, 0);
lean_inc(v_lchild_1590_);
v_key_1591_ = lean_ctor_get(v_x_1587_, 1);
lean_inc(v_key_1591_);
v_val_1592_ = lean_ctor_get(v_x_1587_, 2);
lean_inc(v_val_1592_);
v_rchild_1593_ = lean_ctor_get(v_x_1587_, 3);
lean_inc(v_rchild_1593_);
lean_dec_ref(v_x_1587_);
lean_inc_ref(v_cmp_1586_);
lean_inc(v_x_1588_);
v___x_1594_ = lean_apply_2(v_cmp_1586_, v_x_1588_, v_key_1591_);
v___x_1595_ = lean_unbox(v___x_1594_);
switch(v___x_1595_)
{
case 0:
{
lean_dec(v_rchild_1593_);
lean_dec(v_val_1592_);
v_x_1587_ = v_lchild_1590_;
goto _start;
}
case 1:
{
lean_object* v___x_1597_; 
lean_dec(v_rchild_1593_);
lean_dec(v_lchild_1590_);
lean_dec(v_x_1588_);
lean_dec_ref(v_cmp_1586_);
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_val_1592_);
return v___x_1597_;
}
default: 
{
lean_dec(v_val_1592_);
lean_dec(v_lchild_1590_);
v_x_1587_ = v_rchild_1593_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* v_00_u03b1_1599_, lean_object* v_cmp_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_RBNode_find___redArg(v_cmp_1600_, v_x_1602_, v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* v_cmp_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1606_) == 0)
{
lean_dec(v_x_1607_);
lean_dec_ref(v_cmp_1605_);
return v_x_1608_;
}
else
{
lean_object* v_lchild_1609_; lean_object* v_key_1610_; lean_object* v_val_1611_; lean_object* v_rchild_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_lchild_1609_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_lchild_1609_);
v_key_1610_ = lean_ctor_get(v_x_1606_, 1);
lean_inc(v_key_1610_);
v_val_1611_ = lean_ctor_get(v_x_1606_, 2);
lean_inc(v_val_1611_);
v_rchild_1612_ = lean_ctor_get(v_x_1606_, 3);
lean_inc(v_rchild_1612_);
lean_dec_ref(v_x_1606_);
lean_inc_ref(v_cmp_1605_);
lean_inc(v_key_1610_);
lean_inc(v_x_1607_);
v___x_1613_ = lean_apply_2(v_cmp_1605_, v_x_1607_, v_key_1610_);
v___x_1614_ = lean_unbox(v___x_1613_);
switch(v___x_1614_)
{
case 0:
{
lean_dec(v_rchild_1612_);
lean_dec(v_val_1611_);
lean_dec(v_key_1610_);
v_x_1606_ = v_lchild_1609_;
goto _start;
}
case 1:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v_rchild_1612_);
lean_dec(v_lchild_1609_);
lean_dec(v_x_1608_);
lean_dec(v_x_1607_);
lean_dec_ref(v_cmp_1605_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_key_1610_);
lean_ctor_set(v___x_1616_, 1, v_val_1611_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
default: 
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_lchild_1609_);
lean_dec(v_x_1608_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_key_1610_);
lean_ctor_set(v___x_1618_, 1, v_val_1611_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v_x_1606_ = v_rchild_1612_;
v_x_1608_ = v___x_1619_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* v_00_u03b1_1621_, lean_object* v_00_u03b2_1622_, lean_object* v_cmp_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_1623_, v_x_1624_, v_x_1625_, v_x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t v_color_1628_, lean_object* v_key_1629_, lean_object* v_x1_1630_, lean_object* v_x2_1631_, lean_object* v_x3_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1633_, 0, v_x1_1630_);
lean_ctor_set(v___x_1633_, 1, v_key_1629_);
lean_ctor_set(v___x_1633_, 2, v_x2_1631_);
lean_ctor_set(v___x_1633_, 3, v_x3_1632_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*4, v_color_1628_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* v_color_1634_, lean_object* v_key_1635_, lean_object* v_x1_1636_, lean_object* v_x2_1637_, lean_object* v_x3_1638_){
_start:
{
uint8_t v_color_88__boxed_1639_; lean_object* v_res_1640_; 
v_color_88__boxed_1639_ = lean_unbox(v_color_1634_);
v_res_1640_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_88__boxed_1639_, v_key_1635_, v_x1_1636_, v_x2_1637_, v_x3_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* v_f_1641_, lean_object* v_key_1642_, lean_object* v_val_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_apply_2(v_f_1641_, v_key_1642_, v_val_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* v_inst_1646_, lean_object* v_f_1647_, lean_object* v_lchild_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_RBNode_mapM___redArg(v_inst_1646_, v_f_1647_, v_lchild_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* v_inst_1651_, lean_object* v_f_1652_, lean_object* v_x_1653_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v_toPure_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec(v_f_1652_);
v_toPure_1654_ = lean_ctor_get(v_inst_1651_, 1);
lean_inc(v_toPure_1654_);
lean_dec_ref(v_inst_1651_);
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_apply_2(v_toPure_1654_, lean_box(0), v___x_1655_);
return v___x_1656_;
}
else
{
lean_object* v_toPure_1657_; lean_object* v_toSeq_1658_; uint8_t v_color_1659_; lean_object* v_lchild_1660_; lean_object* v_key_1661_; lean_object* v_val_1662_; lean_object* v_rchild_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_toPure_1657_ = lean_ctor_get(v_inst_1651_, 1);
lean_inc(v_toPure_1657_);
v_toSeq_1658_ = lean_ctor_get(v_inst_1651_, 2);
lean_inc(v_toSeq_1658_);
v_color_1659_ = lean_ctor_get_uint8(v_x_1653_, sizeof(void*)*4);
v_lchild_1660_ = lean_ctor_get(v_x_1653_, 0);
lean_inc(v_lchild_1660_);
v_key_1661_ = lean_ctor_get(v_x_1653_, 1);
lean_inc(v_key_1661_);
v_val_1662_ = lean_ctor_get(v_x_1653_, 2);
lean_inc(v_val_1662_);
v_rchild_1663_ = lean_ctor_get(v_x_1653_, 3);
lean_inc(v_rchild_1663_);
lean_dec_ref(v_x_1653_);
lean_inc(v_f_1652_);
lean_inc_ref(v_inst_1651_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1664_, 0, v_inst_1651_);
lean_closure_set(v___f_1664_, 1, v_f_1652_);
lean_closure_set(v___f_1664_, 2, v_rchild_1663_);
lean_inc(v_key_1661_);
lean_inc(v_f_1652_);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1665_, 0, v_f_1652_);
lean_closure_set(v___f_1665_, 1, v_key_1661_);
lean_closure_set(v___f_1665_, 2, v_val_1662_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1666_, 0, v_inst_1651_);
lean_closure_set(v___f_1666_, 1, v_f_1652_);
lean_closure_set(v___f_1666_, 2, v_lchild_1660_);
v___x_1667_ = lean_box(v_color_1659_);
v___f_1668_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1668_, 0, v___x_1667_);
lean_closure_set(v___f_1668_, 1, v_key_1661_);
v___x_1669_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___f_1668_);
lean_inc(v_toSeq_1658_);
v___x_1670_ = lean_apply_4(v_toSeq_1658_, lean_box(0), lean_box(0), v___x_1669_, v___f_1666_);
lean_inc(v_toSeq_1658_);
v___x_1671_ = lean_apply_4(v_toSeq_1658_, lean_box(0), lean_box(0), v___x_1670_, v___f_1665_);
v___x_1672_ = lean_apply_4(v_toSeq_1658_, lean_box(0), lean_box(0), v___x_1671_, v___f_1664_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* v_inst_1673_, lean_object* v_f_1674_, lean_object* v_rchild_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_RBNode_mapM___redArg(v_inst_1673_, v_f_1674_, v_rchild_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* v_00_u03b1_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_00_u03b3_1680_, lean_object* v_M_1681_, lean_object* v_inst_1682_, lean_object* v_f_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_RBNode_mapM___redArg(v_inst_1682_, v_f_1683_, v_x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* v_f_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_object* v___x_1688_; 
lean_dec(v_f_1686_);
v___x_1688_ = lean_box(0);
return v___x_1688_;
}
else
{
uint8_t v_color_1689_; lean_object* v_lchild_1690_; lean_object* v_key_1691_; lean_object* v_val_1692_; lean_object* v_rchild_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1703_; 
v_color_1689_ = lean_ctor_get_uint8(v_x_1687_, sizeof(void*)*4);
v_lchild_1690_ = lean_ctor_get(v_x_1687_, 0);
v_key_1691_ = lean_ctor_get(v_x_1687_, 1);
v_val_1692_ = lean_ctor_get(v_x_1687_, 2);
v_rchild_1693_ = lean_ctor_get(v_x_1687_, 3);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1695_ = v_x_1687_;
v_isShared_1696_ = v_isSharedCheck_1703_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_rchild_1693_);
lean_inc(v_val_1692_);
lean_inc(v_key_1691_);
lean_inc(v_lchild_1690_);
lean_dec(v_x_1687_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1703_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_inc(v_f_1686_);
v___x_1697_ = l_Lean_RBNode_map___redArg(v_f_1686_, v_lchild_1690_);
lean_inc(v_f_1686_);
lean_inc(v_key_1691_);
v___x_1698_ = lean_apply_2(v_f_1686_, v_key_1691_, v_val_1692_);
v___x_1699_ = l_Lean_RBNode_map___redArg(v_f_1686_, v_rchild_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 3, v___x_1699_);
lean_ctor_set(v___x_1695_, 2, v___x_1698_);
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1701_ = v___x_1695_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_key_1691_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v___x_1699_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*4, v_color_1689_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* v_00_u03b1_1704_, lean_object* v_00_u03b2_1705_, lean_object* v_00_u03b3_1706_, lean_object* v_f_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_RBNode_map___redArg(v_f_1707_, v_x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
return v_x_1710_;
}
else
{
lean_object* v_lchild_1712_; lean_object* v_key_1713_; lean_object* v_val_1714_; lean_object* v_rchild_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_lchild_1712_ = lean_ctor_get(v_x_1711_, 0);
v_key_1713_ = lean_ctor_get(v_x_1711_, 1);
v_val_1714_ = lean_ctor_get(v_x_1711_, 2);
v_rchild_1715_ = lean_ctor_get(v_x_1711_, 3);
v___x_1716_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1710_, v_lchild_1712_);
lean_inc(v_val_1714_);
lean_inc(v_key_1713_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_key_1713_);
lean_ctor_set(v___x_1717_, 1, v_val_1714_);
v___x_1718_ = lean_array_push(v___x_1716_, v___x_1717_);
v_x_1710_ = v___x_1718_;
v_x_1711_ = v_rchild_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1720_, v_x_1721_);
lean_dec(v_x_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* v_n_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
v___x_1727_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_1726_, v_n_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* v_n_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_RBNode_toArray___redArg(v_n_1728_);
lean_dec(v_n_1728_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_n_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_RBNode_toArray___redArg(v_n_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_n_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_RBNode_toArray(v_00_u03b1_1734_, v_00_u03b2_1735_, v_n_1736_);
lean_dec(v_n_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1740_, v_x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b2_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(v_00_u03b1_1743_, v_00_u03b2_1744_, v_x_1745_, v_x_1746_);
lean_dec(v_x_1746_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* v_00_u03b1_1748_, lean_object* v_00_u03b2_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_box(0);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_cmp_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_box(0);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_cmp_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_mkRBMap(v_00_u03b1_1755_, v_00_u03b2_1756_, v_cmp_1757_);
lean_dec_ref(v_cmp_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_box(0);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_RBMap_empty(v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___y_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* v_00_u03b1_1767_, lean_object* v_00_u03b2_1768_, lean_object* v_cmp_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* v_00_u03b1_1771_, lean_object* v_00_u03b2_1772_, lean_object* v_cmp_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_1771_, v_00_u03b2_1772_, v_cmp_1773_);
lean_dec_ref(v_cmp_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* v_00_u03b1_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_cmp_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_00_u03b2_1780_, lean_object* v_cmp_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_instInhabitedRBMap(v_00_u03b1_1779_, v_00_u03b2_1780_, v_cmp_1781_);
lean_dec_ref(v_cmp_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* v_f_1783_, lean_object* v_t_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_RBNode_depth___redArg(v_f_1783_, v_t_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* v_f_1786_, lean_object* v_t_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_RBMap_depth___redArg(v_f_1786_, v_t_1787_);
lean_dec(v_t_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_cmp_1791_, lean_object* v_f_1792_, lean_object* v_t_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_RBNode_depth___redArg(v_f_1792_, v_t_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_00_u03b2_1796_, lean_object* v_cmp_1797_, lean_object* v_f_1798_, lean_object* v_t_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_RBMap_depth(v_00_u03b1_1795_, v_00_u03b2_1796_, v_cmp_1797_, v_f_1798_, v_t_1799_);
lean_dec(v_t_1799_);
lean_dec_ref(v_cmp_1797_);
return v_res_1800_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* v_t_1801_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = l_Lean_RBNode_isSingleton___redArg(v_t_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* v_t_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_Lean_RBMap_isSingleton___redArg(v_t_1803_);
lean_dec(v_t_1803_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* v_00_u03b1_1806_, lean_object* v_00_u03b2_1807_, lean_object* v_cmp_1808_, lean_object* v_t_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Lean_RBNode_isSingleton___redArg(v_t_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_cmp_1813_, lean_object* v_t_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_Lean_RBMap_isSingleton(v_00_u03b1_1811_, v_00_u03b2_1812_, v_cmp_1813_, v_t_1814_);
lean_dec(v_t_1814_);
lean_dec_ref(v_cmp_1813_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* v_f_1817_, lean_object* v_x_1818_, lean_object* v_x_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_RBNode_fold___redArg(v_f_1817_, v_x_1818_, v_x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_00_u03c3_1823_, lean_object* v_cmp_1824_, lean_object* v_f_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_RBNode_fold___redArg(v_f_1825_, v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_00_u03c3_1831_, lean_object* v_cmp_1832_, lean_object* v_f_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_RBMap_fold(v_00_u03b1_1829_, v_00_u03b2_1830_, v_00_u03c3_1831_, v_cmp_1832_, v_f_1833_, v_x_1834_, v_x_1835_);
lean_dec_ref(v_cmp_1832_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* v_f_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_RBNode_revFold___redArg(v_f_1837_, v_x_1838_, v_x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_00_u03c3_1843_, lean_object* v_cmp_1844_, lean_object* v_f_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_RBNode_revFold___redArg(v_f_1845_, v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_00_u03c3_1851_, lean_object* v_cmp_1852_, lean_object* v_f_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_RBMap_revFold(v_00_u03b1_1849_, v_00_u03b2_1850_, v_00_u03c3_1851_, v_cmp_1852_, v_f_1853_, v_x_1854_, v_x_1855_);
lean_dec_ref(v_cmp_1852_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* v_inst_1857_, lean_object* v_f_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_RBNode_foldM___redArg(v_inst_1857_, v_f_1858_, v_x_1859_, v_x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* v_00_u03b1_1862_, lean_object* v_00_u03b2_1863_, lean_object* v_00_u03c3_1864_, lean_object* v_cmp_1865_, lean_object* v_m_1866_, lean_object* v_inst_1867_, lean_object* v_f_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_RBNode_foldM___redArg(v_inst_1867_, v_f_1868_, v_x_1869_, v_x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* v_00_u03b1_1872_, lean_object* v_00_u03b2_1873_, lean_object* v_00_u03c3_1874_, lean_object* v_cmp_1875_, lean_object* v_m_1876_, lean_object* v_inst_1877_, lean_object* v_f_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_RBMap_foldM(v_00_u03b1_1872_, v_00_u03b2_1873_, v_00_u03c3_1874_, v_cmp_1875_, v_m_1876_, v_inst_1877_, v_f_1878_, v_x_1879_, v_x_1880_);
lean_dec_ref(v_cmp_1875_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* v_f_1882_, lean_object* v_x_1883_, lean_object* v_k_1884_, lean_object* v_v_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_apply_2(v_f_1882_, v_k_1884_, v_v_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* v_inst_1887_, lean_object* v_f_1888_, lean_object* v_t_1889_){
_start:
{
lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1890_, 0, v_f_1888_);
v___x_1891_ = lean_box(0);
v___x_1892_ = l_Lean_RBNode_foldM___redArg(v_inst_1887_, v___f_1890_, v___x_1891_, v_t_1889_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* v_00_u03b1_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_cmp_1895_, lean_object* v_m_1896_, lean_object* v_inst_1897_, lean_object* v_f_1898_, lean_object* v_t_1899_){
_start:
{
lean_object* v___f_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1900_, 0, v_f_1898_);
v___x_1901_ = lean_box(0);
v___x_1902_ = l_Lean_RBNode_foldM___redArg(v_inst_1897_, v___f_1900_, v___x_1901_, v_t_1899_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_cmp_1905_, lean_object* v_m_1906_, lean_object* v_inst_1907_, lean_object* v_f_1908_, lean_object* v_t_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_RBMap_forM(v_00_u03b1_1903_, v_00_u03b2_1904_, v_cmp_1905_, v_m_1906_, v_inst_1907_, v_f_1908_, v_t_1909_);
lean_dec_ref(v_cmp_1905_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* v_f_1911_, lean_object* v_a_1912_, lean_object* v_b_1913_, lean_object* v_acc_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_a_1912_);
lean_ctor_set(v___x_1915_, 1, v_b_1913_);
v___x_1916_ = lean_apply_2(v_f_1911_, v___x_1915_, v_acc_1914_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* v_inst_1917_, lean_object* v_t_1918_, lean_object* v_init_1919_, lean_object* v_f_1920_){
_start:
{
lean_object* v_toApplicative_1921_; lean_object* v_toBind_1922_; lean_object* v_toPure_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; 
v_toApplicative_1921_ = lean_ctor_get(v_inst_1917_, 0);
v_toBind_1922_ = lean_ctor_get(v_inst_1917_, 1);
lean_inc(v_toBind_1922_);
v_toPure_1923_ = lean_ctor_get(v_toApplicative_1921_, 1);
lean_inc(v_toPure_1923_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1924_, 0, v_f_1920_);
v___x_1925_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1917_, v___f_1924_, v_t_1918_, v_init_1919_);
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1926_, 0, v_toPure_1923_);
v___x_1927_ = lean_apply_4(v_toBind_1922_, lean_box(0), lean_box(0), v___x_1925_, v___f_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* v_00_u03b1_1928_, lean_object* v_00_u03b2_1929_, lean_object* v_00_u03c3_1930_, lean_object* v_cmp_1931_, lean_object* v_m_1932_, lean_object* v_inst_1933_, lean_object* v_t_1934_, lean_object* v_init_1935_, lean_object* v_f_1936_){
_start:
{
lean_object* v_toApplicative_1937_; lean_object* v_toBind_1938_; lean_object* v_toPure_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v_toApplicative_1937_ = lean_ctor_get(v_inst_1933_, 0);
v_toBind_1938_ = lean_ctor_get(v_inst_1933_, 1);
lean_inc(v_toBind_1938_);
v_toPure_1939_ = lean_ctor_get(v_toApplicative_1937_, 1);
lean_inc(v_toPure_1939_);
v___f_1940_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1940_, 0, v_f_1936_);
v___x_1941_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1933_, v___f_1940_, v_t_1934_, v_init_1935_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1942_, 0, v_toPure_1939_);
v___x_1943_ = lean_apply_4(v_toBind_1938_, lean_box(0), lean_box(0), v___x_1941_, v___f_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* v_00_u03b1_1944_, lean_object* v_00_u03b2_1945_, lean_object* v_00_u03c3_1946_, lean_object* v_cmp_1947_, lean_object* v_m_1948_, lean_object* v_inst_1949_, lean_object* v_t_1950_, lean_object* v_init_1951_, lean_object* v_f_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_RBMap_forIn(v_00_u03b1_1944_, v_00_u03b2_1945_, v_00_u03c3_1946_, v_cmp_1947_, v_m_1948_, v_inst_1949_, v_t_1950_, v_init_1951_, v_f_1952_);
lean_dec_ref(v_cmp_1947_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* v___y_1954_, lean_object* v_a_1955_, lean_object* v_b_1956_, lean_object* v_acc_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1955_);
lean_ctor_set(v___x_1958_, 1, v_b_1956_);
v___x_1959_ = lean_apply_2(v___y_1954_, v___x_1958_, v_acc_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1960_, lean_object* v_00_u03b2_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_toApplicative_1965_; lean_object* v_toBind_1966_; lean_object* v_toPure_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; lean_object* v___f_1970_; lean_object* v___x_1971_; 
v_toApplicative_1965_ = lean_ctor_get(v_inst_1960_, 0);
v_toBind_1966_ = lean_ctor_get(v_inst_1960_, 1);
lean_inc(v_toBind_1966_);
v_toPure_1967_ = lean_ctor_get(v_toApplicative_1965_, 1);
lean_inc(v_toPure_1967_);
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1968_, 0, v___y_1964_);
v___x_1969_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1960_, v___f_1968_, v___y_1962_, v___y_1963_);
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1970_, 0, v_toPure_1967_);
v___x_1971_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1969_, v___f_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* v_inst_1972_){
_start:
{
lean_object* v___f_1973_; 
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1973_, 0, v_inst_1972_);
return v___f_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* v_00_u03b1_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_cmp_1976_, lean_object* v_m_1977_, lean_object* v_inst_1978_){
_start:
{
lean_object* v___f_1979_; 
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1979_, 0, v_inst_1978_);
return v___f_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1980_, lean_object* v_00_u03b2_1981_, lean_object* v_cmp_1982_, lean_object* v_m_1983_, lean_object* v_inst_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_RBMap_instForInProdOfMonad(v_00_u03b1_1980_, v_00_u03b2_1981_, v_cmp_1982_, v_m_1983_, v_inst_1984_);
lean_dec_ref(v_cmp_1982_);
return v_res_1985_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* v_x_1986_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = 1;
return v___x_1987_;
}
else
{
uint8_t v___x_1988_; 
v___x_1988_ = 0;
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* v_x_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Lean_RBMap_isEmpty___redArg(v_x_1989_);
lean_dec(v_x_1989_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object* v_00_u03b1_1992_, lean_object* v_00_u03b2_1993_, lean_object* v_cmp_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
uint8_t v___x_1996_; 
v___x_1996_ = 1;
return v___x_1996_;
}
else
{
uint8_t v___x_1997_; 
v___x_1997_ = 0;
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_cmp_2000_, lean_object* v_x_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l_Lean_RBMap_isEmpty(v_00_u03b1_1998_, v_00_u03b2_1999_, v_cmp_2000_, v_x_2001_);
lean_dec(v_x_2001_);
lean_dec_ref(v_cmp_2000_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* v_ps_2004_, lean_object* v_k_2005_, lean_object* v_v_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_k_2005_);
lean_ctor_set(v___x_2007_, 1, v_v_2006_);
v___x_2008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v_ps_2004_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* v_x_2010_){
_start:
{
lean_object* v___f_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___f_2011_ = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Lean_RBNode_revFold___redArg(v___f_2011_, v___x_2012_, v_x_2010_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* v_00_u03b1_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_cmp_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_RBMap_toList___redArg(v_x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_00_u03b2_2020_, lean_object* v_cmp_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_RBMap_toList(v_00_u03b1_2019_, v_00_u03b2_2020_, v_cmp_2021_, v_x_2022_);
lean_dec_ref(v_cmp_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* v_ps_2024_, lean_object* v_k_2025_, lean_object* v_v_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_k_2025_);
lean_ctor_set(v___x_2027_, 1, v_v_2026_);
v___x_2028_ = lean_array_push(v_ps_2024_, v___x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* v_x_2032_){
_start:
{
lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___f_2033_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
v___x_2034_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
v___x_2035_ = l_Lean_RBNode_fold___redArg(v___f_2033_, v___x_2034_, v_x_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* v_00_u03b1_2036_, lean_object* v_00_u03b2_2037_, lean_object* v_cmp_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_RBMap_toArray___redArg(v_x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_cmp_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_RBMap_toArray(v_00_u03b1_2041_, v_00_u03b2_2042_, v_cmp_2043_, v_x_2044_);
lean_dec_ref(v_cmp_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* v_x_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_RBNode_min___redArg(v_x_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_box(0);
return v___x_2048_;
}
else
{
lean_object* v_val_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2065_; 
v_val_2049_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2051_ = v___x_2047_;
v_isShared_2052_ = v_isSharedCheck_2065_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_val_2049_);
lean_dec(v___x_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2065_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2064_; 
v_fst_2053_ = lean_ctor_get(v_val_2049_, 0);
v_snd_2054_ = lean_ctor_get(v_val_2049_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_val_2049_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2056_ = v_val_2049_;
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_inc(v_fst_2053_);
lean_dec(v_val_2049_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2064_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_fst_2053_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_snd_2054_);
v___x_2059_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2059_);
v___x_2061_ = v___x_2051_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* v_x_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_RBMap_min___redArg(v_x_2066_);
lean_dec(v_x_2066_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* v_00_u03b1_2068_, lean_object* v_00_u03b2_2069_, lean_object* v_cmp_2070_, lean_object* v_x_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_RBNode_min___redArg(v_x_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_box(0);
return v___x_2073_;
}
else
{
lean_object* v_val_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2090_; 
v_val_2074_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2076_ = v___x_2072_;
v_isShared_2077_ = v_isSharedCheck_2090_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_val_2074_);
lean_dec(v___x_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2090_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
v_fst_2078_ = lean_ctor_get(v_val_2074_, 0);
v_snd_2079_ = lean_ctor_get(v_val_2074_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_val_2074_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2081_ = v_val_2074_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_inc(v_fst_2078_);
lean_dec(v_val_2074_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_fst_2078_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_snd_2079_);
v___x_2084_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2084_);
v___x_2086_ = v___x_2076_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* v_00_u03b1_2091_, lean_object* v_00_u03b2_2092_, lean_object* v_cmp_2093_, lean_object* v_x_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_RBMap_min(v_00_u03b1_2091_, v_00_u03b2_2092_, v_cmp_2093_, v_x_2094_);
lean_dec(v_x_2094_);
lean_dec_ref(v_cmp_2093_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* v_x_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_RBNode_max___redArg(v_x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_box(0);
return v___x_2098_;
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2115_; 
v_val_2099_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2101_ = v___x_2097_;
v_isShared_2102_ = v_isSharedCheck_2115_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_val_2099_);
lean_dec(v___x_2097_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2115_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_fst_2103_; lean_object* v_snd_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2114_; 
v_fst_2103_ = lean_ctor_get(v_val_2099_, 0);
v_snd_2104_ = lean_ctor_get(v_val_2099_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_val_2099_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2106_ = v_val_2099_;
v_isShared_2107_ = v_isSharedCheck_2114_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snd_2104_);
lean_inc(v_fst_2103_);
lean_dec(v_val_2099_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2114_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_fst_2103_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_snd_2104_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2109_);
v___x_2111_ = v___x_2101_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_RBMap_max___redArg(v_x_2116_);
lean_dec(v_x_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* v_00_u03b1_2118_, lean_object* v_00_u03b2_2119_, lean_object* v_cmp_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_RBNode_max___redArg(v_x_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_box(0);
return v___x_2123_;
}
else
{
lean_object* v_val_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2140_; 
v_val_2124_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2140_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_val_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2140_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_fst_2128_; lean_object* v_snd_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2139_; 
v_fst_2128_ = lean_ctor_get(v_val_2124_, 0);
v_snd_2129_ = lean_ctor_get(v_val_2124_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_val_2124_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2131_ = v_val_2124_;
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_snd_2129_);
lean_inc(v_fst_2128_);
lean_dec(v_val_2124_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2139_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_fst_2128_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_snd_2129_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2134_);
v___x_2136_ = v___x_2126_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_00_u03b2_2142_, lean_object* v_cmp_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_RBMap_max(v_00_u03b1_2141_, v_00_u03b2_2142_, v_cmp_2143_, v_x_2144_);
lean_dec(v_x_2144_);
lean_dec_ref(v_cmp_2143_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* v___x_2149_, lean_object* v_m_2150_, lean_object* v_prec_2151_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2152_ = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
v___x_2153_ = l_Lean_RBMap_toList___redArg(v_m_2150_);
v___x_2154_ = l_List_repr___redArg(v___x_2149_, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2152_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = l_Repr_addAppParen(v___x_2155_, v_prec_2151_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* v___x_2157_, lean_object* v_m_2158_, lean_object* v_prec_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_2157_, v_m_2158_, v_prec_2159_);
lean_dec(v_prec_2159_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* v_inst_2161_, lean_object* v_inst_2162_){
_start:
{
lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; 
v___f_2163_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2163_, 0, v_inst_2162_);
v___x_2164_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2164_, 0, lean_box(0));
lean_closure_set(v___x_2164_, 1, lean_box(0));
lean_closure_set(v___x_2164_, 2, v_inst_2161_);
lean_closure_set(v___x_2164_, 3, v___f_2163_);
v___f_2165_ = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2165_, 0, v___x_2164_);
return v___f_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* v_00_u03b1_2166_, lean_object* v_00_u03b2_2167_, lean_object* v_cmp_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_RBMap_instRepr___redArg(v_inst_2169_, v_inst_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* v_00_u03b1_2172_, lean_object* v_00_u03b2_2173_, lean_object* v_cmp_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_RBMap_instRepr(v_00_u03b1_2172_, v_00_u03b2_2173_, v_cmp_2174_, v_inst_2175_, v_inst_2176_);
lean_dec_ref(v_cmp_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* v_cmp_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_RBNode_insert___redArg(v_cmp_2178_, v_x_2179_, v_x_2180_, v_x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_cmp_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_RBNode_insert___redArg(v_cmp_2185_, v_x_2186_, v_x_2187_, v_x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* v_cmp_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_RBNode_erase___redArg(v_cmp_2190_, v_x_2192_, v_x_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_cmp_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_RBNode_erase___redArg(v_cmp_2196_, v_x_2198_, v_x_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* v_cmp_2200_, lean_object* v_x_2201_){
_start:
{
if (lean_obj_tag(v_x_2201_) == 0)
{
lean_object* v___x_2202_; 
lean_dec_ref(v_cmp_2200_);
v___x_2202_ = lean_box(0);
return v___x_2202_;
}
else
{
lean_object* v_head_2203_; lean_object* v_tail_2204_; lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v_val_2207_; lean_object* v___x_2208_; 
v_head_2203_ = lean_ctor_get(v_x_2201_, 0);
lean_inc(v_head_2203_);
v_tail_2204_ = lean_ctor_get(v_x_2201_, 1);
lean_inc(v_tail_2204_);
lean_dec_ref(v_x_2201_);
v_fst_2205_ = lean_ctor_get(v_head_2203_, 0);
lean_inc(v_fst_2205_);
v_snd_2206_ = lean_ctor_get(v_head_2203_, 1);
lean_inc(v_snd_2206_);
lean_dec(v_head_2203_);
lean_inc_ref(v_cmp_2200_);
v_val_2207_ = l_Lean_RBMap_ofList___redArg(v_cmp_2200_, v_tail_2204_);
v___x_2208_ = l_Lean_RBNode_insert___redArg(v_cmp_2200_, v_val_2207_, v_fst_2205_, v_snd_2206_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* v_00_u03b1_2209_, lean_object* v_00_u03b2_2210_, lean_object* v_cmp_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_RBMap_ofList___redArg(v_cmp_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* v_cmp_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_RBNode_findCore___redArg(v_cmp_2214_, v_x_2215_, v_x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_cmp_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_RBNode_findCore___redArg(v_cmp_2220_, v_x_2221_, v_x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* v_cmp_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_RBNode_find___redArg(v_cmp_2224_, v_x_2225_, v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* v_00_u03b1_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_cmp_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_RBNode_find___redArg(v_cmp_2230_, v_x_2231_, v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* v_cmp_2234_, lean_object* v_t_2235_, lean_object* v_k_2236_, lean_object* v_v_u2080_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_RBNode_find___redArg(v_cmp_2234_, v_t_2235_, v_k_2236_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_inc(v_v_u2080_2237_);
return v_v_u2080_2237_;
}
else
{
lean_object* v_val_2239_; 
v_val_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_val_2239_);
lean_dec_ref(v___x_2238_);
return v_val_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* v_cmp_2240_, lean_object* v_t_2241_, lean_object* v_k_2242_, lean_object* v_v_u2080_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_RBMap_findD___redArg(v_cmp_2240_, v_t_2241_, v_k_2242_, v_v_u2080_2243_);
lean_dec(v_v_u2080_2243_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* v_00_u03b1_2245_, lean_object* v_00_u03b2_2246_, lean_object* v_cmp_2247_, lean_object* v_t_2248_, lean_object* v_k_2249_, lean_object* v_v_u2080_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_RBNode_find___redArg(v_cmp_2247_, v_t_2248_, v_k_2249_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_inc(v_v_u2080_2250_);
return v_v_u2080_2250_;
}
else
{
lean_object* v_val_2252_; 
v_val_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2252_);
lean_dec_ref(v___x_2251_);
return v_val_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_00_u03b2_2254_, lean_object* v_cmp_2255_, lean_object* v_t_2256_, lean_object* v_k_2257_, lean_object* v_v_u2080_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_RBMap_findD(v_00_u03b1_2253_, v_00_u03b2_2254_, v_cmp_2255_, v_t_2256_, v_k_2257_, v_v_u2080_2258_);
lean_dec(v_v_u2080_2258_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* v_cmp_2260_, lean_object* v_x_2261_, lean_object* v_x_2262_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_box(0);
v___x_2264_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2260_, v_x_2261_, v_x_2262_, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* v_00_u03b1_2265_, lean_object* v_00_u03b2_2266_, lean_object* v_cmp_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2267_, v_x_2268_, v_x_2269_, v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object* v_cmp_2272_, lean_object* v_t_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_RBNode_find___redArg(v_cmp_2272_, v_t_2273_, v_a_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
uint8_t v___x_2276_; 
v___x_2276_ = 0;
return v___x_2276_;
}
else
{
uint8_t v___x_2277_; 
lean_dec_ref(v___x_2275_);
v___x_2277_ = 1;
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* v_cmp_2278_, lean_object* v_t_2279_, lean_object* v_a_2280_){
_start:
{
uint8_t v_res_2281_; lean_object* v_r_2282_; 
v_res_2281_ = l_Lean_RBMap_contains___redArg(v_cmp_2278_, v_t_2279_, v_a_2280_);
v_r_2282_ = lean_box(v_res_2281_);
return v_r_2282_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object* v_00_u03b1_2283_, lean_object* v_00_u03b2_2284_, lean_object* v_cmp_2285_, lean_object* v_t_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_RBNode_find___redArg(v_cmp_2285_, v_t_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
uint8_t v___x_2289_; 
v___x_2289_ = 0;
return v___x_2289_;
}
else
{
uint8_t v___x_2290_; 
lean_dec_ref(v___x_2288_);
v___x_2290_ = 1;
return v___x_2290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* v_00_u03b1_2291_, lean_object* v_00_u03b2_2292_, lean_object* v_cmp_2293_, lean_object* v_t_2294_, lean_object* v_a_2295_){
_start:
{
uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_res_2296_ = l_Lean_RBMap_contains(v_00_u03b1_2291_, v_00_u03b2_2292_, v_cmp_2293_, v_t_2294_, v_a_2295_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* v_cmp_2298_, lean_object* v_r_2299_, lean_object* v_p_2300_){
_start:
{
lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; 
v_fst_2301_ = lean_ctor_get(v_p_2300_, 0);
lean_inc(v_fst_2301_);
v_snd_2302_ = lean_ctor_get(v_p_2300_, 1);
lean_inc(v_snd_2302_);
lean_dec_ref(v_p_2300_);
v___x_2303_ = l_Lean_RBNode_insert___redArg(v_cmp_2298_, v_r_2299_, v_fst_2301_, v_snd_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* v_l_2304_, lean_object* v_cmp_2305_){
_start:
{
lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2306_, 0, v_cmp_2305_);
v___x_2307_ = lean_box(0);
v___x_2308_ = l_List_foldl___redArg(v___f_2306_, v___x_2307_, v_l_2304_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* v_00_u03b1_2309_, lean_object* v_00_u03b2_2310_, lean_object* v_l_2311_, lean_object* v_cmp_2312_){
_start:
{
lean_object* v___f_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___f_2313_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2313_, 0, v_cmp_2312_);
v___x_2314_ = lean_box(0);
v___x_2315_ = l_List_foldl___redArg(v___f_2313_, v___x_2314_, v_l_2311_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* v_cmp_2316_, lean_object* v_x1_2317_, lean_object* v_x2_2318_){
_start:
{
lean_object* v_fst_2319_; lean_object* v_snd_2320_; lean_object* v___x_2321_; 
v_fst_2319_ = lean_ctor_get(v_x2_2318_, 0);
lean_inc(v_fst_2319_);
v_snd_2320_ = lean_ctor_get(v_x2_2318_, 1);
lean_inc(v_snd_2320_);
lean_dec_ref(v_x2_2318_);
v___x_2321_ = l_Lean_RBNode_insert___redArg(v_cmp_2316_, v_x1_2317_, v_fst_2319_, v_snd_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* v_l_2341_, lean_object* v_cmp_2342_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = lean_array_get_size(v_l_2341_);
v___x_2346_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2347_ = lean_nat_dec_lt(v___x_2344_, v___x_2345_);
if (v___x_2347_ == 0)
{
lean_dec_ref(v_cmp_2342_);
lean_dec_ref(v_l_2341_);
return v___x_2343_;
}
else
{
lean_object* v___f_2348_; uint8_t v___x_2349_; 
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2348_, 0, v_cmp_2342_);
v___x_2349_ = lean_nat_dec_le(v___x_2345_, v___x_2345_);
if (v___x_2349_ == 0)
{
if (v___x_2347_ == 0)
{
lean_dec_ref(v___f_2348_);
lean_dec_ref(v_l_2341_);
return v___x_2343_;
}
else
{
size_t v___x_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = lean_usize_of_nat(v___x_2345_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2346_, v___f_2348_, v_l_2341_, v___x_2350_, v___x_2351_, v___x_2343_);
return v___x_2352_;
}
}
else
{
size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = ((size_t)0ULL);
v___x_2354_ = lean_usize_of_nat(v___x_2345_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2346_, v___f_2348_, v_l_2341_, v___x_2353_, v___x_2354_, v___x_2343_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_l_2358_, lean_object* v_cmp_2359_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = lean_array_get_size(v_l_2358_);
v___x_2363_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2364_ = lean_nat_dec_lt(v___x_2361_, v___x_2362_);
if (v___x_2364_ == 0)
{
lean_dec_ref(v_cmp_2359_);
lean_dec_ref(v_l_2358_);
return v___x_2360_;
}
else
{
lean_object* v___f_2365_; uint8_t v___x_2366_; 
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2365_, 0, v_cmp_2359_);
v___x_2366_ = lean_nat_dec_le(v___x_2362_, v___x_2362_);
if (v___x_2366_ == 0)
{
if (v___x_2364_ == 0)
{
lean_dec_ref(v___f_2365_);
lean_dec_ref(v_l_2358_);
return v___x_2360_;
}
else
{
size_t v___x_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = lean_usize_of_nat(v___x_2362_);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2363_, v___f_2365_, v_l_2358_, v___x_2367_, v___x_2368_, v___x_2360_);
return v___x_2369_;
}
}
else
{
size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = lean_usize_of_nat(v___x_2362_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2363_, v___f_2365_, v_l_2358_, v___x_2370_, v___x_2371_, v___x_2360_);
return v___x_2372_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = l_Lean_RBNode_all___redArg(v_x_2374_, v_x_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
uint8_t v_res_2378_; lean_object* v_r_2379_; 
v_res_2378_ = l_Lean_RBMap_all___redArg(v_x_2376_, v_x_2377_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object* v_00_u03b1_2380_, lean_object* v_00_u03b2_2381_, lean_object* v_cmp_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
uint8_t v___x_2385_; 
v___x_2385_ = l_Lean_RBNode_all___redArg(v_x_2384_, v_x_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* v_00_u03b1_2386_, lean_object* v_00_u03b2_2387_, lean_object* v_cmp_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
uint8_t v_res_2391_; lean_object* v_r_2392_; 
v_res_2391_ = l_Lean_RBMap_all(v_00_u03b1_2386_, v_00_u03b2_2387_, v_cmp_2388_, v_x_2389_, v_x_2390_);
lean_dec_ref(v_cmp_2388_);
v_r_2392_ = lean_box(v_res_2391_);
return v_r_2392_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
uint8_t v___x_2395_; 
v___x_2395_ = l_Lean_RBNode_any___redArg(v_x_2394_, v_x_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* v_x_2396_, lean_object* v_x_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Lean_RBMap_any___redArg(v_x_2396_, v_x_2397_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object* v_00_u03b1_2400_, lean_object* v_00_u03b2_2401_, lean_object* v_cmp_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = l_Lean_RBNode_any___redArg(v_x_2404_, v_x_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_cmp_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_){
_start:
{
uint8_t v_res_2411_; lean_object* v_r_2412_; 
v_res_2411_ = l_Lean_RBMap_any(v_00_u03b1_2406_, v_00_u03b2_2407_, v_cmp_2408_, v_x_2409_, v_x_2410_);
lean_dec_ref(v_cmp_2408_);
v_r_2412_ = lean_box(v_res_2411_);
return v_r_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2414_) == 0)
{
return v_x_2413_;
}
else
{
lean_object* v_lchild_2415_; lean_object* v_rchild_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_lchild_2415_ = lean_ctor_get(v_x_2414_, 0);
v_rchild_2416_ = lean_ctor_get(v_x_2414_, 3);
v___x_2417_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2413_, v_lchild_2415_);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_add(v___x_2417_, v___x_2418_);
lean_dec(v___x_2417_);
v_x_2413_ = v___x_2419_;
v_x_2414_ = v_rchild_2416_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* v_x_2421_, lean_object* v_x_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2421_, v_x_2422_);
lean_dec(v_x_2422_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* v_m_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_2425_, v_m_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* v_m_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_RBMap_size___redArg(v_m_2427_);
lean_dec(v_m_2427_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* v_00_u03b1_2429_, lean_object* v_00_u03b2_2430_, lean_object* v_cmp_2431_, lean_object* v_m_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_RBMap_size___redArg(v_m_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_00_u03b2_2435_, lean_object* v_cmp_2436_, lean_object* v_m_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_RBMap_size(v_00_u03b1_2434_, v_00_u03b2_2435_, v_cmp_2436_, v_m_2437_);
lean_dec(v_m_2437_);
lean_dec_ref(v_cmp_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* v_00_u03b1_2439_, lean_object* v_00_u03b2_2440_, lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2441_, v_x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(v_00_u03b1_2444_, v_00_u03b2_2445_, v_x_2446_, v_x_2447_);
lean_dec(v_x_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_le(v___y_2449_, v___y_2450_);
if (v___x_2451_ == 0)
{
lean_inc(v___y_2449_);
return v___y_2449_;
}
else
{
lean_inc(v___y_2450_);
return v___y_2450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec(v___y_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* v_t_2456_){
_start:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; 
v___f_2457_ = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
v___x_2458_ = l_Lean_RBNode_depth___redArg(v___f_2457_, v_t_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* v_t_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_RBMap_maxDepth___redArg(v_t_2459_);
lean_dec(v_t_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* v_00_u03b1_2461_, lean_object* v_00_u03b2_2462_, lean_object* v_cmp_2463_, lean_object* v_t_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_RBMap_maxDepth___redArg(v_t_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_00_u03b2_2467_, lean_object* v_cmp_2468_, lean_object* v_t_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_RBMap_maxDepth(v_00_u03b1_2466_, v_00_u03b2_2467_, v_cmp_2468_, v_t_2469_);
lean_dec(v_t_2469_);
lean_dec_ref(v_cmp_2468_);
return v_res_2470_;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2474_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2475_ = lean_unsigned_to_nat(14u);
v___x_2476_ = lean_unsigned_to_nat(384u);
v___x_2477_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
v___x_2478_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2479_ = l_mkPanicMessageWithDecl(v___x_2478_, v___x_2477_, v___x_2476_, v___x_2475_, v___x_2474_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_t_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_RBNode_min___redArg(v_t_2482_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_inst_2480_);
lean_ctor_set(v___x_2484_, 1, v_inst_2481_);
v___x_2485_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2486_ = l_panic___redArg(v___x_2484_, v___x_2485_);
return v___x_2486_;
}
else
{
lean_object* v_val_2487_; lean_object* v_fst_2488_; lean_object* v_snd_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_inst_2481_);
lean_dec(v_inst_2480_);
v_val_2487_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2487_);
lean_dec_ref(v___x_2483_);
v_fst_2488_ = lean_ctor_get(v_val_2487_, 0);
v_snd_2489_ = lean_ctor_get(v_val_2487_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_val_2487_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v_val_2487_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_snd_2489_);
lean_inc(v_fst_2488_);
lean_dec(v_val_2487_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_fst_2488_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_snd_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_t_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_RBMap_min_x21___redArg(v_inst_2497_, v_inst_2498_, v_t_2499_);
lean_dec(v_t_2499_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* v_00_u03b1_2501_, lean_object* v_00_u03b2_2502_, lean_object* v_cmp_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_t_2506_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_RBNode_min___redArg(v_t_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_inst_2504_);
lean_ctor_set(v___x_2508_, 1, v_inst_2505_);
v___x_2509_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2510_ = l_panic___redArg(v___x_2508_, v___x_2509_);
return v___x_2510_;
}
else
{
lean_object* v_val_2511_; lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_inst_2505_);
lean_dec(v_inst_2504_);
v_val_2511_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_val_2511_);
lean_dec_ref(v___x_2507_);
v_fst_2512_ = lean_ctor_get(v_val_2511_, 0);
v_snd_2513_ = lean_ctor_get(v_val_2511_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_val_2511_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v_val_2511_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_snd_2513_);
lean_inc(v_fst_2512_);
lean_dec(v_val_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_fst_2512_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_snd_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* v_00_u03b1_2521_, lean_object* v_00_u03b2_2522_, lean_object* v_cmp_2523_, lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_t_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_RBMap_min_x21(v_00_u03b1_2521_, v_00_u03b2_2522_, v_cmp_2523_, v_inst_2524_, v_inst_2525_, v_t_2526_);
lean_dec(v_t_2526_);
lean_dec_ref(v_cmp_2523_);
return v_res_2527_;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2529_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2530_ = lean_unsigned_to_nat(14u);
v___x_2531_ = lean_unsigned_to_nat(389u);
v___x_2532_ = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
v___x_2533_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2534_ = l_mkPanicMessageWithDecl(v___x_2533_, v___x_2532_, v___x_2531_, v___x_2530_, v___x_2529_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_t_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_RBNode_max___redArg(v_t_2537_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_inst_2535_);
lean_ctor_set(v___x_2539_, 1, v_inst_2536_);
v___x_2540_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2541_ = l_panic___redArg(v___x_2539_, v___x_2540_);
return v___x_2541_;
}
else
{
lean_object* v_val_2542_; lean_object* v_fst_2543_; lean_object* v_snd_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_inst_2536_);
lean_dec(v_inst_2535_);
v_val_2542_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_val_2542_);
lean_dec_ref(v___x_2538_);
v_fst_2543_ = lean_ctor_get(v_val_2542_, 0);
v_snd_2544_ = lean_ctor_get(v_val_2542_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_val_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v_val_2542_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_snd_2544_);
lean_inc(v_fst_2543_);
lean_dec(v_val_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_fst_2543_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_snd_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* v_inst_2552_, lean_object* v_inst_2553_, lean_object* v_t_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_RBMap_max_x21___redArg(v_inst_2552_, v_inst_2553_, v_t_2554_);
lean_dec(v_t_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* v_00_u03b1_2556_, lean_object* v_00_u03b2_2557_, lean_object* v_cmp_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_t_2561_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_RBNode_max___redArg(v_t_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_inst_2559_);
lean_ctor_set(v___x_2563_, 1, v_inst_2560_);
v___x_2564_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2565_ = l_panic___redArg(v___x_2563_, v___x_2564_);
return v___x_2565_;
}
else
{
lean_object* v_val_2566_; lean_object* v_fst_2567_; lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_inst_2560_);
lean_dec(v_inst_2559_);
v_val_2566_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_val_2566_);
lean_dec_ref(v___x_2562_);
v_fst_2567_ = lean_ctor_get(v_val_2566_, 0);
v_snd_2568_ = lean_ctor_get(v_val_2566_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_val_2566_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v_val_2566_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_inc(v_fst_2567_);
lean_dec(v_val_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_fst_2567_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_snd_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* v_00_u03b1_2576_, lean_object* v_00_u03b2_2577_, lean_object* v_cmp_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_t_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_RBMap_max_x21(v_00_u03b1_2576_, v_00_u03b2_2577_, v_cmp_2578_, v_inst_2579_, v_inst_2580_, v_t_2581_);
lean_dec(v_t_2581_);
lean_dec_ref(v_cmp_2578_);
return v_res_2582_;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2585_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
v___x_2586_ = lean_unsigned_to_nat(14u);
v___x_2587_ = lean_unsigned_to_nat(395u);
v___x_2588_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
v___x_2589_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2590_ = l_mkPanicMessageWithDecl(v___x_2589_, v___x_2588_, v___x_2587_, v___x_2586_, v___x_2585_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* v_cmp_2591_, lean_object* v_inst_2592_, lean_object* v_t_2593_, lean_object* v_k_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_RBNode_find___redArg(v_cmp_2591_, v_t_2593_, v_k_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2597_ = l_panic___redArg(v_inst_2592_, v___x_2596_);
return v___x_2597_;
}
else
{
lean_object* v_val_2598_; 
lean_dec(v_inst_2592_);
v_val_2598_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_val_2598_);
lean_dec_ref(v___x_2595_);
return v_val_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* v_00_u03b1_2599_, lean_object* v_00_u03b2_2600_, lean_object* v_cmp_2601_, lean_object* v_inst_2602_, lean_object* v_t_2603_, lean_object* v_k_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_RBNode_find___redArg(v_cmp_2601_, v_t_2603_, v_k_2604_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2607_ = l_panic___redArg(v_inst_2602_, v___x_2606_);
return v___x_2607_;
}
else
{
lean_object* v_val_2608_; 
lean_dec(v_inst_2602_);
v_val_2608_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_val_2608_);
lean_dec_ref(v___x_2605_);
return v_val_2608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* v_cmp_2609_, lean_object* v_x_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
if (lean_obj_tag(v_x_2610_) == 0)
{
uint8_t v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref(v_cmp_2609_);
v___x_2613_ = 0;
v___x_2614_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2614_, 0, v_x_2610_);
lean_ctor_set(v___x_2614_, 1, v_x_2611_);
lean_ctor_set(v___x_2614_, 2, v_x_2612_);
lean_ctor_set(v___x_2614_, 3, v_x_2610_);
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*4, v___x_2613_);
return v___x_2614_;
}
else
{
uint8_t v_color_2615_; 
v_color_2615_ = lean_ctor_get_uint8(v_x_2610_, sizeof(void*)*4);
if (v_color_2615_ == 0)
{
lean_object* v_lchild_2616_; lean_object* v_key_2617_; lean_object* v_val_2618_; lean_object* v_rchild_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2636_; 
v_lchild_2616_ = lean_ctor_get(v_x_2610_, 0);
v_key_2617_ = lean_ctor_get(v_x_2610_, 1);
v_val_2618_ = lean_ctor_get(v_x_2610_, 2);
v_rchild_2619_ = lean_ctor_get(v_x_2610_, 3);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_x_2610_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2621_ = v_x_2610_;
v_isShared_2622_ = v_isSharedCheck_2636_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_rchild_2619_);
lean_inc(v_val_2618_);
lean_inc(v_key_2617_);
lean_inc(v_lchild_2616_);
lean_dec(v_x_2610_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2636_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; uint8_t v___x_2624_; 
lean_inc_ref(v_cmp_2609_);
lean_inc(v_key_2617_);
lean_inc(v_x_2611_);
v___x_2623_ = lean_apply_2(v_cmp_2609_, v_x_2611_, v_key_2617_);
v___x_2624_ = lean_unbox(v___x_2623_);
switch(v___x_2624_)
{
case 0:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2609_, v_lchild_2616_, v_x_2611_, v_x_2612_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2625_);
v___x_2627_ = v___x_2621_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_key_2617_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_val_2618_);
lean_ctor_set(v_reuseFailAlloc_2628_, 3, v_rchild_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, sizeof(void*)*4, v_color_2615_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
case 1:
{
lean_object* v___x_2630_; 
lean_dec(v_val_2618_);
lean_dec(v_key_2617_);
lean_dec_ref(v_cmp_2609_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 2, v_x_2612_);
lean_ctor_set(v___x_2621_, 1, v_x_2611_);
v___x_2630_ = v___x_2621_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_lchild_2616_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_x_2611_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_x_2612_);
lean_ctor_set(v_reuseFailAlloc_2631_, 3, v_rchild_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2631_, sizeof(void*)*4, v_color_2615_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
default: 
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2609_, v_rchild_2619_, v_x_2611_, v_x_2612_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 3, v___x_2632_);
v___x_2634_ = v___x_2621_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_lchild_2616_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_key_2617_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_val_2618_);
lean_ctor_set(v_reuseFailAlloc_2635_, 3, v___x_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2635_, sizeof(void*)*4, v_color_2615_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
else
{
lean_object* v_lchild_2637_; lean_object* v_key_2638_; lean_object* v_val_2639_; lean_object* v_rchild_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2799_; 
v_lchild_2637_ = lean_ctor_get(v_x_2610_, 0);
v_key_2638_ = lean_ctor_get(v_x_2610_, 1);
v_val_2639_ = lean_ctor_get(v_x_2610_, 2);
v_rchild_2640_ = lean_ctor_get(v_x_2610_, 3);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_x_2610_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2642_ = v_x_2610_;
v_isShared_2643_ = v_isSharedCheck_2799_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_rchild_2640_);
lean_inc(v_val_2639_);
lean_inc(v_key_2638_);
lean_inc(v_lchild_2637_);
lean_dec(v_x_2610_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2799_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
lean_inc_ref(v_cmp_2609_);
lean_inc(v_key_2638_);
lean_inc(v_x_2611_);
v___x_2644_ = lean_apply_2(v_cmp_2609_, v_x_2611_, v_key_2638_);
v___x_2645_ = lean_unbox(v___x_2644_);
switch(v___x_2645_)
{
case 0:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2609_, v_lchild_2637_, v_x_2611_, v_x_2612_);
if (lean_obj_tag(v___x_2646_) == 1)
{
uint8_t v_color_2647_; lean_object* v_lchild_2648_; lean_object* v_key_2649_; lean_object* v_val_2650_; lean_object* v_rchild_2651_; lean_object* v_a_2653_; lean_object* v_kx_2654_; lean_object* v_vx_2655_; lean_object* v_b_2656_; lean_object* v_ky_2657_; lean_object* v_vy_2658_; lean_object* v_c_2659_; lean_object* v_kz_2660_; lean_object* v_vz_2661_; lean_object* v_d_2662_; 
v_color_2647_ = lean_ctor_get_uint8(v___x_2646_, sizeof(void*)*4);
v_lchild_2648_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_lchild_2648_);
v_key_2649_ = lean_ctor_get(v___x_2646_, 1);
lean_inc(v_key_2649_);
v_val_2650_ = lean_ctor_get(v___x_2646_, 2);
lean_inc(v_val_2650_);
v_rchild_2651_ = lean_ctor_get(v___x_2646_, 3);
lean_inc(v_rchild_2651_);
if (v_color_2647_ == 0)
{
if (lean_obj_tag(v_lchild_2648_) == 1)
{
uint8_t v_color_2668_; 
v_color_2668_ = lean_ctor_get_uint8(v_lchild_2648_, sizeof(void*)*4);
if (v_color_2668_ == 0)
{
lean_object* v_lchild_2669_; lean_object* v_key_2670_; lean_object* v_val_2671_; lean_object* v_rchild_2672_; 
lean_dec_ref(v___x_2646_);
v_lchild_2669_ = lean_ctor_get(v_lchild_2648_, 0);
lean_inc(v_lchild_2669_);
v_key_2670_ = lean_ctor_get(v_lchild_2648_, 1);
lean_inc(v_key_2670_);
v_val_2671_ = lean_ctor_get(v_lchild_2648_, 2);
lean_inc(v_val_2671_);
v_rchild_2672_ = lean_ctor_get(v_lchild_2648_, 3);
lean_inc(v_rchild_2672_);
lean_dec_ref(v_lchild_2648_);
v_a_2653_ = v_lchild_2669_;
v_kx_2654_ = v_key_2670_;
v_vx_2655_ = v_val_2671_;
v_b_2656_ = v_rchild_2672_;
v_ky_2657_ = v_key_2649_;
v_vy_2658_ = v_val_2650_;
v_c_2659_ = v_rchild_2651_;
v_kz_2660_ = v_key_2638_;
v_vz_2661_ = v_val_2639_;
v_d_2662_ = v_rchild_2640_;
goto v___jp_2652_;
}
else
{
if (lean_obj_tag(v_rchild_2651_) == 1)
{
uint8_t v_color_2673_; 
v_color_2673_ = lean_ctor_get_uint8(v_rchild_2651_, sizeof(void*)*4);
if (v_color_2673_ == 0)
{
lean_object* v_lchild_2674_; lean_object* v_key_2675_; lean_object* v_val_2676_; lean_object* v_rchild_2677_; 
lean_dec_ref(v___x_2646_);
v_lchild_2674_ = lean_ctor_get(v_rchild_2651_, 0);
lean_inc(v_lchild_2674_);
v_key_2675_ = lean_ctor_get(v_rchild_2651_, 1);
lean_inc(v_key_2675_);
v_val_2676_ = lean_ctor_get(v_rchild_2651_, 2);
lean_inc(v_val_2676_);
v_rchild_2677_ = lean_ctor_get(v_rchild_2651_, 3);
lean_inc(v_rchild_2677_);
lean_dec_ref(v_rchild_2651_);
v_a_2653_ = v_lchild_2648_;
v_kx_2654_ = v_key_2649_;
v_vx_2655_ = v_val_2650_;
v_b_2656_ = v_lchild_2674_;
v_ky_2657_ = v_key_2675_;
v_vy_2658_ = v_val_2676_;
v_c_2659_ = v_rchild_2677_;
v_kz_2660_ = v_key_2638_;
v_vz_2661_ = v_val_2639_;
v_d_2662_ = v_rchild_2640_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref(v_lchild_2648_);
lean_dec(v_val_2650_);
lean_dec(v_key_2649_);
lean_del_object(v___x_2642_);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_rchild_2651_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; 
v_unused_2685_ = lean_ctor_get(v_rchild_2651_, 3);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_rchild_2651_, 2);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_rchild_2651_, 1);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_rchild_2651_, 0);
lean_dec(v_unused_2688_);
v___x_2679_ = v_rchild_2651_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_dec(v_rchild_2651_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 3, v_rchild_2640_);
lean_ctor_set(v___x_2679_, 2, v_val_2639_);
lean_ctor_set(v___x_2679_, 1, v_key_2638_);
lean_ctor_set(v___x_2679_, 0, v___x_2646_);
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_rchild_2640_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_ctor_set_uint8(v___x_2682_, sizeof(void*)*4, v_color_2615_);
return v___x_2682_;
}
}
}
}
else
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_rchild_2651_);
lean_dec(v_val_2650_);
lean_dec(v_key_2649_);
lean_del_object(v___x_2642_);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_lchild_2648_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; lean_object* v_unused_2697_; lean_object* v_unused_2698_; lean_object* v_unused_2699_; 
v_unused_2696_ = lean_ctor_get(v_lchild_2648_, 3);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_lchild_2648_, 2);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_lchild_2648_, 1);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_lchild_2648_, 0);
lean_dec(v_unused_2699_);
v___x_2690_ = v_lchild_2648_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v_lchild_2648_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 3, v_rchild_2640_);
lean_ctor_set(v___x_2690_, 2, v_val_2639_);
lean_ctor_set(v___x_2690_, 1, v_key_2638_);
lean_ctor_set(v___x_2690_, 0, v___x_2646_);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_rchild_2640_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*4, v_color_2615_);
return v___x_2693_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2651_) == 1)
{
uint8_t v_color_2700_; 
v_color_2700_ = lean_ctor_get_uint8(v_rchild_2651_, sizeof(void*)*4);
if (v_color_2700_ == 0)
{
lean_object* v_lchild_2701_; lean_object* v_key_2702_; lean_object* v_val_2703_; lean_object* v_rchild_2704_; 
lean_dec_ref(v___x_2646_);
v_lchild_2701_ = lean_ctor_get(v_rchild_2651_, 0);
lean_inc(v_lchild_2701_);
v_key_2702_ = lean_ctor_get(v_rchild_2651_, 1);
lean_inc(v_key_2702_);
v_val_2703_ = lean_ctor_get(v_rchild_2651_, 2);
lean_inc(v_val_2703_);
v_rchild_2704_ = lean_ctor_get(v_rchild_2651_, 3);
lean_inc(v_rchild_2704_);
lean_dec_ref(v_rchild_2651_);
v_a_2653_ = v_lchild_2648_;
v_kx_2654_ = v_key_2649_;
v_vx_2655_ = v_val_2650_;
v_b_2656_ = v_lchild_2701_;
v_ky_2657_ = v_key_2702_;
v_vy_2658_ = v_val_2703_;
v_c_2659_ = v_rchild_2704_;
v_kz_2660_ = v_key_2638_;
v_vz_2661_ = v_val_2639_;
v_d_2662_ = v_rchild_2640_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec(v_val_2650_);
lean_dec(v_key_2649_);
lean_dec(v_lchild_2648_);
lean_del_object(v___x_2642_);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_rchild_2651_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2712_ = lean_ctor_get(v_rchild_2651_, 3);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_rchild_2651_, 2);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_rchild_2651_, 1);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_rchild_2651_, 0);
lean_dec(v_unused_2715_);
v___x_2706_ = v_rchild_2651_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_dec(v_rchild_2651_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 3, v_rchild_2640_);
lean_ctor_set(v___x_2706_, 2, v_val_2639_);
lean_ctor_set(v___x_2706_, 1, v_key_2638_);
lean_ctor_set(v___x_2706_, 0, v___x_2646_);
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_rchild_2640_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*4, v_color_2615_);
return v___x_2709_;
}
}
}
}
else
{
lean_object* v___x_2716_; 
lean_dec(v_rchild_2651_);
lean_dec(v_val_2650_);
lean_dec(v_key_2649_);
lean_dec(v_lchild_2648_);
lean_del_object(v___x_2642_);
v___x_2716_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2716_, 0, v___x_2646_);
lean_ctor_set(v___x_2716_, 1, v_key_2638_);
lean_ctor_set(v___x_2716_, 2, v_val_2639_);
lean_ctor_set(v___x_2716_, 3, v_rchild_2640_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*4, v_color_2615_);
return v___x_2716_;
}
}
}
else
{
lean_object* v___x_2717_; 
lean_dec(v_rchild_2651_);
lean_dec(v_val_2650_);
lean_dec(v_key_2649_);
lean_dec(v_lchild_2648_);
lean_del_object(v___x_2642_);
v___x_2717_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2717_, 0, v___x_2646_);
lean_ctor_set(v___x_2717_, 1, v_key_2638_);
lean_ctor_set(v___x_2717_, 2, v_val_2639_);
lean_ctor_set(v___x_2717_, 3, v_rchild_2640_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*4, v_color_2615_);
return v___x_2717_;
}
v___jp_2652_:
{
lean_object* v___x_2664_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 3, v_b_2656_);
lean_ctor_set(v___x_2642_, 2, v_vx_2655_);
lean_ctor_set(v___x_2642_, 1, v_kx_2654_);
lean_ctor_set(v___x_2642_, 0, v_a_2653_);
v___x_2664_ = v___x_2642_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2653_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_kx_2654_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_vx_2655_);
lean_ctor_set(v_reuseFailAlloc_2667_, 3, v_b_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2667_, sizeof(void*)*4, v_color_2615_);
v___x_2664_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2665_, 0, v_c_2659_);
lean_ctor_set(v___x_2665_, 1, v_kz_2660_);
lean_ctor_set(v___x_2665_, 2, v_vz_2661_);
lean_ctor_set(v___x_2665_, 3, v_d_2662_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*4, v_color_2615_);
v___x_2666_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v_ky_2657_);
lean_ctor_set(v___x_2666_, 2, v_vy_2658_);
lean_ctor_set(v___x_2666_, 3, v___x_2665_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*4, v_color_2647_);
return v___x_2666_;
}
}
}
else
{
lean_object* v___x_2719_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2646_);
v___x_2719_ = v___x_2642_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2720_, 3, v_rchild_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2720_, sizeof(void*)*4, v_color_2615_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
case 1:
{
lean_object* v___x_2722_; 
lean_dec(v_val_2639_);
lean_dec(v_key_2638_);
lean_dec_ref(v_cmp_2609_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 2, v_x_2612_);
lean_ctor_set(v___x_2642_, 1, v_x_2611_);
v___x_2722_ = v___x_2642_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_lchild_2637_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_x_2611_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_x_2612_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_rchild_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, sizeof(void*)*4, v_color_2615_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
default: 
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2609_, v_rchild_2640_, v_x_2611_, v_x_2612_);
if (lean_obj_tag(v___x_2724_) == 1)
{
uint8_t v_color_2725_; lean_object* v_lchild_2726_; lean_object* v_key_2727_; lean_object* v_val_2728_; lean_object* v_rchild_2729_; lean_object* v_a_2731_; lean_object* v_kx_2732_; lean_object* v_vx_2733_; lean_object* v_b_2734_; lean_object* v_ky_2735_; lean_object* v_vy_2736_; lean_object* v_c_2737_; lean_object* v_kz_2738_; lean_object* v_vz_2739_; lean_object* v_d_2740_; 
v_color_2725_ = lean_ctor_get_uint8(v___x_2724_, sizeof(void*)*4);
v_lchild_2726_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_lchild_2726_);
v_key_2727_ = lean_ctor_get(v___x_2724_, 1);
lean_inc(v_key_2727_);
v_val_2728_ = lean_ctor_get(v___x_2724_, 2);
lean_inc(v_val_2728_);
v_rchild_2729_ = lean_ctor_get(v___x_2724_, 3);
lean_inc(v_rchild_2729_);
if (v_color_2725_ == 0)
{
if (lean_obj_tag(v_lchild_2726_) == 1)
{
uint8_t v_color_2746_; 
v_color_2746_ = lean_ctor_get_uint8(v_lchild_2726_, sizeof(void*)*4);
if (v_color_2746_ == 0)
{
lean_object* v_lchild_2747_; lean_object* v_key_2748_; lean_object* v_val_2749_; lean_object* v_rchild_2750_; 
lean_dec_ref(v___x_2724_);
v_lchild_2747_ = lean_ctor_get(v_lchild_2726_, 0);
lean_inc(v_lchild_2747_);
v_key_2748_ = lean_ctor_get(v_lchild_2726_, 1);
lean_inc(v_key_2748_);
v_val_2749_ = lean_ctor_get(v_lchild_2726_, 2);
lean_inc(v_val_2749_);
v_rchild_2750_ = lean_ctor_get(v_lchild_2726_, 3);
lean_inc(v_rchild_2750_);
lean_dec_ref(v_lchild_2726_);
v_a_2731_ = v_lchild_2637_;
v_kx_2732_ = v_key_2638_;
v_vx_2733_ = v_val_2639_;
v_b_2734_ = v_lchild_2747_;
v_ky_2735_ = v_key_2748_;
v_vy_2736_ = v_val_2749_;
v_c_2737_ = v_rchild_2750_;
v_kz_2738_ = v_key_2727_;
v_vz_2739_ = v_val_2728_;
v_d_2740_ = v_rchild_2729_;
goto v___jp_2730_;
}
else
{
if (lean_obj_tag(v_rchild_2729_) == 1)
{
uint8_t v_color_2751_; 
v_color_2751_ = lean_ctor_get_uint8(v_rchild_2729_, sizeof(void*)*4);
if (v_color_2751_ == 0)
{
lean_object* v_lchild_2752_; lean_object* v_key_2753_; lean_object* v_val_2754_; lean_object* v_rchild_2755_; 
lean_dec_ref(v___x_2724_);
v_lchild_2752_ = lean_ctor_get(v_rchild_2729_, 0);
lean_inc(v_lchild_2752_);
v_key_2753_ = lean_ctor_get(v_rchild_2729_, 1);
lean_inc(v_key_2753_);
v_val_2754_ = lean_ctor_get(v_rchild_2729_, 2);
lean_inc(v_val_2754_);
v_rchild_2755_ = lean_ctor_get(v_rchild_2729_, 3);
lean_inc(v_rchild_2755_);
lean_dec_ref(v_rchild_2729_);
v_a_2731_ = v_lchild_2637_;
v_kx_2732_ = v_key_2638_;
v_vx_2733_ = v_val_2639_;
v_b_2734_ = v_lchild_2726_;
v_ky_2735_ = v_key_2727_;
v_vy_2736_ = v_val_2728_;
v_c_2737_ = v_lchild_2752_;
v_kz_2738_ = v_key_2753_;
v_vz_2739_ = v_val_2754_;
v_d_2740_ = v_rchild_2755_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_lchild_2726_);
lean_dec(v_val_2728_);
lean_dec(v_key_2727_);
lean_del_object(v___x_2642_);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_rchild_2729_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; lean_object* v_unused_2766_; 
v_unused_2763_ = lean_ctor_get(v_rchild_2729_, 3);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_rchild_2729_, 2);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_rchild_2729_, 1);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_rchild_2729_, 0);
lean_dec(v_unused_2766_);
v___x_2757_ = v_rchild_2729_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_dec(v_rchild_2729_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 3, v___x_2724_);
lean_ctor_set(v___x_2757_, 2, v_val_2639_);
lean_ctor_set(v___x_2757_, 1, v_key_2638_);
lean_ctor_set(v___x_2757_, 0, v_lchild_2637_);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_lchild_2637_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v___x_2724_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_ctor_set_uint8(v___x_2760_, sizeof(void*)*4, v_color_2615_);
return v___x_2760_;
}
}
}
}
else
{
lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_rchild_2729_);
lean_dec(v_val_2728_);
lean_dec(v_key_2727_);
lean_del_object(v___x_2642_);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_lchild_2726_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; lean_object* v_unused_2775_; lean_object* v_unused_2776_; lean_object* v_unused_2777_; 
v_unused_2774_ = lean_ctor_get(v_lchild_2726_, 3);
lean_dec(v_unused_2774_);
v_unused_2775_ = lean_ctor_get(v_lchild_2726_, 2);
lean_dec(v_unused_2775_);
v_unused_2776_ = lean_ctor_get(v_lchild_2726_, 1);
lean_dec(v_unused_2776_);
v_unused_2777_ = lean_ctor_get(v_lchild_2726_, 0);
lean_dec(v_unused_2777_);
v___x_2768_ = v_lchild_2726_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_dec(v_lchild_2726_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 3, v___x_2724_);
lean_ctor_set(v___x_2768_, 2, v_val_2639_);
lean_ctor_set(v___x_2768_, 1, v_key_2638_);
lean_ctor_set(v___x_2768_, 0, v_lchild_2637_);
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_lchild_2637_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v___x_2724_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_ctor_set_uint8(v___x_2771_, sizeof(void*)*4, v_color_2615_);
return v___x_2771_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2729_) == 1)
{
uint8_t v_color_2778_; 
v_color_2778_ = lean_ctor_get_uint8(v_rchild_2729_, sizeof(void*)*4);
if (v_color_2778_ == 0)
{
lean_object* v_lchild_2779_; lean_object* v_key_2780_; lean_object* v_val_2781_; lean_object* v_rchild_2782_; 
lean_dec_ref(v___x_2724_);
v_lchild_2779_ = lean_ctor_get(v_rchild_2729_, 0);
lean_inc(v_lchild_2779_);
v_key_2780_ = lean_ctor_get(v_rchild_2729_, 1);
lean_inc(v_key_2780_);
v_val_2781_ = lean_ctor_get(v_rchild_2729_, 2);
lean_inc(v_val_2781_);
v_rchild_2782_ = lean_ctor_get(v_rchild_2729_, 3);
lean_inc(v_rchild_2782_);
lean_dec_ref(v_rchild_2729_);
v_a_2731_ = v_lchild_2637_;
v_kx_2732_ = v_key_2638_;
v_vx_2733_ = v_val_2639_;
v_b_2734_ = v_lchild_2726_;
v_ky_2735_ = v_key_2727_;
v_vy_2736_ = v_val_2728_;
v_c_2737_ = v_lchild_2779_;
v_kz_2738_ = v_key_2780_;
v_vz_2739_ = v_val_2781_;
v_d_2740_ = v_rchild_2782_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_val_2728_);
lean_dec(v_key_2727_);
lean_dec(v_lchild_2726_);
lean_del_object(v___x_2642_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_rchild_2729_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; lean_object* v_unused_2793_; 
v_unused_2790_ = lean_ctor_get(v_rchild_2729_, 3);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_rchild_2729_, 2);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_rchild_2729_, 1);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_rchild_2729_, 0);
lean_dec(v_unused_2793_);
v___x_2784_ = v_rchild_2729_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v_rchild_2729_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 3, v___x_2724_);
lean_ctor_set(v___x_2784_, 2, v_val_2639_);
lean_ctor_set(v___x_2784_, 1, v_key_2638_);
lean_ctor_set(v___x_2784_, 0, v_lchild_2637_);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_lchild_2637_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v___x_2724_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*4, v_color_2615_);
return v___x_2787_;
}
}
}
}
else
{
lean_object* v___x_2794_; 
lean_dec(v_rchild_2729_);
lean_dec(v_val_2728_);
lean_dec(v_key_2727_);
lean_dec(v_lchild_2726_);
lean_del_object(v___x_2642_);
v___x_2794_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2794_, 0, v_lchild_2637_);
lean_ctor_set(v___x_2794_, 1, v_key_2638_);
lean_ctor_set(v___x_2794_, 2, v_val_2639_);
lean_ctor_set(v___x_2794_, 3, v___x_2724_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*4, v_color_2615_);
return v___x_2794_;
}
}
}
else
{
lean_object* v___x_2795_; 
lean_dec(v_rchild_2729_);
lean_dec(v_val_2728_);
lean_dec(v_key_2727_);
lean_dec(v_lchild_2726_);
lean_del_object(v___x_2642_);
v___x_2795_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2795_, 0, v_lchild_2637_);
lean_ctor_set(v___x_2795_, 1, v_key_2638_);
lean_ctor_set(v___x_2795_, 2, v_val_2639_);
lean_ctor_set(v___x_2795_, 3, v___x_2724_);
lean_ctor_set_uint8(v___x_2795_, sizeof(void*)*4, v_color_2615_);
return v___x_2795_;
}
v___jp_2730_:
{
lean_object* v___x_2742_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 3, v_b_2734_);
lean_ctor_set(v___x_2642_, 2, v_vx_2733_);
lean_ctor_set(v___x_2642_, 1, v_kx_2732_);
lean_ctor_set(v___x_2642_, 0, v_a_2731_);
v___x_2742_ = v___x_2642_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2731_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_kx_2732_);
lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_vx_2733_);
lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_b_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2745_, sizeof(void*)*4, v_color_2615_);
v___x_2742_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2743_, 0, v_c_2737_);
lean_ctor_set(v___x_2743_, 1, v_kz_2738_);
lean_ctor_set(v___x_2743_, 2, v_vz_2739_);
lean_ctor_set(v___x_2743_, 3, v_d_2740_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*4, v_color_2615_);
v___x_2744_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v_ky_2735_);
lean_ctor_set(v___x_2744_, 2, v_vy_2736_);
lean_ctor_set(v___x_2744_, 3, v___x_2743_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*4, v_color_2725_);
return v___x_2744_;
}
}
}
else
{
lean_object* v___x_2797_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 3, v___x_2724_);
v___x_2797_ = v___x_2642_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_lchild_2637_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_key_2638_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_val_2639_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v___x_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2798_, sizeof(void*)*4, v_color_2615_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* v_cmp_2800_, lean_object* v_t_2801_, lean_object* v_k_2802_, lean_object* v_v_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = l_Lean_RBNode_isRed___redArg(v_t_2801_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2800_, v_t_2801_, v_k_2802_, v_v_2803_);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2800_, v_t_2801_, v_k_2802_, v_v_2803_);
v___x_2807_ = l_Lean_RBNode_setBlack___redArg(v___x_2806_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* v_cmp_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v___x_2811_; 
lean_dec(v_x_2810_);
lean_dec_ref(v_cmp_2808_);
v___x_2811_ = lean_box(0);
return v___x_2811_;
}
else
{
lean_object* v_lchild_2812_; lean_object* v_key_2813_; lean_object* v_val_2814_; lean_object* v_rchild_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v_lchild_2812_ = lean_ctor_get(v_x_2809_, 0);
lean_inc(v_lchild_2812_);
v_key_2813_ = lean_ctor_get(v_x_2809_, 1);
lean_inc(v_key_2813_);
v_val_2814_ = lean_ctor_get(v_x_2809_, 2);
lean_inc(v_val_2814_);
v_rchild_2815_ = lean_ctor_get(v_x_2809_, 3);
lean_inc(v_rchild_2815_);
lean_dec_ref(v_x_2809_);
lean_inc_ref(v_cmp_2808_);
lean_inc(v_x_2810_);
v___x_2816_ = lean_apply_2(v_cmp_2808_, v_x_2810_, v_key_2813_);
v___x_2817_ = lean_unbox(v___x_2816_);
switch(v___x_2817_)
{
case 0:
{
lean_dec(v_rchild_2815_);
lean_dec(v_val_2814_);
v_x_2809_ = v_lchild_2812_;
goto _start;
}
case 1:
{
lean_object* v___x_2819_; 
lean_dec(v_rchild_2815_);
lean_dec(v_lchild_2812_);
lean_dec(v_x_2810_);
lean_dec_ref(v_cmp_2808_);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_val_2814_);
return v___x_2819_;
}
default: 
{
lean_dec(v_val_2814_);
lean_dec(v_lchild_2812_);
v_x_2809_ = v_rchild_2815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* v_cmp_2821_, lean_object* v_mergeFn_2822_, lean_object* v_x_2823_, lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_dec(v_mergeFn_2822_);
lean_dec_ref(v_cmp_2821_);
return v_x_2823_;
}
else
{
lean_object* v_lchild_2825_; lean_object* v_key_2826_; lean_object* v_val_2827_; lean_object* v_rchild_2828_; lean_object* v_val_2829_; lean_object* v___y_2831_; lean_object* v___x_2834_; 
v_lchild_2825_ = lean_ctor_get(v_x_2824_, 0);
lean_inc(v_lchild_2825_);
v_key_2826_ = lean_ctor_get(v_x_2824_, 1);
lean_inc(v_key_2826_);
v_val_2827_ = lean_ctor_get(v_x_2824_, 2);
lean_inc(v_val_2827_);
v_rchild_2828_ = lean_ctor_get(v_x_2824_, 3);
lean_inc(v_rchild_2828_);
lean_dec_ref(v_x_2824_);
lean_inc(v_mergeFn_2822_);
lean_inc_ref(v_cmp_2821_);
v_val_2829_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2821_, v_mergeFn_2822_, v_x_2823_, v_lchild_2825_);
lean_inc(v_key_2826_);
lean_inc(v_val_2829_);
lean_inc_ref(v_cmp_2821_);
v___x_2834_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2821_, v_val_2829_, v_key_2826_);
if (lean_obj_tag(v___x_2834_) == 0)
{
v___y_2831_ = v_val_2827_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2835_; lean_object* v___x_2836_; 
v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2835_);
lean_dec_ref(v___x_2834_);
lean_inc(v_mergeFn_2822_);
lean_inc(v_key_2826_);
v___x_2836_ = lean_apply_3(v_mergeFn_2822_, v_key_2826_, v_val_2835_, v_val_2827_);
v___y_2831_ = v___x_2836_;
goto v___jp_2830_;
}
v___jp_2830_:
{
lean_object* v___x_2832_; 
lean_inc_ref(v_cmp_2821_);
v___x_2832_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2821_, v_val_2829_, v_key_2826_, v___y_2831_);
v_x_2823_ = v___x_2832_;
v_x_2824_ = v_rchild_2828_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* v_cmp_2837_, lean_object* v_mergeFn_2838_, lean_object* v_t_u2081_2839_, lean_object* v_t_u2082_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2837_, v_mergeFn_2838_, v_t_u2081_2839_, v_t_u2082_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* v_00_u03b1_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_cmp_2844_, lean_object* v_mergeFn_2845_, lean_object* v_t_u2081_2846_, lean_object* v_t_u2082_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2844_, v_mergeFn_2845_, v_t_u2081_2846_, v_t_u2082_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* v_00_u03b1_2849_, lean_object* v_cmp_2850_, lean_object* v_00_u03b2_2851_, lean_object* v_t_2852_, lean_object* v_k_2853_, lean_object* v_v_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2850_, v_t_2852_, v_k_2853_, v_v_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* v_00_u03b1_2856_, lean_object* v_cmp_2857_, lean_object* v_00_u03b2_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2857_, v_x_2859_, v_x_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* v_00_u03b1_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_cmp_2864_, lean_object* v_mergeFn_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2864_, v_mergeFn_2865_, v_x_2866_, v_x_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* v_00_u03b1_2869_, lean_object* v_cmp_2870_, lean_object* v_00_u03b2_2871_, lean_object* v_x_2872_, lean_object* v_x_2873_, lean_object* v_x_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2870_, v_x_2872_, v_x_2873_, v_x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* v_t_u2082_2876_, lean_object* v_cmp_2877_, lean_object* v_mergeFn_2878_, lean_object* v_x_2879_, lean_object* v_x_2880_){
_start:
{
if (lean_obj_tag(v_x_2880_) == 0)
{
lean_dec(v_mergeFn_2878_);
lean_dec_ref(v_cmp_2877_);
lean_dec(v_t_u2082_2876_);
return v_x_2879_;
}
else
{
lean_object* v_lchild_2881_; lean_object* v_key_2882_; lean_object* v_val_2883_; lean_object* v_rchild_2884_; lean_object* v_val_2885_; lean_object* v___x_2886_; 
v_lchild_2881_ = lean_ctor_get(v_x_2880_, 0);
lean_inc(v_lchild_2881_);
v_key_2882_ = lean_ctor_get(v_x_2880_, 1);
lean_inc(v_key_2882_);
v_val_2883_ = lean_ctor_get(v_x_2880_, 2);
lean_inc(v_val_2883_);
v_rchild_2884_ = lean_ctor_get(v_x_2880_, 3);
lean_inc(v_rchild_2884_);
lean_dec_ref(v_x_2880_);
lean_inc(v_mergeFn_2878_);
lean_inc_ref(v_cmp_2877_);
lean_inc(v_t_u2082_2876_);
v_val_2885_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2876_, v_cmp_2877_, v_mergeFn_2878_, v_x_2879_, v_lchild_2881_);
lean_inc(v_key_2882_);
lean_inc(v_t_u2082_2876_);
lean_inc_ref(v_cmp_2877_);
v___x_2886_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2877_, v_t_u2082_2876_, v_key_2882_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_dec(v_val_2883_);
lean_dec(v_key_2882_);
v_x_2879_ = v_val_2885_;
v_x_2880_ = v_rchild_2884_;
goto _start;
}
else
{
lean_object* v_val_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_val_2888_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_val_2888_);
lean_dec_ref(v___x_2886_);
lean_inc(v_mergeFn_2878_);
lean_inc(v_key_2882_);
v___x_2889_ = lean_apply_3(v_mergeFn_2878_, v_key_2882_, v_val_2883_, v_val_2888_);
lean_inc_ref(v_cmp_2877_);
v___x_2890_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2877_, v_val_2885_, v_key_2882_, v___x_2889_);
v_x_2879_ = v___x_2890_;
v_x_2880_ = v_rchild_2884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* v_cmp_2892_, lean_object* v_mergeFn_2893_, lean_object* v_t_u2081_2894_, lean_object* v_t_u2082_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2895_, v_cmp_2892_, v_mergeFn_2893_, v___x_2896_, v_t_u2081_2894_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* v_00_u03b1_2898_, lean_object* v_00_u03b2_2899_, lean_object* v_cmp_2900_, lean_object* v_00_u03b3_2901_, lean_object* v_00_u03b4_2902_, lean_object* v_mergeFn_2903_, lean_object* v_t_u2081_2904_, lean_object* v_t_u2082_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_RBMap_intersectBy___redArg(v_cmp_2900_, v_mergeFn_2903_, v_t_u2081_2904_, v_t_u2082_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* v_00_u03b1_2907_, lean_object* v_00_u03b2_2908_, lean_object* v_00_u03b4_2909_, lean_object* v_00_u03b3_2910_, lean_object* v_t_u2082_2911_, lean_object* v_cmp_2912_, lean_object* v_mergeFn_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2911_, v_cmp_2912_, v_mergeFn_2913_, v_x_2914_, v_x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* v_f_2917_, lean_object* v_cmp_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_){
_start:
{
if (lean_obj_tag(v_x_2920_) == 0)
{
lean_dec_ref(v_cmp_2918_);
lean_dec_ref(v_f_2917_);
return v_x_2919_;
}
else
{
lean_object* v_lchild_2921_; lean_object* v_key_2922_; lean_object* v_val_2923_; lean_object* v_rchild_2924_; lean_object* v_val_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v_lchild_2921_ = lean_ctor_get(v_x_2920_, 0);
lean_inc(v_lchild_2921_);
v_key_2922_ = lean_ctor_get(v_x_2920_, 1);
lean_inc(v_key_2922_);
v_val_2923_ = lean_ctor_get(v_x_2920_, 2);
lean_inc(v_val_2923_);
v_rchild_2924_ = lean_ctor_get(v_x_2920_, 3);
lean_inc(v_rchild_2924_);
lean_dec_ref(v_x_2920_);
lean_inc_ref(v_cmp_2918_);
lean_inc_ref(v_f_2917_);
v_val_2925_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2917_, v_cmp_2918_, v_x_2919_, v_lchild_2921_);
lean_inc_ref(v_f_2917_);
lean_inc(v_val_2923_);
lean_inc(v_key_2922_);
v___x_2926_ = lean_apply_2(v_f_2917_, v_key_2922_, v_val_2923_);
v___x_2927_ = lean_unbox(v___x_2926_);
if (v___x_2927_ == 0)
{
lean_dec(v_val_2923_);
lean_dec(v_key_2922_);
v_x_2919_ = v_val_2925_;
v_x_2920_ = v_rchild_2924_;
goto _start;
}
else
{
lean_object* v___x_2929_; 
lean_inc_ref(v_cmp_2918_);
v___x_2929_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2918_, v_val_2925_, v_key_2922_, v_val_2923_);
v_x_2919_ = v___x_2929_;
v_x_2920_ = v_rchild_2924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* v_cmp_2931_, lean_object* v_f_2932_, lean_object* v_m_2933_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = lean_box(0);
v___x_2935_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2932_, v_cmp_2931_, v___x_2934_, v_m_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* v_00_u03b1_2936_, lean_object* v_00_u03b2_2937_, lean_object* v_cmp_2938_, lean_object* v_f_2939_, lean_object* v_m_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_RBMap_filter___redArg(v_cmp_2938_, v_f_2939_, v_m_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* v_00_u03b1_2942_, lean_object* v_00_u03b2_2943_, lean_object* v_f_2944_, lean_object* v_cmp_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2944_, v_cmp_2945_, v_x_2946_, v_x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* v_f_2949_, lean_object* v_cmp_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
if (lean_obj_tag(v_x_2952_) == 0)
{
lean_dec_ref(v_cmp_2950_);
lean_dec_ref(v_f_2949_);
return v_x_2951_;
}
else
{
lean_object* v_lchild_2953_; lean_object* v_key_2954_; lean_object* v_val_2955_; lean_object* v_rchild_2956_; lean_object* v_val_2957_; lean_object* v___x_2958_; 
v_lchild_2953_ = lean_ctor_get(v_x_2952_, 0);
lean_inc(v_lchild_2953_);
v_key_2954_ = lean_ctor_get(v_x_2952_, 1);
lean_inc(v_key_2954_);
v_val_2955_ = lean_ctor_get(v_x_2952_, 2);
lean_inc(v_val_2955_);
v_rchild_2956_ = lean_ctor_get(v_x_2952_, 3);
lean_inc(v_rchild_2956_);
lean_dec_ref(v_x_2952_);
lean_inc_ref(v_cmp_2950_);
lean_inc_ref(v_f_2949_);
v_val_2957_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2949_, v_cmp_2950_, v_x_2951_, v_lchild_2953_);
lean_inc_ref(v_f_2949_);
lean_inc(v_key_2954_);
v___x_2958_ = lean_apply_2(v_f_2949_, v_key_2954_, v_val_2955_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_dec(v_key_2954_);
v_x_2951_ = v_val_2957_;
v_x_2952_ = v_rchild_2956_;
goto _start;
}
else
{
lean_object* v_val_2960_; lean_object* v___x_2961_; 
v_val_2960_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_val_2960_);
lean_dec_ref(v___x_2958_);
lean_inc_ref(v_cmp_2950_);
v___x_2961_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2950_, v_val_2957_, v_key_2954_, v_val_2960_);
v_x_2951_ = v___x_2961_;
v_x_2952_ = v_rchild_2956_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* v_cmp_2963_, lean_object* v_f_2964_, lean_object* v_m_2965_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = lean_box(0);
v___x_2967_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2964_, v_cmp_2963_, v___x_2966_, v_m_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* v_00_u03b1_2968_, lean_object* v_00_u03b2_2969_, lean_object* v_cmp_2970_, lean_object* v_00_u03b3_2971_, lean_object* v_f_2972_, lean_object* v_m_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_RBMap_filterMap___redArg(v_cmp_2970_, v_f_2972_, v_m_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* v_00_u03b1_2975_, lean_object* v_00_u03b2_2976_, lean_object* v_00_u03b3_2977_, lean_object* v_f_2978_, lean_object* v_cmp_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2978_, v_cmp_2979_, v_x_2980_, v_x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* v_cmp_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_){
_start:
{
if (lean_obj_tag(v_x_2985_) == 0)
{
lean_dec_ref(v_cmp_2983_);
return v_x_2984_;
}
else
{
lean_object* v_head_2986_; lean_object* v_tail_2987_; lean_object* v_fst_2988_; lean_object* v_snd_2989_; lean_object* v___x_2990_; 
v_head_2986_ = lean_ctor_get(v_x_2985_, 0);
lean_inc(v_head_2986_);
v_tail_2987_ = lean_ctor_get(v_x_2985_, 1);
lean_inc(v_tail_2987_);
lean_dec_ref(v_x_2985_);
v_fst_2988_ = lean_ctor_get(v_head_2986_, 0);
lean_inc(v_fst_2988_);
v_snd_2989_ = lean_ctor_get(v_head_2986_, 1);
lean_inc(v_snd_2989_);
lean_dec(v_head_2986_);
lean_inc_ref(v_cmp_2983_);
v___x_2990_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2983_, v_x_2984_, v_fst_2988_, v_snd_2989_);
v_x_2984_ = v___x_2990_;
v_x_2985_ = v_tail_2987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* v_l_2992_, lean_object* v_cmp_2993_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_2993_, v___x_2994_, v_l_2992_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* v_00_u03b1_2996_, lean_object* v_00_u03b2_2997_, lean_object* v_l_2998_, lean_object* v_cmp_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_rbmapOf___redArg(v_l_2998_, v_cmp_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* v_00_u03b1_3001_, lean_object* v_00_u03b2_3002_, lean_object* v_cmp_3003_, lean_object* v_x_3004_, lean_object* v_x_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3003_, v_x_3004_, v_x_3005_);
return v___x_3006_;
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
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
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
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RBMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_RBMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_RBMap(builtin);
}
#ifdef __cplusplus
}
#endif
