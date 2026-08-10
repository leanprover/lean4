// Lean compiler output
// Module: Lean.Data.RBMap
// Imports: public import Init.Data.Ord.Basic public import Init.Data.Nat.Internal.Linear public import Init.Data.Array.Basic import Init.WFTactics
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
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_RBColor_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_RBColor_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg(lean_object* v_red_22_){
_start:
{
lean_inc(v_red_22_);
return v_red_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg___boxed(lean_object* v_red_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_RBColor_red_elim___redArg(v_red_23_);
lean_dec(v_red_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_red_28_){
_start:
{
lean_inc(v_red_28_);
return v_red_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_red_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_RBColor_red_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_red_32_);
lean_dec(v_red_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg(lean_object* v_black_35_){
_start:
{
lean_inc(v_black_35_);
return v_black_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg___boxed(lean_object* v_black_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_RBColor_black_elim___redArg(v_black_36_);
lean_dec(v_black_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_black_41_){
_start:
{
lean_inc(v_black_41_);
return v_black_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_black_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_RBColor_black_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_black_45_);
lean_dec(v_black_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg(lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v___x_49_; 
v___x_49_ = lean_unsigned_to_nat(0u);
return v___x_49_;
}
else
{
lean_object* v___x_50_; 
v___x_50_ = lean_unsigned_to_nat(1u);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___redArg___boxed(lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_RBNode_ctorIdx___redArg(v_x_51_);
lean_dec(v_x_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_x_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_RBNode_ctorIdx___redArg(v_x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___boxed(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_RBNode_ctorIdx(v_00_u03b1_57_, v_00_u03b2_58_, v_x_59_);
lean_dec(v_x_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___redArg(lean_object* v_t_61_, lean_object* v_k_62_){
_start:
{
if (lean_obj_tag(v_t_61_) == 0)
{
return v_k_62_;
}
else
{
uint8_t v_color_63_; lean_object* v_lchild_64_; lean_object* v_key_65_; lean_object* v_val_66_; lean_object* v_rchild_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_color_63_ = lean_ctor_get_uint8(v_t_61_, sizeof(void*)*4);
v_lchild_64_ = lean_ctor_get(v_t_61_, 0);
lean_inc(v_lchild_64_);
v_key_65_ = lean_ctor_get(v_t_61_, 1);
lean_inc(v_key_65_);
v_val_66_ = lean_ctor_get(v_t_61_, 2);
lean_inc(v_val_66_);
v_rchild_67_ = lean_ctor_get(v_t_61_, 3);
lean_inc(v_rchild_67_);
lean_dec_ref_known(v_t_61_, 4);
v___x_68_ = lean_box(v_color_63_);
v___x_69_ = lean_apply_5(v_k_62_, v___x_68_, v_lchild_64_, v_key_65_, v_val_66_, v_rchild_67_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_motive_72_, lean_object* v_ctorIdx_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_k_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_RBNode_ctorElim___redArg(v_t_74_, v_k_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___boxed(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_motive_80_, lean_object* v_ctorIdx_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_k_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_RBNode_ctorElim(v_00_u03b1_78_, v_00_u03b2_79_, v_motive_80_, v_ctorIdx_81_, v_t_82_, v_h_83_, v_k_84_);
lean_dec(v_ctorIdx_81_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim___redArg(lean_object* v_t_86_, lean_object* v_leaf_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_RBNode_ctorElim___redArg(v_t_86_, v_leaf_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_leaf_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_RBNode_ctorElim___redArg(v_t_92_, v_leaf_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim___redArg(lean_object* v_t_96_, lean_object* v_node_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_RBNode_ctorElim___redArg(v_t_96_, v_node_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_motive_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_node_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_RBNode_ctorElim___redArg(v_t_102_, v_node_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object* v_f_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v_f_106_);
v___x_108_ = lean_unsigned_to_nat(0u);
return v___x_108_;
}
else
{
lean_object* v_lchild_109_; lean_object* v_rchild_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_lchild_109_ = lean_ctor_get(v_x_107_, 0);
v_rchild_110_ = lean_ctor_get(v_x_107_, 3);
lean_inc_ref_n(v_f_106_, 2);
v___x_111_ = l_Lean_RBNode_depth___redArg(v_f_106_, v_lchild_109_);
v___x_112_ = l_Lean_RBNode_depth___redArg(v_f_106_, v_rchild_110_);
v___x_113_ = lean_apply_2(v_f_106_, v___x_111_, v___x_112_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_add(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object* v_f_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_RBNode_depth___redArg(v_f_116_, v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_f_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_RBNode_depth___redArg(v_f_121_, v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_f_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_RBNode_depth(v_00_u03b1_124_, v_00_u03b2_125_, v_f_126_, v_x_127_);
lean_dec(v_x_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v_lchild_131_; 
v_lchild_131_ = lean_ctor_get(v_x_129_, 0);
if (lean_obj_tag(v_lchild_131_) == 0)
{
lean_object* v_key_132_; lean_object* v_val_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_key_132_ = lean_ctor_get(v_x_129_, 1);
v_val_133_ = lean_ctor_get(v_x_129_, 2);
lean_inc(v_val_133_);
lean_inc(v_key_132_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_key_132_);
lean_ctor_set(v___x_134_, 1, v_val_133_);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
else
{
v_x_129_ = v_lchild_131_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_RBNode_min___redArg(v_x_137_);
lean_dec(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_RBNode_min___redArg(v_x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_RBNode_min(v_00_u03b1_143_, v_00_u03b2_144_, v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object* v_x_147_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v_rchild_149_; 
v_rchild_149_ = lean_ctor_get(v_x_147_, 3);
if (lean_obj_tag(v_rchild_149_) == 0)
{
lean_object* v_key_150_; lean_object* v_val_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_key_150_ = lean_ctor_get(v_x_147_, 1);
v_val_151_ = lean_ctor_get(v_x_147_, 2);
lean_inc(v_val_151_);
lean_inc(v_key_150_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_key_150_);
lean_ctor_set(v___x_152_, 1, v_val_151_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
else
{
v_x_147_ = v_rchild_149_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_RBNode_max___redArg(v_x_155_);
lean_dec(v_x_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_x_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_RBNode_max___redArg(v_x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_RBNode_max(v_00_u03b1_161_, v_00_u03b2_162_, v_x_163_);
lean_dec(v_x_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object* v_f_165_, lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_dec(v_f_165_);
return v_x_166_;
}
else
{
lean_object* v_lchild_168_; lean_object* v_key_169_; lean_object* v_val_170_; lean_object* v_rchild_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_lchild_168_ = lean_ctor_get(v_x_167_, 0);
lean_inc(v_lchild_168_);
v_key_169_ = lean_ctor_get(v_x_167_, 1);
lean_inc(v_key_169_);
v_val_170_ = lean_ctor_get(v_x_167_, 2);
lean_inc(v_val_170_);
v_rchild_171_ = lean_ctor_get(v_x_167_, 3);
lean_inc(v_rchild_171_);
lean_dec_ref_known(v_x_167_, 4);
lean_inc_n(v_f_165_, 2);
v___x_172_ = l_Lean_RBNode_fold___redArg(v_f_165_, v_x_166_, v_lchild_168_);
v___x_173_ = lean_apply_3(v_f_165_, v___x_172_, v_key_169_, v_val_170_);
v_x_166_ = v___x_173_;
v_x_167_ = v_rchild_171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object* v_00_u03b1_175_, lean_object* v_00_u03b2_176_, lean_object* v_00_u03c3_177_, lean_object* v_f_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_RBNode_fold___redArg(v_f_178_, v_x_179_, v_x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object* v_f_182_, lean_object* v_key_183_, lean_object* v_val_184_, lean_object* v_toBind_185_, lean_object* v___f_186_, lean_object* v_____r_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_apply_2(v_f_182_, v_key_183_, v_val_184_);
v___x_189_ = lean_apply_4(v_toBind_185_, lean_box(0), lean_box(0), v___x_188_, v___f_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object* v_inst_190_, lean_object* v_f_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v_toApplicative_193_; lean_object* v_toPure_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_toApplicative_193_ = lean_ctor_get(v_inst_190_, 0);
lean_inc_ref(v_toApplicative_193_);
lean_dec(v_f_191_);
lean_dec_ref(v_inst_190_);
v_toPure_194_ = lean_ctor_get(v_toApplicative_193_, 1);
lean_inc(v_toPure_194_);
lean_dec_ref(v_toApplicative_193_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_2(v_toPure_194_, lean_box(0), v___x_195_);
return v___x_196_;
}
else
{
lean_object* v_toBind_197_; lean_object* v_lchild_198_; lean_object* v_key_199_; lean_object* v_val_200_; lean_object* v_rchild_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_toBind_197_ = lean_ctor_get(v_inst_190_, 1);
lean_inc_n(v_toBind_197_, 2);
v_lchild_198_ = lean_ctor_get(v_x_192_, 0);
lean_inc(v_lchild_198_);
v_key_199_ = lean_ctor_get(v_x_192_, 1);
lean_inc(v_key_199_);
v_val_200_ = lean_ctor_get(v_x_192_, 2);
lean_inc(v_val_200_);
v_rchild_201_ = lean_ctor_get(v_x_192_, 3);
lean_inc(v_rchild_201_);
lean_dec_ref_known(v_x_192_, 4);
lean_inc_n(v_f_191_, 2);
lean_inc_ref(v_inst_190_);
v___f_202_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_202_, 0, v_inst_190_);
lean_closure_set(v___f_202_, 1, v_f_191_);
lean_closure_set(v___f_202_, 2, v_rchild_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_203_, 0, v_f_191_);
lean_closure_set(v___f_203_, 1, v_key_199_);
lean_closure_set(v___f_203_, 2, v_val_200_);
lean_closure_set(v___f_203_, 3, v_toBind_197_);
lean_closure_set(v___f_203_, 4, v___f_202_);
v___x_204_ = l_Lean_RBNode_forM___redArg(v_inst_190_, v_f_191_, v_lchild_198_);
v___x_205_ = lean_apply_4(v_toBind_197_, lean_box(0), lean_box(0), v___x_204_, v___f_203_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object* v_inst_206_, lean_object* v_f_207_, lean_object* v_rchild_208_, lean_object* v_____r_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_RBNode_forM___redArg(v_inst_206_, v_f_207_, v_rchild_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_m_213_, lean_object* v_inst_214_, lean_object* v_f_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_RBNode_forM___redArg(v_inst_214_, v_f_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object* v_f_218_, lean_object* v_key_219_, lean_object* v_val_220_, lean_object* v_toBind_221_, lean_object* v___f_222_, lean_object* v_b_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_apply_3(v_f_218_, v_b_223_, v_key_219_, v_val_220_);
v___x_225_ = lean_apply_4(v_toBind_221_, lean_box(0), lean_box(0), v___x_224_, v___f_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object* v_inst_226_, lean_object* v_f_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v_toApplicative_230_; lean_object* v_toPure_231_; lean_object* v___x_232_; 
v_toApplicative_230_ = lean_ctor_get(v_inst_226_, 0);
lean_inc_ref(v_toApplicative_230_);
lean_dec(v_f_227_);
lean_dec_ref(v_inst_226_);
v_toPure_231_ = lean_ctor_get(v_toApplicative_230_, 1);
lean_inc(v_toPure_231_);
lean_dec_ref(v_toApplicative_230_);
v___x_232_ = lean_apply_2(v_toPure_231_, lean_box(0), v_x_228_);
return v___x_232_;
}
else
{
lean_object* v_toBind_233_; lean_object* v_lchild_234_; lean_object* v_key_235_; lean_object* v_val_236_; lean_object* v_rchild_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_toBind_233_ = lean_ctor_get(v_inst_226_, 1);
lean_inc_n(v_toBind_233_, 2);
v_lchild_234_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_lchild_234_);
v_key_235_ = lean_ctor_get(v_x_229_, 1);
lean_inc(v_key_235_);
v_val_236_ = lean_ctor_get(v_x_229_, 2);
lean_inc(v_val_236_);
v_rchild_237_ = lean_ctor_get(v_x_229_, 3);
lean_inc(v_rchild_237_);
lean_dec_ref_known(v_x_229_, 4);
lean_inc_n(v_f_227_, 2);
lean_inc_ref(v_inst_226_);
v___f_238_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_238_, 0, v_inst_226_);
lean_closure_set(v___f_238_, 1, v_f_227_);
lean_closure_set(v___f_238_, 2, v_rchild_237_);
v___f_239_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_239_, 0, v_f_227_);
lean_closure_set(v___f_239_, 1, v_key_235_);
lean_closure_set(v___f_239_, 2, v_val_236_);
lean_closure_set(v___f_239_, 3, v_toBind_233_);
lean_closure_set(v___f_239_, 4, v___f_238_);
v___x_240_ = l_Lean_RBNode_foldM___redArg(v_inst_226_, v_f_227_, v_x_228_, v_lchild_234_);
v___x_241_ = lean_apply_4(v_toBind_233_, lean_box(0), lean_box(0), v___x_240_, v___f_239_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object* v_inst_242_, lean_object* v_f_243_, lean_object* v_rchild_244_, lean_object* v_b_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_RBNode_foldM___redArg(v_inst_242_, v_f_243_, v_b_245_, v_rchild_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_00_u03c3_249_, lean_object* v_m_250_, lean_object* v_inst_251_, lean_object* v_f_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_RBNode_foldM___redArg(v_inst_251_, v_f_252_, v_x_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object* v_toPure_256_, lean_object* v_f_257_, lean_object* v_key_258_, lean_object* v_val_259_, lean_object* v_toBind_260_, lean_object* v___f_261_, lean_object* v_____do__lift_262_){
_start:
{
if (lean_obj_tag(v_____do__lift_262_) == 0)
{
lean_object* v___x_263_; 
lean_dec(v___f_261_);
lean_dec(v_toBind_260_);
lean_dec(v_val_259_);
lean_dec(v_key_258_);
lean_dec(v_f_257_);
v___x_263_ = lean_apply_2(v_toPure_256_, lean_box(0), v_____do__lift_262_);
return v___x_263_;
}
else
{
lean_object* v_a_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_toPure_256_);
v_a_264_ = lean_ctor_get(v_____do__lift_262_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v_____do__lift_262_, 1);
v___x_265_ = lean_apply_3(v_f_257_, v_key_258_, v_val_259_, v_a_264_);
v___x_266_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_265_, v___f_261_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object* v_inst_267_, lean_object* v_f_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
if (lean_obj_tag(v_a_269_) == 0)
{
lean_object* v_toApplicative_271_; lean_object* v_toPure_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_toApplicative_271_ = lean_ctor_get(v_inst_267_, 0);
lean_inc_ref(v_toApplicative_271_);
lean_dec(v_f_268_);
lean_dec_ref(v_inst_267_);
v_toPure_272_ = lean_ctor_get(v_toApplicative_271_, 1);
lean_inc(v_toPure_272_);
lean_dec_ref(v_toApplicative_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_a_270_);
v___x_274_ = lean_apply_2(v_toPure_272_, lean_box(0), v___x_273_);
return v___x_274_;
}
else
{
lean_object* v_toApplicative_275_; lean_object* v_toBind_276_; lean_object* v_toPure_277_; lean_object* v_lchild_278_; lean_object* v_key_279_; lean_object* v_val_280_; lean_object* v_rchild_281_; lean_object* v___f_282_; lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_toApplicative_275_ = lean_ctor_get(v_inst_267_, 0);
v_toBind_276_ = lean_ctor_get(v_inst_267_, 1);
lean_inc_n(v_toBind_276_, 2);
v_toPure_277_ = lean_ctor_get(v_toApplicative_275_, 1);
v_lchild_278_ = lean_ctor_get(v_a_269_, 0);
lean_inc(v_lchild_278_);
v_key_279_ = lean_ctor_get(v_a_269_, 1);
lean_inc(v_key_279_);
v_val_280_ = lean_ctor_get(v_a_269_, 2);
lean_inc(v_val_280_);
v_rchild_281_ = lean_ctor_get(v_a_269_, 3);
lean_inc(v_rchild_281_);
lean_dec_ref_known(v_a_269_, 4);
lean_inc_n(v_f_268_, 2);
lean_inc_ref(v_inst_267_);
lean_inc_n(v_toPure_277_, 2);
v___f_282_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0), 5, 4);
lean_closure_set(v___f_282_, 0, v_toPure_277_);
lean_closure_set(v___f_282_, 1, v_inst_267_);
lean_closure_set(v___f_282_, 2, v_f_268_);
lean_closure_set(v___f_282_, 3, v_rchild_281_);
v___f_283_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1), 7, 6);
lean_closure_set(v___f_283_, 0, v_toPure_277_);
lean_closure_set(v___f_283_, 1, v_f_268_);
lean_closure_set(v___f_283_, 2, v_key_279_);
lean_closure_set(v___f_283_, 3, v_val_280_);
lean_closure_set(v___f_283_, 4, v_toBind_276_);
lean_closure_set(v___f_283_, 5, v___f_282_);
v___x_284_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_267_, v_f_268_, v_lchild_278_, v_a_270_);
v___x_285_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_284_, v___f_283_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object* v_toPure_286_, lean_object* v_inst_287_, lean_object* v_f_288_, lean_object* v_rchild_289_, lean_object* v_____do__lift_290_){
_start:
{
if (lean_obj_tag(v_____do__lift_290_) == 0)
{
lean_object* v___x_291_; 
lean_dec(v_rchild_289_);
lean_dec(v_f_288_);
lean_dec_ref(v_inst_287_);
v___x_291_ = lean_apply_2(v_toPure_286_, lean_box(0), v_____do__lift_290_);
return v___x_291_;
}
else
{
lean_object* v_a_292_; lean_object* v___x_293_; 
lean_dec(v_toPure_286_);
v_a_292_ = lean_ctor_get(v_____do__lift_290_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v_____do__lift_290_, 1);
v___x_293_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_287_, v_f_288_, v_rchild_289_, v_a_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object* v_00_u03b1_294_, lean_object* v_00_u03b2_295_, lean_object* v_00_u03c3_296_, lean_object* v_m_297_, lean_object* v_inst_298_, lean_object* v_f_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_298_, v_f_299_, v_a_300_, v_a_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object* v_toPure_303_, lean_object* v_____do__lift_304_){
_start:
{
lean_object* v_a_305_; lean_object* v___x_306_; 
v_a_305_ = lean_ctor_get(v_____do__lift_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref(v_____do__lift_304_);
v___x_306_ = lean_apply_2(v_toPure_303_, lean_box(0), v_a_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object* v_inst_307_, lean_object* v_as_308_, lean_object* v_init_309_, lean_object* v_f_310_){
_start:
{
lean_object* v_toApplicative_311_; lean_object* v_toBind_312_; lean_object* v_toPure_313_; lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___x_316_; 
v_toApplicative_311_ = lean_ctor_get(v_inst_307_, 0);
v_toBind_312_ = lean_ctor_get(v_inst_307_, 1);
lean_inc(v_toBind_312_);
v_toPure_313_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_inc(v_toPure_313_);
v___x_314_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_307_, v_f_310_, v_as_308_, v_init_309_);
v___f_315_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_315_, 0, v_toPure_313_);
v___x_316_ = lean_apply_4(v_toBind_312_, lean_box(0), lean_box(0), v___x_314_, v___f_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_00_u03c3_319_, lean_object* v_m_320_, lean_object* v_inst_321_, lean_object* v_as_322_, lean_object* v_init_323_, lean_object* v_f_324_){
_start:
{
lean_object* v_toApplicative_325_; lean_object* v_toBind_326_; lean_object* v_toPure_327_; lean_object* v___x_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
v_toApplicative_325_ = lean_ctor_get(v_inst_321_, 0);
v_toBind_326_ = lean_ctor_get(v_inst_321_, 1);
lean_inc(v_toBind_326_);
v_toPure_327_ = lean_ctor_get(v_toApplicative_325_, 1);
lean_inc(v_toPure_327_);
v___x_328_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_321_, v_f_324_, v_as_322_, v_init_323_);
v___f_329_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_329_, 0, v_toPure_327_);
v___x_330_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v___x_328_, v___f_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object* v_f_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_dec(v_f_331_);
return v_x_332_;
}
else
{
lean_object* v_lchild_334_; lean_object* v_key_335_; lean_object* v_val_336_; lean_object* v_rchild_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_lchild_334_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_lchild_334_);
v_key_335_ = lean_ctor_get(v_x_333_, 1);
lean_inc(v_key_335_);
v_val_336_ = lean_ctor_get(v_x_333_, 2);
lean_inc(v_val_336_);
v_rchild_337_ = lean_ctor_get(v_x_333_, 3);
lean_inc(v_rchild_337_);
lean_dec_ref_known(v_x_333_, 4);
lean_inc_n(v_f_331_, 2);
v___x_338_ = l_Lean_RBNode_revFold___redArg(v_f_331_, v_x_332_, v_rchild_337_);
v___x_339_ = lean_apply_3(v_f_331_, v___x_338_, v_key_335_, v_val_336_);
v_x_332_ = v___x_339_;
v_x_333_ = v_lchild_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_00_u03c3_343_, lean_object* v_f_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_RBNode_revFold___redArg(v_f_344_, v_x_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___redArg(lean_object* v_p_348_, lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
uint8_t v___x_350_; 
lean_dec_ref(v_p_348_);
v___x_350_ = 1;
return v___x_350_;
}
else
{
lean_object* v_lchild_351_; lean_object* v_key_352_; lean_object* v_val_353_; lean_object* v_rchild_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_lchild_351_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_lchild_351_);
v_key_352_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_key_352_);
v_val_353_ = lean_ctor_get(v_x_349_, 2);
lean_inc(v_val_353_);
v_rchild_354_ = lean_ctor_get(v_x_349_, 3);
lean_inc(v_rchild_354_);
lean_dec_ref_known(v_x_349_, 4);
lean_inc_ref(v_p_348_);
v___x_355_ = lean_apply_2(v_p_348_, v_key_352_, v_val_353_);
v___x_356_ = lean_unbox(v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
lean_dec(v_rchild_354_);
lean_dec(v_lchild_351_);
lean_dec_ref(v_p_348_);
v___x_357_ = lean_unbox(v___x_355_);
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
lean_inc_ref(v_p_348_);
v___x_358_ = l_Lean_RBNode_all___redArg(v_p_348_, v_lchild_351_);
if (v___x_358_ == 0)
{
lean_dec(v_rchild_354_);
lean_dec_ref(v_p_348_);
return v___x_358_;
}
else
{
v_x_349_ = v_rchild_354_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object* v_p_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Lean_RBNode_all___redArg(v_p_360_, v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_p_366_, lean_object* v_x_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = l_Lean_RBNode_all___redArg(v_p_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___boxed(lean_object* v_00_u03b1_369_, lean_object* v_00_u03b2_370_, lean_object* v_p_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_RBNode_all(v_00_u03b1_369_, v_00_u03b2_370_, v_p_371_, v_x_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any___redArg(lean_object* v_p_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
uint8_t v___x_377_; 
lean_dec_ref(v_p_375_);
v___x_377_ = 0;
return v___x_377_;
}
else
{
lean_object* v_lchild_378_; lean_object* v_key_379_; lean_object* v_val_380_; lean_object* v_rchild_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_lchild_378_ = lean_ctor_get(v_x_376_, 0);
lean_inc(v_lchild_378_);
v_key_379_ = lean_ctor_get(v_x_376_, 1);
lean_inc(v_key_379_);
v_val_380_ = lean_ctor_get(v_x_376_, 2);
lean_inc(v_val_380_);
v_rchild_381_ = lean_ctor_get(v_x_376_, 3);
lean_inc(v_rchild_381_);
lean_dec_ref_known(v_x_376_, 4);
lean_inc_ref(v_p_375_);
v___x_382_ = lean_apply_2(v_p_375_, v_key_379_, v_val_380_);
v___x_383_ = lean_unbox(v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
lean_inc_ref(v_p_375_);
v___x_384_ = l_Lean_RBNode_any___redArg(v_p_375_, v_lchild_378_);
if (v___x_384_ == 0)
{
v_x_376_ = v_rchild_381_;
goto _start;
}
else
{
lean_dec(v_rchild_381_);
lean_dec_ref(v_p_375_);
return v___x_384_;
}
}
else
{
uint8_t v___x_386_; 
lean_dec(v_rchild_381_);
lean_dec(v_lchild_378_);
lean_dec_ref(v_p_375_);
v___x_386_ = lean_unbox(v___x_382_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object* v_p_387_, lean_object* v_x_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_RBNode_any___redArg(v_p_387_, v_x_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object* v_00_u03b1_391_, lean_object* v_00_u03b2_392_, lean_object* v_p_393_, lean_object* v_x_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = l_Lean_RBNode_any___redArg(v_p_393_, v_x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_p_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_RBNode_any(v_00_u03b1_396_, v_00_u03b2_397_, v_p_398_, v_x_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object* v_k_402_, lean_object* v_v_403_){
_start:
{
uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = 0;
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_k_402_);
lean_ctor_set(v___x_406_, 2, v_v_403_);
lean_ctor_set(v___x_406_, 3, v___x_405_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*4, v___x_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_k_409_, lean_object* v_v_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_RBNode_singleton___redArg(v_k_409_, v_v_410_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object* v_x_412_){
_start:
{
if (lean_obj_tag(v_x_412_) == 1)
{
lean_object* v_lchild_413_; 
v_lchild_413_ = lean_ctor_get(v_x_412_, 0);
if (lean_obj_tag(v_lchild_413_) == 0)
{
lean_object* v_rchild_414_; 
v_rchild_414_ = lean_ctor_get(v_x_412_, 3);
if (lean_obj_tag(v_rchild_414_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 1;
return v___x_415_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
}
else
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object* v_x_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_RBNode_isSingleton___redArg(v_x_419_);
lean_dec(v_x_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_x_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_RBNode_isSingleton___redArg(v_x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object* v_00_u03b1_426_, lean_object* v_00_u03b2_427_, lean_object* v_x_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_Lean_RBNode_isSingleton(v_00_u03b1_426_, v_00_u03b2_427_, v_x_428_);
lean_dec(v_x_428_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_a_436_; lean_object* v_kx_437_; lean_object* v_vx_438_; lean_object* v_b_439_; 
if (lean_obj_tag(v_x_431_) == 1)
{
uint8_t v_color_442_; lean_object* v_lchild_443_; lean_object* v_key_444_; lean_object* v_val_445_; lean_object* v_rchild_446_; lean_object* v_a_448_; lean_object* v_kx_449_; lean_object* v_vx_450_; lean_object* v_b_451_; lean_object* v_ky_452_; lean_object* v_vy_453_; lean_object* v_c_454_; lean_object* v_kz_455_; lean_object* v_vz_456_; lean_object* v_d_457_; 
v_color_442_ = lean_ctor_get_uint8(v_x_431_, sizeof(void*)*4);
v_lchild_443_ = lean_ctor_get(v_x_431_, 0);
v_key_444_ = lean_ctor_get(v_x_431_, 1);
v_val_445_ = lean_ctor_get(v_x_431_, 2);
v_rchild_446_ = lean_ctor_get(v_x_431_, 3);
if (v_color_442_ == 0)
{
if (lean_obj_tag(v_lchild_443_) == 1)
{
uint8_t v_color_462_; 
v_color_462_ = lean_ctor_get_uint8(v_lchild_443_, sizeof(void*)*4);
if (v_color_462_ == 0)
{
lean_object* v_lchild_463_; lean_object* v_key_464_; lean_object* v_val_465_; lean_object* v_rchild_466_; 
lean_inc_ref(v_lchild_443_);
lean_inc(v_rchild_446_);
lean_inc(v_val_445_);
lean_inc(v_key_444_);
lean_dec_ref_known(v_x_431_, 4);
v_lchild_463_ = lean_ctor_get(v_lchild_443_, 0);
lean_inc(v_lchild_463_);
v_key_464_ = lean_ctor_get(v_lchild_443_, 1);
lean_inc(v_key_464_);
v_val_465_ = lean_ctor_get(v_lchild_443_, 2);
lean_inc(v_val_465_);
v_rchild_466_ = lean_ctor_get(v_lchild_443_, 3);
lean_inc(v_rchild_466_);
lean_dec_ref_known(v_lchild_443_, 4);
v_a_448_ = v_lchild_463_;
v_kx_449_ = v_key_464_;
v_vx_450_ = v_val_465_;
v_b_451_ = v_rchild_466_;
v_ky_452_ = v_key_444_;
v_vy_453_ = v_val_445_;
v_c_454_ = v_rchild_446_;
v_kz_455_ = v_x_432_;
v_vz_456_ = v_x_433_;
v_d_457_ = v_x_434_;
goto v___jp_447_;
}
else
{
if (lean_obj_tag(v_rchild_446_) == 1)
{
uint8_t v_color_467_; 
v_color_467_ = lean_ctor_get_uint8(v_rchild_446_, sizeof(void*)*4);
if (v_color_467_ == 0)
{
lean_object* v_lchild_468_; lean_object* v_key_469_; lean_object* v_val_470_; lean_object* v_rchild_471_; 
lean_inc_ref(v_rchild_446_);
lean_inc_ref(v_lchild_443_);
lean_inc(v_val_445_);
lean_inc(v_key_444_);
lean_dec_ref_known(v_x_431_, 4);
v_lchild_468_ = lean_ctor_get(v_rchild_446_, 0);
lean_inc(v_lchild_468_);
v_key_469_ = lean_ctor_get(v_rchild_446_, 1);
lean_inc(v_key_469_);
v_val_470_ = lean_ctor_get(v_rchild_446_, 2);
lean_inc(v_val_470_);
v_rchild_471_ = lean_ctor_get(v_rchild_446_, 3);
lean_inc(v_rchild_471_);
lean_dec_ref_known(v_rchild_446_, 4);
v_a_448_ = v_lchild_443_;
v_kx_449_ = v_key_444_;
v_vx_450_ = v_val_445_;
v_b_451_ = v_lchild_468_;
v_ky_452_ = v_key_469_;
v_vy_453_ = v_val_470_;
v_c_454_ = v_rchild_471_;
v_kz_455_ = v_x_432_;
v_vz_456_ = v_x_433_;
v_d_457_ = v_x_434_;
goto v___jp_447_;
}
else
{
v_a_436_ = v_x_431_;
v_kx_437_ = v_x_432_;
v_vx_438_ = v_x_433_;
v_b_439_ = v_x_434_;
goto v___jp_435_;
}
}
else
{
v_a_436_ = v_x_431_;
v_kx_437_ = v_x_432_;
v_vx_438_ = v_x_433_;
v_b_439_ = v_x_434_;
goto v___jp_435_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_446_) == 1)
{
uint8_t v_color_472_; 
v_color_472_ = lean_ctor_get_uint8(v_rchild_446_, sizeof(void*)*4);
if (v_color_472_ == 0)
{
lean_object* v_lchild_473_; lean_object* v_key_474_; lean_object* v_val_475_; lean_object* v_rchild_476_; 
lean_inc_ref(v_rchild_446_);
lean_inc(v_val_445_);
lean_inc(v_key_444_);
lean_inc(v_lchild_443_);
lean_dec_ref_known(v_x_431_, 4);
v_lchild_473_ = lean_ctor_get(v_rchild_446_, 0);
lean_inc(v_lchild_473_);
v_key_474_ = lean_ctor_get(v_rchild_446_, 1);
lean_inc(v_key_474_);
v_val_475_ = lean_ctor_get(v_rchild_446_, 2);
lean_inc(v_val_475_);
v_rchild_476_ = lean_ctor_get(v_rchild_446_, 3);
lean_inc(v_rchild_476_);
lean_dec_ref_known(v_rchild_446_, 4);
v_a_448_ = v_lchild_443_;
v_kx_449_ = v_key_444_;
v_vx_450_ = v_val_445_;
v_b_451_ = v_lchild_473_;
v_ky_452_ = v_key_474_;
v_vy_453_ = v_val_475_;
v_c_454_ = v_rchild_476_;
v_kz_455_ = v_x_432_;
v_vz_456_ = v_x_433_;
v_d_457_ = v_x_434_;
goto v___jp_447_;
}
else
{
v_a_436_ = v_x_431_;
v_kx_437_ = v_x_432_;
v_vx_438_ = v_x_433_;
v_b_439_ = v_x_434_;
goto v___jp_435_;
}
}
else
{
v_a_436_ = v_x_431_;
v_kx_437_ = v_x_432_;
v_vx_438_ = v_x_433_;
v_b_439_ = v_x_434_;
goto v___jp_435_;
}
}
}
else
{
v_a_436_ = v_x_431_;
v_kx_437_ = v_x_432_;
v_vx_438_ = v_x_433_;
v_b_439_ = v_x_434_;
goto v___jp_435_;
}
v___jp_447_:
{
uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = 1;
v___x_459_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_459_, 0, v_a_448_);
lean_ctor_set(v___x_459_, 1, v_kx_449_);
lean_ctor_set(v___x_459_, 2, v_vx_450_);
lean_ctor_set(v___x_459_, 3, v_b_451_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*4, v___x_458_);
v___x_460_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_460_, 0, v_c_454_);
lean_ctor_set(v___x_460_, 1, v_kz_455_);
lean_ctor_set(v___x_460_, 2, v_vz_456_);
lean_ctor_set(v___x_460_, 3, v_d_457_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*4, v___x_458_);
v___x_461_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v_ky_452_);
lean_ctor_set(v___x_461_, 2, v_vy_453_);
lean_ctor_set(v___x_461_, 3, v___x_460_);
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*4, v_color_442_);
return v___x_461_;
}
}
else
{
v_a_436_ = v_x_431_;
v_kx_437_ = v_x_432_;
v_vx_438_ = v_x_433_;
v_b_439_ = v_x_434_;
goto v___jp_435_;
}
v___jp_435_:
{
uint8_t v___x_440_; lean_object* v___x_441_; 
v___x_440_ = 1;
v___x_441_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_441_, 0, v_a_436_);
lean_ctor_set(v___x_441_, 1, v_kx_437_);
lean_ctor_set(v___x_441_, 2, v_vx_438_);
lean_ctor_set(v___x_441_, 3, v_b_439_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*4, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_a_484_; lean_object* v_kx_485_; lean_object* v_vx_486_; lean_object* v_b_487_; 
if (lean_obj_tag(v_x_479_) == 1)
{
uint8_t v_color_490_; lean_object* v_lchild_491_; lean_object* v_key_492_; lean_object* v_val_493_; lean_object* v_rchild_494_; lean_object* v_a_496_; lean_object* v_kx_497_; lean_object* v_vx_498_; lean_object* v_b_499_; lean_object* v_ky_500_; lean_object* v_vy_501_; lean_object* v_c_502_; lean_object* v_kz_503_; lean_object* v_vz_504_; lean_object* v_d_505_; 
v_color_490_ = lean_ctor_get_uint8(v_x_479_, sizeof(void*)*4);
v_lchild_491_ = lean_ctor_get(v_x_479_, 0);
v_key_492_ = lean_ctor_get(v_x_479_, 1);
v_val_493_ = lean_ctor_get(v_x_479_, 2);
v_rchild_494_ = lean_ctor_get(v_x_479_, 3);
if (v_color_490_ == 0)
{
if (lean_obj_tag(v_lchild_491_) == 1)
{
uint8_t v_color_510_; 
v_color_510_ = lean_ctor_get_uint8(v_lchild_491_, sizeof(void*)*4);
if (v_color_510_ == 0)
{
lean_object* v_lchild_511_; lean_object* v_key_512_; lean_object* v_val_513_; lean_object* v_rchild_514_; 
lean_inc_ref(v_lchild_491_);
lean_inc(v_rchild_494_);
lean_inc(v_val_493_);
lean_inc(v_key_492_);
lean_dec_ref_known(v_x_479_, 4);
v_lchild_511_ = lean_ctor_get(v_lchild_491_, 0);
lean_inc(v_lchild_511_);
v_key_512_ = lean_ctor_get(v_lchild_491_, 1);
lean_inc(v_key_512_);
v_val_513_ = lean_ctor_get(v_lchild_491_, 2);
lean_inc(v_val_513_);
v_rchild_514_ = lean_ctor_get(v_lchild_491_, 3);
lean_inc(v_rchild_514_);
lean_dec_ref_known(v_lchild_491_, 4);
v_a_496_ = v_lchild_511_;
v_kx_497_ = v_key_512_;
v_vx_498_ = v_val_513_;
v_b_499_ = v_rchild_514_;
v_ky_500_ = v_key_492_;
v_vy_501_ = v_val_493_;
v_c_502_ = v_rchild_494_;
v_kz_503_ = v_x_480_;
v_vz_504_ = v_x_481_;
v_d_505_ = v_x_482_;
goto v___jp_495_;
}
else
{
if (lean_obj_tag(v_rchild_494_) == 1)
{
uint8_t v_color_515_; 
v_color_515_ = lean_ctor_get_uint8(v_rchild_494_, sizeof(void*)*4);
if (v_color_515_ == 0)
{
lean_object* v_lchild_516_; lean_object* v_key_517_; lean_object* v_val_518_; lean_object* v_rchild_519_; 
lean_inc_ref(v_rchild_494_);
lean_inc_ref(v_lchild_491_);
lean_inc(v_val_493_);
lean_inc(v_key_492_);
lean_dec_ref_known(v_x_479_, 4);
v_lchild_516_ = lean_ctor_get(v_rchild_494_, 0);
lean_inc(v_lchild_516_);
v_key_517_ = lean_ctor_get(v_rchild_494_, 1);
lean_inc(v_key_517_);
v_val_518_ = lean_ctor_get(v_rchild_494_, 2);
lean_inc(v_val_518_);
v_rchild_519_ = lean_ctor_get(v_rchild_494_, 3);
lean_inc(v_rchild_519_);
lean_dec_ref_known(v_rchild_494_, 4);
v_a_496_ = v_lchild_491_;
v_kx_497_ = v_key_492_;
v_vx_498_ = v_val_493_;
v_b_499_ = v_lchild_516_;
v_ky_500_ = v_key_517_;
v_vy_501_ = v_val_518_;
v_c_502_ = v_rchild_519_;
v_kz_503_ = v_x_480_;
v_vz_504_ = v_x_481_;
v_d_505_ = v_x_482_;
goto v___jp_495_;
}
else
{
v_a_484_ = v_x_479_;
v_kx_485_ = v_x_480_;
v_vx_486_ = v_x_481_;
v_b_487_ = v_x_482_;
goto v___jp_483_;
}
}
else
{
v_a_484_ = v_x_479_;
v_kx_485_ = v_x_480_;
v_vx_486_ = v_x_481_;
v_b_487_ = v_x_482_;
goto v___jp_483_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_494_) == 1)
{
uint8_t v_color_520_; 
v_color_520_ = lean_ctor_get_uint8(v_rchild_494_, sizeof(void*)*4);
if (v_color_520_ == 0)
{
lean_object* v_lchild_521_; lean_object* v_key_522_; lean_object* v_val_523_; lean_object* v_rchild_524_; 
lean_inc_ref(v_rchild_494_);
lean_inc(v_val_493_);
lean_inc(v_key_492_);
lean_inc(v_lchild_491_);
lean_dec_ref_known(v_x_479_, 4);
v_lchild_521_ = lean_ctor_get(v_rchild_494_, 0);
lean_inc(v_lchild_521_);
v_key_522_ = lean_ctor_get(v_rchild_494_, 1);
lean_inc(v_key_522_);
v_val_523_ = lean_ctor_get(v_rchild_494_, 2);
lean_inc(v_val_523_);
v_rchild_524_ = lean_ctor_get(v_rchild_494_, 3);
lean_inc(v_rchild_524_);
lean_dec_ref_known(v_rchild_494_, 4);
v_a_496_ = v_lchild_491_;
v_kx_497_ = v_key_492_;
v_vx_498_ = v_val_493_;
v_b_499_ = v_lchild_521_;
v_ky_500_ = v_key_522_;
v_vy_501_ = v_val_523_;
v_c_502_ = v_rchild_524_;
v_kz_503_ = v_x_480_;
v_vz_504_ = v_x_481_;
v_d_505_ = v_x_482_;
goto v___jp_495_;
}
else
{
v_a_484_ = v_x_479_;
v_kx_485_ = v_x_480_;
v_vx_486_ = v_x_481_;
v_b_487_ = v_x_482_;
goto v___jp_483_;
}
}
else
{
v_a_484_ = v_x_479_;
v_kx_485_ = v_x_480_;
v_vx_486_ = v_x_481_;
v_b_487_ = v_x_482_;
goto v___jp_483_;
}
}
}
else
{
v_a_484_ = v_x_479_;
v_kx_485_ = v_x_480_;
v_vx_486_ = v_x_481_;
v_b_487_ = v_x_482_;
goto v___jp_483_;
}
v___jp_495_:
{
uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = 1;
v___x_507_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_507_, 0, v_a_496_);
lean_ctor_set(v___x_507_, 1, v_kx_497_);
lean_ctor_set(v___x_507_, 2, v_vx_498_);
lean_ctor_set(v___x_507_, 3, v_b_499_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*4, v___x_506_);
v___x_508_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_508_, 0, v_c_502_);
lean_ctor_set(v___x_508_, 1, v_kz_503_);
lean_ctor_set(v___x_508_, 2, v_vz_504_);
lean_ctor_set(v___x_508_, 3, v_d_505_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*4, v___x_506_);
v___x_509_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v_ky_500_);
lean_ctor_set(v___x_509_, 2, v_vy_501_);
lean_ctor_set(v___x_509_, 3, v___x_508_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*4, v_color_490_);
return v___x_509_;
}
}
else
{
v_a_484_ = v_x_479_;
v_kx_485_ = v_x_480_;
v_vx_486_ = v_x_481_;
v_b_487_ = v_x_482_;
goto v___jp_483_;
}
v___jp_483_:
{
uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_488_ = 1;
v___x_489_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_489_, 0, v_a_484_);
lean_ctor_set(v___x_489_, 1, v_kx_485_);
lean_ctor_set(v___x_489_, 2, v_vx_486_);
lean_ctor_set(v___x_489_, 3, v_b_487_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*4, v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_a_530_; lean_object* v_kx_531_; lean_object* v_vx_532_; lean_object* v_b_533_; 
if (lean_obj_tag(v_x_528_) == 1)
{
uint8_t v_color_536_; lean_object* v_lchild_537_; lean_object* v_key_538_; lean_object* v_val_539_; lean_object* v_rchild_540_; lean_object* v_a_542_; lean_object* v_kx_543_; lean_object* v_vx_544_; lean_object* v_b_545_; lean_object* v_ky_546_; lean_object* v_vy_547_; lean_object* v_c_548_; lean_object* v_kz_549_; lean_object* v_vz_550_; lean_object* v_d_551_; 
v_color_536_ = lean_ctor_get_uint8(v_x_528_, sizeof(void*)*4);
v_lchild_537_ = lean_ctor_get(v_x_528_, 0);
v_key_538_ = lean_ctor_get(v_x_528_, 1);
v_val_539_ = lean_ctor_get(v_x_528_, 2);
v_rchild_540_ = lean_ctor_get(v_x_528_, 3);
if (v_color_536_ == 0)
{
if (lean_obj_tag(v_lchild_537_) == 1)
{
uint8_t v_color_556_; 
v_color_556_ = lean_ctor_get_uint8(v_lchild_537_, sizeof(void*)*4);
if (v_color_556_ == 0)
{
lean_object* v_lchild_557_; lean_object* v_key_558_; lean_object* v_val_559_; lean_object* v_rchild_560_; 
lean_inc_ref(v_lchild_537_);
lean_inc(v_rchild_540_);
lean_inc(v_val_539_);
lean_inc(v_key_538_);
lean_dec_ref_known(v_x_528_, 4);
v_lchild_557_ = lean_ctor_get(v_lchild_537_, 0);
lean_inc(v_lchild_557_);
v_key_558_ = lean_ctor_get(v_lchild_537_, 1);
lean_inc(v_key_558_);
v_val_559_ = lean_ctor_get(v_lchild_537_, 2);
lean_inc(v_val_559_);
v_rchild_560_ = lean_ctor_get(v_lchild_537_, 3);
lean_inc(v_rchild_560_);
lean_dec_ref_known(v_lchild_537_, 4);
v_a_542_ = v_x_525_;
v_kx_543_ = v_x_526_;
v_vx_544_ = v_x_527_;
v_b_545_ = v_lchild_557_;
v_ky_546_ = v_key_558_;
v_vy_547_ = v_val_559_;
v_c_548_ = v_rchild_560_;
v_kz_549_ = v_key_538_;
v_vz_550_ = v_val_539_;
v_d_551_ = v_rchild_540_;
goto v___jp_541_;
}
else
{
if (lean_obj_tag(v_rchild_540_) == 1)
{
uint8_t v_color_561_; 
v_color_561_ = lean_ctor_get_uint8(v_rchild_540_, sizeof(void*)*4);
if (v_color_561_ == 0)
{
lean_object* v_lchild_562_; lean_object* v_key_563_; lean_object* v_val_564_; lean_object* v_rchild_565_; 
lean_inc_ref(v_rchild_540_);
lean_inc_ref(v_lchild_537_);
lean_inc(v_val_539_);
lean_inc(v_key_538_);
lean_dec_ref_known(v_x_528_, 4);
v_lchild_562_ = lean_ctor_get(v_rchild_540_, 0);
lean_inc(v_lchild_562_);
v_key_563_ = lean_ctor_get(v_rchild_540_, 1);
lean_inc(v_key_563_);
v_val_564_ = lean_ctor_get(v_rchild_540_, 2);
lean_inc(v_val_564_);
v_rchild_565_ = lean_ctor_get(v_rchild_540_, 3);
lean_inc(v_rchild_565_);
lean_dec_ref_known(v_rchild_540_, 4);
v_a_542_ = v_x_525_;
v_kx_543_ = v_x_526_;
v_vx_544_ = v_x_527_;
v_b_545_ = v_lchild_537_;
v_ky_546_ = v_key_538_;
v_vy_547_ = v_val_539_;
v_c_548_ = v_lchild_562_;
v_kz_549_ = v_key_563_;
v_vz_550_ = v_val_564_;
v_d_551_ = v_rchild_565_;
goto v___jp_541_;
}
else
{
v_a_530_ = v_x_525_;
v_kx_531_ = v_x_526_;
v_vx_532_ = v_x_527_;
v_b_533_ = v_x_528_;
goto v___jp_529_;
}
}
else
{
v_a_530_ = v_x_525_;
v_kx_531_ = v_x_526_;
v_vx_532_ = v_x_527_;
v_b_533_ = v_x_528_;
goto v___jp_529_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_540_) == 1)
{
uint8_t v_color_566_; 
v_color_566_ = lean_ctor_get_uint8(v_rchild_540_, sizeof(void*)*4);
if (v_color_566_ == 0)
{
lean_object* v_lchild_567_; lean_object* v_key_568_; lean_object* v_val_569_; lean_object* v_rchild_570_; 
lean_inc_ref(v_rchild_540_);
lean_inc(v_val_539_);
lean_inc(v_key_538_);
lean_inc(v_lchild_537_);
lean_dec_ref_known(v_x_528_, 4);
v_lchild_567_ = lean_ctor_get(v_rchild_540_, 0);
lean_inc(v_lchild_567_);
v_key_568_ = lean_ctor_get(v_rchild_540_, 1);
lean_inc(v_key_568_);
v_val_569_ = lean_ctor_get(v_rchild_540_, 2);
lean_inc(v_val_569_);
v_rchild_570_ = lean_ctor_get(v_rchild_540_, 3);
lean_inc(v_rchild_570_);
lean_dec_ref_known(v_rchild_540_, 4);
v_a_542_ = v_x_525_;
v_kx_543_ = v_x_526_;
v_vx_544_ = v_x_527_;
v_b_545_ = v_lchild_537_;
v_ky_546_ = v_key_538_;
v_vy_547_ = v_val_539_;
v_c_548_ = v_lchild_567_;
v_kz_549_ = v_key_568_;
v_vz_550_ = v_val_569_;
v_d_551_ = v_rchild_570_;
goto v___jp_541_;
}
else
{
v_a_530_ = v_x_525_;
v_kx_531_ = v_x_526_;
v_vx_532_ = v_x_527_;
v_b_533_ = v_x_528_;
goto v___jp_529_;
}
}
else
{
v_a_530_ = v_x_525_;
v_kx_531_ = v_x_526_;
v_vx_532_ = v_x_527_;
v_b_533_ = v_x_528_;
goto v___jp_529_;
}
}
}
else
{
v_a_530_ = v_x_525_;
v_kx_531_ = v_x_526_;
v_vx_532_ = v_x_527_;
v_b_533_ = v_x_528_;
goto v___jp_529_;
}
v___jp_541_:
{
uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = 1;
v___x_553_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_553_, 0, v_a_542_);
lean_ctor_set(v___x_553_, 1, v_kx_543_);
lean_ctor_set(v___x_553_, 2, v_vx_544_);
lean_ctor_set(v___x_553_, 3, v_b_545_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*4, v___x_552_);
v___x_554_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_554_, 0, v_c_548_);
lean_ctor_set(v___x_554_, 1, v_kz_549_);
lean_ctor_set(v___x_554_, 2, v_vz_550_);
lean_ctor_set(v___x_554_, 3, v_d_551_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*4, v___x_552_);
v___x_555_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v_ky_546_);
lean_ctor_set(v___x_555_, 2, v_vy_547_);
lean_ctor_set(v___x_555_, 3, v___x_554_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*4, v_color_536_);
return v___x_555_;
}
}
else
{
v_a_530_ = v_x_525_;
v_kx_531_ = v_x_526_;
v_vx_532_ = v_x_527_;
v_b_533_ = v_x_528_;
goto v___jp_529_;
}
v___jp_529_:
{
uint8_t v___x_534_; lean_object* v___x_535_; 
v___x_534_ = 1;
v___x_535_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_535_, 0, v_a_530_);
lean_ctor_set(v___x_535_, 1, v_kx_531_);
lean_ctor_set(v___x_535_, 2, v_vx_532_);
lean_ctor_set(v___x_535_, 3, v_b_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*4, v___x_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_a_578_; lean_object* v_kx_579_; lean_object* v_vx_580_; lean_object* v_b_581_; 
if (lean_obj_tag(v_x_576_) == 1)
{
uint8_t v_color_584_; lean_object* v_lchild_585_; lean_object* v_key_586_; lean_object* v_val_587_; lean_object* v_rchild_588_; lean_object* v_a_590_; lean_object* v_kx_591_; lean_object* v_vx_592_; lean_object* v_b_593_; lean_object* v_ky_594_; lean_object* v_vy_595_; lean_object* v_c_596_; lean_object* v_kz_597_; lean_object* v_vz_598_; lean_object* v_d_599_; 
v_color_584_ = lean_ctor_get_uint8(v_x_576_, sizeof(void*)*4);
v_lchild_585_ = lean_ctor_get(v_x_576_, 0);
v_key_586_ = lean_ctor_get(v_x_576_, 1);
v_val_587_ = lean_ctor_get(v_x_576_, 2);
v_rchild_588_ = lean_ctor_get(v_x_576_, 3);
if (v_color_584_ == 0)
{
if (lean_obj_tag(v_lchild_585_) == 1)
{
uint8_t v_color_604_; 
v_color_604_ = lean_ctor_get_uint8(v_lchild_585_, sizeof(void*)*4);
if (v_color_604_ == 0)
{
lean_object* v_lchild_605_; lean_object* v_key_606_; lean_object* v_val_607_; lean_object* v_rchild_608_; 
lean_inc_ref(v_lchild_585_);
lean_inc(v_rchild_588_);
lean_inc(v_val_587_);
lean_inc(v_key_586_);
lean_dec_ref_known(v_x_576_, 4);
v_lchild_605_ = lean_ctor_get(v_lchild_585_, 0);
lean_inc(v_lchild_605_);
v_key_606_ = lean_ctor_get(v_lchild_585_, 1);
lean_inc(v_key_606_);
v_val_607_ = lean_ctor_get(v_lchild_585_, 2);
lean_inc(v_val_607_);
v_rchild_608_ = lean_ctor_get(v_lchild_585_, 3);
lean_inc(v_rchild_608_);
lean_dec_ref_known(v_lchild_585_, 4);
v_a_590_ = v_x_573_;
v_kx_591_ = v_x_574_;
v_vx_592_ = v_x_575_;
v_b_593_ = v_lchild_605_;
v_ky_594_ = v_key_606_;
v_vy_595_ = v_val_607_;
v_c_596_ = v_rchild_608_;
v_kz_597_ = v_key_586_;
v_vz_598_ = v_val_587_;
v_d_599_ = v_rchild_588_;
goto v___jp_589_;
}
else
{
if (lean_obj_tag(v_rchild_588_) == 1)
{
uint8_t v_color_609_; 
v_color_609_ = lean_ctor_get_uint8(v_rchild_588_, sizeof(void*)*4);
if (v_color_609_ == 0)
{
lean_object* v_lchild_610_; lean_object* v_key_611_; lean_object* v_val_612_; lean_object* v_rchild_613_; 
lean_inc_ref(v_rchild_588_);
lean_inc_ref(v_lchild_585_);
lean_inc(v_val_587_);
lean_inc(v_key_586_);
lean_dec_ref_known(v_x_576_, 4);
v_lchild_610_ = lean_ctor_get(v_rchild_588_, 0);
lean_inc(v_lchild_610_);
v_key_611_ = lean_ctor_get(v_rchild_588_, 1);
lean_inc(v_key_611_);
v_val_612_ = lean_ctor_get(v_rchild_588_, 2);
lean_inc(v_val_612_);
v_rchild_613_ = lean_ctor_get(v_rchild_588_, 3);
lean_inc(v_rchild_613_);
lean_dec_ref_known(v_rchild_588_, 4);
v_a_590_ = v_x_573_;
v_kx_591_ = v_x_574_;
v_vx_592_ = v_x_575_;
v_b_593_ = v_lchild_585_;
v_ky_594_ = v_key_586_;
v_vy_595_ = v_val_587_;
v_c_596_ = v_lchild_610_;
v_kz_597_ = v_key_611_;
v_vz_598_ = v_val_612_;
v_d_599_ = v_rchild_613_;
goto v___jp_589_;
}
else
{
v_a_578_ = v_x_573_;
v_kx_579_ = v_x_574_;
v_vx_580_ = v_x_575_;
v_b_581_ = v_x_576_;
goto v___jp_577_;
}
}
else
{
v_a_578_ = v_x_573_;
v_kx_579_ = v_x_574_;
v_vx_580_ = v_x_575_;
v_b_581_ = v_x_576_;
goto v___jp_577_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_588_) == 1)
{
uint8_t v_color_614_; 
v_color_614_ = lean_ctor_get_uint8(v_rchild_588_, sizeof(void*)*4);
if (v_color_614_ == 0)
{
lean_object* v_lchild_615_; lean_object* v_key_616_; lean_object* v_val_617_; lean_object* v_rchild_618_; 
lean_inc_ref(v_rchild_588_);
lean_inc(v_val_587_);
lean_inc(v_key_586_);
lean_inc(v_lchild_585_);
lean_dec_ref_known(v_x_576_, 4);
v_lchild_615_ = lean_ctor_get(v_rchild_588_, 0);
lean_inc(v_lchild_615_);
v_key_616_ = lean_ctor_get(v_rchild_588_, 1);
lean_inc(v_key_616_);
v_val_617_ = lean_ctor_get(v_rchild_588_, 2);
lean_inc(v_val_617_);
v_rchild_618_ = lean_ctor_get(v_rchild_588_, 3);
lean_inc(v_rchild_618_);
lean_dec_ref_known(v_rchild_588_, 4);
v_a_590_ = v_x_573_;
v_kx_591_ = v_x_574_;
v_vx_592_ = v_x_575_;
v_b_593_ = v_lchild_585_;
v_ky_594_ = v_key_586_;
v_vy_595_ = v_val_587_;
v_c_596_ = v_lchild_615_;
v_kz_597_ = v_key_616_;
v_vz_598_ = v_val_617_;
v_d_599_ = v_rchild_618_;
goto v___jp_589_;
}
else
{
v_a_578_ = v_x_573_;
v_kx_579_ = v_x_574_;
v_vx_580_ = v_x_575_;
v_b_581_ = v_x_576_;
goto v___jp_577_;
}
}
else
{
v_a_578_ = v_x_573_;
v_kx_579_ = v_x_574_;
v_vx_580_ = v_x_575_;
v_b_581_ = v_x_576_;
goto v___jp_577_;
}
}
}
else
{
v_a_578_ = v_x_573_;
v_kx_579_ = v_x_574_;
v_vx_580_ = v_x_575_;
v_b_581_ = v_x_576_;
goto v___jp_577_;
}
v___jp_589_:
{
uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = 1;
v___x_601_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_601_, 0, v_a_590_);
lean_ctor_set(v___x_601_, 1, v_kx_591_);
lean_ctor_set(v___x_601_, 2, v_vx_592_);
lean_ctor_set(v___x_601_, 3, v_b_593_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*4, v___x_600_);
v___x_602_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_602_, 0, v_c_596_);
lean_ctor_set(v___x_602_, 1, v_kz_597_);
lean_ctor_set(v___x_602_, 2, v_vz_598_);
lean_ctor_set(v___x_602_, 3, v_d_599_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*4, v___x_600_);
v___x_603_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v_ky_594_);
lean_ctor_set(v___x_603_, 2, v_vy_595_);
lean_ctor_set(v___x_603_, 3, v___x_602_);
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*4, v_color_584_);
return v___x_603_;
}
}
else
{
v_a_578_ = v_x_573_;
v_kx_579_ = v_x_574_;
v_vx_580_ = v_x_575_;
v_b_581_ = v_x_576_;
goto v___jp_577_;
}
v___jp_577_:
{
uint8_t v___x_582_; lean_object* v___x_583_; 
v___x_582_ = 1;
v___x_583_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_583_, 0, v_a_578_);
lean_ctor_set(v___x_583_, 1, v_kx_579_);
lean_ctor_set(v___x_583_, 2, v_vx_580_);
lean_ctor_set(v___x_583_, 3, v_b_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*4, v___x_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___redArg(lean_object* v_x_619_){
_start:
{
if (lean_obj_tag(v_x_619_) == 1)
{
uint8_t v_color_620_; 
v_color_620_ = lean_ctor_get_uint8(v_x_619_, sizeof(void*)*4);
if (v_color_620_ == 0)
{
uint8_t v___x_621_; 
v___x_621_ = 1;
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = 0;
return v___x_622_;
}
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object* v_x_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_Lean_RBNode_isRed___redArg(v_x_624_);
lean_dec(v_x_624_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object* v_00_u03b1_627_, lean_object* v_00_u03b2_628_, lean_object* v_x_629_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = l_Lean_RBNode_isRed___redArg(v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object* v_00_u03b1_631_, lean_object* v_00_u03b2_632_, lean_object* v_x_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Lean_RBNode_isRed(v_00_u03b1_631_, v_00_u03b2_632_, v_x_633_);
lean_dec(v_x_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___redArg(lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 1)
{
uint8_t v_color_637_; 
v_color_637_ = lean_ctor_get_uint8(v_x_636_, sizeof(void*)*4);
if (v_color_637_ == 1)
{
uint8_t v___x_638_; 
v___x_638_ = 1;
return v___x_638_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
else
{
uint8_t v___x_640_; 
v___x_640_ = 0;
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object* v_x_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Lean_RBNode_isBlack___redArg(v_x_641_);
lean_dec(v_x_641_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b2_645_, lean_object* v_x_646_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = l_Lean_RBNode_isBlack___redArg(v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Lean_RBNode_isBlack(v_00_u03b1_648_, v_00_u03b2_649_, v_x_650_);
lean_dec(v_x_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object* v_cmp_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
uint8_t v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v_cmp_653_);
v___x_657_ = 0;
v___x_658_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_658_, 0, v_x_654_);
lean_ctor_set(v___x_658_, 1, v_x_655_);
lean_ctor_set(v___x_658_, 2, v_x_656_);
lean_ctor_set(v___x_658_, 3, v_x_654_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*4, v___x_657_);
return v___x_658_;
}
else
{
uint8_t v_color_659_; 
v_color_659_ = lean_ctor_get_uint8(v_x_654_, sizeof(void*)*4);
if (v_color_659_ == 0)
{
lean_object* v_lchild_660_; lean_object* v_key_661_; lean_object* v_val_662_; lean_object* v_rchild_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_680_; 
v_lchild_660_ = lean_ctor_get(v_x_654_, 0);
v_key_661_ = lean_ctor_get(v_x_654_, 1);
v_val_662_ = lean_ctor_get(v_x_654_, 2);
v_rchild_663_ = lean_ctor_get(v_x_654_, 3);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_680_ == 0)
{
v___x_665_ = v_x_654_;
v_isShared_666_ = v_isSharedCheck_680_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_rchild_663_);
lean_inc(v_val_662_);
lean_inc(v_key_661_);
lean_inc(v_lchild_660_);
lean_dec(v_x_654_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_680_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
lean_inc_ref(v_cmp_653_);
lean_inc(v_key_661_);
lean_inc(v_x_655_);
v___x_667_ = lean_apply_2(v_cmp_653_, v_x_655_, v_key_661_);
v___x_668_ = lean_unbox(v___x_667_);
switch(v___x_668_)
{
case 0:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_RBNode_ins___redArg(v_cmp_653_, v_lchild_660_, v_x_655_, v_x_656_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_669_);
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_key_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_val_662_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_rchild_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_672_, sizeof(void*)*4, v_color_659_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
case 1:
{
lean_object* v___x_674_; 
lean_dec(v_val_662_);
lean_dec(v_key_661_);
lean_dec_ref(v_cmp_653_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 2, v_x_656_);
lean_ctor_set(v___x_665_, 1, v_x_655_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_lchild_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_x_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_x_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_rchild_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_675_, sizeof(void*)*4, v_color_659_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
default: 
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = l_Lean_RBNode_ins___redArg(v_cmp_653_, v_rchild_663_, v_x_655_, v_x_656_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v___x_676_);
v___x_678_ = v___x_665_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_lchild_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_key_661_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_val_662_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v___x_676_);
lean_ctor_set_uint8(v_reuseFailAlloc_679_, sizeof(void*)*4, v_color_659_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
else
{
lean_object* v_lchild_681_; lean_object* v_key_682_; lean_object* v_val_683_; lean_object* v_rchild_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_843_; 
v_lchild_681_ = lean_ctor_get(v_x_654_, 0);
v_key_682_ = lean_ctor_get(v_x_654_, 1);
v_val_683_ = lean_ctor_get(v_x_654_, 2);
v_rchild_684_ = lean_ctor_get(v_x_654_, 3);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_843_ == 0)
{
v___x_686_ = v_x_654_;
v_isShared_687_ = v_isSharedCheck_843_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_rchild_684_);
lean_inc(v_val_683_);
lean_inc(v_key_682_);
lean_inc(v_lchild_681_);
lean_dec(v_x_654_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_843_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
lean_inc_ref(v_cmp_653_);
lean_inc(v_key_682_);
lean_inc(v_x_655_);
v___x_688_ = lean_apply_2(v_cmp_653_, v_x_655_, v_key_682_);
v___x_689_ = lean_unbox(v___x_688_);
switch(v___x_689_)
{
case 0:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_RBNode_ins___redArg(v_cmp_653_, v_lchild_681_, v_x_655_, v_x_656_);
if (lean_obj_tag(v___x_690_) == 1)
{
uint8_t v_color_691_; lean_object* v_lchild_692_; lean_object* v_key_693_; lean_object* v_val_694_; lean_object* v_rchild_695_; lean_object* v_a_697_; lean_object* v_kx_698_; lean_object* v_vx_699_; lean_object* v_b_700_; lean_object* v_ky_701_; lean_object* v_vy_702_; lean_object* v_c_703_; lean_object* v_kz_704_; lean_object* v_vz_705_; lean_object* v_d_706_; 
v_color_691_ = lean_ctor_get_uint8(v___x_690_, sizeof(void*)*4);
v_lchild_692_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_lchild_692_);
v_key_693_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_key_693_);
v_val_694_ = lean_ctor_get(v___x_690_, 2);
lean_inc(v_val_694_);
v_rchild_695_ = lean_ctor_get(v___x_690_, 3);
lean_inc(v_rchild_695_);
if (v_color_691_ == 0)
{
if (lean_obj_tag(v_lchild_692_) == 1)
{
uint8_t v_color_712_; 
v_color_712_ = lean_ctor_get_uint8(v_lchild_692_, sizeof(void*)*4);
if (v_color_712_ == 0)
{
lean_object* v_lchild_713_; lean_object* v_key_714_; lean_object* v_val_715_; lean_object* v_rchild_716_; 
lean_dec_ref_known(v___x_690_, 4);
v_lchild_713_ = lean_ctor_get(v_lchild_692_, 0);
lean_inc(v_lchild_713_);
v_key_714_ = lean_ctor_get(v_lchild_692_, 1);
lean_inc(v_key_714_);
v_val_715_ = lean_ctor_get(v_lchild_692_, 2);
lean_inc(v_val_715_);
v_rchild_716_ = lean_ctor_get(v_lchild_692_, 3);
lean_inc(v_rchild_716_);
lean_dec_ref_known(v_lchild_692_, 4);
v_a_697_ = v_lchild_713_;
v_kx_698_ = v_key_714_;
v_vx_699_ = v_val_715_;
v_b_700_ = v_rchild_716_;
v_ky_701_ = v_key_693_;
v_vy_702_ = v_val_694_;
v_c_703_ = v_rchild_695_;
v_kz_704_ = v_key_682_;
v_vz_705_ = v_val_683_;
v_d_706_ = v_rchild_684_;
goto v___jp_696_;
}
else
{
if (lean_obj_tag(v_rchild_695_) == 1)
{
uint8_t v_color_717_; 
v_color_717_ = lean_ctor_get_uint8(v_rchild_695_, sizeof(void*)*4);
if (v_color_717_ == 0)
{
lean_object* v_lchild_718_; lean_object* v_key_719_; lean_object* v_val_720_; lean_object* v_rchild_721_; 
lean_dec_ref_known(v___x_690_, 4);
v_lchild_718_ = lean_ctor_get(v_rchild_695_, 0);
lean_inc(v_lchild_718_);
v_key_719_ = lean_ctor_get(v_rchild_695_, 1);
lean_inc(v_key_719_);
v_val_720_ = lean_ctor_get(v_rchild_695_, 2);
lean_inc(v_val_720_);
v_rchild_721_ = lean_ctor_get(v_rchild_695_, 3);
lean_inc(v_rchild_721_);
lean_dec_ref_known(v_rchild_695_, 4);
v_a_697_ = v_lchild_692_;
v_kx_698_ = v_key_693_;
v_vx_699_ = v_val_694_;
v_b_700_ = v_lchild_718_;
v_ky_701_ = v_key_719_;
v_vy_702_ = v_val_720_;
v_c_703_ = v_rchild_721_;
v_kz_704_ = v_key_682_;
v_vz_705_ = v_val_683_;
v_d_706_ = v_rchild_684_;
goto v___jp_696_;
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref_known(v_lchild_692_, 4);
lean_dec(v_val_694_);
lean_dec(v_key_693_);
lean_del_object(v___x_686_);
v_isSharedCheck_728_ = !lean_is_exclusive(v_rchild_695_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_729_ = lean_ctor_get(v_rchild_695_, 3);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_rchild_695_, 2);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_rchild_695_, 1);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_rchild_695_, 0);
lean_dec(v_unused_732_);
v___x_723_ = v_rchild_695_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_dec(v_rchild_695_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 3, v_rchild_684_);
lean_ctor_set(v___x_723_, 2, v_val_683_);
lean_ctor_set(v___x_723_, 1, v_key_682_);
lean_ctor_set(v___x_723_, 0, v___x_690_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_rchild_684_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*4, v_color_659_);
return v___x_726_;
}
}
}
}
else
{
lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_rchild_695_);
lean_dec(v_val_694_);
lean_dec(v_key_693_);
lean_del_object(v___x_686_);
v_isSharedCheck_739_ = !lean_is_exclusive(v_lchild_692_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; lean_object* v_unused_741_; lean_object* v_unused_742_; lean_object* v_unused_743_; 
v_unused_740_ = lean_ctor_get(v_lchild_692_, 3);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_lchild_692_, 2);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_lchild_692_, 1);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_lchild_692_, 0);
lean_dec(v_unused_743_);
v___x_734_ = v_lchild_692_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_dec(v_lchild_692_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 3, v_rchild_684_);
lean_ctor_set(v___x_734_, 2, v_val_683_);
lean_ctor_set(v___x_734_, 1, v_key_682_);
lean_ctor_set(v___x_734_, 0, v___x_690_);
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v_rchild_684_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*4, v_color_659_);
return v___x_737_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_695_) == 1)
{
uint8_t v_color_744_; 
v_color_744_ = lean_ctor_get_uint8(v_rchild_695_, sizeof(void*)*4);
if (v_color_744_ == 0)
{
lean_object* v_lchild_745_; lean_object* v_key_746_; lean_object* v_val_747_; lean_object* v_rchild_748_; 
lean_dec_ref_known(v___x_690_, 4);
v_lchild_745_ = lean_ctor_get(v_rchild_695_, 0);
lean_inc(v_lchild_745_);
v_key_746_ = lean_ctor_get(v_rchild_695_, 1);
lean_inc(v_key_746_);
v_val_747_ = lean_ctor_get(v_rchild_695_, 2);
lean_inc(v_val_747_);
v_rchild_748_ = lean_ctor_get(v_rchild_695_, 3);
lean_inc(v_rchild_748_);
lean_dec_ref_known(v_rchild_695_, 4);
v_a_697_ = v_lchild_692_;
v_kx_698_ = v_key_693_;
v_vx_699_ = v_val_694_;
v_b_700_ = v_lchild_745_;
v_ky_701_ = v_key_746_;
v_vy_702_ = v_val_747_;
v_c_703_ = v_rchild_748_;
v_kz_704_ = v_key_682_;
v_vz_705_ = v_val_683_;
v_d_706_ = v_rchild_684_;
goto v___jp_696_;
}
else
{
lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_val_694_);
lean_dec(v_key_693_);
lean_dec(v_lchild_692_);
lean_del_object(v___x_686_);
v_isSharedCheck_755_ = !lean_is_exclusive(v_rchild_695_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; 
v_unused_756_ = lean_ctor_get(v_rchild_695_, 3);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_rchild_695_, 2);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_rchild_695_, 1);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_rchild_695_, 0);
lean_dec(v_unused_759_);
v___x_750_ = v_rchild_695_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_dec(v_rchild_695_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 3, v_rchild_684_);
lean_ctor_set(v___x_750_, 2, v_val_683_);
lean_ctor_set(v___x_750_, 1, v_key_682_);
lean_ctor_set(v___x_750_, 0, v___x_690_);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_rchild_684_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*4, v_color_659_);
return v___x_753_;
}
}
}
}
else
{
lean_object* v___x_760_; 
lean_dec(v_rchild_695_);
lean_dec(v_val_694_);
lean_dec(v_key_693_);
lean_dec(v_lchild_692_);
lean_del_object(v___x_686_);
v___x_760_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_760_, 0, v___x_690_);
lean_ctor_set(v___x_760_, 1, v_key_682_);
lean_ctor_set(v___x_760_, 2, v_val_683_);
lean_ctor_set(v___x_760_, 3, v_rchild_684_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*4, v_color_659_);
return v___x_760_;
}
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_rchild_695_);
lean_dec(v_val_694_);
lean_dec(v_key_693_);
lean_dec(v_lchild_692_);
lean_del_object(v___x_686_);
v___x_761_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_761_, 0, v___x_690_);
lean_ctor_set(v___x_761_, 1, v_key_682_);
lean_ctor_set(v___x_761_, 2, v_val_683_);
lean_ctor_set(v___x_761_, 3, v_rchild_684_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*4, v_color_659_);
return v___x_761_;
}
v___jp_696_:
{
lean_object* v___x_708_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v_b_700_);
lean_ctor_set(v___x_686_, 2, v_vx_699_);
lean_ctor_set(v___x_686_, 1, v_kx_698_);
lean_ctor_set(v___x_686_, 0, v_a_697_);
v___x_708_ = v___x_686_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_697_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_kx_698_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_vx_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_b_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_711_, sizeof(void*)*4, v_color_659_);
v___x_708_ = v_reuseFailAlloc_711_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_709_, 0, v_c_703_);
lean_ctor_set(v___x_709_, 1, v_kz_704_);
lean_ctor_set(v___x_709_, 2, v_vz_705_);
lean_ctor_set(v___x_709_, 3, v_d_706_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*4, v_color_659_);
v___x_710_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v_ky_701_);
lean_ctor_set(v___x_710_, 2, v_vy_702_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*4, v_color_691_);
return v___x_710_;
}
}
}
else
{
lean_object* v___x_763_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_763_ = v___x_686_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_rchild_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_764_, sizeof(void*)*4, v_color_659_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
case 1:
{
lean_object* v___x_766_; 
lean_dec(v_val_683_);
lean_dec(v_key_682_);
lean_dec_ref(v_cmp_653_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 2, v_x_656_);
lean_ctor_set(v___x_686_, 1, v_x_655_);
v___x_766_ = v___x_686_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_lchild_681_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_x_655_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_x_656_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_rchild_684_);
lean_ctor_set_uint8(v_reuseFailAlloc_767_, sizeof(void*)*4, v_color_659_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
default: 
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_RBNode_ins___redArg(v_cmp_653_, v_rchild_684_, v_x_655_, v_x_656_);
if (lean_obj_tag(v___x_768_) == 1)
{
uint8_t v_color_769_; lean_object* v_lchild_770_; lean_object* v_key_771_; lean_object* v_val_772_; lean_object* v_rchild_773_; lean_object* v_a_775_; lean_object* v_kx_776_; lean_object* v_vx_777_; lean_object* v_b_778_; lean_object* v_ky_779_; lean_object* v_vy_780_; lean_object* v_c_781_; lean_object* v_kz_782_; lean_object* v_vz_783_; lean_object* v_d_784_; 
v_color_769_ = lean_ctor_get_uint8(v___x_768_, sizeof(void*)*4);
v_lchild_770_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_lchild_770_);
v_key_771_ = lean_ctor_get(v___x_768_, 1);
lean_inc(v_key_771_);
v_val_772_ = lean_ctor_get(v___x_768_, 2);
lean_inc(v_val_772_);
v_rchild_773_ = lean_ctor_get(v___x_768_, 3);
lean_inc(v_rchild_773_);
if (v_color_769_ == 0)
{
if (lean_obj_tag(v_lchild_770_) == 1)
{
uint8_t v_color_790_; 
v_color_790_ = lean_ctor_get_uint8(v_lchild_770_, sizeof(void*)*4);
if (v_color_790_ == 0)
{
lean_object* v_lchild_791_; lean_object* v_key_792_; lean_object* v_val_793_; lean_object* v_rchild_794_; 
lean_dec_ref_known(v___x_768_, 4);
v_lchild_791_ = lean_ctor_get(v_lchild_770_, 0);
lean_inc(v_lchild_791_);
v_key_792_ = lean_ctor_get(v_lchild_770_, 1);
lean_inc(v_key_792_);
v_val_793_ = lean_ctor_get(v_lchild_770_, 2);
lean_inc(v_val_793_);
v_rchild_794_ = lean_ctor_get(v_lchild_770_, 3);
lean_inc(v_rchild_794_);
lean_dec_ref_known(v_lchild_770_, 4);
v_a_775_ = v_lchild_681_;
v_kx_776_ = v_key_682_;
v_vx_777_ = v_val_683_;
v_b_778_ = v_lchild_791_;
v_ky_779_ = v_key_792_;
v_vy_780_ = v_val_793_;
v_c_781_ = v_rchild_794_;
v_kz_782_ = v_key_771_;
v_vz_783_ = v_val_772_;
v_d_784_ = v_rchild_773_;
goto v___jp_774_;
}
else
{
if (lean_obj_tag(v_rchild_773_) == 1)
{
uint8_t v_color_795_; 
v_color_795_ = lean_ctor_get_uint8(v_rchild_773_, sizeof(void*)*4);
if (v_color_795_ == 0)
{
lean_object* v_lchild_796_; lean_object* v_key_797_; lean_object* v_val_798_; lean_object* v_rchild_799_; 
lean_dec_ref_known(v___x_768_, 4);
v_lchild_796_ = lean_ctor_get(v_rchild_773_, 0);
lean_inc(v_lchild_796_);
v_key_797_ = lean_ctor_get(v_rchild_773_, 1);
lean_inc(v_key_797_);
v_val_798_ = lean_ctor_get(v_rchild_773_, 2);
lean_inc(v_val_798_);
v_rchild_799_ = lean_ctor_get(v_rchild_773_, 3);
lean_inc(v_rchild_799_);
lean_dec_ref_known(v_rchild_773_, 4);
v_a_775_ = v_lchild_681_;
v_kx_776_ = v_key_682_;
v_vx_777_ = v_val_683_;
v_b_778_ = v_lchild_770_;
v_ky_779_ = v_key_771_;
v_vy_780_ = v_val_772_;
v_c_781_ = v_lchild_796_;
v_kz_782_ = v_key_797_;
v_vz_783_ = v_val_798_;
v_d_784_ = v_rchild_799_;
goto v___jp_774_;
}
else
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref_known(v_lchild_770_, 4);
lean_dec(v_val_772_);
lean_dec(v_key_771_);
lean_del_object(v___x_686_);
v_isSharedCheck_806_ = !lean_is_exclusive(v_rchild_773_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_807_ = lean_ctor_get(v_rchild_773_, 3);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_rchild_773_, 2);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_rchild_773_, 1);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_rchild_773_, 0);
lean_dec(v_unused_810_);
v___x_801_ = v_rchild_773_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_dec(v_rchild_773_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 3, v___x_768_);
lean_ctor_set(v___x_801_, 2, v_val_683_);
lean_ctor_set(v___x_801_, 1, v_key_682_);
lean_ctor_set(v___x_801_, 0, v_lchild_681_);
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_lchild_681_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v___x_768_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_ctor_set_uint8(v___x_804_, sizeof(void*)*4, v_color_659_);
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_rchild_773_);
lean_dec(v_val_772_);
lean_dec(v_key_771_);
lean_del_object(v___x_686_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_lchild_770_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_818_ = lean_ctor_get(v_lchild_770_, 3);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_lchild_770_, 2);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_lchild_770_, 1);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_lchild_770_, 0);
lean_dec(v_unused_821_);
v___x_812_ = v_lchild_770_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_lchild_770_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 3, v___x_768_);
lean_ctor_set(v___x_812_, 2, v_val_683_);
lean_ctor_set(v___x_812_, 1, v_key_682_);
lean_ctor_set(v___x_812_, 0, v_lchild_681_);
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_lchild_681_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v___x_768_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*4, v_color_659_);
return v___x_815_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_773_) == 1)
{
uint8_t v_color_822_; 
v_color_822_ = lean_ctor_get_uint8(v_rchild_773_, sizeof(void*)*4);
if (v_color_822_ == 0)
{
lean_object* v_lchild_823_; lean_object* v_key_824_; lean_object* v_val_825_; lean_object* v_rchild_826_; 
lean_dec_ref_known(v___x_768_, 4);
v_lchild_823_ = lean_ctor_get(v_rchild_773_, 0);
lean_inc(v_lchild_823_);
v_key_824_ = lean_ctor_get(v_rchild_773_, 1);
lean_inc(v_key_824_);
v_val_825_ = lean_ctor_get(v_rchild_773_, 2);
lean_inc(v_val_825_);
v_rchild_826_ = lean_ctor_get(v_rchild_773_, 3);
lean_inc(v_rchild_826_);
lean_dec_ref_known(v_rchild_773_, 4);
v_a_775_ = v_lchild_681_;
v_kx_776_ = v_key_682_;
v_vx_777_ = v_val_683_;
v_b_778_ = v_lchild_770_;
v_ky_779_ = v_key_771_;
v_vy_780_ = v_val_772_;
v_c_781_ = v_lchild_823_;
v_kz_782_ = v_key_824_;
v_vz_783_ = v_val_825_;
v_d_784_ = v_rchild_826_;
goto v___jp_774_;
}
else
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_val_772_);
lean_dec(v_key_771_);
lean_dec(v_lchild_770_);
lean_del_object(v___x_686_);
v_isSharedCheck_833_ = !lean_is_exclusive(v_rchild_773_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; 
v_unused_834_ = lean_ctor_get(v_rchild_773_, 3);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_rchild_773_, 2);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_rchild_773_, 1);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_rchild_773_, 0);
lean_dec(v_unused_837_);
v___x_828_ = v_rchild_773_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_rchild_773_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 3, v___x_768_);
lean_ctor_set(v___x_828_, 2, v_val_683_);
lean_ctor_set(v___x_828_, 1, v_key_682_);
lean_ctor_set(v___x_828_, 0, v_lchild_681_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_lchild_681_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v___x_768_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_ctor_set_uint8(v___x_831_, sizeof(void*)*4, v_color_659_);
return v___x_831_;
}
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v_rchild_773_);
lean_dec(v_val_772_);
lean_dec(v_key_771_);
lean_dec(v_lchild_770_);
lean_del_object(v___x_686_);
v___x_838_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_838_, 0, v_lchild_681_);
lean_ctor_set(v___x_838_, 1, v_key_682_);
lean_ctor_set(v___x_838_, 2, v_val_683_);
lean_ctor_set(v___x_838_, 3, v___x_768_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*4, v_color_659_);
return v___x_838_;
}
}
}
else
{
lean_object* v___x_839_; 
lean_dec(v_rchild_773_);
lean_dec(v_val_772_);
lean_dec(v_key_771_);
lean_dec(v_lchild_770_);
lean_del_object(v___x_686_);
v___x_839_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_839_, 0, v_lchild_681_);
lean_ctor_set(v___x_839_, 1, v_key_682_);
lean_ctor_set(v___x_839_, 2, v_val_683_);
lean_ctor_set(v___x_839_, 3, v___x_768_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*4, v_color_659_);
return v___x_839_;
}
v___jp_774_:
{
lean_object* v___x_786_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v_b_778_);
lean_ctor_set(v___x_686_, 2, v_vx_777_);
lean_ctor_set(v___x_686_, 1, v_kx_776_);
lean_ctor_set(v___x_686_, 0, v_a_775_);
v___x_786_ = v___x_686_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_775_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_kx_776_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_vx_777_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_b_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_789_, sizeof(void*)*4, v_color_659_);
v___x_786_ = v_reuseFailAlloc_789_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_787_, 0, v_c_781_);
lean_ctor_set(v___x_787_, 1, v_kz_782_);
lean_ctor_set(v___x_787_, 2, v_vz_783_);
lean_ctor_set(v___x_787_, 3, v_d_784_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*4, v_color_659_);
v___x_788_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v_ky_779_);
lean_ctor_set(v___x_788_, 2, v_vy_780_);
lean_ctor_set(v___x_788_, 3, v___x_787_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*4, v_color_769_);
return v___x_788_;
}
}
}
else
{
lean_object* v___x_841_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 3, v___x_768_);
v___x_841_ = v___x_686_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_lchild_681_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_key_682_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_val_683_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v___x_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*4, v_color_659_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object* v_00_u03b1_844_, lean_object* v_00_u03b2_845_, lean_object* v_cmp_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_RBNode_ins___redArg(v_cmp_846_, v_x_847_, v_x_848_, v_x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object* v_x_851_){
_start:
{
if (lean_obj_tag(v_x_851_) == 1)
{
lean_object* v_lchild_852_; lean_object* v_key_853_; lean_object* v_val_854_; lean_object* v_rchild_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_863_; 
v_lchild_852_ = lean_ctor_get(v_x_851_, 0);
v_key_853_ = lean_ctor_get(v_x_851_, 1);
v_val_854_ = lean_ctor_get(v_x_851_, 2);
v_rchild_855_ = lean_ctor_get(v_x_851_, 3);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_851_);
if (v_isSharedCheck_863_ == 0)
{
v___x_857_ = v_x_851_;
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_rchild_855_);
lean_inc(v_val_854_);
lean_inc(v_key_853_);
lean_inc(v_lchild_852_);
lean_dec(v_x_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_863_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
uint8_t v___x_859_; lean_object* v___x_861_; 
v___x_859_ = 1;
if (v_isShared_858_ == 0)
{
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_lchild_852_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_key_853_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_val_854_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_rchild_855_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*4, v___x_859_);
return v___x_861_;
}
}
}
else
{
return v_x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_RBNode_setBlack___redArg(v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object* v_cmp_868_, lean_object* v_t_869_, lean_object* v_k_870_, lean_object* v_v_871_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_RBNode_isRed___redArg(v_t_869_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_RBNode_ins___redArg(v_cmp_868_, v_t_869_, v_k_870_, v_v_871_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = l_Lean_RBNode_ins___redArg(v_cmp_868_, v_t_869_, v_k_870_, v_v_871_);
v___x_875_ = l_Lean_RBNode_setBlack___redArg(v___x_874_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object* v_00_u03b1_876_, lean_object* v_00_u03b2_877_, lean_object* v_cmp_878_, lean_object* v_t_879_, lean_object* v_k_880_, lean_object* v_v_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_RBNode_insert___redArg(v_cmp_878_, v_t_879_, v_k_880_, v_v_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 1)
{
lean_object* v_lchild_884_; lean_object* v_key_885_; lean_object* v_val_886_; lean_object* v_rchild_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
v_lchild_884_ = lean_ctor_get(v_x_883_, 0);
v_key_885_ = lean_ctor_get(v_x_883_, 1);
v_val_886_ = lean_ctor_get(v_x_883_, 2);
v_rchild_887_ = lean_ctor_get(v_x_883_, 3);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_883_);
if (v_isSharedCheck_895_ == 0)
{
v___x_889_ = v_x_883_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_rchild_887_);
lean_inc(v_val_886_);
lean_inc(v_key_885_);
lean_inc(v_lchild_884_);
lean_dec(v_x_883_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; lean_object* v___x_893_; 
v___x_891_ = 0;
if (v_isShared_890_ == 0)
{
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_lchild_884_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_key_885_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_val_886_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_rchild_887_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*4, v___x_891_);
return v___x_893_;
}
}
}
else
{
return v_x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_RBNode_setRed___redArg(v_x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_a_905_; lean_object* v_kx_906_; lean_object* v_vx_907_; lean_object* v_b_908_; lean_object* v_a_912_; lean_object* v_kx_913_; lean_object* v_vx_914_; lean_object* v_b_915_; lean_object* v_ky_916_; lean_object* v_vy_917_; lean_object* v_c_918_; lean_object* v_kz_919_; lean_object* v_vz_920_; lean_object* v_d_921_; lean_object* v_l_928_; lean_object* v_k_929_; lean_object* v_v_930_; lean_object* v_a_931_; lean_object* v_ky_932_; lean_object* v_vy_933_; lean_object* v_b_934_; lean_object* v___y_953_; lean_object* v___y_954_; uint8_t v___y_955_; uint8_t v___y_956_; lean_object* v___y_957_; lean_object* v_a_958_; lean_object* v_kx_959_; lean_object* v_vx_960_; lean_object* v_b_961_; lean_object* v_ky_962_; lean_object* v_vy_963_; lean_object* v_c_964_; lean_object* v_kz_965_; lean_object* v_vz_966_; lean_object* v_d_967_; lean_object* v___y_973_; lean_object* v___y_974_; uint8_t v___y_975_; uint8_t v___y_976_; lean_object* v___y_977_; lean_object* v_a_978_; lean_object* v_kx_979_; lean_object* v_vx_980_; lean_object* v_b_981_; lean_object* v_l_985_; lean_object* v_k_986_; lean_object* v_v_987_; lean_object* v_a_988_; lean_object* v_ky_989_; lean_object* v_vy_990_; lean_object* v_b_991_; lean_object* v_kz_992_; lean_object* v_vz_993_; lean_object* v_c_994_; lean_object* v_l_1026_; lean_object* v_k_1027_; lean_object* v_v_1028_; lean_object* v_r_1029_; 
if (lean_obj_tag(v_x_900_) == 1)
{
uint8_t v_color_1032_; 
v_color_1032_ = lean_ctor_get_uint8(v_x_900_, sizeof(void*)*4);
if (v_color_1032_ == 0)
{
lean_object* v_lchild_1033_; lean_object* v_key_1034_; lean_object* v_val_1035_; lean_object* v_rchild_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1045_; 
v_lchild_1033_ = lean_ctor_get(v_x_900_, 0);
v_key_1034_ = lean_ctor_get(v_x_900_, 1);
v_val_1035_ = lean_ctor_get(v_x_900_, 2);
v_rchild_1036_ = lean_ctor_get(v_x_900_, 3);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_900_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1038_ = v_x_900_;
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_rchild_1036_);
lean_inc(v_val_1035_);
lean_inc(v_key_1034_);
lean_inc(v_lchild_1033_);
lean_dec(v_x_900_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1045_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
uint8_t v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = 1;
if (v_isShared_1039_ == 0)
{
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_lchild_1033_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_key_1034_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_val_1035_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v_rchild_1036_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*4, v___x_1040_);
v___x_1043_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_x_901_);
lean_ctor_set(v___x_1043_, 2, v_x_902_);
lean_ctor_set(v___x_1043_, 3, v_x_903_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*4, v_color_1032_);
return v___x_1043_;
}
}
}
else
{
if (lean_obj_tag(v_x_903_) == 1)
{
uint8_t v_color_1046_; 
v_color_1046_ = lean_ctor_get_uint8(v_x_903_, sizeof(void*)*4);
if (v_color_1046_ == 0)
{
lean_object* v_lchild_1047_; 
v_lchild_1047_ = lean_ctor_get(v_x_903_, 0);
if (lean_obj_tag(v_lchild_1047_) == 1)
{
uint8_t v_color_1048_; 
v_color_1048_ = lean_ctor_get_uint8(v_lchild_1047_, sizeof(void*)*4);
if (v_color_1048_ == 1)
{
lean_object* v_key_1049_; lean_object* v_val_1050_; lean_object* v_rchild_1051_; lean_object* v_lchild_1052_; lean_object* v_key_1053_; lean_object* v_val_1054_; lean_object* v_rchild_1055_; 
lean_inc_ref(v_lchild_1047_);
v_key_1049_ = lean_ctor_get(v_x_903_, 1);
lean_inc(v_key_1049_);
v_val_1050_ = lean_ctor_get(v_x_903_, 2);
lean_inc(v_val_1050_);
v_rchild_1051_ = lean_ctor_get(v_x_903_, 3);
lean_inc(v_rchild_1051_);
lean_dec_ref_known(v_x_903_, 4);
v_lchild_1052_ = lean_ctor_get(v_lchild_1047_, 0);
lean_inc(v_lchild_1052_);
v_key_1053_ = lean_ctor_get(v_lchild_1047_, 1);
lean_inc(v_key_1053_);
v_val_1054_ = lean_ctor_get(v_lchild_1047_, 2);
lean_inc(v_val_1054_);
v_rchild_1055_ = lean_ctor_get(v_lchild_1047_, 3);
lean_inc(v_rchild_1055_);
lean_dec_ref_known(v_lchild_1047_, 4);
v_l_985_ = v_x_900_;
v_k_986_ = v_x_901_;
v_v_987_ = v_x_902_;
v_a_988_ = v_lchild_1052_;
v_ky_989_ = v_key_1053_;
v_vy_990_ = v_val_1054_;
v_b_991_ = v_rchild_1055_;
v_kz_992_ = v_key_1049_;
v_vz_993_ = v_val_1050_;
v_c_994_ = v_rchild_1051_;
goto v___jp_984_;
}
else
{
v_l_1026_ = v_x_900_;
v_k_1027_ = v_x_901_;
v_v_1028_ = v_x_902_;
v_r_1029_ = v_x_903_;
goto v___jp_1025_;
}
}
else
{
v_l_1026_ = v_x_900_;
v_k_1027_ = v_x_901_;
v_v_1028_ = v_x_902_;
v_r_1029_ = v_x_903_;
goto v___jp_1025_;
}
}
else
{
lean_object* v_lchild_1056_; lean_object* v_key_1057_; lean_object* v_val_1058_; lean_object* v_rchild_1059_; 
v_lchild_1056_ = lean_ctor_get(v_x_903_, 0);
lean_inc(v_lchild_1056_);
v_key_1057_ = lean_ctor_get(v_x_903_, 1);
lean_inc(v_key_1057_);
v_val_1058_ = lean_ctor_get(v_x_903_, 2);
lean_inc(v_val_1058_);
v_rchild_1059_ = lean_ctor_get(v_x_903_, 3);
lean_inc(v_rchild_1059_);
lean_dec_ref_known(v_x_903_, 4);
v_l_928_ = v_x_900_;
v_k_929_ = v_x_901_;
v_v_930_ = v_x_902_;
v_a_931_ = v_lchild_1056_;
v_ky_932_ = v_key_1057_;
v_vy_933_ = v_val_1058_;
v_b_934_ = v_rchild_1059_;
goto v___jp_927_;
}
}
else
{
v_l_1026_ = v_x_900_;
v_k_1027_ = v_x_901_;
v_v_1028_ = v_x_902_;
v_r_1029_ = v_x_903_;
goto v___jp_1025_;
}
}
}
else
{
if (lean_obj_tag(v_x_903_) == 1)
{
uint8_t v_color_1060_; 
v_color_1060_ = lean_ctor_get_uint8(v_x_903_, sizeof(void*)*4);
if (v_color_1060_ == 0)
{
lean_object* v_lchild_1061_; 
v_lchild_1061_ = lean_ctor_get(v_x_903_, 0);
if (lean_obj_tag(v_lchild_1061_) == 1)
{
uint8_t v_color_1062_; 
v_color_1062_ = lean_ctor_get_uint8(v_lchild_1061_, sizeof(void*)*4);
if (v_color_1062_ == 1)
{
lean_object* v_key_1063_; lean_object* v_val_1064_; lean_object* v_rchild_1065_; lean_object* v_lchild_1066_; lean_object* v_key_1067_; lean_object* v_val_1068_; lean_object* v_rchild_1069_; 
lean_inc_ref(v_lchild_1061_);
v_key_1063_ = lean_ctor_get(v_x_903_, 1);
lean_inc(v_key_1063_);
v_val_1064_ = lean_ctor_get(v_x_903_, 2);
lean_inc(v_val_1064_);
v_rchild_1065_ = lean_ctor_get(v_x_903_, 3);
lean_inc(v_rchild_1065_);
lean_dec_ref_known(v_x_903_, 4);
v_lchild_1066_ = lean_ctor_get(v_lchild_1061_, 0);
lean_inc(v_lchild_1066_);
v_key_1067_ = lean_ctor_get(v_lchild_1061_, 1);
lean_inc(v_key_1067_);
v_val_1068_ = lean_ctor_get(v_lchild_1061_, 2);
lean_inc(v_val_1068_);
v_rchild_1069_ = lean_ctor_get(v_lchild_1061_, 3);
lean_inc(v_rchild_1069_);
lean_dec_ref_known(v_lchild_1061_, 4);
v_l_985_ = v_x_900_;
v_k_986_ = v_x_901_;
v_v_987_ = v_x_902_;
v_a_988_ = v_lchild_1066_;
v_ky_989_ = v_key_1067_;
v_vy_990_ = v_val_1068_;
v_b_991_ = v_rchild_1069_;
v_kz_992_ = v_key_1063_;
v_vz_993_ = v_val_1064_;
v_c_994_ = v_rchild_1065_;
goto v___jp_984_;
}
else
{
v_l_1026_ = v_x_900_;
v_k_1027_ = v_x_901_;
v_v_1028_ = v_x_902_;
v_r_1029_ = v_x_903_;
goto v___jp_1025_;
}
}
else
{
v_l_1026_ = v_x_900_;
v_k_1027_ = v_x_901_;
v_v_1028_ = v_x_902_;
v_r_1029_ = v_x_903_;
goto v___jp_1025_;
}
}
else
{
lean_object* v_lchild_1070_; lean_object* v_key_1071_; lean_object* v_val_1072_; lean_object* v_rchild_1073_; 
v_lchild_1070_ = lean_ctor_get(v_x_903_, 0);
lean_inc(v_lchild_1070_);
v_key_1071_ = lean_ctor_get(v_x_903_, 1);
lean_inc(v_key_1071_);
v_val_1072_ = lean_ctor_get(v_x_903_, 2);
lean_inc(v_val_1072_);
v_rchild_1073_ = lean_ctor_get(v_x_903_, 3);
lean_inc(v_rchild_1073_);
lean_dec_ref_known(v_x_903_, 4);
v_l_928_ = v_x_900_;
v_k_929_ = v_x_901_;
v_v_930_ = v_x_902_;
v_a_931_ = v_lchild_1070_;
v_ky_932_ = v_key_1071_;
v_vy_933_ = v_val_1072_;
v_b_934_ = v_rchild_1073_;
goto v___jp_927_;
}
}
else
{
v_l_1026_ = v_x_900_;
v_k_1027_ = v_x_901_;
v_v_1028_ = v_x_902_;
v_r_1029_ = v_x_903_;
goto v___jp_1025_;
}
}
v___jp_904_:
{
uint8_t v___x_909_; lean_object* v___x_910_; 
v___x_909_ = 1;
v___x_910_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_910_, 0, v_a_905_);
lean_ctor_set(v___x_910_, 1, v_kx_906_);
lean_ctor_set(v___x_910_, 2, v_vx_907_);
lean_ctor_set(v___x_910_, 3, v_b_908_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*4, v___x_909_);
return v___x_910_;
}
v___jp_911_:
{
uint8_t v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_922_ = 0;
v___x_923_ = 1;
v___x_924_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_924_, 0, v_a_912_);
lean_ctor_set(v___x_924_, 1, v_kx_913_);
lean_ctor_set(v___x_924_, 2, v_vx_914_);
lean_ctor_set(v___x_924_, 3, v_b_915_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*4, v___x_923_);
v___x_925_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_925_, 0, v_c_918_);
lean_ctor_set(v___x_925_, 1, v_kz_919_);
lean_ctor_set(v___x_925_, 2, v_vz_920_);
lean_ctor_set(v___x_925_, 3, v_d_921_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*4, v___x_923_);
v___x_926_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v_ky_916_);
lean_ctor_set(v___x_926_, 2, v_vy_917_);
lean_ctor_set(v___x_926_, 3, v___x_925_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*4, v___x_922_);
return v___x_926_;
}
v___jp_927_:
{
uint8_t v___x_935_; lean_object* v___x_936_; 
v___x_935_ = 0;
lean_inc(v_b_934_);
lean_inc(v_vy_933_);
lean_inc(v_ky_932_);
lean_inc(v_a_931_);
v___x_936_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_936_, 0, v_a_931_);
lean_ctor_set(v___x_936_, 1, v_ky_932_);
lean_ctor_set(v___x_936_, 2, v_vy_933_);
lean_ctor_set(v___x_936_, 3, v_b_934_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*4, v___x_935_);
if (lean_obj_tag(v_a_931_) == 1)
{
uint8_t v_color_937_; 
v_color_937_ = lean_ctor_get_uint8(v_a_931_, sizeof(void*)*4);
if (v_color_937_ == 0)
{
lean_object* v_lchild_938_; lean_object* v_key_939_; lean_object* v_val_940_; lean_object* v_rchild_941_; 
lean_dec_ref_known(v___x_936_, 4);
v_lchild_938_ = lean_ctor_get(v_a_931_, 0);
lean_inc(v_lchild_938_);
v_key_939_ = lean_ctor_get(v_a_931_, 1);
lean_inc(v_key_939_);
v_val_940_ = lean_ctor_get(v_a_931_, 2);
lean_inc(v_val_940_);
v_rchild_941_ = lean_ctor_get(v_a_931_, 3);
lean_inc(v_rchild_941_);
lean_dec_ref_known(v_a_931_, 4);
v_a_912_ = v_l_928_;
v_kx_913_ = v_k_929_;
v_vx_914_ = v_v_930_;
v_b_915_ = v_lchild_938_;
v_ky_916_ = v_key_939_;
v_vy_917_ = v_val_940_;
v_c_918_ = v_rchild_941_;
v_kz_919_ = v_ky_932_;
v_vz_920_ = v_vy_933_;
v_d_921_ = v_b_934_;
goto v___jp_911_;
}
else
{
if (lean_obj_tag(v_b_934_) == 1)
{
uint8_t v_color_942_; 
v_color_942_ = lean_ctor_get_uint8(v_b_934_, sizeof(void*)*4);
if (v_color_942_ == 0)
{
lean_object* v_lchild_943_; lean_object* v_key_944_; lean_object* v_val_945_; lean_object* v_rchild_946_; 
lean_dec_ref_known(v___x_936_, 4);
v_lchild_943_ = lean_ctor_get(v_b_934_, 0);
lean_inc(v_lchild_943_);
v_key_944_ = lean_ctor_get(v_b_934_, 1);
lean_inc(v_key_944_);
v_val_945_ = lean_ctor_get(v_b_934_, 2);
lean_inc(v_val_945_);
v_rchild_946_ = lean_ctor_get(v_b_934_, 3);
lean_inc(v_rchild_946_);
lean_dec_ref_known(v_b_934_, 4);
v_a_912_ = v_l_928_;
v_kx_913_ = v_k_929_;
v_vx_914_ = v_v_930_;
v_b_915_ = v_a_931_;
v_ky_916_ = v_ky_932_;
v_vy_917_ = v_vy_933_;
v_c_918_ = v_lchild_943_;
v_kz_919_ = v_key_944_;
v_vz_920_ = v_val_945_;
v_d_921_ = v_rchild_946_;
goto v___jp_911_;
}
else
{
lean_dec_ref_known(v_b_934_, 4);
lean_dec_ref_known(v_a_931_, 4);
lean_dec(v_vy_933_);
lean_dec(v_ky_932_);
v_a_905_ = v_l_928_;
v_kx_906_ = v_k_929_;
v_vx_907_ = v_v_930_;
v_b_908_ = v___x_936_;
goto v___jp_904_;
}
}
else
{
lean_dec_ref_known(v_a_931_, 4);
lean_dec(v_b_934_);
lean_dec(v_vy_933_);
lean_dec(v_ky_932_);
v_a_905_ = v_l_928_;
v_kx_906_ = v_k_929_;
v_vx_907_ = v_v_930_;
v_b_908_ = v___x_936_;
goto v___jp_904_;
}
}
}
else
{
if (lean_obj_tag(v_b_934_) == 1)
{
uint8_t v_color_947_; 
v_color_947_ = lean_ctor_get_uint8(v_b_934_, sizeof(void*)*4);
if (v_color_947_ == 0)
{
lean_object* v_lchild_948_; lean_object* v_key_949_; lean_object* v_val_950_; lean_object* v_rchild_951_; 
lean_dec_ref_known(v___x_936_, 4);
v_lchild_948_ = lean_ctor_get(v_b_934_, 0);
lean_inc(v_lchild_948_);
v_key_949_ = lean_ctor_get(v_b_934_, 1);
lean_inc(v_key_949_);
v_val_950_ = lean_ctor_get(v_b_934_, 2);
lean_inc(v_val_950_);
v_rchild_951_ = lean_ctor_get(v_b_934_, 3);
lean_inc(v_rchild_951_);
lean_dec_ref_known(v_b_934_, 4);
v_a_912_ = v_l_928_;
v_kx_913_ = v_k_929_;
v_vx_914_ = v_v_930_;
v_b_915_ = v_a_931_;
v_ky_916_ = v_ky_932_;
v_vy_917_ = v_vy_933_;
v_c_918_ = v_lchild_948_;
v_kz_919_ = v_key_949_;
v_vz_920_ = v_val_950_;
v_d_921_ = v_rchild_951_;
goto v___jp_911_;
}
else
{
lean_dec_ref_known(v_b_934_, 4);
lean_dec(v_vy_933_);
lean_dec(v_ky_932_);
lean_dec(v_a_931_);
v_a_905_ = v_l_928_;
v_kx_906_ = v_k_929_;
v_vx_907_ = v_v_930_;
v_b_908_ = v___x_936_;
goto v___jp_904_;
}
}
else
{
lean_dec(v_b_934_);
lean_dec(v_vy_933_);
lean_dec(v_ky_932_);
lean_dec(v_a_931_);
v_a_905_ = v_l_928_;
v_kx_906_ = v_k_929_;
v_vx_907_ = v_v_930_;
v_b_908_ = v___x_936_;
goto v___jp_904_;
}
}
}
v___jp_952_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_968_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_968_, 0, v_a_958_);
lean_ctor_set(v___x_968_, 1, v_kx_959_);
lean_ctor_set(v___x_968_, 2, v_vx_960_);
lean_ctor_set(v___x_968_, 3, v_b_961_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*4, v___y_955_);
v___x_969_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_969_, 0, v_c_964_);
lean_ctor_set(v___x_969_, 1, v_kz_965_);
lean_ctor_set(v___x_969_, 2, v_vz_966_);
lean_ctor_set(v___x_969_, 3, v_d_967_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*4, v___y_955_);
v___x_970_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v_ky_962_);
lean_ctor_set(v___x_970_, 2, v_vy_963_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*4, v___y_956_);
v___x_971_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_971_, 0, v___y_953_);
lean_ctor_set(v___x_971_, 1, v___y_954_);
lean_ctor_set(v___x_971_, 2, v___y_957_);
lean_ctor_set(v___x_971_, 3, v___x_970_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*4, v___y_956_);
return v___x_971_;
}
v___jp_972_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_982_, 0, v_a_978_);
lean_ctor_set(v___x_982_, 1, v_kx_979_);
lean_ctor_set(v___x_982_, 2, v_vx_980_);
lean_ctor_set(v___x_982_, 3, v_b_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*4, v___y_975_);
v___x_983_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_983_, 0, v___y_973_);
lean_ctor_set(v___x_983_, 1, v___y_974_);
lean_ctor_set(v___x_983_, 2, v___y_977_);
lean_ctor_set(v___x_983_, 3, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*4, v___y_976_);
return v___x_983_;
}
v___jp_984_:
{
uint8_t v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_995_ = 0;
v___x_996_ = 1;
v___x_997_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_997_, 0, v_l_985_);
lean_ctor_set(v___x_997_, 1, v_k_986_);
lean_ctor_set(v___x_997_, 2, v_v_987_);
lean_ctor_set(v___x_997_, 3, v_a_988_);
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*4, v___x_996_);
v___x_998_ = l_Lean_RBNode_setRed___redArg(v_c_994_);
if (lean_obj_tag(v___x_998_) == 1)
{
uint8_t v_color_999_; 
v_color_999_ = lean_ctor_get_uint8(v___x_998_, sizeof(void*)*4);
if (v_color_999_ == 0)
{
lean_object* v_lchild_1000_; 
v_lchild_1000_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_lchild_1000_);
if (lean_obj_tag(v_lchild_1000_) == 1)
{
uint8_t v_color_1001_; 
v_color_1001_ = lean_ctor_get_uint8(v_lchild_1000_, sizeof(void*)*4);
if (v_color_1001_ == 0)
{
lean_object* v_key_1002_; lean_object* v_val_1003_; lean_object* v_rchild_1004_; lean_object* v_lchild_1005_; lean_object* v_key_1006_; lean_object* v_val_1007_; lean_object* v_rchild_1008_; 
v_key_1002_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_key_1002_);
v_val_1003_ = lean_ctor_get(v___x_998_, 2);
lean_inc(v_val_1003_);
v_rchild_1004_ = lean_ctor_get(v___x_998_, 3);
lean_inc(v_rchild_1004_);
lean_dec_ref_known(v___x_998_, 4);
v_lchild_1005_ = lean_ctor_get(v_lchild_1000_, 0);
lean_inc(v_lchild_1005_);
v_key_1006_ = lean_ctor_get(v_lchild_1000_, 1);
lean_inc(v_key_1006_);
v_val_1007_ = lean_ctor_get(v_lchild_1000_, 2);
lean_inc(v_val_1007_);
v_rchild_1008_ = lean_ctor_get(v_lchild_1000_, 3);
lean_inc(v_rchild_1008_);
lean_dec_ref_known(v_lchild_1000_, 4);
v___y_953_ = v___x_997_;
v___y_954_ = v_ky_989_;
v___y_955_ = v___x_996_;
v___y_956_ = v___x_995_;
v___y_957_ = v_vy_990_;
v_a_958_ = v_b_991_;
v_kx_959_ = v_kz_992_;
v_vx_960_ = v_vz_993_;
v_b_961_ = v_lchild_1005_;
v_ky_962_ = v_key_1006_;
v_vy_963_ = v_val_1007_;
v_c_964_ = v_rchild_1008_;
v_kz_965_ = v_key_1002_;
v_vz_966_ = v_val_1003_;
v_d_967_ = v_rchild_1004_;
goto v___jp_952_;
}
else
{
lean_object* v_rchild_1009_; 
v_rchild_1009_ = lean_ctor_get(v___x_998_, 3);
lean_inc(v_rchild_1009_);
if (lean_obj_tag(v_rchild_1009_) == 1)
{
uint8_t v_color_1010_; 
v_color_1010_ = lean_ctor_get_uint8(v_rchild_1009_, sizeof(void*)*4);
if (v_color_1010_ == 0)
{
lean_object* v_key_1011_; lean_object* v_val_1012_; lean_object* v_lchild_1013_; lean_object* v_key_1014_; lean_object* v_val_1015_; lean_object* v_rchild_1016_; 
v_key_1011_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_key_1011_);
v_val_1012_ = lean_ctor_get(v___x_998_, 2);
lean_inc(v_val_1012_);
lean_dec_ref_known(v___x_998_, 4);
v_lchild_1013_ = lean_ctor_get(v_rchild_1009_, 0);
lean_inc(v_lchild_1013_);
v_key_1014_ = lean_ctor_get(v_rchild_1009_, 1);
lean_inc(v_key_1014_);
v_val_1015_ = lean_ctor_get(v_rchild_1009_, 2);
lean_inc(v_val_1015_);
v_rchild_1016_ = lean_ctor_get(v_rchild_1009_, 3);
lean_inc(v_rchild_1016_);
lean_dec_ref_known(v_rchild_1009_, 4);
v___y_953_ = v___x_997_;
v___y_954_ = v_ky_989_;
v___y_955_ = v___x_996_;
v___y_956_ = v___x_995_;
v___y_957_ = v_vy_990_;
v_a_958_ = v_b_991_;
v_kx_959_ = v_kz_992_;
v_vx_960_ = v_vz_993_;
v_b_961_ = v_lchild_1000_;
v_ky_962_ = v_key_1011_;
v_vy_963_ = v_val_1012_;
v_c_964_ = v_lchild_1013_;
v_kz_965_ = v_key_1014_;
v_vz_966_ = v_val_1015_;
v_d_967_ = v_rchild_1016_;
goto v___jp_952_;
}
else
{
lean_dec_ref_known(v_rchild_1009_, 4);
lean_dec_ref_known(v_lchild_1000_, 4);
v___y_973_ = v___x_997_;
v___y_974_ = v_ky_989_;
v___y_975_ = v___x_996_;
v___y_976_ = v___x_995_;
v___y_977_ = v_vy_990_;
v_a_978_ = v_b_991_;
v_kx_979_ = v_kz_992_;
v_vx_980_ = v_vz_993_;
v_b_981_ = v___x_998_;
goto v___jp_972_;
}
}
else
{
lean_dec(v_rchild_1009_);
lean_dec_ref_known(v_lchild_1000_, 4);
v___y_973_ = v___x_997_;
v___y_974_ = v_ky_989_;
v___y_975_ = v___x_996_;
v___y_976_ = v___x_995_;
v___y_977_ = v_vy_990_;
v_a_978_ = v_b_991_;
v_kx_979_ = v_kz_992_;
v_vx_980_ = v_vz_993_;
v_b_981_ = v___x_998_;
goto v___jp_972_;
}
}
}
else
{
lean_object* v_rchild_1017_; 
v_rchild_1017_ = lean_ctor_get(v___x_998_, 3);
lean_inc(v_rchild_1017_);
if (lean_obj_tag(v_rchild_1017_) == 1)
{
uint8_t v_color_1018_; 
v_color_1018_ = lean_ctor_get_uint8(v_rchild_1017_, sizeof(void*)*4);
if (v_color_1018_ == 0)
{
lean_object* v_key_1019_; lean_object* v_val_1020_; lean_object* v_lchild_1021_; lean_object* v_key_1022_; lean_object* v_val_1023_; lean_object* v_rchild_1024_; 
v_key_1019_ = lean_ctor_get(v___x_998_, 1);
lean_inc(v_key_1019_);
v_val_1020_ = lean_ctor_get(v___x_998_, 2);
lean_inc(v_val_1020_);
lean_dec_ref_known(v___x_998_, 4);
v_lchild_1021_ = lean_ctor_get(v_rchild_1017_, 0);
lean_inc(v_lchild_1021_);
v_key_1022_ = lean_ctor_get(v_rchild_1017_, 1);
lean_inc(v_key_1022_);
v_val_1023_ = lean_ctor_get(v_rchild_1017_, 2);
lean_inc(v_val_1023_);
v_rchild_1024_ = lean_ctor_get(v_rchild_1017_, 3);
lean_inc(v_rchild_1024_);
lean_dec_ref_known(v_rchild_1017_, 4);
v___y_953_ = v___x_997_;
v___y_954_ = v_ky_989_;
v___y_955_ = v___x_996_;
v___y_956_ = v___x_995_;
v___y_957_ = v_vy_990_;
v_a_958_ = v_b_991_;
v_kx_959_ = v_kz_992_;
v_vx_960_ = v_vz_993_;
v_b_961_ = v_lchild_1000_;
v_ky_962_ = v_key_1019_;
v_vy_963_ = v_val_1020_;
v_c_964_ = v_lchild_1021_;
v_kz_965_ = v_key_1022_;
v_vz_966_ = v_val_1023_;
v_d_967_ = v_rchild_1024_;
goto v___jp_952_;
}
else
{
lean_dec_ref_known(v_rchild_1017_, 4);
lean_dec(v_lchild_1000_);
v___y_973_ = v___x_997_;
v___y_974_ = v_ky_989_;
v___y_975_ = v___x_996_;
v___y_976_ = v___x_995_;
v___y_977_ = v_vy_990_;
v_a_978_ = v_b_991_;
v_kx_979_ = v_kz_992_;
v_vx_980_ = v_vz_993_;
v_b_981_ = v___x_998_;
goto v___jp_972_;
}
}
else
{
lean_dec(v_rchild_1017_);
lean_dec(v_lchild_1000_);
v___y_973_ = v___x_997_;
v___y_974_ = v_ky_989_;
v___y_975_ = v___x_996_;
v___y_976_ = v___x_995_;
v___y_977_ = v_vy_990_;
v_a_978_ = v_b_991_;
v_kx_979_ = v_kz_992_;
v_vx_980_ = v_vz_993_;
v_b_981_ = v___x_998_;
goto v___jp_972_;
}
}
}
else
{
v___y_973_ = v___x_997_;
v___y_974_ = v_ky_989_;
v___y_975_ = v___x_996_;
v___y_976_ = v___x_995_;
v___y_977_ = v_vy_990_;
v_a_978_ = v_b_991_;
v_kx_979_ = v_kz_992_;
v_vx_980_ = v_vz_993_;
v_b_981_ = v___x_998_;
goto v___jp_972_;
}
}
else
{
v___y_973_ = v___x_997_;
v___y_974_ = v_ky_989_;
v___y_975_ = v___x_996_;
v___y_976_ = v___x_995_;
v___y_977_ = v_vy_990_;
v_a_978_ = v_b_991_;
v_kx_979_ = v_kz_992_;
v_vx_980_ = v_vz_993_;
v_b_981_ = v___x_998_;
goto v___jp_972_;
}
}
v___jp_1025_:
{
uint8_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = 0;
v___x_1031_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1031_, 0, v_l_1026_);
lean_ctor_set(v___x_1031_, 1, v_k_1027_);
lean_ctor_set(v___x_1031_, 2, v_v_1028_);
lean_ctor_set(v___x_1031_, 3, v_r_1029_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*4, v___x_1030_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object* v_00_u03b1_1074_, lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_RBNode_balLeft___redArg(v_x_1076_, v_x_1077_, v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object* v_l_1081_, lean_object* v_k_1082_, lean_object* v_v_1083_, lean_object* v_r_1084_){
_start:
{
uint8_t v___y_1089_; lean_object* v_a_1090_; lean_object* v_kx_1091_; lean_object* v_vx_1092_; lean_object* v_b_1093_; lean_object* v_ky_1094_; lean_object* v_vy_1095_; lean_object* v_c_1096_; lean_object* v_kz_1097_; lean_object* v_vz_1098_; lean_object* v_d_1099_; lean_object* v___y_1105_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1114_; uint8_t v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v_a_1119_; lean_object* v_kx_1120_; lean_object* v_vx_1121_; lean_object* v_b_1122_; lean_object* v_ky_1123_; lean_object* v_vy_1124_; lean_object* v_c_1125_; lean_object* v_kz_1126_; lean_object* v_vz_1127_; lean_object* v_d_1128_; uint8_t v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v_a_1138_; lean_object* v_kx_1139_; lean_object* v_vx_1140_; lean_object* v_b_1141_; 
if (lean_obj_tag(v_r_1084_) == 1)
{
uint8_t v_color_1242_; 
v_color_1242_ = lean_ctor_get_uint8(v_r_1084_, sizeof(void*)*4);
if (v_color_1242_ == 0)
{
lean_object* v_lchild_1243_; lean_object* v_key_1244_; lean_object* v_val_1245_; lean_object* v_rchild_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1255_; 
v_lchild_1243_ = lean_ctor_get(v_r_1084_, 0);
v_key_1244_ = lean_ctor_get(v_r_1084_, 1);
v_val_1245_ = lean_ctor_get(v_r_1084_, 2);
v_rchild_1246_ = lean_ctor_get(v_r_1084_, 3);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_r_1084_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1248_ = v_r_1084_;
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_rchild_1246_);
lean_inc(v_val_1245_);
lean_inc(v_key_1244_);
lean_inc(v_lchild_1243_);
lean_dec(v_r_1084_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1255_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
uint8_t v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = 1;
if (v_isShared_1249_ == 0)
{
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_lchild_1243_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_key_1244_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_val_1245_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_rchild_1246_);
v___x_1252_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; 
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*4, v___x_1250_);
v___x_1253_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1253_, 0, v_l_1081_);
lean_ctor_set(v___x_1253_, 1, v_k_1082_);
lean_ctor_set(v___x_1253_, 2, v_v_1083_);
lean_ctor_set(v___x_1253_, 3, v___x_1252_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*4, v_color_1242_);
return v___x_1253_;
}
}
}
else
{
goto v___jp_1143_;
}
}
else
{
goto v___jp_1143_;
}
v___jp_1085_:
{
uint8_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = 0;
v___x_1087_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1087_, 0, v_l_1081_);
lean_ctor_set(v___x_1087_, 1, v_k_1082_);
lean_ctor_set(v___x_1087_, 2, v_v_1083_);
lean_ctor_set(v___x_1087_, 3, v_r_1084_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*4, v___x_1086_);
return v___x_1087_;
}
v___jp_1088_:
{
uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = 0;
v___x_1101_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1101_, 0, v_a_1090_);
lean_ctor_set(v___x_1101_, 1, v_kx_1091_);
lean_ctor_set(v___x_1101_, 2, v_vx_1092_);
lean_ctor_set(v___x_1101_, 3, v_b_1093_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*4, v___y_1089_);
v___x_1102_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1102_, 0, v_c_1096_);
lean_ctor_set(v___x_1102_, 1, v_kz_1097_);
lean_ctor_set(v___x_1102_, 2, v_vz_1098_);
lean_ctor_set(v___x_1102_, 3, v_d_1099_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*4, v___y_1089_);
v___x_1103_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v_ky_1094_);
lean_ctor_set(v___x_1103_, 2, v_vy_1095_);
lean_ctor_set(v___x_1103_, 3, v___x_1102_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*4, v___x_1100_);
return v___x_1103_;
}
v___jp_1104_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1111_, 0, v___y_1109_);
lean_ctor_set(v___x_1111_, 1, v_k_1082_);
lean_ctor_set(v___x_1111_, 2, v_v_1083_);
lean_ctor_set(v___x_1111_, 3, v_r_1084_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*4, v___y_1107_);
v___x_1112_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1112_, 0, v___y_1110_);
lean_ctor_set(v___x_1112_, 1, v___y_1108_);
lean_ctor_set(v___x_1112_, 2, v___y_1105_);
lean_ctor_set(v___x_1112_, 3, v___x_1111_);
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*4, v___y_1106_);
return v___x_1112_;
}
v___jp_1113_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1129_, 0, v_a_1119_);
lean_ctor_set(v___x_1129_, 1, v_kx_1120_);
lean_ctor_set(v___x_1129_, 2, v_vx_1121_);
lean_ctor_set(v___x_1129_, 3, v_b_1122_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*4, v___y_1116_);
v___x_1130_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1130_, 0, v_c_1125_);
lean_ctor_set(v___x_1130_, 1, v_kz_1126_);
lean_ctor_set(v___x_1130_, 2, v_vz_1127_);
lean_ctor_set(v___x_1130_, 3, v_d_1128_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*4, v___y_1116_);
v___x_1131_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v_ky_1123_);
lean_ctor_set(v___x_1131_, 2, v_vy_1124_);
lean_ctor_set(v___x_1131_, 3, v___x_1130_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4, v___y_1115_);
v___y_1105_ = v___y_1114_;
v___y_1106_ = v___y_1115_;
v___y_1107_ = v___y_1116_;
v___y_1108_ = v___y_1117_;
v___y_1109_ = v___y_1118_;
v___y_1110_ = v___x_1131_;
goto v___jp_1104_;
}
v___jp_1132_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1142_, 0, v_a_1138_);
lean_ctor_set(v___x_1142_, 1, v_kx_1139_);
lean_ctor_set(v___x_1142_, 2, v_vx_1140_);
lean_ctor_set(v___x_1142_, 3, v_b_1141_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*4, v___y_1135_);
v___y_1105_ = v___y_1134_;
v___y_1106_ = v___y_1133_;
v___y_1107_ = v___y_1135_;
v___y_1108_ = v___y_1136_;
v___y_1109_ = v___y_1137_;
v___y_1110_ = v___x_1142_;
goto v___jp_1104_;
}
v___jp_1143_:
{
if (lean_obj_tag(v_l_1081_) == 1)
{
uint8_t v_color_1144_; 
v_color_1144_ = lean_ctor_get_uint8(v_l_1081_, sizeof(void*)*4);
if (v_color_1144_ == 0)
{
lean_object* v_rchild_1145_; 
v_rchild_1145_ = lean_ctor_get(v_l_1081_, 3);
if (lean_obj_tag(v_rchild_1145_) == 1)
{
uint8_t v_color_1146_; 
v_color_1146_ = lean_ctor_get_uint8(v_rchild_1145_, sizeof(void*)*4);
if (v_color_1146_ == 1)
{
lean_object* v_lchild_1147_; lean_object* v_key_1148_; lean_object* v_val_1149_; lean_object* v_lchild_1150_; lean_object* v_key_1151_; lean_object* v_val_1152_; lean_object* v_rchild_1153_; lean_object* v___x_1154_; 
lean_inc_ref(v_rchild_1145_);
v_lchild_1147_ = lean_ctor_get(v_l_1081_, 0);
lean_inc(v_lchild_1147_);
v_key_1148_ = lean_ctor_get(v_l_1081_, 1);
lean_inc(v_key_1148_);
v_val_1149_ = lean_ctor_get(v_l_1081_, 2);
lean_inc(v_val_1149_);
lean_dec_ref_known(v_l_1081_, 4);
v_lchild_1150_ = lean_ctor_get(v_rchild_1145_, 0);
lean_inc(v_lchild_1150_);
v_key_1151_ = lean_ctor_get(v_rchild_1145_, 1);
lean_inc(v_key_1151_);
v_val_1152_ = lean_ctor_get(v_rchild_1145_, 2);
lean_inc(v_val_1152_);
v_rchild_1153_ = lean_ctor_get(v_rchild_1145_, 3);
lean_inc(v_rchild_1153_);
lean_dec_ref_known(v_rchild_1145_, 4);
v___x_1154_ = l_Lean_RBNode_setRed___redArg(v_lchild_1147_);
if (lean_obj_tag(v___x_1154_) == 1)
{
uint8_t v_color_1155_; 
v_color_1155_ = lean_ctor_get_uint8(v___x_1154_, sizeof(void*)*4);
if (v_color_1155_ == 0)
{
lean_object* v_lchild_1156_; 
v_lchild_1156_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_lchild_1156_);
if (lean_obj_tag(v_lchild_1156_) == 1)
{
uint8_t v_color_1157_; 
v_color_1157_ = lean_ctor_get_uint8(v_lchild_1156_, sizeof(void*)*4);
if (v_color_1157_ == 0)
{
lean_object* v_key_1158_; lean_object* v_val_1159_; lean_object* v_rchild_1160_; lean_object* v_lchild_1161_; lean_object* v_key_1162_; lean_object* v_val_1163_; lean_object* v_rchild_1164_; 
v_key_1158_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_key_1158_);
v_val_1159_ = lean_ctor_get(v___x_1154_, 2);
lean_inc(v_val_1159_);
v_rchild_1160_ = lean_ctor_get(v___x_1154_, 3);
lean_inc(v_rchild_1160_);
lean_dec_ref_known(v___x_1154_, 4);
v_lchild_1161_ = lean_ctor_get(v_lchild_1156_, 0);
lean_inc(v_lchild_1161_);
v_key_1162_ = lean_ctor_get(v_lchild_1156_, 1);
lean_inc(v_key_1162_);
v_val_1163_ = lean_ctor_get(v_lchild_1156_, 2);
lean_inc(v_val_1163_);
v_rchild_1164_ = lean_ctor_get(v_lchild_1156_, 3);
lean_inc(v_rchild_1164_);
lean_dec_ref_known(v_lchild_1156_, 4);
v___y_1114_ = v_val_1152_;
v___y_1115_ = v_color_1144_;
v___y_1116_ = v_color_1146_;
v___y_1117_ = v_key_1151_;
v___y_1118_ = v_rchild_1153_;
v_a_1119_ = v_lchild_1161_;
v_kx_1120_ = v_key_1162_;
v_vx_1121_ = v_val_1163_;
v_b_1122_ = v_rchild_1164_;
v_ky_1123_ = v_key_1158_;
v_vy_1124_ = v_val_1159_;
v_c_1125_ = v_rchild_1160_;
v_kz_1126_ = v_key_1148_;
v_vz_1127_ = v_val_1149_;
v_d_1128_ = v_lchild_1150_;
goto v___jp_1113_;
}
else
{
lean_object* v_rchild_1165_; 
v_rchild_1165_ = lean_ctor_get(v___x_1154_, 3);
lean_inc(v_rchild_1165_);
if (lean_obj_tag(v_rchild_1165_) == 1)
{
uint8_t v_color_1166_; 
v_color_1166_ = lean_ctor_get_uint8(v_rchild_1165_, sizeof(void*)*4);
if (v_color_1166_ == 0)
{
lean_object* v_key_1167_; lean_object* v_val_1168_; lean_object* v_lchild_1169_; lean_object* v_key_1170_; lean_object* v_val_1171_; lean_object* v_rchild_1172_; 
v_key_1167_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_key_1167_);
v_val_1168_ = lean_ctor_get(v___x_1154_, 2);
lean_inc(v_val_1168_);
lean_dec_ref_known(v___x_1154_, 4);
v_lchild_1169_ = lean_ctor_get(v_rchild_1165_, 0);
lean_inc(v_lchild_1169_);
v_key_1170_ = lean_ctor_get(v_rchild_1165_, 1);
lean_inc(v_key_1170_);
v_val_1171_ = lean_ctor_get(v_rchild_1165_, 2);
lean_inc(v_val_1171_);
v_rchild_1172_ = lean_ctor_get(v_rchild_1165_, 3);
lean_inc(v_rchild_1172_);
lean_dec_ref_known(v_rchild_1165_, 4);
v___y_1114_ = v_val_1152_;
v___y_1115_ = v_color_1144_;
v___y_1116_ = v_color_1146_;
v___y_1117_ = v_key_1151_;
v___y_1118_ = v_rchild_1153_;
v_a_1119_ = v_lchild_1156_;
v_kx_1120_ = v_key_1167_;
v_vx_1121_ = v_val_1168_;
v_b_1122_ = v_lchild_1169_;
v_ky_1123_ = v_key_1170_;
v_vy_1124_ = v_val_1171_;
v_c_1125_ = v_rchild_1172_;
v_kz_1126_ = v_key_1148_;
v_vz_1127_ = v_val_1149_;
v_d_1128_ = v_lchild_1150_;
goto v___jp_1113_;
}
else
{
lean_dec_ref_known(v_rchild_1165_, 4);
lean_dec_ref_known(v_lchild_1156_, 4);
v___y_1133_ = v_color_1144_;
v___y_1134_ = v_val_1152_;
v___y_1135_ = v_color_1146_;
v___y_1136_ = v_key_1151_;
v___y_1137_ = v_rchild_1153_;
v_a_1138_ = v___x_1154_;
v_kx_1139_ = v_key_1148_;
v_vx_1140_ = v_val_1149_;
v_b_1141_ = v_lchild_1150_;
goto v___jp_1132_;
}
}
else
{
lean_dec(v_rchild_1165_);
lean_dec_ref_known(v_lchild_1156_, 4);
v___y_1133_ = v_color_1144_;
v___y_1134_ = v_val_1152_;
v___y_1135_ = v_color_1146_;
v___y_1136_ = v_key_1151_;
v___y_1137_ = v_rchild_1153_;
v_a_1138_ = v___x_1154_;
v_kx_1139_ = v_key_1148_;
v_vx_1140_ = v_val_1149_;
v_b_1141_ = v_lchild_1150_;
goto v___jp_1132_;
}
}
}
else
{
lean_object* v_rchild_1173_; 
v_rchild_1173_ = lean_ctor_get(v___x_1154_, 3);
lean_inc(v_rchild_1173_);
if (lean_obj_tag(v_rchild_1173_) == 1)
{
uint8_t v_color_1174_; 
v_color_1174_ = lean_ctor_get_uint8(v_rchild_1173_, sizeof(void*)*4);
if (v_color_1174_ == 0)
{
lean_object* v_key_1175_; lean_object* v_val_1176_; lean_object* v_lchild_1177_; lean_object* v_key_1178_; lean_object* v_val_1179_; lean_object* v_rchild_1180_; 
v_key_1175_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_key_1175_);
v_val_1176_ = lean_ctor_get(v___x_1154_, 2);
lean_inc(v_val_1176_);
lean_dec_ref_known(v___x_1154_, 4);
v_lchild_1177_ = lean_ctor_get(v_rchild_1173_, 0);
lean_inc(v_lchild_1177_);
v_key_1178_ = lean_ctor_get(v_rchild_1173_, 1);
lean_inc(v_key_1178_);
v_val_1179_ = lean_ctor_get(v_rchild_1173_, 2);
lean_inc(v_val_1179_);
v_rchild_1180_ = lean_ctor_get(v_rchild_1173_, 3);
lean_inc(v_rchild_1180_);
lean_dec_ref_known(v_rchild_1173_, 4);
v___y_1114_ = v_val_1152_;
v___y_1115_ = v_color_1144_;
v___y_1116_ = v_color_1146_;
v___y_1117_ = v_key_1151_;
v___y_1118_ = v_rchild_1153_;
v_a_1119_ = v_lchild_1156_;
v_kx_1120_ = v_key_1175_;
v_vx_1121_ = v_val_1176_;
v_b_1122_ = v_lchild_1177_;
v_ky_1123_ = v_key_1178_;
v_vy_1124_ = v_val_1179_;
v_c_1125_ = v_rchild_1180_;
v_kz_1126_ = v_key_1148_;
v_vz_1127_ = v_val_1149_;
v_d_1128_ = v_lchild_1150_;
goto v___jp_1113_;
}
else
{
lean_dec_ref_known(v_rchild_1173_, 4);
lean_dec(v_lchild_1156_);
v___y_1133_ = v_color_1144_;
v___y_1134_ = v_val_1152_;
v___y_1135_ = v_color_1146_;
v___y_1136_ = v_key_1151_;
v___y_1137_ = v_rchild_1153_;
v_a_1138_ = v___x_1154_;
v_kx_1139_ = v_key_1148_;
v_vx_1140_ = v_val_1149_;
v_b_1141_ = v_lchild_1150_;
goto v___jp_1132_;
}
}
else
{
lean_dec(v_rchild_1173_);
lean_dec(v_lchild_1156_);
v___y_1133_ = v_color_1144_;
v___y_1134_ = v_val_1152_;
v___y_1135_ = v_color_1146_;
v___y_1136_ = v_key_1151_;
v___y_1137_ = v_rchild_1153_;
v_a_1138_ = v___x_1154_;
v_kx_1139_ = v_key_1148_;
v_vx_1140_ = v_val_1149_;
v_b_1141_ = v_lchild_1150_;
goto v___jp_1132_;
}
}
}
else
{
v___y_1133_ = v_color_1144_;
v___y_1134_ = v_val_1152_;
v___y_1135_ = v_color_1146_;
v___y_1136_ = v_key_1151_;
v___y_1137_ = v_rchild_1153_;
v_a_1138_ = v___x_1154_;
v_kx_1139_ = v_key_1148_;
v_vx_1140_ = v_val_1149_;
v_b_1141_ = v_lchild_1150_;
goto v___jp_1132_;
}
}
else
{
v___y_1133_ = v_color_1144_;
v___y_1134_ = v_val_1152_;
v___y_1135_ = v_color_1146_;
v___y_1136_ = v_key_1151_;
v___y_1137_ = v_rchild_1153_;
v_a_1138_ = v___x_1154_;
v_kx_1139_ = v_key_1148_;
v_vx_1140_ = v_val_1149_;
v_b_1141_ = v_lchild_1150_;
goto v___jp_1132_;
}
}
else
{
goto v___jp_1085_;
}
}
else
{
goto v___jp_1085_;
}
}
else
{
lean_object* v_lchild_1181_; lean_object* v_key_1182_; lean_object* v_val_1183_; lean_object* v_rchild_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1241_; 
v_lchild_1181_ = lean_ctor_get(v_l_1081_, 0);
v_key_1182_ = lean_ctor_get(v_l_1081_, 1);
v_val_1183_ = lean_ctor_get(v_l_1081_, 2);
v_rchild_1184_ = lean_ctor_get(v_l_1081_, 3);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_l_1081_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1186_ = v_l_1081_;
v_isShared_1187_ = v_isSharedCheck_1241_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_rchild_1184_);
lean_inc(v_val_1183_);
lean_inc(v_key_1182_);
lean_inc(v_lchild_1181_);
lean_dec(v_l_1081_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1241_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
uint8_t v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = 0;
lean_inc(v_rchild_1184_);
lean_inc(v_val_1183_);
lean_inc(v_key_1182_);
lean_inc(v_lchild_1181_);
if (v_isShared_1187_ == 0)
{
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_lchild_1181_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_key_1182_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_val_1183_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_rchild_1184_);
v___x_1190_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*4, v___x_1188_);
if (lean_obj_tag(v_lchild_1181_) == 1)
{
uint8_t v_color_1191_; 
v_color_1191_ = lean_ctor_get_uint8(v_lchild_1181_, sizeof(void*)*4);
if (v_color_1191_ == 0)
{
lean_object* v_lchild_1192_; lean_object* v_key_1193_; lean_object* v_val_1194_; lean_object* v_rchild_1195_; 
lean_dec_ref(v___x_1190_);
v_lchild_1192_ = lean_ctor_get(v_lchild_1181_, 0);
lean_inc(v_lchild_1192_);
v_key_1193_ = lean_ctor_get(v_lchild_1181_, 1);
lean_inc(v_key_1193_);
v_val_1194_ = lean_ctor_get(v_lchild_1181_, 2);
lean_inc(v_val_1194_);
v_rchild_1195_ = lean_ctor_get(v_lchild_1181_, 3);
lean_inc(v_rchild_1195_);
lean_dec_ref_known(v_lchild_1181_, 4);
v___y_1089_ = v_color_1144_;
v_a_1090_ = v_lchild_1192_;
v_kx_1091_ = v_key_1193_;
v_vx_1092_ = v_val_1194_;
v_b_1093_ = v_rchild_1195_;
v_ky_1094_ = v_key_1182_;
v_vy_1095_ = v_val_1183_;
v_c_1096_ = v_rchild_1184_;
v_kz_1097_ = v_k_1082_;
v_vz_1098_ = v_v_1083_;
v_d_1099_ = v_r_1084_;
goto v___jp_1088_;
}
else
{
if (lean_obj_tag(v_rchild_1184_) == 1)
{
uint8_t v_color_1196_; 
v_color_1196_ = lean_ctor_get_uint8(v_rchild_1184_, sizeof(void*)*4);
if (v_color_1196_ == 0)
{
lean_object* v_lchild_1197_; lean_object* v_key_1198_; lean_object* v_val_1199_; lean_object* v_rchild_1200_; 
lean_dec_ref(v___x_1190_);
v_lchild_1197_ = lean_ctor_get(v_rchild_1184_, 0);
lean_inc(v_lchild_1197_);
v_key_1198_ = lean_ctor_get(v_rchild_1184_, 1);
lean_inc(v_key_1198_);
v_val_1199_ = lean_ctor_get(v_rchild_1184_, 2);
lean_inc(v_val_1199_);
v_rchild_1200_ = lean_ctor_get(v_rchild_1184_, 3);
lean_inc(v_rchild_1200_);
lean_dec_ref_known(v_rchild_1184_, 4);
v___y_1089_ = v_color_1144_;
v_a_1090_ = v_lchild_1181_;
v_kx_1091_ = v_key_1182_;
v_vx_1092_ = v_val_1183_;
v_b_1093_ = v_lchild_1197_;
v_ky_1094_ = v_key_1198_;
v_vy_1095_ = v_val_1199_;
v_c_1096_ = v_rchild_1200_;
v_kz_1097_ = v_k_1082_;
v_vz_1098_ = v_v_1083_;
v_d_1099_ = v_r_1084_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref_known(v_lchild_1181_, 4);
lean_dec(v_val_1183_);
lean_dec(v_key_1182_);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_rchild_1184_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; lean_object* v_unused_1210_; lean_object* v_unused_1211_; 
v_unused_1208_ = lean_ctor_get(v_rchild_1184_, 3);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_rchild_1184_, 2);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_rchild_1184_, 1);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_rchild_1184_, 0);
lean_dec(v_unused_1211_);
v___x_1202_ = v_rchild_1184_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v_rchild_1184_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 3, v_r_1084_);
lean_ctor_set(v___x_1202_, 2, v_v_1083_);
lean_ctor_set(v___x_1202_, 1, v_k_1082_);
lean_ctor_set(v___x_1202_, 0, v___x_1190_);
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1082_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1083_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_r_1084_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*4, v_color_1144_);
return v___x_1205_;
}
}
}
}
else
{
lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_rchild_1184_);
lean_dec(v_val_1183_);
lean_dec(v_key_1182_);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_lchild_1181_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; 
v_unused_1219_ = lean_ctor_get(v_lchild_1181_, 3);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_lchild_1181_, 2);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_lchild_1181_, 1);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_lchild_1181_, 0);
lean_dec(v_unused_1222_);
v___x_1213_ = v_lchild_1181_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_dec(v_lchild_1181_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 3, v_r_1084_);
lean_ctor_set(v___x_1213_, 2, v_v_1083_);
lean_ctor_set(v___x_1213_, 1, v_k_1082_);
lean_ctor_set(v___x_1213_, 0, v___x_1190_);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_k_1082_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_v_1083_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_r_1084_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*4, v_color_1144_);
return v___x_1216_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_1184_) == 1)
{
uint8_t v_color_1223_; 
v_color_1223_ = lean_ctor_get_uint8(v_rchild_1184_, sizeof(void*)*4);
if (v_color_1223_ == 0)
{
lean_object* v_lchild_1224_; lean_object* v_key_1225_; lean_object* v_val_1226_; lean_object* v_rchild_1227_; 
lean_dec_ref(v___x_1190_);
v_lchild_1224_ = lean_ctor_get(v_rchild_1184_, 0);
lean_inc(v_lchild_1224_);
v_key_1225_ = lean_ctor_get(v_rchild_1184_, 1);
lean_inc(v_key_1225_);
v_val_1226_ = lean_ctor_get(v_rchild_1184_, 2);
lean_inc(v_val_1226_);
v_rchild_1227_ = lean_ctor_get(v_rchild_1184_, 3);
lean_inc(v_rchild_1227_);
lean_dec_ref_known(v_rchild_1184_, 4);
v___y_1089_ = v_color_1144_;
v_a_1090_ = v_lchild_1181_;
v_kx_1091_ = v_key_1182_;
v_vx_1092_ = v_val_1183_;
v_b_1093_ = v_lchild_1224_;
v_ky_1094_ = v_key_1225_;
v_vy_1095_ = v_val_1226_;
v_c_1096_ = v_rchild_1227_;
v_kz_1097_ = v_k_1082_;
v_vz_1098_ = v_v_1083_;
v_d_1099_ = v_r_1084_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_val_1183_);
lean_dec(v_key_1182_);
lean_dec(v_lchild_1181_);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_rchild_1184_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; lean_object* v_unused_1238_; 
v_unused_1235_ = lean_ctor_get(v_rchild_1184_, 3);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_rchild_1184_, 2);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_rchild_1184_, 1);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_rchild_1184_, 0);
lean_dec(v_unused_1238_);
v___x_1229_ = v_rchild_1184_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v_rchild_1184_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 3, v_r_1084_);
lean_ctor_set(v___x_1229_, 2, v_v_1083_);
lean_ctor_set(v___x_1229_, 1, v_k_1082_);
lean_ctor_set(v___x_1229_, 0, v___x_1190_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_k_1082_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_v_1083_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_r_1084_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*4, v_color_1144_);
return v___x_1232_;
}
}
}
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_rchild_1184_);
lean_dec(v_val_1183_);
lean_dec(v_key_1182_);
lean_dec(v_lchild_1181_);
v___x_1239_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1190_);
lean_ctor_set(v___x_1239_, 1, v_k_1082_);
lean_ctor_set(v___x_1239_, 2, v_v_1083_);
lean_ctor_set(v___x_1239_, 3, v_r_1084_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*4, v_color_1144_);
return v___x_1239_;
}
}
}
}
}
}
else
{
goto v___jp_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_l_1258_, lean_object* v_k_1259_, lean_object* v_v_1260_, lean_object* v_r_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_RBNode_balRight___redArg(v_l_1258_, v_k_1259_, v_v_1260_, v_r_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object* v_x_1263_){
_start:
{
if (lean_obj_tag(v_x_1263_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_unsigned_to_nat(0u);
return v___x_1264_;
}
else
{
lean_object* v_lchild_1265_; lean_object* v_rchild_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_lchild_1265_ = lean_ctor_get(v_x_1263_, 0);
v_rchild_1266_ = lean_ctor_get(v_x_1263_, 3);
v___x_1267_ = l_Lean_RBNode_size___redArg(v_lchild_1265_);
v___x_1268_ = l_Lean_RBNode_size___redArg(v_rchild_1266_);
v___x_1269_ = lean_nat_add(v___x_1267_, v___x_1268_);
lean_dec(v___x_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_RBNode_size___redArg(v_x_1272_);
lean_dec(v_x_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_RBNode_size___redArg(v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_RBNode_size(v_00_u03b1_1278_, v_00_u03b2_1279_, v_x_1280_);
lean_dec(v_x_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(lean_object* v_x_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_h__2_1284_);
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_apply_1(v_h__1_1283_, v___x_1285_);
return v___x_1286_;
}
else
{
uint8_t v_color_1287_; lean_object* v_lchild_1288_; lean_object* v_key_1289_; lean_object* v_val_1290_; lean_object* v_rchild_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec(v_h__1_1283_);
v_color_1287_ = lean_ctor_get_uint8(v_x_1282_, sizeof(void*)*4);
v_lchild_1288_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_lchild_1288_);
v_key_1289_ = lean_ctor_get(v_x_1282_, 1);
lean_inc(v_key_1289_);
v_val_1290_ = lean_ctor_get(v_x_1282_, 2);
lean_inc(v_val_1290_);
v_rchild_1291_ = lean_ctor_get(v_x_1282_, 3);
lean_inc(v_rchild_1291_);
lean_dec_ref_known(v_x_1282_, 4);
v___x_1292_ = lean_box(v_color_1287_);
v___x_1293_ = lean_apply_5(v_h__2_1284_, v___x_1292_, v_lchild_1288_, v_key_1289_, v_val_1290_, v_rchild_1291_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object* v_00_u03b1_1294_, lean_object* v_00_u03b2_1295_, lean_object* v_motive_1296_, lean_object* v_x_1297_, lean_object* v_h__1_1298_, lean_object* v_h__2_1299_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v_h__2_1299_);
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_apply_1(v_h__1_1298_, v___x_1300_);
return v___x_1301_;
}
else
{
uint8_t v_color_1302_; lean_object* v_lchild_1303_; lean_object* v_key_1304_; lean_object* v_val_1305_; lean_object* v_rchild_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v_h__1_1298_);
v_color_1302_ = lean_ctor_get_uint8(v_x_1297_, sizeof(void*)*4);
v_lchild_1303_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_lchild_1303_);
v_key_1304_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_key_1304_);
v_val_1305_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_val_1305_);
v_rchild_1306_ = lean_ctor_get(v_x_1297_, 3);
lean_inc(v_rchild_1306_);
lean_dec_ref_known(v_x_1297_, 4);
v___x_1307_ = lean_box(v_color_1302_);
v___x_1308_ = lean_apply_5(v_h__2_1299_, v___x_1307_, v_lchild_1303_, v_key_1304_, v_val_1305_, v_rchild_1306_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 0)
{
return v_x_1310_;
}
else
{
if (lean_obj_tag(v_x_1310_) == 0)
{
return v_x_1309_;
}
else
{
uint8_t v_color_1311_; lean_object* v_lchild_1312_; lean_object* v_key_1313_; lean_object* v_val_1314_; lean_object* v_rchild_1315_; uint8_t v_color_1316_; lean_object* v_lchild_1317_; lean_object* v_key_1318_; lean_object* v_val_1319_; lean_object* v_rchild_1320_; lean_object* v_bc_1322_; lean_object* v_bc_1326_; 
v_color_1311_ = lean_ctor_get_uint8(v_x_1309_, sizeof(void*)*4);
v_lchild_1312_ = lean_ctor_get(v_x_1309_, 0);
v_key_1313_ = lean_ctor_get(v_x_1309_, 1);
v_val_1314_ = lean_ctor_get(v_x_1309_, 2);
v_rchild_1315_ = lean_ctor_get(v_x_1309_, 3);
v_color_1316_ = lean_ctor_get_uint8(v_x_1310_, sizeof(void*)*4);
v_lchild_1317_ = lean_ctor_get(v_x_1310_, 0);
v_key_1318_ = lean_ctor_get(v_x_1310_, 1);
v_val_1319_ = lean_ctor_get(v_x_1310_, 2);
v_rchild_1320_ = lean_ctor_get(v_x_1310_, 3);
if (v_color_1316_ == 0)
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1363_; 
lean_inc(v_rchild_1320_);
lean_inc(v_val_1319_);
lean_inc(v_key_1318_);
lean_inc(v_lchild_1317_);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1310_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; 
v_unused_1364_ = lean_ctor_get(v_x_1310_, 3);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_x_1310_, 2);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_x_1310_, 1);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_x_1310_, 0);
lean_dec(v_unused_1367_);
v___x_1330_ = v_x_1310_;
v_isShared_1331_ = v_isSharedCheck_1363_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v_x_1310_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1363_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
if (v_color_1311_ == 0)
{
lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1354_; 
lean_inc(v_rchild_1315_);
lean_inc(v_val_1314_);
lean_inc(v_key_1313_);
lean_inc(v_lchild_1312_);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; lean_object* v_unused_1356_; lean_object* v_unused_1357_; lean_object* v_unused_1358_; 
v_unused_1355_ = lean_ctor_get(v_x_1309_, 3);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_x_1309_, 2);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_x_1309_, 1);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_x_1309_, 0);
lean_dec(v_unused_1358_);
v___x_1333_ = v_x_1309_;
v_isShared_1334_ = v_isSharedCheck_1354_;
goto v_resetjp_1332_;
}
else
{
lean_dec(v_x_1309_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1354_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1315_, v_lchild_1317_);
if (lean_obj_tag(v___x_1335_) == 1)
{
uint8_t v_color_1336_; 
v_color_1336_ = lean_ctor_get_uint8(v___x_1335_, sizeof(void*)*4);
if (v_color_1336_ == 0)
{
lean_object* v_lchild_1337_; lean_object* v_key_1338_; lean_object* v_val_1339_; lean_object* v_rchild_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1353_; 
v_lchild_1337_ = lean_ctor_get(v___x_1335_, 0);
v_key_1338_ = lean_ctor_get(v___x_1335_, 1);
v_val_1339_ = lean_ctor_get(v___x_1335_, 2);
v_rchild_1340_ = lean_ctor_get(v___x_1335_, 3);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1342_ = v___x_1335_;
v_isShared_1343_ = v_isSharedCheck_1353_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_rchild_1340_);
lean_inc(v_val_1339_);
lean_inc(v_key_1338_);
lean_inc(v_lchild_1337_);
lean_dec(v___x_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1353_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 3, v_lchild_1337_);
lean_ctor_set(v___x_1342_, 2, v_val_1314_);
lean_ctor_set(v___x_1342_, 1, v_key_1313_);
lean_ctor_set(v___x_1342_, 0, v_lchild_1312_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_lchild_1312_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_key_1313_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_val_1314_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_lchild_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, sizeof(void*)*4, v_color_1336_);
v___x_1345_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_rchild_1340_);
v___x_1347_ = v___x_1330_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_rchild_1340_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_val_1319_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_rchild_1320_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*4, v_color_1336_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 3, v___x_1347_);
lean_ctor_set(v___x_1333_, 2, v_val_1339_);
lean_ctor_set(v___x_1333_, 1, v_key_1338_);
lean_ctor_set(v___x_1333_, 0, v___x_1345_);
v___x_1349_ = v___x_1333_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_key_1338_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_val_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*4, v_color_1336_);
return v___x_1349_;
}
}
}
}
}
else
{
lean_del_object(v___x_1333_);
lean_del_object(v___x_1330_);
v_bc_1326_ = v___x_1335_;
goto v___jp_1325_;
}
}
else
{
lean_del_object(v___x_1333_);
lean_del_object(v___x_1330_);
v_bc_1326_ = v___x_1335_;
goto v___jp_1325_;
}
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = l_Lean_RBNode_appendTrees___redArg(v_x_1309_, v_lchild_1317_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1359_);
v___x_1361_ = v___x_1330_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_val_1319_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_rchild_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*4, v_color_1316_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1402_; 
lean_inc(v_rchild_1315_);
lean_inc(v_val_1314_);
lean_inc(v_key_1313_);
lean_inc(v_lchild_1312_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1403_ = lean_ctor_get(v_x_1309_, 3);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_x_1309_, 2);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_x_1309_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_x_1309_, 0);
lean_dec(v_unused_1406_);
v___x_1369_ = v_x_1309_;
v_isShared_1370_ = v_isSharedCheck_1402_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v_x_1309_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1402_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
if (v_color_1311_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1315_, v_x_1310_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 3, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_lchild_1312_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_key_1313_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_val_1314_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v___x_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1374_, sizeof(void*)*4, v_color_1311_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1397_; 
lean_inc(v_rchild_1320_);
lean_inc(v_val_1319_);
lean_inc(v_key_1318_);
lean_inc(v_lchild_1317_);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1310_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1398_ = lean_ctor_get(v_x_1310_, 3);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_x_1310_, 2);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_x_1310_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_x_1310_, 0);
lean_dec(v_unused_1401_);
v___x_1376_ = v_x_1310_;
v_isShared_1377_ = v_isSharedCheck_1397_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v_x_1310_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1397_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1315_, v_lchild_1317_);
if (lean_obj_tag(v___x_1378_) == 1)
{
uint8_t v_color_1379_; 
v_color_1379_ = lean_ctor_get_uint8(v___x_1378_, sizeof(void*)*4);
if (v_color_1379_ == 0)
{
lean_object* v_lchild_1380_; lean_object* v_key_1381_; lean_object* v_val_1382_; lean_object* v_rchild_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1396_; 
v_lchild_1380_ = lean_ctor_get(v___x_1378_, 0);
v_key_1381_ = lean_ctor_get(v___x_1378_, 1);
v_val_1382_ = lean_ctor_get(v___x_1378_, 2);
v_rchild_1383_ = lean_ctor_get(v___x_1378_, 3);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1385_ = v___x_1378_;
v_isShared_1386_ = v_isSharedCheck_1396_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_rchild_1383_);
lean_inc(v_val_1382_);
lean_inc(v_key_1381_);
lean_inc(v_lchild_1380_);
lean_dec(v___x_1378_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1396_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 3, v_lchild_1380_);
lean_ctor_set(v___x_1385_, 2, v_val_1314_);
lean_ctor_set(v___x_1385_, 1, v_key_1313_);
lean_ctor_set(v___x_1385_, 0, v_lchild_1312_);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_lchild_1312_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_key_1313_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_val_1314_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_lchild_1380_);
v___x_1388_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*4, v_color_1311_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v_rchild_1383_);
v___x_1390_ = v___x_1376_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_rchild_1383_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_val_1319_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_rchild_1320_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
lean_ctor_set_uint8(v___x_1390_, sizeof(void*)*4, v_color_1311_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 3, v___x_1390_);
lean_ctor_set(v___x_1369_, 2, v_val_1382_);
lean_ctor_set(v___x_1369_, 1, v_key_1381_);
lean_ctor_set(v___x_1369_, 0, v___x_1388_);
v___x_1392_ = v___x_1369_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_key_1381_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_val_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*4, v_color_1379_);
return v___x_1392_;
}
}
}
}
}
else
{
lean_del_object(v___x_1376_);
lean_del_object(v___x_1369_);
v_bc_1322_ = v___x_1378_;
goto v___jp_1321_;
}
}
else
{
lean_del_object(v___x_1376_);
lean_del_object(v___x_1369_);
v_bc_1322_ = v___x_1378_;
goto v___jp_1321_;
}
}
}
}
}
v___jp_1321_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1323_, 0, v_bc_1322_);
lean_ctor_set(v___x_1323_, 1, v_key_1318_);
lean_ctor_set(v___x_1323_, 2, v_val_1319_);
lean_ctor_set(v___x_1323_, 3, v_rchild_1320_);
lean_ctor_set_uint8(v___x_1323_, sizeof(void*)*4, v_color_1311_);
v___x_1324_ = l_Lean_RBNode_balLeft___redArg(v_lchild_1312_, v_key_1313_, v_val_1314_, v___x_1323_);
return v___x_1324_;
}
v___jp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1327_, 0, v_bc_1326_);
lean_ctor_set(v___x_1327_, 1, v_key_1318_);
lean_ctor_set(v___x_1327_, 2, v_val_1319_);
lean_ctor_set(v___x_1327_, 3, v_rchild_1320_);
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*4, v_color_1311_);
v___x_1328_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1328_, 0, v_lchild_1312_);
lean_ctor_set(v___x_1328_, 1, v_key_1313_);
lean_ctor_set(v___x_1328_, 2, v_val_1314_);
lean_ctor_set(v___x_1328_, 3, v___x_1327_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*4, v_color_1311_);
return v___x_1328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* v_00_u03b1_1407_, lean_object* v_00_u03b2_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_RBNode_appendTrees___redArg(v_x_1409_, v_x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v_h__1_1414_, lean_object* v_h__2_1415_, lean_object* v_h__3_1416_, lean_object* v_h__4_1417_, lean_object* v_h__5_1418_, lean_object* v_h__6_1419_){
_start:
{
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_h__6_1419_);
lean_dec(v_h__5_1418_);
lean_dec(v_h__4_1417_);
lean_dec(v_h__3_1416_);
lean_dec(v_h__2_1415_);
v___x_1420_ = lean_apply_1(v_h__1_1414_, v_x_1413_);
return v___x_1420_;
}
else
{
lean_dec(v_h__1_1414_);
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1421_; 
lean_dec(v_h__6_1419_);
lean_dec(v_h__5_1418_);
lean_dec(v_h__4_1417_);
lean_dec(v_h__3_1416_);
v___x_1421_ = lean_apply_2(v_h__2_1415_, v_x_1412_, lean_box(0));
return v___x_1421_;
}
else
{
uint8_t v_color_1422_; 
lean_dec(v_h__2_1415_);
v_color_1422_ = lean_ctor_get_uint8(v_x_1413_, sizeof(void*)*4);
if (v_color_1422_ == 0)
{
uint8_t v_color_1423_; 
lean_dec(v_h__6_1419_);
lean_dec(v_h__4_1417_);
v_color_1423_ = lean_ctor_get_uint8(v_x_1412_, sizeof(void*)*4);
if (v_color_1423_ == 0)
{
lean_object* v_lchild_1424_; lean_object* v_key_1425_; lean_object* v_val_1426_; lean_object* v_rchild_1427_; lean_object* v_lchild_1428_; lean_object* v_key_1429_; lean_object* v_val_1430_; lean_object* v_rchild_1431_; lean_object* v___x_1432_; 
lean_dec(v_h__5_1418_);
v_lchild_1424_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_lchild_1424_);
v_key_1425_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_key_1425_);
v_val_1426_ = lean_ctor_get(v_x_1412_, 2);
lean_inc(v_val_1426_);
v_rchild_1427_ = lean_ctor_get(v_x_1412_, 3);
lean_inc(v_rchild_1427_);
lean_dec_ref_known(v_x_1412_, 4);
v_lchild_1428_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_lchild_1428_);
v_key_1429_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_key_1429_);
v_val_1430_ = lean_ctor_get(v_x_1413_, 2);
lean_inc(v_val_1430_);
v_rchild_1431_ = lean_ctor_get(v_x_1413_, 3);
lean_inc(v_rchild_1431_);
lean_dec_ref_known(v_x_1413_, 4);
v___x_1432_ = lean_apply_8(v_h__3_1416_, v_lchild_1424_, v_key_1425_, v_val_1426_, v_rchild_1427_, v_lchild_1428_, v_key_1429_, v_val_1430_, v_rchild_1431_);
return v___x_1432_;
}
else
{
lean_object* v_lchild_1433_; lean_object* v_key_1434_; lean_object* v_val_1435_; lean_object* v_rchild_1436_; lean_object* v___x_1437_; 
lean_dec(v_h__3_1416_);
v_lchild_1433_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_lchild_1433_);
v_key_1434_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_key_1434_);
v_val_1435_ = lean_ctor_get(v_x_1413_, 2);
lean_inc(v_val_1435_);
v_rchild_1436_ = lean_ctor_get(v_x_1413_, 3);
lean_inc(v_rchild_1436_);
lean_dec_ref_known(v_x_1413_, 4);
v___x_1437_ = lean_apply_7(v_h__5_1418_, v_x_1412_, v_lchild_1433_, v_key_1434_, v_val_1435_, v_rchild_1436_, lean_box(0), lean_box(0));
return v___x_1437_;
}
}
else
{
uint8_t v_color_1438_; 
lean_dec(v_h__5_1418_);
lean_dec(v_h__3_1416_);
v_color_1438_ = lean_ctor_get_uint8(v_x_1412_, sizeof(void*)*4);
if (v_color_1438_ == 0)
{
lean_object* v_lchild_1439_; lean_object* v_key_1440_; lean_object* v_val_1441_; lean_object* v_rchild_1442_; lean_object* v___x_1443_; 
lean_dec(v_h__4_1417_);
v_lchild_1439_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_lchild_1439_);
v_key_1440_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_key_1440_);
v_val_1441_ = lean_ctor_get(v_x_1412_, 2);
lean_inc(v_val_1441_);
v_rchild_1442_ = lean_ctor_get(v_x_1412_, 3);
lean_inc(v_rchild_1442_);
lean_dec_ref_known(v_x_1412_, 4);
v___x_1443_ = lean_apply_7(v_h__6_1419_, v_lchild_1439_, v_key_1440_, v_val_1441_, v_rchild_1442_, v_x_1413_, lean_box(0), lean_box(0));
return v___x_1443_;
}
else
{
lean_object* v_lchild_1444_; lean_object* v_key_1445_; lean_object* v_val_1446_; lean_object* v_rchild_1447_; lean_object* v_lchild_1448_; lean_object* v_key_1449_; lean_object* v_val_1450_; lean_object* v_rchild_1451_; lean_object* v___x_1452_; 
lean_dec(v_h__6_1419_);
v_lchild_1444_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_lchild_1444_);
v_key_1445_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_key_1445_);
v_val_1446_ = lean_ctor_get(v_x_1412_, 2);
lean_inc(v_val_1446_);
v_rchild_1447_ = lean_ctor_get(v_x_1412_, 3);
lean_inc(v_rchild_1447_);
lean_dec_ref_known(v_x_1412_, 4);
v_lchild_1448_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_lchild_1448_);
v_key_1449_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_key_1449_);
v_val_1450_ = lean_ctor_get(v_x_1413_, 2);
lean_inc(v_val_1450_);
v_rchild_1451_ = lean_ctor_get(v_x_1413_, 3);
lean_inc(v_rchild_1451_);
lean_dec_ref_known(v_x_1413_, 4);
v___x_1452_ = lean_apply_8(v_h__4_1417_, v_lchild_1444_, v_key_1445_, v_val_1446_, v_rchild_1447_, v_lchild_1448_, v_key_1449_, v_val_1450_, v_rchild_1451_);
return v___x_1452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* v_00_u03b1_1453_, lean_object* v_00_u03b2_1454_, lean_object* v_motive_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v_h__1_1458_, lean_object* v_h__2_1459_, lean_object* v_h__3_1460_, lean_object* v_h__4_1461_, lean_object* v_h__5_1462_, lean_object* v_h__6_1463_){
_start:
{
if (lean_obj_tag(v_x_1456_) == 0)
{
lean_object* v___x_1464_; 
lean_dec(v_h__6_1463_);
lean_dec(v_h__5_1462_);
lean_dec(v_h__4_1461_);
lean_dec(v_h__3_1460_);
lean_dec(v_h__2_1459_);
v___x_1464_ = lean_apply_1(v_h__1_1458_, v_x_1457_);
return v___x_1464_;
}
else
{
lean_dec(v_h__1_1458_);
if (lean_obj_tag(v_x_1457_) == 0)
{
lean_object* v___x_1465_; 
lean_dec(v_h__6_1463_);
lean_dec(v_h__5_1462_);
lean_dec(v_h__4_1461_);
lean_dec(v_h__3_1460_);
v___x_1465_ = lean_apply_2(v_h__2_1459_, v_x_1456_, lean_box(0));
return v___x_1465_;
}
else
{
uint8_t v_color_1466_; 
lean_dec(v_h__2_1459_);
v_color_1466_ = lean_ctor_get_uint8(v_x_1457_, sizeof(void*)*4);
if (v_color_1466_ == 0)
{
uint8_t v_color_1467_; 
lean_dec(v_h__6_1463_);
lean_dec(v_h__4_1461_);
v_color_1467_ = lean_ctor_get_uint8(v_x_1456_, sizeof(void*)*4);
if (v_color_1467_ == 0)
{
lean_object* v_lchild_1468_; lean_object* v_key_1469_; lean_object* v_val_1470_; lean_object* v_rchild_1471_; lean_object* v_lchild_1472_; lean_object* v_key_1473_; lean_object* v_val_1474_; lean_object* v_rchild_1475_; lean_object* v___x_1476_; 
lean_dec(v_h__5_1462_);
v_lchild_1468_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_lchild_1468_);
v_key_1469_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_key_1469_);
v_val_1470_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_val_1470_);
v_rchild_1471_ = lean_ctor_get(v_x_1456_, 3);
lean_inc(v_rchild_1471_);
lean_dec_ref_known(v_x_1456_, 4);
v_lchild_1472_ = lean_ctor_get(v_x_1457_, 0);
lean_inc(v_lchild_1472_);
v_key_1473_ = lean_ctor_get(v_x_1457_, 1);
lean_inc(v_key_1473_);
v_val_1474_ = lean_ctor_get(v_x_1457_, 2);
lean_inc(v_val_1474_);
v_rchild_1475_ = lean_ctor_get(v_x_1457_, 3);
lean_inc(v_rchild_1475_);
lean_dec_ref_known(v_x_1457_, 4);
v___x_1476_ = lean_apply_8(v_h__3_1460_, v_lchild_1468_, v_key_1469_, v_val_1470_, v_rchild_1471_, v_lchild_1472_, v_key_1473_, v_val_1474_, v_rchild_1475_);
return v___x_1476_;
}
else
{
lean_object* v_lchild_1477_; lean_object* v_key_1478_; lean_object* v_val_1479_; lean_object* v_rchild_1480_; lean_object* v___x_1481_; 
lean_dec(v_h__3_1460_);
v_lchild_1477_ = lean_ctor_get(v_x_1457_, 0);
lean_inc(v_lchild_1477_);
v_key_1478_ = lean_ctor_get(v_x_1457_, 1);
lean_inc(v_key_1478_);
v_val_1479_ = lean_ctor_get(v_x_1457_, 2);
lean_inc(v_val_1479_);
v_rchild_1480_ = lean_ctor_get(v_x_1457_, 3);
lean_inc(v_rchild_1480_);
lean_dec_ref_known(v_x_1457_, 4);
v___x_1481_ = lean_apply_7(v_h__5_1462_, v_x_1456_, v_lchild_1477_, v_key_1478_, v_val_1479_, v_rchild_1480_, lean_box(0), lean_box(0));
return v___x_1481_;
}
}
else
{
uint8_t v_color_1482_; 
lean_dec(v_h__5_1462_);
lean_dec(v_h__3_1460_);
v_color_1482_ = lean_ctor_get_uint8(v_x_1456_, sizeof(void*)*4);
if (v_color_1482_ == 0)
{
lean_object* v_lchild_1483_; lean_object* v_key_1484_; lean_object* v_val_1485_; lean_object* v_rchild_1486_; lean_object* v___x_1487_; 
lean_dec(v_h__4_1461_);
v_lchild_1483_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_lchild_1483_);
v_key_1484_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_key_1484_);
v_val_1485_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_val_1485_);
v_rchild_1486_ = lean_ctor_get(v_x_1456_, 3);
lean_inc(v_rchild_1486_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1487_ = lean_apply_7(v_h__6_1463_, v_lchild_1483_, v_key_1484_, v_val_1485_, v_rchild_1486_, v_x_1457_, lean_box(0), lean_box(0));
return v___x_1487_;
}
else
{
lean_object* v_lchild_1488_; lean_object* v_key_1489_; lean_object* v_val_1490_; lean_object* v_rchild_1491_; lean_object* v_lchild_1492_; lean_object* v_key_1493_; lean_object* v_val_1494_; lean_object* v_rchild_1495_; lean_object* v___x_1496_; 
lean_dec(v_h__6_1463_);
v_lchild_1488_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_lchild_1488_);
v_key_1489_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_key_1489_);
v_val_1490_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_val_1490_);
v_rchild_1491_ = lean_ctor_get(v_x_1456_, 3);
lean_inc(v_rchild_1491_);
lean_dec_ref_known(v_x_1456_, 4);
v_lchild_1492_ = lean_ctor_get(v_x_1457_, 0);
lean_inc(v_lchild_1492_);
v_key_1493_ = lean_ctor_get(v_x_1457_, 1);
lean_inc(v_key_1493_);
v_val_1494_ = lean_ctor_get(v_x_1457_, 2);
lean_inc(v_val_1494_);
v_rchild_1495_ = lean_ctor_get(v_x_1457_, 3);
lean_inc(v_rchild_1495_);
lean_dec_ref_known(v_x_1457_, 4);
v___x_1496_ = lean_apply_8(v_h__4_1461_, v_lchild_1488_, v_key_1489_, v_val_1490_, v_rchild_1491_, v_lchild_1492_, v_key_1493_, v_val_1494_, v_rchild_1495_);
return v___x_1496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* v_x_1497_, lean_object* v_h__1_1498_, lean_object* v_h__2_1499_){
_start:
{
if (lean_obj_tag(v_x_1497_) == 1)
{
uint8_t v_color_1500_; 
v_color_1500_ = lean_ctor_get_uint8(v_x_1497_, sizeof(void*)*4);
if (v_color_1500_ == 0)
{
lean_object* v_lchild_1501_; lean_object* v_key_1502_; lean_object* v_val_1503_; lean_object* v_rchild_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__2_1499_);
v_lchild_1501_ = lean_ctor_get(v_x_1497_, 0);
lean_inc(v_lchild_1501_);
v_key_1502_ = lean_ctor_get(v_x_1497_, 1);
lean_inc(v_key_1502_);
v_val_1503_ = lean_ctor_get(v_x_1497_, 2);
lean_inc(v_val_1503_);
v_rchild_1504_ = lean_ctor_get(v_x_1497_, 3);
lean_inc(v_rchild_1504_);
lean_dec_ref_known(v_x_1497_, 4);
v___x_1505_ = lean_apply_4(v_h__1_1498_, v_lchild_1501_, v_key_1502_, v_val_1503_, v_rchild_1504_);
return v___x_1505_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_h__1_1498_);
v___x_1506_ = lean_apply_2(v_h__2_1499_, v_x_1497_, lean_box(0));
return v___x_1506_;
}
}
else
{
lean_object* v___x_1507_; 
lean_dec(v_h__1_1498_);
v___x_1507_ = lean_apply_2(v_h__2_1499_, v_x_1497_, lean_box(0));
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* v_00_u03b1_1508_, lean_object* v_00_u03b2_1509_, lean_object* v_motive_1510_, lean_object* v_x_1511_, lean_object* v_h__1_1512_, lean_object* v_h__2_1513_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 1)
{
uint8_t v_color_1514_; 
v_color_1514_ = lean_ctor_get_uint8(v_x_1511_, sizeof(void*)*4);
if (v_color_1514_ == 0)
{
lean_object* v_lchild_1515_; lean_object* v_key_1516_; lean_object* v_val_1517_; lean_object* v_rchild_1518_; lean_object* v___x_1519_; 
lean_dec(v_h__2_1513_);
v_lchild_1515_ = lean_ctor_get(v_x_1511_, 0);
lean_inc(v_lchild_1515_);
v_key_1516_ = lean_ctor_get(v_x_1511_, 1);
lean_inc(v_key_1516_);
v_val_1517_ = lean_ctor_get(v_x_1511_, 2);
lean_inc(v_val_1517_);
v_rchild_1518_ = lean_ctor_get(v_x_1511_, 3);
lean_inc(v_rchild_1518_);
lean_dec_ref_known(v_x_1511_, 4);
v___x_1519_ = lean_apply_4(v_h__1_1512_, v_lchild_1515_, v_key_1516_, v_val_1517_, v_rchild_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec(v_h__1_1512_);
v___x_1520_ = lean_apply_2(v_h__2_1513_, v_x_1511_, lean_box(0));
return v___x_1520_;
}
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_h__1_1512_);
v___x_1521_ = lean_apply_2(v_h__2_1513_, v_x_1511_, lean_box(0));
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* v_cmp_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
if (lean_obj_tag(v_x_1524_) == 0)
{
lean_dec(v_x_1523_);
lean_dec_ref(v_cmp_1522_);
return v_x_1524_;
}
else
{
lean_object* v_lchild_1525_; lean_object* v_key_1526_; lean_object* v_val_1527_; lean_object* v_rchild_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1551_; 
v_lchild_1525_ = lean_ctor_get(v_x_1524_, 0);
v_key_1526_ = lean_ctor_get(v_x_1524_, 1);
v_val_1527_ = lean_ctor_get(v_x_1524_, 2);
v_rchild_1528_ = lean_ctor_get(v_x_1524_, 3);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1524_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1530_ = v_x_1524_;
v_isShared_1531_ = v_isSharedCheck_1551_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_rchild_1528_);
lean_inc(v_val_1527_);
lean_inc(v_key_1526_);
lean_inc(v_lchild_1525_);
lean_dec(v_x_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1551_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
lean_inc_ref(v_cmp_1522_);
lean_inc(v_key_1526_);
lean_inc(v_x_1523_);
v___x_1532_ = lean_apply_2(v_cmp_1522_, v_x_1523_, v_key_1526_);
v___x_1533_ = lean_unbox(v___x_1532_);
switch(v___x_1533_)
{
case 0:
{
uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1525_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = 0;
v___x_1536_ = l_Lean_RBNode_del___redArg(v_cmp_1522_, v_x_1523_, v_lchild_1525_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1536_);
v___x_1538_ = v___x_1530_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_key_1526_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_val_1527_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_rchild_1528_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*4, v___x_1535_);
return v___x_1538_;
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_del_object(v___x_1530_);
v___x_1540_ = l_Lean_RBNode_del___redArg(v_cmp_1522_, v_x_1523_, v_lchild_1525_);
v___x_1541_ = l_Lean_RBNode_balLeft___redArg(v___x_1540_, v_key_1526_, v_val_1527_, v_rchild_1528_);
return v___x_1541_;
}
}
case 1:
{
lean_object* v___x_1542_; 
lean_del_object(v___x_1530_);
lean_dec(v_val_1527_);
lean_dec(v_key_1526_);
lean_dec(v_x_1523_);
lean_dec_ref(v_cmp_1522_);
v___x_1542_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_1525_, v_rchild_1528_);
return v___x_1542_;
}
default: 
{
uint8_t v___x_1543_; 
v___x_1543_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1528_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = 0;
v___x_1545_ = l_Lean_RBNode_del___redArg(v_cmp_1522_, v_x_1523_, v_rchild_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 3, v___x_1545_);
v___x_1547_ = v___x_1530_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_lchild_1525_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_key_1526_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_val_1527_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_ctor_set_uint8(v___x_1547_, sizeof(void*)*4, v___x_1544_);
return v___x_1547_;
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1530_);
v___x_1549_ = l_Lean_RBNode_del___redArg(v_cmp_1522_, v_x_1523_, v_rchild_1528_);
v___x_1550_ = l_Lean_RBNode_balRight___redArg(v_lchild_1525_, v_key_1526_, v_val_1527_, v___x_1549_);
return v___x_1550_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_cmp_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_RBNode_del___redArg(v_cmp_1554_, v_x_1555_, v_x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* v_cmp_1558_, lean_object* v_x_1559_, lean_object* v_t_1560_){
_start:
{
lean_object* v_t_1561_; lean_object* v___x_1562_; 
v_t_1561_ = l_Lean_RBNode_del___redArg(v_cmp_1558_, v_x_1559_, v_t_1560_);
v___x_1562_ = l_Lean_RBNode_setBlack___redArg(v_t_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* v_00_u03b1_1563_, lean_object* v_00_u03b2_1564_, lean_object* v_cmp_1565_, lean_object* v_x_1566_, lean_object* v_t_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_RBNode_erase___redArg(v_cmp_1565_, v_x_1566_, v_t_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* v_cmp_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_){
_start:
{
if (lean_obj_tag(v_x_1570_) == 0)
{
lean_object* v___x_1572_; 
lean_dec(v_x_1571_);
lean_dec_ref(v_cmp_1569_);
v___x_1572_ = lean_box(0);
return v___x_1572_;
}
else
{
lean_object* v_lchild_1573_; lean_object* v_key_1574_; lean_object* v_val_1575_; lean_object* v_rchild_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v_lchild_1573_ = lean_ctor_get(v_x_1570_, 0);
lean_inc(v_lchild_1573_);
v_key_1574_ = lean_ctor_get(v_x_1570_, 1);
lean_inc_n(v_key_1574_, 2);
v_val_1575_ = lean_ctor_get(v_x_1570_, 2);
lean_inc(v_val_1575_);
v_rchild_1576_ = lean_ctor_get(v_x_1570_, 3);
lean_inc(v_rchild_1576_);
lean_dec_ref_known(v_x_1570_, 4);
lean_inc_ref(v_cmp_1569_);
lean_inc(v_x_1571_);
v___x_1577_ = lean_apply_2(v_cmp_1569_, v_x_1571_, v_key_1574_);
v___x_1578_ = lean_unbox(v___x_1577_);
switch(v___x_1578_)
{
case 0:
{
lean_dec(v_rchild_1576_);
lean_dec(v_val_1575_);
lean_dec(v_key_1574_);
v_x_1570_ = v_lchild_1573_;
goto _start;
}
case 1:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec(v_rchild_1576_);
lean_dec(v_lchild_1573_);
lean_dec(v_x_1571_);
lean_dec_ref(v_cmp_1569_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_key_1574_);
lean_ctor_set(v___x_1580_, 1, v_val_1575_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
default: 
{
lean_dec(v_val_1575_);
lean_dec(v_key_1574_);
lean_dec(v_lchild_1573_);
v_x_1570_ = v_rchild_1576_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_cmp_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_RBNode_findCore___redArg(v_cmp_1585_, v_x_1586_, v_x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* v_cmp_1589_, lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1590_) == 0)
{
lean_object* v___x_1592_; 
lean_dec(v_x_1591_);
lean_dec_ref(v_cmp_1589_);
v___x_1592_ = lean_box(0);
return v___x_1592_;
}
else
{
lean_object* v_lchild_1593_; lean_object* v_key_1594_; lean_object* v_val_1595_; lean_object* v_rchild_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_lchild_1593_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_lchild_1593_);
v_key_1594_ = lean_ctor_get(v_x_1590_, 1);
lean_inc(v_key_1594_);
v_val_1595_ = lean_ctor_get(v_x_1590_, 2);
lean_inc(v_val_1595_);
v_rchild_1596_ = lean_ctor_get(v_x_1590_, 3);
lean_inc(v_rchild_1596_);
lean_dec_ref_known(v_x_1590_, 4);
lean_inc_ref(v_cmp_1589_);
lean_inc(v_x_1591_);
v___x_1597_ = lean_apply_2(v_cmp_1589_, v_x_1591_, v_key_1594_);
v___x_1598_ = lean_unbox(v___x_1597_);
switch(v___x_1598_)
{
case 0:
{
lean_dec(v_rchild_1596_);
lean_dec(v_val_1595_);
v_x_1590_ = v_lchild_1593_;
goto _start;
}
case 1:
{
lean_object* v___x_1600_; 
lean_dec(v_rchild_1596_);
lean_dec(v_lchild_1593_);
lean_dec(v_x_1591_);
lean_dec_ref(v_cmp_1589_);
v___x_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_val_1595_);
return v___x_1600_;
}
default: 
{
lean_dec(v_val_1595_);
lean_dec(v_lchild_1593_);
v_x_1590_ = v_rchild_1596_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* v_00_u03b1_1602_, lean_object* v_cmp_1603_, lean_object* v_00_u03b2_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_RBNode_find___redArg(v_cmp_1603_, v_x_1605_, v_x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* v_cmp_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
if (lean_obj_tag(v_x_1609_) == 0)
{
lean_dec(v_x_1610_);
lean_dec_ref(v_cmp_1608_);
return v_x_1611_;
}
else
{
lean_object* v_lchild_1612_; lean_object* v_key_1613_; lean_object* v_val_1614_; lean_object* v_rchild_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_lchild_1612_ = lean_ctor_get(v_x_1609_, 0);
lean_inc(v_lchild_1612_);
v_key_1613_ = lean_ctor_get(v_x_1609_, 1);
lean_inc_n(v_key_1613_, 2);
v_val_1614_ = lean_ctor_get(v_x_1609_, 2);
lean_inc(v_val_1614_);
v_rchild_1615_ = lean_ctor_get(v_x_1609_, 3);
lean_inc(v_rchild_1615_);
lean_dec_ref_known(v_x_1609_, 4);
lean_inc_ref(v_cmp_1608_);
lean_inc(v_x_1610_);
v___x_1616_ = lean_apply_2(v_cmp_1608_, v_x_1610_, v_key_1613_);
v___x_1617_ = lean_unbox(v___x_1616_);
switch(v___x_1617_)
{
case 0:
{
lean_dec(v_rchild_1615_);
lean_dec(v_val_1614_);
lean_dec(v_key_1613_);
v_x_1609_ = v_lchild_1612_;
goto _start;
}
case 1:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v_rchild_1615_);
lean_dec(v_lchild_1612_);
lean_dec(v_x_1611_);
lean_dec(v_x_1610_);
lean_dec_ref(v_cmp_1608_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_key_1613_);
lean_ctor_set(v___x_1619_, 1, v_val_1614_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
default: 
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v_lchild_1612_);
lean_dec(v_x_1611_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v_key_1613_);
lean_ctor_set(v___x_1621_, 1, v_val_1614_);
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
v_x_1609_ = v_rchild_1615_;
v_x_1611_ = v___x_1622_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* v_00_u03b1_1624_, lean_object* v_00_u03b2_1625_, lean_object* v_cmp_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_1626_, v_x_1627_, v_x_1628_, v_x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t v_color_1631_, lean_object* v_key_1632_, lean_object* v_x1_1633_, lean_object* v_x2_1634_, lean_object* v_x3_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1636_, 0, v_x1_1633_);
lean_ctor_set(v___x_1636_, 1, v_key_1632_);
lean_ctor_set(v___x_1636_, 2, v_x2_1634_);
lean_ctor_set(v___x_1636_, 3, v_x3_1635_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*4, v_color_1631_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* v_color_1637_, lean_object* v_key_1638_, lean_object* v_x1_1639_, lean_object* v_x2_1640_, lean_object* v_x3_1641_){
_start:
{
uint8_t v_color_88__boxed_1642_; lean_object* v_res_1643_; 
v_color_88__boxed_1642_ = lean_unbox(v_color_1637_);
v_res_1643_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_88__boxed_1642_, v_key_1638_, v_x1_1639_, v_x2_1640_, v_x3_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* v_f_1644_, lean_object* v_key_1645_, lean_object* v_val_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_apply_2(v_f_1644_, v_key_1645_, v_val_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* v_inst_1649_, lean_object* v_f_1650_, lean_object* v_lchild_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_RBNode_mapM___redArg(v_inst_1649_, v_f_1650_, v_lchild_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* v_inst_1654_, lean_object* v_f_1655_, lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 0)
{
lean_object* v_toPure_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec(v_f_1655_);
v_toPure_1657_ = lean_ctor_get(v_inst_1654_, 1);
lean_inc(v_toPure_1657_);
lean_dec_ref(v_inst_1654_);
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___x_1658_);
return v___x_1659_;
}
else
{
lean_object* v_toPure_1660_; lean_object* v_toSeq_1661_; uint8_t v_color_1662_; lean_object* v_lchild_1663_; lean_object* v_key_1664_; lean_object* v_val_1665_; lean_object* v_rchild_1666_; lean_object* v___f_1667_; lean_object* v___f_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_toPure_1660_ = lean_ctor_get(v_inst_1654_, 1);
lean_inc(v_toPure_1660_);
v_toSeq_1661_ = lean_ctor_get(v_inst_1654_, 2);
lean_inc_n(v_toSeq_1661_, 3);
v_color_1662_ = lean_ctor_get_uint8(v_x_1656_, sizeof(void*)*4);
v_lchild_1663_ = lean_ctor_get(v_x_1656_, 0);
lean_inc(v_lchild_1663_);
v_key_1664_ = lean_ctor_get(v_x_1656_, 1);
lean_inc_n(v_key_1664_, 2);
v_val_1665_ = lean_ctor_get(v_x_1656_, 2);
lean_inc(v_val_1665_);
v_rchild_1666_ = lean_ctor_get(v_x_1656_, 3);
lean_inc(v_rchild_1666_);
lean_dec_ref_known(v_x_1656_, 4);
lean_inc_n(v_f_1655_, 2);
lean_inc_ref(v_inst_1654_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1667_, 0, v_inst_1654_);
lean_closure_set(v___f_1667_, 1, v_f_1655_);
lean_closure_set(v___f_1667_, 2, v_rchild_1666_);
v___f_1668_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1668_, 0, v_f_1655_);
lean_closure_set(v___f_1668_, 1, v_key_1664_);
lean_closure_set(v___f_1668_, 2, v_val_1665_);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1669_, 0, v_inst_1654_);
lean_closure_set(v___f_1669_, 1, v_f_1655_);
lean_closure_set(v___f_1669_, 2, v_lchild_1663_);
v___x_1670_ = lean_box(v_color_1662_);
v___f_1671_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1671_, 0, v___x_1670_);
lean_closure_set(v___f_1671_, 1, v_key_1664_);
v___x_1672_ = lean_apply_2(v_toPure_1660_, lean_box(0), v___f_1671_);
v___x_1673_ = lean_apply_4(v_toSeq_1661_, lean_box(0), lean_box(0), v___x_1672_, v___f_1669_);
v___x_1674_ = lean_apply_4(v_toSeq_1661_, lean_box(0), lean_box(0), v___x_1673_, v___f_1668_);
v___x_1675_ = lean_apply_4(v_toSeq_1661_, lean_box(0), lean_box(0), v___x_1674_, v___f_1667_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* v_inst_1676_, lean_object* v_f_1677_, lean_object* v_rchild_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_RBNode_mapM___redArg(v_inst_1676_, v_f_1677_, v_rchild_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* v_00_u03b1_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_00_u03b3_1683_, lean_object* v_M_1684_, lean_object* v_inst_1685_, lean_object* v_f_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_RBNode_mapM___redArg(v_inst_1685_, v_f_1686_, v_x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* v_f_1689_, lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_dec(v_f_1689_);
v___x_1691_ = lean_box(0);
return v___x_1691_;
}
else
{
uint8_t v_color_1692_; lean_object* v_lchild_1693_; lean_object* v_key_1694_; lean_object* v_val_1695_; lean_object* v_rchild_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1706_; 
v_color_1692_ = lean_ctor_get_uint8(v_x_1690_, sizeof(void*)*4);
v_lchild_1693_ = lean_ctor_get(v_x_1690_, 0);
v_key_1694_ = lean_ctor_get(v_x_1690_, 1);
v_val_1695_ = lean_ctor_get(v_x_1690_, 2);
v_rchild_1696_ = lean_ctor_get(v_x_1690_, 3);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1690_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1698_ = v_x_1690_;
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_rchild_1696_);
lean_inc(v_val_1695_);
lean_inc(v_key_1694_);
lean_inc(v_lchild_1693_);
lean_dec(v_x_1690_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_inc_n(v_f_1689_, 2);
v___x_1700_ = l_Lean_RBNode_map___redArg(v_f_1689_, v_lchild_1693_);
lean_inc(v_key_1694_);
v___x_1701_ = lean_apply_2(v_f_1689_, v_key_1694_, v_val_1695_);
v___x_1702_ = l_Lean_RBNode_map___redArg(v_f_1689_, v_rchild_1696_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 3, v___x_1702_);
lean_ctor_set(v___x_1698_, 2, v___x_1701_);
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1704_ = v___x_1698_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_key_1694_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v___x_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1705_, sizeof(void*)*4, v_color_1692_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* v_00_u03b1_1707_, lean_object* v_00_u03b2_1708_, lean_object* v_00_u03b3_1709_, lean_object* v_f_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_RBNode_map___redArg(v_f_1710_, v_x_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
if (lean_obj_tag(v_x_1714_) == 0)
{
return v_x_1713_;
}
else
{
lean_object* v_lchild_1715_; lean_object* v_key_1716_; lean_object* v_val_1717_; lean_object* v_rchild_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_lchild_1715_ = lean_ctor_get(v_x_1714_, 0);
v_key_1716_ = lean_ctor_get(v_x_1714_, 1);
v_val_1717_ = lean_ctor_get(v_x_1714_, 2);
v_rchild_1718_ = lean_ctor_get(v_x_1714_, 3);
v___x_1719_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1713_, v_lchild_1715_);
lean_inc(v_val_1717_);
lean_inc(v_key_1716_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_key_1716_);
lean_ctor_set(v___x_1720_, 1, v_val_1717_);
v___x_1721_ = lean_array_push(v___x_1719_, v___x_1720_);
v_x_1713_ = v___x_1721_;
v_x_1714_ = v_rchild_1718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1723_, v_x_1724_);
lean_dec(v_x_1724_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* v_n_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
v___x_1730_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_1729_, v_n_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* v_n_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_RBNode_toArray___redArg(v_n_1731_);
lean_dec(v_n_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* v_00_u03b1_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_n_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_RBNode_toArray___redArg(v_n_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_n_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_RBNode_toArray(v_00_u03b1_1737_, v_00_u03b2_1738_, v_n_1739_);
lean_dec(v_n_1739_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1743_, v_x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(v_00_u03b1_1746_, v_00_u03b2_1747_, v_x_1748_, v_x_1749_);
lean_dec(v_x_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b2_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_, lean_object* v_cmp_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_box(0);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_cmp_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_mkRBMap(v_00_u03b1_1758_, v_00_u03b2_1759_, v_cmp_1760_);
lean_dec_ref(v_cmp_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_box(0);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_RBMap_empty(v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec_ref(v___y_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_, lean_object* v_cmp_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_box(0);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_cmp_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_1774_, v_00_u03b2_1775_, v_cmp_1776_);
lean_dec_ref(v_cmp_1776_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* v_00_u03b1_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_cmp_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_box(0);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_cmp_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_instInhabitedRBMap(v_00_u03b1_1782_, v_00_u03b2_1783_, v_cmp_1784_);
lean_dec_ref(v_cmp_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* v_f_1786_, lean_object* v_t_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_RBNode_depth___redArg(v_f_1786_, v_t_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* v_f_1789_, lean_object* v_t_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_RBMap_depth___redArg(v_f_1789_, v_t_1790_);
lean_dec(v_t_1790_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_cmp_1794_, lean_object* v_f_1795_, lean_object* v_t_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_RBNode_depth___redArg(v_f_1795_, v_t_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_cmp_1800_, lean_object* v_f_1801_, lean_object* v_t_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_RBMap_depth(v_00_u03b1_1798_, v_00_u03b2_1799_, v_cmp_1800_, v_f_1801_, v_t_1802_);
lean_dec(v_t_1802_);
lean_dec_ref(v_cmp_1800_);
return v_res_1803_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* v_t_1804_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Lean_RBNode_isSingleton___redArg(v_t_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* v_t_1806_){
_start:
{
uint8_t v_res_1807_; lean_object* v_r_1808_; 
v_res_1807_ = l_Lean_RBMap_isSingleton___redArg(v_t_1806_);
lean_dec(v_t_1806_);
v_r_1808_ = lean_box(v_res_1807_);
return v_r_1808_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_cmp_1811_, lean_object* v_t_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Lean_RBNode_isSingleton___redArg(v_t_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* v_00_u03b1_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_cmp_1816_, lean_object* v_t_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Lean_RBMap_isSingleton(v_00_u03b1_1814_, v_00_u03b2_1815_, v_cmp_1816_, v_t_1817_);
lean_dec(v_t_1817_);
lean_dec_ref(v_cmp_1816_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* v_f_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_RBNode_fold___redArg(v_f_1820_, v_x_1821_, v_x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_00_u03c3_1826_, lean_object* v_cmp_1827_, lean_object* v_f_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_RBNode_fold___redArg(v_f_1828_, v_x_1829_, v_x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* v_00_u03b1_1832_, lean_object* v_00_u03b2_1833_, lean_object* v_00_u03c3_1834_, lean_object* v_cmp_1835_, lean_object* v_f_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_RBMap_fold(v_00_u03b1_1832_, v_00_u03b2_1833_, v_00_u03c3_1834_, v_cmp_1835_, v_f_1836_, v_x_1837_, v_x_1838_);
lean_dec_ref(v_cmp_1835_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* v_f_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_RBNode_revFold___redArg(v_f_1840_, v_x_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* v_00_u03b1_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_00_u03c3_1846_, lean_object* v_cmp_1847_, lean_object* v_f_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_RBNode_revFold___redArg(v_f_1848_, v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_00_u03b2_1853_, lean_object* v_00_u03c3_1854_, lean_object* v_cmp_1855_, lean_object* v_f_1856_, lean_object* v_x_1857_, lean_object* v_x_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_RBMap_revFold(v_00_u03b1_1852_, v_00_u03b2_1853_, v_00_u03c3_1854_, v_cmp_1855_, v_f_1856_, v_x_1857_, v_x_1858_);
lean_dec_ref(v_cmp_1855_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* v_inst_1860_, lean_object* v_f_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_RBNode_foldM___redArg(v_inst_1860_, v_f_1861_, v_x_1862_, v_x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* v_00_u03b1_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_00_u03c3_1867_, lean_object* v_cmp_1868_, lean_object* v_m_1869_, lean_object* v_inst_1870_, lean_object* v_f_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_RBNode_foldM___redArg(v_inst_1870_, v_f_1871_, v_x_1872_, v_x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_00_u03b2_1876_, lean_object* v_00_u03c3_1877_, lean_object* v_cmp_1878_, lean_object* v_m_1879_, lean_object* v_inst_1880_, lean_object* v_f_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_RBMap_foldM(v_00_u03b1_1875_, v_00_u03b2_1876_, v_00_u03c3_1877_, v_cmp_1878_, v_m_1879_, v_inst_1880_, v_f_1881_, v_x_1882_, v_x_1883_);
lean_dec_ref(v_cmp_1878_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* v_f_1885_, lean_object* v_x_1886_, lean_object* v_k_1887_, lean_object* v_v_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_apply_2(v_f_1885_, v_k_1887_, v_v_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* v_inst_1890_, lean_object* v_f_1891_, lean_object* v_t_1892_){
_start:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1893_, 0, v_f_1891_);
v___x_1894_ = lean_box(0);
v___x_1895_ = l_Lean_RBNode_foldM___redArg(v_inst_1890_, v___f_1893_, v___x_1894_, v_t_1892_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* v_00_u03b1_1896_, lean_object* v_00_u03b2_1897_, lean_object* v_cmp_1898_, lean_object* v_m_1899_, lean_object* v_inst_1900_, lean_object* v_f_1901_, lean_object* v_t_1902_){
_start:
{
lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1903_, 0, v_f_1901_);
v___x_1904_ = lean_box(0);
v___x_1905_ = l_Lean_RBNode_foldM___redArg(v_inst_1900_, v___f_1903_, v___x_1904_, v_t_1902_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_cmp_1908_, lean_object* v_m_1909_, lean_object* v_inst_1910_, lean_object* v_f_1911_, lean_object* v_t_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_RBMap_forM(v_00_u03b1_1906_, v_00_u03b2_1907_, v_cmp_1908_, v_m_1909_, v_inst_1910_, v_f_1911_, v_t_1912_);
lean_dec_ref(v_cmp_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* v_f_1914_, lean_object* v_a_1915_, lean_object* v_b_1916_, lean_object* v_acc_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_a_1915_);
lean_ctor_set(v___x_1918_, 1, v_b_1916_);
v___x_1919_ = lean_apply_2(v_f_1914_, v___x_1918_, v_acc_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* v_inst_1920_, lean_object* v_t_1921_, lean_object* v_init_1922_, lean_object* v_f_1923_){
_start:
{
lean_object* v_toApplicative_1924_; lean_object* v_toBind_1925_; lean_object* v_toPure_1926_; lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; 
v_toApplicative_1924_ = lean_ctor_get(v_inst_1920_, 0);
v_toBind_1925_ = lean_ctor_get(v_inst_1920_, 1);
lean_inc(v_toBind_1925_);
v_toPure_1926_ = lean_ctor_get(v_toApplicative_1924_, 1);
lean_inc(v_toPure_1926_);
v___f_1927_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1927_, 0, v_f_1923_);
v___x_1928_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1920_, v___f_1927_, v_t_1921_, v_init_1922_);
v___f_1929_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1929_, 0, v_toPure_1926_);
v___x_1930_ = lean_apply_4(v_toBind_1925_, lean_box(0), lean_box(0), v___x_1928_, v___f_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* v_00_u03b1_1931_, lean_object* v_00_u03b2_1932_, lean_object* v_00_u03c3_1933_, lean_object* v_cmp_1934_, lean_object* v_m_1935_, lean_object* v_inst_1936_, lean_object* v_t_1937_, lean_object* v_init_1938_, lean_object* v_f_1939_){
_start:
{
lean_object* v_toApplicative_1940_; lean_object* v_toBind_1941_; lean_object* v_toPure_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; 
v_toApplicative_1940_ = lean_ctor_get(v_inst_1936_, 0);
v_toBind_1941_ = lean_ctor_get(v_inst_1936_, 1);
lean_inc(v_toBind_1941_);
v_toPure_1942_ = lean_ctor_get(v_toApplicative_1940_, 1);
lean_inc(v_toPure_1942_);
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1943_, 0, v_f_1939_);
v___x_1944_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1936_, v___f_1943_, v_t_1937_, v_init_1938_);
v___f_1945_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1945_, 0, v_toPure_1942_);
v___x_1946_ = lean_apply_4(v_toBind_1941_, lean_box(0), lean_box(0), v___x_1944_, v___f_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_00_u03b2_1948_, lean_object* v_00_u03c3_1949_, lean_object* v_cmp_1950_, lean_object* v_m_1951_, lean_object* v_inst_1952_, lean_object* v_t_1953_, lean_object* v_init_1954_, lean_object* v_f_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_RBMap_forIn(v_00_u03b1_1947_, v_00_u03b2_1948_, v_00_u03c3_1949_, v_cmp_1950_, v_m_1951_, v_inst_1952_, v_t_1953_, v_init_1954_, v_f_1955_);
lean_dec_ref(v_cmp_1950_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* v___y_1957_, lean_object* v_a_1958_, lean_object* v_b_1959_, lean_object* v_acc_1960_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_a_1958_);
lean_ctor_set(v___x_1961_, 1, v_b_1959_);
v___x_1962_ = lean_apply_2(v___y_1957_, v___x_1961_, v_acc_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1963_, lean_object* v_00_u03b2_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_toApplicative_1968_; lean_object* v_toBind_1969_; lean_object* v_toPure_1970_; lean_object* v___f_1971_; lean_object* v___x_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; 
v_toApplicative_1968_ = lean_ctor_get(v_inst_1963_, 0);
v_toBind_1969_ = lean_ctor_get(v_inst_1963_, 1);
lean_inc(v_toBind_1969_);
v_toPure_1970_ = lean_ctor_get(v_toApplicative_1968_, 1);
lean_inc(v_toPure_1970_);
v___f_1971_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1971_, 0, v___y_1967_);
v___x_1972_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1963_, v___f_1971_, v___y_1965_, v___y_1966_);
v___f_1973_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1973_, 0, v_toPure_1970_);
v___x_1974_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v___x_1972_, v___f_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* v_inst_1975_){
_start:
{
lean_object* v___f_1976_; 
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1976_, 0, v_inst_1975_);
return v___f_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* v_00_u03b1_1977_, lean_object* v_00_u03b2_1978_, lean_object* v_cmp_1979_, lean_object* v_m_1980_, lean_object* v_inst_1981_){
_start:
{
lean_object* v___f_1982_; 
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1982_, 0, v_inst_1981_);
return v___f_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1983_, lean_object* v_00_u03b2_1984_, lean_object* v_cmp_1985_, lean_object* v_m_1986_, lean_object* v_inst_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_RBMap_instForInProdOfMonad(v_00_u03b1_1983_, v_00_u03b2_1984_, v_cmp_1985_, v_m_1986_, v_inst_1987_);
lean_dec_ref(v_cmp_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* v_x_1989_){
_start:
{
if (lean_obj_tag(v_x_1989_) == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = 1;
return v___x_1990_;
}
else
{
uint8_t v___x_1991_; 
v___x_1991_ = 0;
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* v_x_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_RBMap_isEmpty___redArg(v_x_1992_);
lean_dec(v_x_1992_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object* v_00_u03b1_1995_, lean_object* v_00_u03b2_1996_, lean_object* v_cmp_1997_, lean_object* v_x_1998_){
_start:
{
if (lean_obj_tag(v_x_1998_) == 0)
{
uint8_t v___x_1999_; 
v___x_1999_ = 1;
return v___x_1999_;
}
else
{
uint8_t v___x_2000_; 
v___x_2000_ = 0;
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* v_00_u03b1_2001_, lean_object* v_00_u03b2_2002_, lean_object* v_cmp_2003_, lean_object* v_x_2004_){
_start:
{
uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_res_2005_ = l_Lean_RBMap_isEmpty(v_00_u03b1_2001_, v_00_u03b2_2002_, v_cmp_2003_, v_x_2004_);
lean_dec(v_x_2004_);
lean_dec_ref(v_cmp_2003_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* v_ps_2007_, lean_object* v_k_2008_, lean_object* v_v_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_k_2008_);
lean_ctor_set(v___x_2010_, 1, v_v_2009_);
v___x_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v_ps_2007_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* v_x_2013_){
_start:
{
lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___f_2014_ = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Lean_RBNode_revFold___redArg(v___f_2014_, v___x_2015_, v_x_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_cmp_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_RBMap_toList___redArg(v_x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_cmp_2024_, lean_object* v_x_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_RBMap_toList(v_00_u03b1_2022_, v_00_u03b2_2023_, v_cmp_2024_, v_x_2025_);
lean_dec_ref(v_cmp_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* v_ps_2027_, lean_object* v_k_2028_, lean_object* v_v_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_k_2028_);
lean_ctor_set(v___x_2030_, 1, v_v_2029_);
v___x_2031_ = lean_array_push(v_ps_2027_, v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* v_x_2035_){
_start:
{
lean_object* v___f_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___f_2036_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
v___x_2037_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
v___x_2038_ = l_Lean_RBNode_fold___redArg(v___f_2036_, v___x_2037_, v_x_2035_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_cmp_2041_, lean_object* v_x_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_RBMap_toArray___redArg(v_x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* v_00_u03b1_2044_, lean_object* v_00_u03b2_2045_, lean_object* v_cmp_2046_, lean_object* v_x_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_RBMap_toArray(v_00_u03b1_2044_, v_00_u03b2_2045_, v_cmp_2046_, v_x_2047_);
lean_dec_ref(v_cmp_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_RBNode_min___redArg(v_x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_box(0);
return v___x_2051_;
}
else
{
lean_object* v_val_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2068_; 
v_val_2052_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2054_ = v___x_2050_;
v_isShared_2055_ = v_isSharedCheck_2068_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_val_2052_);
lean_dec(v___x_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2068_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_fst_2056_; lean_object* v_snd_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2067_; 
v_fst_2056_ = lean_ctor_get(v_val_2052_, 0);
v_snd_2057_ = lean_ctor_get(v_val_2052_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_val_2052_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2059_ = v_val_2052_;
v_isShared_2060_ = v_isSharedCheck_2067_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snd_2057_);
lean_inc(v_fst_2056_);
lean_dec(v_val_2052_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2067_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_snd_2057_);
v___x_2062_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2064_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2062_);
v___x_2064_ = v___x_2054_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Lean_RBMap_min___redArg(v_x_2069_);
lean_dec(v_x_2069_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* v_00_u03b1_2071_, lean_object* v_00_u03b2_2072_, lean_object* v_cmp_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_RBNode_min___redArg(v_x_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_box(0);
return v___x_2076_;
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2093_; 
v_val_2077_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2093_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_val_2077_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2093_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2092_; 
v_fst_2081_ = lean_ctor_get(v_val_2077_, 0);
v_snd_2082_ = lean_ctor_get(v_val_2077_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_val_2077_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2084_ = v_val_2077_;
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_inc(v_fst_2081_);
lean_dec(v_val_2077_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_fst_2081_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_snd_2082_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2087_);
v___x_2089_ = v___x_2079_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_00_u03b2_2095_, lean_object* v_cmp_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_RBMap_min(v_00_u03b1_2094_, v_00_u03b2_2095_, v_cmp_2096_, v_x_2097_);
lean_dec(v_x_2097_);
lean_dec_ref(v_cmp_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* v_x_2099_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_RBNode_max___redArg(v_x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_box(0);
return v___x_2101_;
}
else
{
lean_object* v_val_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2118_; 
v_val_2102_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2104_ = v___x_2100_;
v_isShared_2105_ = v_isSharedCheck_2118_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_val_2102_);
lean_dec(v___x_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2118_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_fst_2106_; lean_object* v_snd_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_fst_2106_ = lean_ctor_get(v_val_2102_, 0);
v_snd_2107_ = lean_ctor_get(v_val_2102_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_val_2102_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2109_ = v_val_2102_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_snd_2107_);
lean_inc(v_fst_2106_);
lean_dec(v_val_2102_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_fst_2106_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_snd_2107_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2112_);
v___x_2114_ = v___x_2104_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* v_x_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_RBMap_max___redArg(v_x_2119_);
lean_dec(v_x_2119_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* v_00_u03b1_2121_, lean_object* v_00_u03b2_2122_, lean_object* v_cmp_2123_, lean_object* v_x_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_RBNode_max___redArg(v_x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_box(0);
return v___x_2126_;
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2143_; 
v_val_2127_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2129_ = v___x_2125_;
v_isShared_2130_ = v_isSharedCheck_2143_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_val_2127_);
lean_dec(v___x_2125_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2143_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_fst_2131_; lean_object* v_snd_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
v_fst_2131_ = lean_ctor_get(v_val_2127_, 0);
v_snd_2132_ = lean_ctor_get(v_val_2127_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_val_2127_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v_val_2127_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_snd_2132_);
lean_inc(v_fst_2131_);
lean_dec(v_val_2127_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_fst_2131_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_snd_2132_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2137_);
v___x_2139_ = v___x_2129_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_00_u03b2_2145_, lean_object* v_cmp_2146_, lean_object* v_x_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_RBMap_max(v_00_u03b1_2144_, v_00_u03b2_2145_, v_cmp_2146_, v_x_2147_);
lean_dec(v_x_2147_);
lean_dec_ref(v_cmp_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* v___x_2152_, lean_object* v_m_2153_, lean_object* v_prec_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2155_ = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
v___x_2156_ = l_Lean_RBMap_toList___redArg(v_m_2153_);
v___x_2157_ = l_List_repr___redArg(v___x_2152_, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2155_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Repr_addAppParen(v___x_2158_, v_prec_2154_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* v___x_2160_, lean_object* v_m_2161_, lean_object* v_prec_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_2160_, v_m_2161_, v_prec_2162_);
lean_dec(v_prec_2162_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* v_inst_2164_, lean_object* v_inst_2165_){
_start:
{
lean_object* v___f_2166_; lean_object* v___x_2167_; lean_object* v___f_2168_; 
v___f_2166_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2166_, 0, v_inst_2165_);
v___x_2167_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2167_, 0, lean_box(0));
lean_closure_set(v___x_2167_, 1, lean_box(0));
lean_closure_set(v___x_2167_, 2, v_inst_2164_);
lean_closure_set(v___x_2167_, 3, v___f_2166_);
v___f_2168_ = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2168_, 0, v___x_2167_);
return v___f_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* v_00_u03b1_2169_, lean_object* v_00_u03b2_2170_, lean_object* v_cmp_2171_, lean_object* v_inst_2172_, lean_object* v_inst_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_RBMap_instRepr___redArg(v_inst_2172_, v_inst_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_cmp_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_RBMap_instRepr(v_00_u03b1_2175_, v_00_u03b2_2176_, v_cmp_2177_, v_inst_2178_, v_inst_2179_);
lean_dec_ref(v_cmp_2177_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* v_cmp_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_RBNode_insert___redArg(v_cmp_2181_, v_x_2182_, v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* v_00_u03b1_2186_, lean_object* v_00_u03b2_2187_, lean_object* v_cmp_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_RBNode_insert___redArg(v_cmp_2188_, v_x_2189_, v_x_2190_, v_x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* v_cmp_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_RBNode_erase___redArg(v_cmp_2193_, v_x_2195_, v_x_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* v_00_u03b1_2197_, lean_object* v_00_u03b2_2198_, lean_object* v_cmp_2199_, lean_object* v_x_2200_, lean_object* v_x_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_RBNode_erase___redArg(v_cmp_2199_, v_x_2201_, v_x_2200_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* v_cmp_2203_, lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 0)
{
lean_object* v___x_2205_; 
lean_dec_ref(v_cmp_2203_);
v___x_2205_ = lean_box(0);
return v___x_2205_;
}
else
{
lean_object* v_head_2206_; lean_object* v_tail_2207_; lean_object* v_fst_2208_; lean_object* v_snd_2209_; lean_object* v_val_2210_; lean_object* v___x_2211_; 
v_head_2206_ = lean_ctor_get(v_x_2204_, 0);
lean_inc(v_head_2206_);
v_tail_2207_ = lean_ctor_get(v_x_2204_, 1);
lean_inc(v_tail_2207_);
lean_dec_ref_known(v_x_2204_, 2);
v_fst_2208_ = lean_ctor_get(v_head_2206_, 0);
lean_inc(v_fst_2208_);
v_snd_2209_ = lean_ctor_get(v_head_2206_, 1);
lean_inc(v_snd_2209_);
lean_dec(v_head_2206_);
lean_inc_ref(v_cmp_2203_);
v_val_2210_ = l_Lean_RBMap_ofList___redArg(v_cmp_2203_, v_tail_2207_);
v___x_2211_ = l_Lean_RBNode_insert___redArg(v_cmp_2203_, v_val_2210_, v_fst_2208_, v_snd_2209_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_cmp_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_RBMap_ofList___redArg(v_cmp_2214_, v_x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* v_cmp_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_RBNode_findCore___redArg(v_cmp_2217_, v_x_2218_, v_x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* v_00_u03b1_2221_, lean_object* v_00_u03b2_2222_, lean_object* v_cmp_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_RBNode_findCore___redArg(v_cmp_2223_, v_x_2224_, v_x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* v_cmp_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_RBNode_find___redArg(v_cmp_2227_, v_x_2228_, v_x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* v_00_u03b1_2231_, lean_object* v_00_u03b2_2232_, lean_object* v_cmp_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_RBNode_find___redArg(v_cmp_2233_, v_x_2234_, v_x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* v_cmp_2237_, lean_object* v_t_2238_, lean_object* v_k_2239_, lean_object* v_v_u2080_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_RBNode_find___redArg(v_cmp_2237_, v_t_2238_, v_k_2239_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_inc(v_v_u2080_2240_);
return v_v_u2080_2240_;
}
else
{
lean_object* v_val_2242_; 
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v___x_2241_, 1);
return v_val_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* v_cmp_2243_, lean_object* v_t_2244_, lean_object* v_k_2245_, lean_object* v_v_u2080_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_RBMap_findD___redArg(v_cmp_2243_, v_t_2244_, v_k_2245_, v_v_u2080_2246_);
lean_dec(v_v_u2080_2246_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* v_00_u03b1_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_cmp_2250_, lean_object* v_t_2251_, lean_object* v_k_2252_, lean_object* v_v_u2080_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_RBNode_find___redArg(v_cmp_2250_, v_t_2251_, v_k_2252_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_inc(v_v_u2080_2253_);
return v_v_u2080_2253_;
}
else
{
lean_object* v_val_2255_; 
v_val_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_val_2255_);
lean_dec_ref_known(v___x_2254_, 1);
return v_val_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_00_u03b2_2257_, lean_object* v_cmp_2258_, lean_object* v_t_2259_, lean_object* v_k_2260_, lean_object* v_v_u2080_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_RBMap_findD(v_00_u03b1_2256_, v_00_u03b2_2257_, v_cmp_2258_, v_t_2259_, v_k_2260_, v_v_u2080_2261_);
lean_dec(v_v_u2080_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* v_cmp_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_box(0);
v___x_2267_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2263_, v_x_2264_, v_x_2265_, v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* v_00_u03b1_2268_, lean_object* v_00_u03b2_2269_, lean_object* v_cmp_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
v___x_2274_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2270_, v_x_2271_, v_x_2272_, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object* v_cmp_2275_, lean_object* v_t_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_RBNode_find___redArg(v_cmp_2275_, v_t_2276_, v_a_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
uint8_t v___x_2279_; 
v___x_2279_ = 0;
return v___x_2279_;
}
else
{
uint8_t v___x_2280_; 
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = 1;
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* v_cmp_2281_, lean_object* v_t_2282_, lean_object* v_a_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Lean_RBMap_contains___redArg(v_cmp_2281_, v_t_2282_, v_a_2283_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_cmp_2288_, lean_object* v_t_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_RBNode_find___redArg(v_cmp_2288_, v_t_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2291_) == 0)
{
uint8_t v___x_2292_; 
v___x_2292_ = 0;
return v___x_2292_;
}
else
{
uint8_t v___x_2293_; 
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = 1;
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_00_u03b2_2295_, lean_object* v_cmp_2296_, lean_object* v_t_2297_, lean_object* v_a_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Lean_RBMap_contains(v_00_u03b1_2294_, v_00_u03b2_2295_, v_cmp_2296_, v_t_2297_, v_a_2298_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* v_cmp_2301_, lean_object* v_r_2302_, lean_object* v_p_2303_){
_start:
{
lean_object* v_fst_2304_; lean_object* v_snd_2305_; lean_object* v___x_2306_; 
v_fst_2304_ = lean_ctor_get(v_p_2303_, 0);
lean_inc(v_fst_2304_);
v_snd_2305_ = lean_ctor_get(v_p_2303_, 1);
lean_inc(v_snd_2305_);
lean_dec_ref(v_p_2303_);
v___x_2306_ = l_Lean_RBNode_insert___redArg(v_cmp_2301_, v_r_2302_, v_fst_2304_, v_snd_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* v_l_2307_, lean_object* v_cmp_2308_){
_start:
{
lean_object* v___f_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2309_, 0, v_cmp_2308_);
v___x_2310_ = lean_box(0);
v___x_2311_ = l_List_foldl___redArg(v___f_2309_, v___x_2310_, v_l_2307_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_l_2314_, lean_object* v_cmp_2315_){
_start:
{
lean_object* v___f_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2316_, 0, v_cmp_2315_);
v___x_2317_ = lean_box(0);
v___x_2318_ = l_List_foldl___redArg(v___f_2316_, v___x_2317_, v_l_2314_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* v_cmp_2319_, lean_object* v_x1_2320_, lean_object* v_x2_2321_){
_start:
{
lean_object* v_fst_2322_; lean_object* v_snd_2323_; lean_object* v___x_2324_; 
v_fst_2322_ = lean_ctor_get(v_x2_2321_, 0);
lean_inc(v_fst_2322_);
v_snd_2323_ = lean_ctor_get(v_x2_2321_, 1);
lean_inc(v_snd_2323_);
lean_dec_ref(v_x2_2321_);
v___x_2324_ = l_Lean_RBNode_insert___redArg(v_cmp_2319_, v_x1_2320_, v_fst_2322_, v_snd_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* v_l_2344_, lean_object* v_cmp_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2346_ = lean_box(0);
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_array_get_size(v_l_2344_);
v___x_2349_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2350_ = lean_nat_dec_lt(v___x_2347_, v___x_2348_);
if (v___x_2350_ == 0)
{
lean_dec_ref(v_cmp_2345_);
lean_dec_ref(v_l_2344_);
return v___x_2346_;
}
else
{
lean_object* v___f_2351_; uint8_t v___x_2352_; 
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2351_, 0, v_cmp_2345_);
v___x_2352_ = lean_nat_dec_le(v___x_2348_, v___x_2348_);
if (v___x_2352_ == 0)
{
if (v___x_2350_ == 0)
{
lean_dec_ref(v___f_2351_);
lean_dec_ref(v_l_2344_);
return v___x_2346_;
}
else
{
size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = ((size_t)0ULL);
v___x_2354_ = lean_usize_of_nat(v___x_2348_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2349_, v___f_2351_, v_l_2344_, v___x_2353_, v___x_2354_, v___x_2346_);
return v___x_2355_;
}
}
else
{
size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((size_t)0ULL);
v___x_2357_ = lean_usize_of_nat(v___x_2348_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2349_, v___f_2351_, v_l_2344_, v___x_2356_, v___x_2357_, v___x_2346_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* v_00_u03b1_2359_, lean_object* v_00_u03b2_2360_, lean_object* v_l_2361_, lean_object* v_cmp_2362_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = lean_array_get_size(v_l_2361_);
v___x_2366_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2367_ = lean_nat_dec_lt(v___x_2364_, v___x_2365_);
if (v___x_2367_ == 0)
{
lean_dec_ref(v_cmp_2362_);
lean_dec_ref(v_l_2361_);
return v___x_2363_;
}
else
{
lean_object* v___f_2368_; uint8_t v___x_2369_; 
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2368_, 0, v_cmp_2362_);
v___x_2369_ = lean_nat_dec_le(v___x_2365_, v___x_2365_);
if (v___x_2369_ == 0)
{
if (v___x_2367_ == 0)
{
lean_dec_ref(v___f_2368_);
lean_dec_ref(v_l_2361_);
return v___x_2363_;
}
else
{
size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = lean_usize_of_nat(v___x_2365_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2366_, v___f_2368_, v_l_2361_, v___x_2370_, v___x_2371_, v___x_2363_);
return v___x_2372_;
}
}
else
{
size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = ((size_t)0ULL);
v___x_2374_ = lean_usize_of_nat(v___x_2365_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2366_, v___f_2368_, v_l_2361_, v___x_2373_, v___x_2374_, v___x_2363_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_RBNode_all___redArg(v_x_2377_, v_x_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_res_2381_ = l_Lean_RBMap_all___redArg(v_x_2379_, v_x_2380_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object* v_00_u03b1_2383_, lean_object* v_00_u03b2_2384_, lean_object* v_cmp_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_){
_start:
{
uint8_t v___x_2388_; 
v___x_2388_ = l_Lean_RBNode_all___redArg(v_x_2387_, v_x_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_00_u03b2_2390_, lean_object* v_cmp_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
uint8_t v_res_2394_; lean_object* v_r_2395_; 
v_res_2394_ = l_Lean_RBMap_all(v_00_u03b1_2389_, v_00_u03b2_2390_, v_cmp_2391_, v_x_2392_, v_x_2393_);
lean_dec_ref(v_cmp_2391_);
v_r_2395_ = lean_box(v_res_2394_);
return v_r_2395_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object* v_x_2396_, lean_object* v_x_2397_){
_start:
{
uint8_t v___x_2398_; 
v___x_2398_ = l_Lean_RBNode_any___redArg(v_x_2397_, v_x_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* v_x_2399_, lean_object* v_x_2400_){
_start:
{
uint8_t v_res_2401_; lean_object* v_r_2402_; 
v_res_2401_ = l_Lean_RBMap_any___redArg(v_x_2399_, v_x_2400_);
v_r_2402_ = lean_box(v_res_2401_);
return v_r_2402_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object* v_00_u03b1_2403_, lean_object* v_00_u03b2_2404_, lean_object* v_cmp_2405_, lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
uint8_t v___x_2408_; 
v___x_2408_ = l_Lean_RBNode_any___redArg(v_x_2407_, v_x_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_00_u03b2_2410_, lean_object* v_cmp_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Lean_RBMap_any(v_00_u03b1_2409_, v_00_u03b2_2410_, v_cmp_2411_, v_x_2412_, v_x_2413_);
lean_dec_ref(v_cmp_2411_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
if (lean_obj_tag(v_x_2417_) == 0)
{
return v_x_2416_;
}
else
{
lean_object* v_lchild_2418_; lean_object* v_rchild_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_lchild_2418_ = lean_ctor_get(v_x_2417_, 0);
v_rchild_2419_ = lean_ctor_get(v_x_2417_, 3);
v___x_2420_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2416_, v_lchild_2418_);
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_add(v___x_2420_, v___x_2421_);
lean_dec(v___x_2420_);
v_x_2416_ = v___x_2422_;
v_x_2417_ = v_rchild_2419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2424_, v_x_2425_);
lean_dec(v_x_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* v_m_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_2428_, v_m_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* v_m_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_RBMap_size___redArg(v_m_2430_);
lean_dec(v_m_2430_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* v_00_u03b1_2432_, lean_object* v_00_u03b2_2433_, lean_object* v_cmp_2434_, lean_object* v_m_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_RBMap_size___redArg(v_m_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_00_u03b2_2438_, lean_object* v_cmp_2439_, lean_object* v_m_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_RBMap_size(v_00_u03b1_2437_, v_00_u03b2_2438_, v_cmp_2439_, v_m_2440_);
lean_dec(v_m_2440_);
lean_dec_ref(v_cmp_2439_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* v_00_u03b1_2442_, lean_object* v_00_u03b2_2443_, lean_object* v_x_2444_, lean_object* v_x_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2444_, v_x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(v_00_u03b1_2447_, v_00_u03b2_2448_, v_x_2449_, v_x_2450_);
lean_dec(v_x_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_nat_dec_le(v___y_2452_, v___y_2453_);
if (v___x_2454_ == 0)
{
lean_inc(v___y_2452_);
return v___y_2452_;
}
else
{
lean_inc(v___y_2453_);
return v___y_2453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* v_t_2459_){
_start:
{
lean_object* v___f_2460_; lean_object* v___x_2461_; 
v___f_2460_ = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
v___x_2461_ = l_Lean_RBNode_depth___redArg(v___f_2460_, v_t_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* v_t_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_RBMap_maxDepth___redArg(v_t_2462_);
lean_dec(v_t_2462_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* v_00_u03b1_2464_, lean_object* v_00_u03b2_2465_, lean_object* v_cmp_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_RBMap_maxDepth___redArg(v_t_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_cmp_2471_, lean_object* v_t_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_RBMap_maxDepth(v_00_u03b1_2469_, v_00_u03b2_2470_, v_cmp_2471_, v_t_2472_);
lean_dec(v_t_2472_);
lean_dec_ref(v_cmp_2471_);
return v_res_2473_;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2477_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2478_ = lean_unsigned_to_nat(14u);
v___x_2479_ = lean_unsigned_to_nat(386u);
v___x_2480_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
v___x_2481_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2482_ = l_mkPanicMessageWithDecl(v___x_2481_, v___x_2480_, v___x_2479_, v___x_2478_, v___x_2477_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_t_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_RBNode_min___redArg(v_t_2485_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v_inst_2483_);
lean_ctor_set(v___x_2487_, 1, v_inst_2484_);
v___x_2488_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2489_ = l_panic___redArg(v___x_2487_, v___x_2488_);
lean_dec_ref_known(v___x_2487_, 2);
return v___x_2489_;
}
else
{
lean_object* v_val_2490_; lean_object* v_fst_2491_; lean_object* v_snd_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_inst_2484_);
lean_dec(v_inst_2483_);
v_val_2490_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_val_2490_);
lean_dec_ref_known(v___x_2486_, 1);
v_fst_2491_ = lean_ctor_get(v_val_2490_, 0);
v_snd_2492_ = lean_ctor_get(v_val_2490_, 1);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_val_2490_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v_val_2490_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_snd_2492_);
lean_inc(v_fst_2491_);
lean_dec(v_val_2490_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_fst_2491_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_snd_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_t_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_RBMap_min_x21___redArg(v_inst_2500_, v_inst_2501_, v_t_2502_);
lean_dec(v_t_2502_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* v_00_u03b1_2504_, lean_object* v_00_u03b2_2505_, lean_object* v_cmp_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_t_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_RBNode_min___redArg(v_t_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_inst_2507_);
lean_ctor_set(v___x_2511_, 1, v_inst_2508_);
v___x_2512_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2513_ = l_panic___redArg(v___x_2511_, v___x_2512_);
lean_dec_ref_known(v___x_2511_, 2);
return v___x_2513_;
}
else
{
lean_object* v_val_2514_; lean_object* v_fst_2515_; lean_object* v_snd_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_inst_2508_);
lean_dec(v_inst_2507_);
v_val_2514_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v___x_2510_, 1);
v_fst_2515_ = lean_ctor_get(v_val_2514_, 0);
v_snd_2516_ = lean_ctor_get(v_val_2514_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_val_2514_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v_val_2514_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_snd_2516_);
lean_inc(v_fst_2515_);
lean_dec(v_val_2514_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_fst_2515_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_snd_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* v_00_u03b1_2524_, lean_object* v_00_u03b2_2525_, lean_object* v_cmp_2526_, lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_t_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_RBMap_min_x21(v_00_u03b1_2524_, v_00_u03b2_2525_, v_cmp_2526_, v_inst_2527_, v_inst_2528_, v_t_2529_);
lean_dec(v_t_2529_);
lean_dec_ref(v_cmp_2526_);
return v_res_2530_;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2532_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2533_ = lean_unsigned_to_nat(14u);
v___x_2534_ = lean_unsigned_to_nat(391u);
v___x_2535_ = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
v___x_2536_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2537_ = l_mkPanicMessageWithDecl(v___x_2536_, v___x_2535_, v___x_2534_, v___x_2533_, v___x_2532_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_t_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_RBNode_max___redArg(v_t_2540_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_inst_2538_);
lean_ctor_set(v___x_2542_, 1, v_inst_2539_);
v___x_2543_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2544_ = l_panic___redArg(v___x_2542_, v___x_2543_);
lean_dec_ref_known(v___x_2542_, 2);
return v___x_2544_;
}
else
{
lean_object* v_val_2545_; lean_object* v_fst_2546_; lean_object* v_snd_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_inst_2539_);
lean_dec(v_inst_2538_);
v_val_2545_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_val_2545_);
lean_dec_ref_known(v___x_2541_, 1);
v_fst_2546_ = lean_ctor_get(v_val_2545_, 0);
v_snd_2547_ = lean_ctor_get(v_val_2545_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_val_2545_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v_val_2545_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_snd_2547_);
lean_inc(v_fst_2546_);
lean_dec(v_val_2545_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_fst_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_snd_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_t_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_RBMap_max_x21___redArg(v_inst_2555_, v_inst_2556_, v_t_2557_);
lean_dec(v_t_2557_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* v_00_u03b1_2559_, lean_object* v_00_u03b2_2560_, lean_object* v_cmp_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_t_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_RBNode_max___redArg(v_t_2564_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_inst_2562_);
lean_ctor_set(v___x_2566_, 1, v_inst_2563_);
v___x_2567_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2568_ = l_panic___redArg(v___x_2566_, v___x_2567_);
lean_dec_ref_known(v___x_2566_, 2);
return v___x_2568_;
}
else
{
lean_object* v_val_2569_; lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_inst_2563_);
lean_dec(v_inst_2562_);
v_val_2569_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_val_2569_);
lean_dec_ref_known(v___x_2565_, 1);
v_fst_2570_ = lean_ctor_get(v_val_2569_, 0);
v_snd_2571_ = lean_ctor_get(v_val_2569_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_val_2569_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v_val_2569_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_inc(v_fst_2570_);
lean_dec(v_val_2569_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_fst_2570_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_snd_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* v_00_u03b1_2579_, lean_object* v_00_u03b2_2580_, lean_object* v_cmp_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_t_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_RBMap_max_x21(v_00_u03b1_2579_, v_00_u03b2_2580_, v_cmp_2581_, v_inst_2582_, v_inst_2583_, v_t_2584_);
lean_dec(v_t_2584_);
lean_dec_ref(v_cmp_2581_);
return v_res_2585_;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2588_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
v___x_2589_ = lean_unsigned_to_nat(14u);
v___x_2590_ = lean_unsigned_to_nat(397u);
v___x_2591_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
v___x_2592_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2593_ = l_mkPanicMessageWithDecl(v___x_2592_, v___x_2591_, v___x_2590_, v___x_2589_, v___x_2588_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* v_cmp_2594_, lean_object* v_inst_2595_, lean_object* v_t_2596_, lean_object* v_k_2597_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_RBNode_find___redArg(v_cmp_2594_, v_t_2596_, v_k_2597_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2600_ = l_panic___redArg(v_inst_2595_, v___x_2599_);
return v___x_2600_;
}
else
{
lean_object* v_val_2601_; 
v_val_2601_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v___x_2598_, 1);
return v_val_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg___boxed(lean_object* v_cmp_2602_, lean_object* v_inst_2603_, lean_object* v_t_2604_, lean_object* v_k_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_RBMap_find_x21___redArg(v_cmp_2602_, v_inst_2603_, v_t_2604_, v_k_2605_);
lean_dec(v_inst_2603_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* v_00_u03b1_2607_, lean_object* v_00_u03b2_2608_, lean_object* v_cmp_2609_, lean_object* v_inst_2610_, lean_object* v_t_2611_, lean_object* v_k_2612_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_RBNode_find___redArg(v_cmp_2609_, v_t_2611_, v_k_2612_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2615_ = l_panic___redArg(v_inst_2610_, v___x_2614_);
return v___x_2615_;
}
else
{
lean_object* v_val_2616_; 
v_val_2616_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v___x_2613_, 1);
return v_val_2616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___boxed(lean_object* v_00_u03b1_2617_, lean_object* v_00_u03b2_2618_, lean_object* v_cmp_2619_, lean_object* v_inst_2620_, lean_object* v_t_2621_, lean_object* v_k_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_RBMap_find_x21(v_00_u03b1_2617_, v_00_u03b2_2618_, v_cmp_2619_, v_inst_2620_, v_t_2621_, v_k_2622_);
lean_dec(v_inst_2620_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* v_cmp_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_){
_start:
{
if (lean_obj_tag(v_x_2625_) == 0)
{
uint8_t v___x_2628_; lean_object* v___x_2629_; 
lean_dec_ref(v_cmp_2624_);
v___x_2628_ = 0;
v___x_2629_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2629_, 0, v_x_2625_);
lean_ctor_set(v___x_2629_, 1, v_x_2626_);
lean_ctor_set(v___x_2629_, 2, v_x_2627_);
lean_ctor_set(v___x_2629_, 3, v_x_2625_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*4, v___x_2628_);
return v___x_2629_;
}
else
{
uint8_t v_color_2630_; 
v_color_2630_ = lean_ctor_get_uint8(v_x_2625_, sizeof(void*)*4);
if (v_color_2630_ == 0)
{
lean_object* v_lchild_2631_; lean_object* v_key_2632_; lean_object* v_val_2633_; lean_object* v_rchild_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2651_; 
v_lchild_2631_ = lean_ctor_get(v_x_2625_, 0);
v_key_2632_ = lean_ctor_get(v_x_2625_, 1);
v_val_2633_ = lean_ctor_get(v_x_2625_, 2);
v_rchild_2634_ = lean_ctor_get(v_x_2625_, 3);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_x_2625_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2636_ = v_x_2625_;
v_isShared_2637_ = v_isSharedCheck_2651_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_rchild_2634_);
lean_inc(v_val_2633_);
lean_inc(v_key_2632_);
lean_inc(v_lchild_2631_);
lean_dec(v_x_2625_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2651_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
lean_inc_ref(v_cmp_2624_);
lean_inc(v_key_2632_);
lean_inc(v_x_2626_);
v___x_2638_ = lean_apply_2(v_cmp_2624_, v_x_2626_, v_key_2632_);
v___x_2639_ = lean_unbox(v___x_2638_);
switch(v___x_2639_)
{
case 0:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2624_, v_lchild_2631_, v_x_2626_, v_x_2627_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2640_);
v___x_2642_ = v___x_2636_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_key_2632_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_val_2633_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_rchild_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*4, v_color_2630_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
case 1:
{
lean_object* v___x_2645_; 
lean_dec(v_val_2633_);
lean_dec(v_key_2632_);
lean_dec_ref(v_cmp_2624_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 2, v_x_2627_);
lean_ctor_set(v___x_2636_, 1, v_x_2626_);
v___x_2645_ = v___x_2636_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_lchild_2631_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_x_2626_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_x_2627_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_rchild_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2646_, sizeof(void*)*4, v_color_2630_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
default: 
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2647_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2624_, v_rchild_2634_, v_x_2626_, v_x_2627_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 3, v___x_2647_);
v___x_2649_ = v___x_2636_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_lchild_2631_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_key_2632_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v_val_2633_);
lean_ctor_set(v_reuseFailAlloc_2650_, 3, v___x_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2650_, sizeof(void*)*4, v_color_2630_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v_lchild_2652_; lean_object* v_key_2653_; lean_object* v_val_2654_; lean_object* v_rchild_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2814_; 
v_lchild_2652_ = lean_ctor_get(v_x_2625_, 0);
v_key_2653_ = lean_ctor_get(v_x_2625_, 1);
v_val_2654_ = lean_ctor_get(v_x_2625_, 2);
v_rchild_2655_ = lean_ctor_get(v_x_2625_, 3);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_x_2625_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2657_ = v_x_2625_;
v_isShared_2658_ = v_isSharedCheck_2814_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_rchild_2655_);
lean_inc(v_val_2654_);
lean_inc(v_key_2653_);
lean_inc(v_lchild_2652_);
lean_dec(v_x_2625_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2814_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; uint8_t v___x_2660_; 
lean_inc_ref(v_cmp_2624_);
lean_inc(v_key_2653_);
lean_inc(v_x_2626_);
v___x_2659_ = lean_apply_2(v_cmp_2624_, v_x_2626_, v_key_2653_);
v___x_2660_ = lean_unbox(v___x_2659_);
switch(v___x_2660_)
{
case 0:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2624_, v_lchild_2652_, v_x_2626_, v_x_2627_);
if (lean_obj_tag(v___x_2661_) == 1)
{
uint8_t v_color_2662_; lean_object* v_lchild_2663_; lean_object* v_key_2664_; lean_object* v_val_2665_; lean_object* v_rchild_2666_; lean_object* v_a_2668_; lean_object* v_kx_2669_; lean_object* v_vx_2670_; lean_object* v_b_2671_; lean_object* v_ky_2672_; lean_object* v_vy_2673_; lean_object* v_c_2674_; lean_object* v_kz_2675_; lean_object* v_vz_2676_; lean_object* v_d_2677_; 
v_color_2662_ = lean_ctor_get_uint8(v___x_2661_, sizeof(void*)*4);
v_lchild_2663_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_lchild_2663_);
v_key_2664_ = lean_ctor_get(v___x_2661_, 1);
lean_inc(v_key_2664_);
v_val_2665_ = lean_ctor_get(v___x_2661_, 2);
lean_inc(v_val_2665_);
v_rchild_2666_ = lean_ctor_get(v___x_2661_, 3);
lean_inc(v_rchild_2666_);
if (v_color_2662_ == 0)
{
if (lean_obj_tag(v_lchild_2663_) == 1)
{
uint8_t v_color_2683_; 
v_color_2683_ = lean_ctor_get_uint8(v_lchild_2663_, sizeof(void*)*4);
if (v_color_2683_ == 0)
{
lean_object* v_lchild_2684_; lean_object* v_key_2685_; lean_object* v_val_2686_; lean_object* v_rchild_2687_; 
lean_dec_ref_known(v___x_2661_, 4);
v_lchild_2684_ = lean_ctor_get(v_lchild_2663_, 0);
lean_inc(v_lchild_2684_);
v_key_2685_ = lean_ctor_get(v_lchild_2663_, 1);
lean_inc(v_key_2685_);
v_val_2686_ = lean_ctor_get(v_lchild_2663_, 2);
lean_inc(v_val_2686_);
v_rchild_2687_ = lean_ctor_get(v_lchild_2663_, 3);
lean_inc(v_rchild_2687_);
lean_dec_ref_known(v_lchild_2663_, 4);
v_a_2668_ = v_lchild_2684_;
v_kx_2669_ = v_key_2685_;
v_vx_2670_ = v_val_2686_;
v_b_2671_ = v_rchild_2687_;
v_ky_2672_ = v_key_2664_;
v_vy_2673_ = v_val_2665_;
v_c_2674_ = v_rchild_2666_;
v_kz_2675_ = v_key_2653_;
v_vz_2676_ = v_val_2654_;
v_d_2677_ = v_rchild_2655_;
goto v___jp_2667_;
}
else
{
if (lean_obj_tag(v_rchild_2666_) == 1)
{
uint8_t v_color_2688_; 
v_color_2688_ = lean_ctor_get_uint8(v_rchild_2666_, sizeof(void*)*4);
if (v_color_2688_ == 0)
{
lean_object* v_lchild_2689_; lean_object* v_key_2690_; lean_object* v_val_2691_; lean_object* v_rchild_2692_; 
lean_dec_ref_known(v___x_2661_, 4);
v_lchild_2689_ = lean_ctor_get(v_rchild_2666_, 0);
lean_inc(v_lchild_2689_);
v_key_2690_ = lean_ctor_get(v_rchild_2666_, 1);
lean_inc(v_key_2690_);
v_val_2691_ = lean_ctor_get(v_rchild_2666_, 2);
lean_inc(v_val_2691_);
v_rchild_2692_ = lean_ctor_get(v_rchild_2666_, 3);
lean_inc(v_rchild_2692_);
lean_dec_ref_known(v_rchild_2666_, 4);
v_a_2668_ = v_lchild_2663_;
v_kx_2669_ = v_key_2664_;
v_vx_2670_ = v_val_2665_;
v_b_2671_ = v_lchild_2689_;
v_ky_2672_ = v_key_2690_;
v_vy_2673_ = v_val_2691_;
v_c_2674_ = v_rchild_2692_;
v_kz_2675_ = v_key_2653_;
v_vz_2676_ = v_val_2654_;
v_d_2677_ = v_rchild_2655_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec_ref_known(v_lchild_2663_, 4);
lean_dec(v_val_2665_);
lean_dec(v_key_2664_);
lean_del_object(v___x_2657_);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_rchild_2666_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; lean_object* v_unused_2701_; lean_object* v_unused_2702_; lean_object* v_unused_2703_; 
v_unused_2700_ = lean_ctor_get(v_rchild_2666_, 3);
lean_dec(v_unused_2700_);
v_unused_2701_ = lean_ctor_get(v_rchild_2666_, 2);
lean_dec(v_unused_2701_);
v_unused_2702_ = lean_ctor_get(v_rchild_2666_, 1);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_rchild_2666_, 0);
lean_dec(v_unused_2703_);
v___x_2694_ = v_rchild_2666_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v_rchild_2666_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 3, v_rchild_2655_);
lean_ctor_set(v___x_2694_, 2, v_val_2654_);
lean_ctor_set(v___x_2694_, 1, v_key_2653_);
lean_ctor_set(v___x_2694_, 0, v___x_2661_);
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_rchild_2655_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*4, v_color_2630_);
return v___x_2697_;
}
}
}
}
else
{
lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_rchild_2666_);
lean_dec(v_val_2665_);
lean_dec(v_key_2664_);
lean_del_object(v___x_2657_);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_lchild_2663_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; lean_object* v_unused_2714_; 
v_unused_2711_ = lean_ctor_get(v_lchild_2663_, 3);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_lchild_2663_, 2);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_lchild_2663_, 1);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_lchild_2663_, 0);
lean_dec(v_unused_2714_);
v___x_2705_ = v_lchild_2663_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v_lchild_2663_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 3, v_rchild_2655_);
lean_ctor_set(v___x_2705_, 2, v_val_2654_);
lean_ctor_set(v___x_2705_, 1, v_key_2653_);
lean_ctor_set(v___x_2705_, 0, v___x_2661_);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_rchild_2655_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*4, v_color_2630_);
return v___x_2708_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2666_) == 1)
{
uint8_t v_color_2715_; 
v_color_2715_ = lean_ctor_get_uint8(v_rchild_2666_, sizeof(void*)*4);
if (v_color_2715_ == 0)
{
lean_object* v_lchild_2716_; lean_object* v_key_2717_; lean_object* v_val_2718_; lean_object* v_rchild_2719_; 
lean_dec_ref_known(v___x_2661_, 4);
v_lchild_2716_ = lean_ctor_get(v_rchild_2666_, 0);
lean_inc(v_lchild_2716_);
v_key_2717_ = lean_ctor_get(v_rchild_2666_, 1);
lean_inc(v_key_2717_);
v_val_2718_ = lean_ctor_get(v_rchild_2666_, 2);
lean_inc(v_val_2718_);
v_rchild_2719_ = lean_ctor_get(v_rchild_2666_, 3);
lean_inc(v_rchild_2719_);
lean_dec_ref_known(v_rchild_2666_, 4);
v_a_2668_ = v_lchild_2663_;
v_kx_2669_ = v_key_2664_;
v_vx_2670_ = v_val_2665_;
v_b_2671_ = v_lchild_2716_;
v_ky_2672_ = v_key_2717_;
v_vy_2673_ = v_val_2718_;
v_c_2674_ = v_rchild_2719_;
v_kz_2675_ = v_key_2653_;
v_vz_2676_ = v_val_2654_;
v_d_2677_ = v_rchild_2655_;
goto v___jp_2667_;
}
else
{
lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_val_2665_);
lean_dec(v_key_2664_);
lean_dec(v_lchild_2663_);
lean_del_object(v___x_2657_);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_rchild_2666_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; lean_object* v_unused_2728_; lean_object* v_unused_2729_; lean_object* v_unused_2730_; 
v_unused_2727_ = lean_ctor_get(v_rchild_2666_, 3);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_rchild_2666_, 2);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v_rchild_2666_, 1);
lean_dec(v_unused_2729_);
v_unused_2730_ = lean_ctor_get(v_rchild_2666_, 0);
lean_dec(v_unused_2730_);
v___x_2721_ = v_rchild_2666_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_dec(v_rchild_2666_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 3, v_rchild_2655_);
lean_ctor_set(v___x_2721_, 2, v_val_2654_);
lean_ctor_set(v___x_2721_, 1, v_key_2653_);
lean_ctor_set(v___x_2721_, 0, v___x_2661_);
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_rchild_2655_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*4, v_color_2630_);
return v___x_2724_;
}
}
}
}
else
{
lean_object* v___x_2731_; 
lean_dec(v_rchild_2666_);
lean_dec(v_val_2665_);
lean_dec(v_key_2664_);
lean_dec(v_lchild_2663_);
lean_del_object(v___x_2657_);
v___x_2731_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2731_, 0, v___x_2661_);
lean_ctor_set(v___x_2731_, 1, v_key_2653_);
lean_ctor_set(v___x_2731_, 2, v_val_2654_);
lean_ctor_set(v___x_2731_, 3, v_rchild_2655_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*4, v_color_2630_);
return v___x_2731_;
}
}
}
else
{
lean_object* v___x_2732_; 
lean_dec(v_rchild_2666_);
lean_dec(v_val_2665_);
lean_dec(v_key_2664_);
lean_dec(v_lchild_2663_);
lean_del_object(v___x_2657_);
v___x_2732_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2732_, 0, v___x_2661_);
lean_ctor_set(v___x_2732_, 1, v_key_2653_);
lean_ctor_set(v___x_2732_, 2, v_val_2654_);
lean_ctor_set(v___x_2732_, 3, v_rchild_2655_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*4, v_color_2630_);
return v___x_2732_;
}
v___jp_2667_:
{
lean_object* v___x_2679_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 3, v_b_2671_);
lean_ctor_set(v___x_2657_, 2, v_vx_2670_);
lean_ctor_set(v___x_2657_, 1, v_kx_2669_);
lean_ctor_set(v___x_2657_, 0, v_a_2668_);
v___x_2679_ = v___x_2657_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2668_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_kx_2669_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_vx_2670_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_b_2671_);
lean_ctor_set_uint8(v_reuseFailAlloc_2682_, sizeof(void*)*4, v_color_2630_);
v___x_2679_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2680_, 0, v_c_2674_);
lean_ctor_set(v___x_2680_, 1, v_kz_2675_);
lean_ctor_set(v___x_2680_, 2, v_vz_2676_);
lean_ctor_set(v___x_2680_, 3, v_d_2677_);
lean_ctor_set_uint8(v___x_2680_, sizeof(void*)*4, v_color_2630_);
v___x_2681_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v_ky_2672_);
lean_ctor_set(v___x_2681_, 2, v_vy_2673_);
lean_ctor_set(v___x_2681_, 3, v___x_2680_);
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*4, v_color_2662_);
return v___x_2681_;
}
}
}
else
{
lean_object* v___x_2734_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2661_);
v___x_2734_ = v___x_2657_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_rchild_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2735_, sizeof(void*)*4, v_color_2630_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
case 1:
{
lean_object* v___x_2737_; 
lean_dec(v_val_2654_);
lean_dec(v_key_2653_);
lean_dec_ref(v_cmp_2624_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 2, v_x_2627_);
lean_ctor_set(v___x_2657_, 1, v_x_2626_);
v___x_2737_ = v___x_2657_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_lchild_2652_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_x_2626_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_x_2627_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_rchild_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2738_, sizeof(void*)*4, v_color_2630_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
default: 
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2624_, v_rchild_2655_, v_x_2626_, v_x_2627_);
if (lean_obj_tag(v___x_2739_) == 1)
{
uint8_t v_color_2740_; lean_object* v_lchild_2741_; lean_object* v_key_2742_; lean_object* v_val_2743_; lean_object* v_rchild_2744_; lean_object* v_a_2746_; lean_object* v_kx_2747_; lean_object* v_vx_2748_; lean_object* v_b_2749_; lean_object* v_ky_2750_; lean_object* v_vy_2751_; lean_object* v_c_2752_; lean_object* v_kz_2753_; lean_object* v_vz_2754_; lean_object* v_d_2755_; 
v_color_2740_ = lean_ctor_get_uint8(v___x_2739_, sizeof(void*)*4);
v_lchild_2741_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_lchild_2741_);
v_key_2742_ = lean_ctor_get(v___x_2739_, 1);
lean_inc(v_key_2742_);
v_val_2743_ = lean_ctor_get(v___x_2739_, 2);
lean_inc(v_val_2743_);
v_rchild_2744_ = lean_ctor_get(v___x_2739_, 3);
lean_inc(v_rchild_2744_);
if (v_color_2740_ == 0)
{
if (lean_obj_tag(v_lchild_2741_) == 1)
{
uint8_t v_color_2761_; 
v_color_2761_ = lean_ctor_get_uint8(v_lchild_2741_, sizeof(void*)*4);
if (v_color_2761_ == 0)
{
lean_object* v_lchild_2762_; lean_object* v_key_2763_; lean_object* v_val_2764_; lean_object* v_rchild_2765_; 
lean_dec_ref_known(v___x_2739_, 4);
v_lchild_2762_ = lean_ctor_get(v_lchild_2741_, 0);
lean_inc(v_lchild_2762_);
v_key_2763_ = lean_ctor_get(v_lchild_2741_, 1);
lean_inc(v_key_2763_);
v_val_2764_ = lean_ctor_get(v_lchild_2741_, 2);
lean_inc(v_val_2764_);
v_rchild_2765_ = lean_ctor_get(v_lchild_2741_, 3);
lean_inc(v_rchild_2765_);
lean_dec_ref_known(v_lchild_2741_, 4);
v_a_2746_ = v_lchild_2652_;
v_kx_2747_ = v_key_2653_;
v_vx_2748_ = v_val_2654_;
v_b_2749_ = v_lchild_2762_;
v_ky_2750_ = v_key_2763_;
v_vy_2751_ = v_val_2764_;
v_c_2752_ = v_rchild_2765_;
v_kz_2753_ = v_key_2742_;
v_vz_2754_ = v_val_2743_;
v_d_2755_ = v_rchild_2744_;
goto v___jp_2745_;
}
else
{
if (lean_obj_tag(v_rchild_2744_) == 1)
{
uint8_t v_color_2766_; 
v_color_2766_ = lean_ctor_get_uint8(v_rchild_2744_, sizeof(void*)*4);
if (v_color_2766_ == 0)
{
lean_object* v_lchild_2767_; lean_object* v_key_2768_; lean_object* v_val_2769_; lean_object* v_rchild_2770_; 
lean_dec_ref_known(v___x_2739_, 4);
v_lchild_2767_ = lean_ctor_get(v_rchild_2744_, 0);
lean_inc(v_lchild_2767_);
v_key_2768_ = lean_ctor_get(v_rchild_2744_, 1);
lean_inc(v_key_2768_);
v_val_2769_ = lean_ctor_get(v_rchild_2744_, 2);
lean_inc(v_val_2769_);
v_rchild_2770_ = lean_ctor_get(v_rchild_2744_, 3);
lean_inc(v_rchild_2770_);
lean_dec_ref_known(v_rchild_2744_, 4);
v_a_2746_ = v_lchild_2652_;
v_kx_2747_ = v_key_2653_;
v_vx_2748_ = v_val_2654_;
v_b_2749_ = v_lchild_2741_;
v_ky_2750_ = v_key_2742_;
v_vy_2751_ = v_val_2743_;
v_c_2752_ = v_lchild_2767_;
v_kz_2753_ = v_key_2768_;
v_vz_2754_ = v_val_2769_;
v_d_2755_ = v_rchild_2770_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref_known(v_lchild_2741_, 4);
lean_dec(v_val_2743_);
lean_dec(v_key_2742_);
lean_del_object(v___x_2657_);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_rchild_2744_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; lean_object* v_unused_2779_; lean_object* v_unused_2780_; lean_object* v_unused_2781_; 
v_unused_2778_ = lean_ctor_get(v_rchild_2744_, 3);
lean_dec(v_unused_2778_);
v_unused_2779_ = lean_ctor_get(v_rchild_2744_, 2);
lean_dec(v_unused_2779_);
v_unused_2780_ = lean_ctor_get(v_rchild_2744_, 1);
lean_dec(v_unused_2780_);
v_unused_2781_ = lean_ctor_get(v_rchild_2744_, 0);
lean_dec(v_unused_2781_);
v___x_2772_ = v_rchild_2744_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v_rchild_2744_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 3, v___x_2739_);
lean_ctor_set(v___x_2772_, 2, v_val_2654_);
lean_ctor_set(v___x_2772_, 1, v_key_2653_);
lean_ctor_set(v___x_2772_, 0, v_lchild_2652_);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_lchild_2652_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v___x_2739_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*4, v_color_2630_);
return v___x_2775_;
}
}
}
}
else
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_rchild_2744_);
lean_dec(v_val_2743_);
lean_dec(v_key_2742_);
lean_del_object(v___x_2657_);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_lchild_2741_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; 
v_unused_2789_ = lean_ctor_get(v_lchild_2741_, 3);
lean_dec(v_unused_2789_);
v_unused_2790_ = lean_ctor_get(v_lchild_2741_, 2);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_lchild_2741_, 1);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_lchild_2741_, 0);
lean_dec(v_unused_2792_);
v___x_2783_ = v_lchild_2741_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v_lchild_2741_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 3, v___x_2739_);
lean_ctor_set(v___x_2783_, 2, v_val_2654_);
lean_ctor_set(v___x_2783_, 1, v_key_2653_);
lean_ctor_set(v___x_2783_, 0, v_lchild_2652_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_lchild_2652_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2787_, 3, v___x_2739_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*4, v_color_2630_);
return v___x_2786_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2744_) == 1)
{
uint8_t v_color_2793_; 
v_color_2793_ = lean_ctor_get_uint8(v_rchild_2744_, sizeof(void*)*4);
if (v_color_2793_ == 0)
{
lean_object* v_lchild_2794_; lean_object* v_key_2795_; lean_object* v_val_2796_; lean_object* v_rchild_2797_; 
lean_dec_ref_known(v___x_2739_, 4);
v_lchild_2794_ = lean_ctor_get(v_rchild_2744_, 0);
lean_inc(v_lchild_2794_);
v_key_2795_ = lean_ctor_get(v_rchild_2744_, 1);
lean_inc(v_key_2795_);
v_val_2796_ = lean_ctor_get(v_rchild_2744_, 2);
lean_inc(v_val_2796_);
v_rchild_2797_ = lean_ctor_get(v_rchild_2744_, 3);
lean_inc(v_rchild_2797_);
lean_dec_ref_known(v_rchild_2744_, 4);
v_a_2746_ = v_lchild_2652_;
v_kx_2747_ = v_key_2653_;
v_vx_2748_ = v_val_2654_;
v_b_2749_ = v_lchild_2741_;
v_ky_2750_ = v_key_2742_;
v_vy_2751_ = v_val_2743_;
v_c_2752_ = v_lchild_2794_;
v_kz_2753_ = v_key_2795_;
v_vz_2754_ = v_val_2796_;
v_d_2755_ = v_rchild_2797_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_val_2743_);
lean_dec(v_key_2742_);
lean_dec(v_lchild_2741_);
lean_del_object(v___x_2657_);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_rchild_2744_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2805_ = lean_ctor_get(v_rchild_2744_, 3);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_rchild_2744_, 2);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_rchild_2744_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_rchild_2744_, 0);
lean_dec(v_unused_2808_);
v___x_2799_ = v_rchild_2744_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_dec(v_rchild_2744_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 3, v___x_2739_);
lean_ctor_set(v___x_2799_, 2, v_val_2654_);
lean_ctor_set(v___x_2799_, 1, v_key_2653_);
lean_ctor_set(v___x_2799_, 0, v_lchild_2652_);
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_lchild_2652_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2803_, 3, v___x_2739_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*4, v_color_2630_);
return v___x_2802_;
}
}
}
}
else
{
lean_object* v___x_2809_; 
lean_dec(v_rchild_2744_);
lean_dec(v_val_2743_);
lean_dec(v_key_2742_);
lean_dec(v_lchild_2741_);
lean_del_object(v___x_2657_);
v___x_2809_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2809_, 0, v_lchild_2652_);
lean_ctor_set(v___x_2809_, 1, v_key_2653_);
lean_ctor_set(v___x_2809_, 2, v_val_2654_);
lean_ctor_set(v___x_2809_, 3, v___x_2739_);
lean_ctor_set_uint8(v___x_2809_, sizeof(void*)*4, v_color_2630_);
return v___x_2809_;
}
}
}
else
{
lean_object* v___x_2810_; 
lean_dec(v_rchild_2744_);
lean_dec(v_val_2743_);
lean_dec(v_key_2742_);
lean_dec(v_lchild_2741_);
lean_del_object(v___x_2657_);
v___x_2810_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2810_, 0, v_lchild_2652_);
lean_ctor_set(v___x_2810_, 1, v_key_2653_);
lean_ctor_set(v___x_2810_, 2, v_val_2654_);
lean_ctor_set(v___x_2810_, 3, v___x_2739_);
lean_ctor_set_uint8(v___x_2810_, sizeof(void*)*4, v_color_2630_);
return v___x_2810_;
}
v___jp_2745_:
{
lean_object* v___x_2757_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 3, v_b_2749_);
lean_ctor_set(v___x_2657_, 2, v_vx_2748_);
lean_ctor_set(v___x_2657_, 1, v_kx_2747_);
lean_ctor_set(v___x_2657_, 0, v_a_2746_);
v___x_2757_ = v___x_2657_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2746_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_kx_2747_);
lean_ctor_set(v_reuseFailAlloc_2760_, 2, v_vx_2748_);
lean_ctor_set(v_reuseFailAlloc_2760_, 3, v_b_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*4, v_color_2630_);
v___x_2757_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2758_, 0, v_c_2752_);
lean_ctor_set(v___x_2758_, 1, v_kz_2753_);
lean_ctor_set(v___x_2758_, 2, v_vz_2754_);
lean_ctor_set(v___x_2758_, 3, v_d_2755_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*4, v_color_2630_);
v___x_2759_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v_ky_2750_);
lean_ctor_set(v___x_2759_, 2, v_vy_2751_);
lean_ctor_set(v___x_2759_, 3, v___x_2758_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*4, v_color_2740_);
return v___x_2759_;
}
}
}
else
{
lean_object* v___x_2812_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 3, v___x_2739_);
v___x_2812_ = v___x_2657_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_lchild_2652_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_key_2653_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_val_2654_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v___x_2739_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, sizeof(void*)*4, v_color_2630_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* v_cmp_2815_, lean_object* v_t_2816_, lean_object* v_k_2817_, lean_object* v_v_2818_){
_start:
{
uint8_t v___x_2819_; 
v___x_2819_ = l_Lean_RBNode_isRed___redArg(v_t_2816_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2815_, v_t_2816_, v_k_2817_, v_v_2818_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2815_, v_t_2816_, v_k_2817_, v_v_2818_);
v___x_2822_ = l_Lean_RBNode_setBlack___redArg(v___x_2821_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* v_cmp_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v___x_2826_; 
lean_dec(v_x_2825_);
lean_dec_ref(v_cmp_2823_);
v___x_2826_ = lean_box(0);
return v___x_2826_;
}
else
{
lean_object* v_lchild_2827_; lean_object* v_key_2828_; lean_object* v_val_2829_; lean_object* v_rchild_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v_lchild_2827_ = lean_ctor_get(v_x_2824_, 0);
lean_inc(v_lchild_2827_);
v_key_2828_ = lean_ctor_get(v_x_2824_, 1);
lean_inc(v_key_2828_);
v_val_2829_ = lean_ctor_get(v_x_2824_, 2);
lean_inc(v_val_2829_);
v_rchild_2830_ = lean_ctor_get(v_x_2824_, 3);
lean_inc(v_rchild_2830_);
lean_dec_ref_known(v_x_2824_, 4);
lean_inc_ref(v_cmp_2823_);
lean_inc(v_x_2825_);
v___x_2831_ = lean_apply_2(v_cmp_2823_, v_x_2825_, v_key_2828_);
v___x_2832_ = lean_unbox(v___x_2831_);
switch(v___x_2832_)
{
case 0:
{
lean_dec(v_rchild_2830_);
lean_dec(v_val_2829_);
v_x_2824_ = v_lchild_2827_;
goto _start;
}
case 1:
{
lean_object* v___x_2834_; 
lean_dec(v_rchild_2830_);
lean_dec(v_lchild_2827_);
lean_dec(v_x_2825_);
lean_dec_ref(v_cmp_2823_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_val_2829_);
return v___x_2834_;
}
default: 
{
lean_dec(v_val_2829_);
lean_dec(v_lchild_2827_);
v_x_2824_ = v_rchild_2830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* v_cmp_2836_, lean_object* v_mergeFn_2837_, lean_object* v_x_2838_, lean_object* v_x_2839_){
_start:
{
if (lean_obj_tag(v_x_2839_) == 0)
{
lean_dec(v_mergeFn_2837_);
lean_dec_ref(v_cmp_2836_);
return v_x_2838_;
}
else
{
lean_object* v_lchild_2840_; lean_object* v_key_2841_; lean_object* v_val_2842_; lean_object* v_rchild_2843_; lean_object* v_val_2844_; lean_object* v___y_2846_; lean_object* v___x_2849_; 
v_lchild_2840_ = lean_ctor_get(v_x_2839_, 0);
lean_inc(v_lchild_2840_);
v_key_2841_ = lean_ctor_get(v_x_2839_, 1);
lean_inc_n(v_key_2841_, 2);
v_val_2842_ = lean_ctor_get(v_x_2839_, 2);
lean_inc(v_val_2842_);
v_rchild_2843_ = lean_ctor_get(v_x_2839_, 3);
lean_inc(v_rchild_2843_);
lean_dec_ref_known(v_x_2839_, 4);
lean_inc(v_mergeFn_2837_);
lean_inc_ref_n(v_cmp_2836_, 2);
v_val_2844_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2836_, v_mergeFn_2837_, v_x_2838_, v_lchild_2840_);
lean_inc(v_val_2844_);
v___x_2849_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2836_, v_val_2844_, v_key_2841_);
if (lean_obj_tag(v___x_2849_) == 0)
{
v___y_2846_ = v_val_2842_;
goto v___jp_2845_;
}
else
{
lean_object* v_val_2850_; lean_object* v___x_2851_; 
v_val_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_val_2850_);
lean_dec_ref_known(v___x_2849_, 1);
lean_inc(v_mergeFn_2837_);
lean_inc(v_key_2841_);
v___x_2851_ = lean_apply_3(v_mergeFn_2837_, v_key_2841_, v_val_2850_, v_val_2842_);
v___y_2846_ = v___x_2851_;
goto v___jp_2845_;
}
v___jp_2845_:
{
lean_object* v___x_2847_; 
lean_inc_ref(v_cmp_2836_);
v___x_2847_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2836_, v_val_2844_, v_key_2841_, v___y_2846_);
v_x_2838_ = v___x_2847_;
v_x_2839_ = v_rchild_2843_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* v_cmp_2852_, lean_object* v_mergeFn_2853_, lean_object* v_t_u2081_2854_, lean_object* v_t_u2082_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2852_, v_mergeFn_2853_, v_t_u2081_2854_, v_t_u2082_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* v_00_u03b1_2857_, lean_object* v_00_u03b2_2858_, lean_object* v_cmp_2859_, lean_object* v_mergeFn_2860_, lean_object* v_t_u2081_2861_, lean_object* v_t_u2082_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2859_, v_mergeFn_2860_, v_t_u2081_2861_, v_t_u2082_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* v_00_u03b1_2864_, lean_object* v_cmp_2865_, lean_object* v_00_u03b2_2866_, lean_object* v_t_2867_, lean_object* v_k_2868_, lean_object* v_v_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2865_, v_t_2867_, v_k_2868_, v_v_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* v_00_u03b1_2871_, lean_object* v_cmp_2872_, lean_object* v_00_u03b2_2873_, lean_object* v_x_2874_, lean_object* v_x_2875_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2872_, v_x_2874_, v_x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* v_00_u03b1_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_cmp_2879_, lean_object* v_mergeFn_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2879_, v_mergeFn_2880_, v_x_2881_, v_x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* v_00_u03b1_2884_, lean_object* v_cmp_2885_, lean_object* v_00_u03b2_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2885_, v_x_2887_, v_x_2888_, v_x_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* v_t_u2082_2891_, lean_object* v_cmp_2892_, lean_object* v_mergeFn_2893_, lean_object* v_x_2894_, lean_object* v_x_2895_){
_start:
{
if (lean_obj_tag(v_x_2895_) == 0)
{
lean_dec(v_mergeFn_2893_);
lean_dec_ref(v_cmp_2892_);
lean_dec(v_t_u2082_2891_);
return v_x_2894_;
}
else
{
lean_object* v_lchild_2896_; lean_object* v_key_2897_; lean_object* v_val_2898_; lean_object* v_rchild_2899_; lean_object* v_val_2900_; lean_object* v___x_2901_; 
v_lchild_2896_ = lean_ctor_get(v_x_2895_, 0);
lean_inc(v_lchild_2896_);
v_key_2897_ = lean_ctor_get(v_x_2895_, 1);
lean_inc_n(v_key_2897_, 2);
v_val_2898_ = lean_ctor_get(v_x_2895_, 2);
lean_inc(v_val_2898_);
v_rchild_2899_ = lean_ctor_get(v_x_2895_, 3);
lean_inc(v_rchild_2899_);
lean_dec_ref_known(v_x_2895_, 4);
lean_inc(v_mergeFn_2893_);
lean_inc_ref_n(v_cmp_2892_, 2);
lean_inc_n(v_t_u2082_2891_, 2);
v_val_2900_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2891_, v_cmp_2892_, v_mergeFn_2893_, v_x_2894_, v_lchild_2896_);
v___x_2901_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2892_, v_t_u2082_2891_, v_key_2897_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_dec(v_val_2898_);
lean_dec(v_key_2897_);
v_x_2894_ = v_val_2900_;
v_x_2895_ = v_rchild_2899_;
goto _start;
}
else
{
lean_object* v_val_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_val_2903_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v___x_2901_, 1);
lean_inc(v_mergeFn_2893_);
lean_inc(v_key_2897_);
v___x_2904_ = lean_apply_3(v_mergeFn_2893_, v_key_2897_, v_val_2898_, v_val_2903_);
lean_inc_ref(v_cmp_2892_);
v___x_2905_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2892_, v_val_2900_, v_key_2897_, v___x_2904_);
v_x_2894_ = v___x_2905_;
v_x_2895_ = v_rchild_2899_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* v_cmp_2907_, lean_object* v_mergeFn_2908_, lean_object* v_t_u2081_2909_, lean_object* v_t_u2082_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_box(0);
v___x_2912_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2910_, v_cmp_2907_, v_mergeFn_2908_, v___x_2911_, v_t_u2081_2909_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* v_00_u03b1_2913_, lean_object* v_00_u03b2_2914_, lean_object* v_cmp_2915_, lean_object* v_00_u03b3_2916_, lean_object* v_00_u03b4_2917_, lean_object* v_mergeFn_2918_, lean_object* v_t_u2081_2919_, lean_object* v_t_u2082_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_RBMap_intersectBy___redArg(v_cmp_2915_, v_mergeFn_2918_, v_t_u2081_2919_, v_t_u2082_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* v_00_u03b1_2922_, lean_object* v_00_u03b2_2923_, lean_object* v_00_u03b4_2924_, lean_object* v_00_u03b3_2925_, lean_object* v_t_u2082_2926_, lean_object* v_cmp_2927_, lean_object* v_mergeFn_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2926_, v_cmp_2927_, v_mergeFn_2928_, v_x_2929_, v_x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* v_f_2932_, lean_object* v_cmp_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_dec_ref(v_cmp_2933_);
lean_dec_ref(v_f_2932_);
return v_x_2934_;
}
else
{
lean_object* v_lchild_2936_; lean_object* v_key_2937_; lean_object* v_val_2938_; lean_object* v_rchild_2939_; lean_object* v_val_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v_lchild_2936_ = lean_ctor_get(v_x_2935_, 0);
lean_inc(v_lchild_2936_);
v_key_2937_ = lean_ctor_get(v_x_2935_, 1);
lean_inc_n(v_key_2937_, 2);
v_val_2938_ = lean_ctor_get(v_x_2935_, 2);
lean_inc_n(v_val_2938_, 2);
v_rchild_2939_ = lean_ctor_get(v_x_2935_, 3);
lean_inc(v_rchild_2939_);
lean_dec_ref_known(v_x_2935_, 4);
lean_inc_ref(v_cmp_2933_);
lean_inc_ref_n(v_f_2932_, 2);
v_val_2940_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2932_, v_cmp_2933_, v_x_2934_, v_lchild_2936_);
v___x_2941_ = lean_apply_2(v_f_2932_, v_key_2937_, v_val_2938_);
v___x_2942_ = lean_unbox(v___x_2941_);
if (v___x_2942_ == 0)
{
lean_dec(v_val_2938_);
lean_dec(v_key_2937_);
v_x_2934_ = v_val_2940_;
v_x_2935_ = v_rchild_2939_;
goto _start;
}
else
{
lean_object* v___x_2944_; 
lean_inc_ref(v_cmp_2933_);
v___x_2944_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2933_, v_val_2940_, v_key_2937_, v_val_2938_);
v_x_2934_ = v___x_2944_;
v_x_2935_ = v_rchild_2939_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* v_cmp_2946_, lean_object* v_f_2947_, lean_object* v_m_2948_){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = lean_box(0);
v___x_2950_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2947_, v_cmp_2946_, v___x_2949_, v_m_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* v_00_u03b1_2951_, lean_object* v_00_u03b2_2952_, lean_object* v_cmp_2953_, lean_object* v_f_2954_, lean_object* v_m_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_RBMap_filter___redArg(v_cmp_2953_, v_f_2954_, v_m_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* v_00_u03b1_2957_, lean_object* v_00_u03b2_2958_, lean_object* v_f_2959_, lean_object* v_cmp_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2959_, v_cmp_2960_, v_x_2961_, v_x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* v_f_2964_, lean_object* v_cmp_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_){
_start:
{
if (lean_obj_tag(v_x_2967_) == 0)
{
lean_dec_ref(v_cmp_2965_);
lean_dec_ref(v_f_2964_);
return v_x_2966_;
}
else
{
lean_object* v_lchild_2968_; lean_object* v_key_2969_; lean_object* v_val_2970_; lean_object* v_rchild_2971_; lean_object* v_val_2972_; lean_object* v___x_2973_; 
v_lchild_2968_ = lean_ctor_get(v_x_2967_, 0);
lean_inc(v_lchild_2968_);
v_key_2969_ = lean_ctor_get(v_x_2967_, 1);
lean_inc_n(v_key_2969_, 2);
v_val_2970_ = lean_ctor_get(v_x_2967_, 2);
lean_inc(v_val_2970_);
v_rchild_2971_ = lean_ctor_get(v_x_2967_, 3);
lean_inc(v_rchild_2971_);
lean_dec_ref_known(v_x_2967_, 4);
lean_inc_ref(v_cmp_2965_);
lean_inc_ref_n(v_f_2964_, 2);
v_val_2972_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2964_, v_cmp_2965_, v_x_2966_, v_lchild_2968_);
v___x_2973_ = lean_apply_2(v_f_2964_, v_key_2969_, v_val_2970_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_dec(v_key_2969_);
v_x_2966_ = v_val_2972_;
v_x_2967_ = v_rchild_2971_;
goto _start;
}
else
{
lean_object* v_val_2975_; lean_object* v___x_2976_; 
v_val_2975_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_val_2975_);
lean_dec_ref_known(v___x_2973_, 1);
lean_inc_ref(v_cmp_2965_);
v___x_2976_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2965_, v_val_2972_, v_key_2969_, v_val_2975_);
v_x_2966_ = v___x_2976_;
v_x_2967_ = v_rchild_2971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* v_cmp_2978_, lean_object* v_f_2979_, lean_object* v_m_2980_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = lean_box(0);
v___x_2982_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2979_, v_cmp_2978_, v___x_2981_, v_m_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* v_00_u03b1_2983_, lean_object* v_00_u03b2_2984_, lean_object* v_cmp_2985_, lean_object* v_00_u03b3_2986_, lean_object* v_f_2987_, lean_object* v_m_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_RBMap_filterMap___redArg(v_cmp_2985_, v_f_2987_, v_m_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* v_00_u03b1_2990_, lean_object* v_00_u03b2_2991_, lean_object* v_00_u03b3_2992_, lean_object* v_f_2993_, lean_object* v_cmp_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2993_, v_cmp_2994_, v_x_2995_, v_x_2996_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* v_cmp_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
if (lean_obj_tag(v_x_3000_) == 0)
{
lean_dec_ref(v_cmp_2998_);
return v_x_2999_;
}
else
{
lean_object* v_head_3001_; lean_object* v_tail_3002_; lean_object* v_fst_3003_; lean_object* v_snd_3004_; lean_object* v___x_3005_; 
v_head_3001_ = lean_ctor_get(v_x_3000_, 0);
lean_inc(v_head_3001_);
v_tail_3002_ = lean_ctor_get(v_x_3000_, 1);
lean_inc(v_tail_3002_);
lean_dec_ref_known(v_x_3000_, 2);
v_fst_3003_ = lean_ctor_get(v_head_3001_, 0);
lean_inc(v_fst_3003_);
v_snd_3004_ = lean_ctor_get(v_head_3001_, 1);
lean_inc(v_snd_3004_);
lean_dec(v_head_3001_);
lean_inc_ref(v_cmp_2998_);
v___x_3005_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2998_, v_x_2999_, v_fst_3003_, v_snd_3004_);
v_x_2999_ = v___x_3005_;
v_x_3000_ = v_tail_3002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* v_l_3007_, lean_object* v_cmp_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_box(0);
v___x_3010_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3008_, v___x_3009_, v_l_3007_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* v_00_u03b1_3011_, lean_object* v_00_u03b2_3012_, lean_object* v_l_3013_, lean_object* v_cmp_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_rbmapOf___redArg(v_l_3013_, v_cmp_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* v_00_u03b1_3016_, lean_object* v_00_u03b2_3017_, lean_object* v_cmp_3018_, lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3018_, v_x_3019_, v_x_3020_);
return v___x_3021_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_RBMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
