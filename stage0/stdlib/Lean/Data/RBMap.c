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
lean_inc_ref_n(v_f_111_, 2);
v___x_116_ = l_Lean_RBNode_depth___redArg(v_f_111_, v_lchild_114_);
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
lean_inc_n(v_f_170_, 2);
v___x_177_ = l_Lean_RBNode_fold___redArg(v_f_170_, v_x_171_, v_lchild_173_);
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
lean_inc_n(v_toBind_202_, 2);
v_lchild_203_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_lchild_203_);
v_key_204_ = lean_ctor_get(v_x_197_, 1);
lean_inc(v_key_204_);
v_val_205_ = lean_ctor_get(v_x_197_, 2);
lean_inc(v_val_205_);
v_rchild_206_ = lean_ctor_get(v_x_197_, 3);
lean_inc(v_rchild_206_);
lean_dec_ref(v_x_197_);
lean_inc_n(v_f_196_, 2);
lean_inc_ref(v_inst_195_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_207_, 0, v_inst_195_);
lean_closure_set(v___f_207_, 1, v_f_196_);
lean_closure_set(v___f_207_, 2, v_rchild_206_);
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
lean_inc_n(v_toBind_238_, 2);
v_lchild_239_ = lean_ctor_get(v_x_234_, 0);
lean_inc(v_lchild_239_);
v_key_240_ = lean_ctor_get(v_x_234_, 1);
lean_inc(v_key_240_);
v_val_241_ = lean_ctor_get(v_x_234_, 2);
lean_inc(v_val_241_);
v_rchild_242_ = lean_ctor_get(v_x_234_, 3);
lean_inc(v_rchild_242_);
lean_dec_ref(v_x_234_);
lean_inc_n(v_f_232_, 2);
lean_inc_ref(v_inst_231_);
v___f_243_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_243_, 0, v_inst_231_);
lean_closure_set(v___f_243_, 1, v_f_232_);
lean_closure_set(v___f_243_, 2, v_rchild_242_);
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
lean_inc_n(v_toBind_281_, 2);
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
lean_inc_n(v_f_273_, 2);
lean_inc_ref(v_inst_272_);
lean_inc_n(v_toPure_282_, 2);
v___f_287_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0), 5, 4);
lean_closure_set(v___f_287_, 0, v_toPure_282_);
lean_closure_set(v___f_287_, 1, v_inst_272_);
lean_closure_set(v___f_287_, 2, v_f_273_);
lean_closure_set(v___f_287_, 3, v_rchild_286_);
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
lean_inc_n(v_f_336_, 2);
v___x_343_ = l_Lean_RBNode_revFold___redArg(v_f_336_, v_x_337_, v_rchild_342_);
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
lean_object* v_a_910_; lean_object* v_kx_911_; lean_object* v_vx_912_; lean_object* v_b_913_; lean_object* v_a_917_; lean_object* v_kx_918_; lean_object* v_vx_919_; lean_object* v_b_920_; lean_object* v_ky_921_; lean_object* v_vy_922_; lean_object* v_c_923_; lean_object* v_kz_924_; lean_object* v_vz_925_; lean_object* v_d_926_; lean_object* v_l_933_; lean_object* v_k_934_; lean_object* v_v_935_; lean_object* v_a_936_; lean_object* v_ky_937_; lean_object* v_vy_938_; lean_object* v_b_939_; lean_object* v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; lean_object* v___y_961_; uint8_t v___y_962_; lean_object* v_a_963_; lean_object* v_kx_964_; lean_object* v_vx_965_; lean_object* v_b_966_; lean_object* v_ky_967_; lean_object* v_vy_968_; lean_object* v_c_969_; lean_object* v_kz_970_; lean_object* v_vz_971_; lean_object* v_d_972_; lean_object* v___y_978_; lean_object* v___y_979_; uint8_t v___y_980_; lean_object* v___y_981_; uint8_t v___y_982_; lean_object* v_a_983_; lean_object* v_kx_984_; lean_object* v_vx_985_; lean_object* v_b_986_; lean_object* v_l_990_; lean_object* v_k_991_; lean_object* v_v_992_; lean_object* v_a_993_; lean_object* v_ky_994_; lean_object* v_vy_995_; lean_object* v_b_996_; lean_object* v_kz_997_; lean_object* v_vz_998_; lean_object* v_c_999_; lean_object* v_l_1031_; lean_object* v_k_1032_; lean_object* v_v_1033_; lean_object* v_r_1034_; 
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
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*4, v___y_960_);
v___x_974_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_974_, 0, v_c_969_);
lean_ctor_set(v___x_974_, 1, v_kz_970_);
lean_ctor_set(v___x_974_, 2, v_vz_971_);
lean_ctor_set(v___x_974_, 3, v_d_972_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*4, v___y_960_);
v___x_975_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v_ky_967_);
lean_ctor_set(v___x_975_, 2, v_vy_968_);
lean_ctor_set(v___x_975_, 3, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*4, v___y_962_);
v___x_976_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_976_, 0, v___y_961_);
lean_ctor_set(v___x_976_, 1, v___y_959_);
lean_ctor_set(v___x_976_, 2, v___y_958_);
lean_ctor_set(v___x_976_, 3, v___x_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*4, v___y_962_);
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
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*4, v___y_980_);
v___x_988_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_988_, 0, v___y_981_);
lean_ctor_set(v___x_988_, 1, v___y_979_);
lean_ctor_set(v___x_988_, 2, v___y_978_);
lean_ctor_set(v___x_988_, 3, v___x_987_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*4, v___y_982_);
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
v___y_958_ = v_vy_995_;
v___y_959_ = v_ky_994_;
v___y_960_ = v___x_1001_;
v___y_961_ = v___x_1002_;
v___y_962_ = v___x_1000_;
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
v___y_958_ = v_vy_995_;
v___y_959_ = v_ky_994_;
v___y_960_ = v___x_1001_;
v___y_961_ = v___x_1002_;
v___y_962_ = v___x_1000_;
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
v___y_978_ = v_vy_995_;
v___y_979_ = v_ky_994_;
v___y_980_ = v___x_1001_;
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1000_;
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
v___y_978_ = v_vy_995_;
v___y_979_ = v_ky_994_;
v___y_980_ = v___x_1001_;
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1000_;
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
v___y_958_ = v_vy_995_;
v___y_959_ = v_ky_994_;
v___y_960_ = v___x_1001_;
v___y_961_ = v___x_1002_;
v___y_962_ = v___x_1000_;
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
v___y_978_ = v_vy_995_;
v___y_979_ = v_ky_994_;
v___y_980_ = v___x_1001_;
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1000_;
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
v___y_978_ = v_vy_995_;
v___y_979_ = v_ky_994_;
v___y_980_ = v___x_1001_;
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1000_;
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
v___y_978_ = v_vy_995_;
v___y_979_ = v_ky_994_;
v___y_980_ = v___x_1001_;
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1000_;
v_a_983_ = v_b_996_;
v_kx_984_ = v_kz_997_;
v_vx_985_ = v_vz_998_;
v_b_986_ = v___x_1003_;
goto v___jp_977_;
}
}
else
{
v___y_978_ = v_vy_995_;
v___y_979_ = v_ky_994_;
v___y_980_ = v___x_1001_;
v___y_981_ = v___x_1002_;
v___y_982_ = v___x_1000_;
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
uint8_t v___y_1094_; lean_object* v_a_1095_; lean_object* v_kx_1096_; lean_object* v_vx_1097_; lean_object* v_b_1098_; lean_object* v_ky_1099_; lean_object* v_vy_1100_; lean_object* v_c_1101_; lean_object* v_kz_1102_; lean_object* v_vz_1103_; lean_object* v_d_1104_; lean_object* v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1119_; uint8_t v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v_a_1124_; lean_object* v_kx_1125_; lean_object* v_vx_1126_; lean_object* v_b_1127_; lean_object* v_ky_1128_; lean_object* v_vy_1129_; lean_object* v_c_1130_; lean_object* v_kz_1131_; lean_object* v_vz_1132_; lean_object* v_d_1133_; lean_object* v___y_1138_; uint8_t v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; lean_object* v_a_1143_; lean_object* v_kx_1144_; lean_object* v_vx_1145_; lean_object* v_b_1146_; 
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
lean_ctor_set(v___x_1116_, 0, v___y_1113_);
lean_ctor_set(v___x_1116_, 1, v_k_1087_);
lean_ctor_set(v___x_1116_, 2, v_v_1088_);
lean_ctor_set(v___x_1116_, 3, v_r_1089_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*4, v___y_1111_);
v___x_1117_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1117_, 0, v___y_1115_);
lean_ctor_set(v___x_1117_, 1, v___y_1110_);
lean_ctor_set(v___x_1117_, 2, v___y_1112_);
lean_ctor_set(v___x_1117_, 3, v___x_1116_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*4, v___y_1114_);
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
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*4, v___y_1123_);
v___y_1110_ = v___y_1119_;
v___y_1111_ = v___y_1120_;
v___y_1112_ = v___y_1122_;
v___y_1113_ = v___y_1121_;
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
v___y_1112_ = v___y_1141_;
v___y_1113_ = v___y_1140_;
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
v___y_1119_ = v_key_1156_;
v___y_1120_ = v_color_1151_;
v___y_1121_ = v_rchild_1158_;
v___y_1122_ = v_val_1157_;
v___y_1123_ = v_color_1149_;
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
v___y_1119_ = v_key_1156_;
v___y_1120_ = v_color_1151_;
v___y_1121_ = v_rchild_1158_;
v___y_1122_ = v_val_1157_;
v___y_1123_ = v_color_1149_;
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
v___y_1138_ = v_key_1156_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_rchild_1158_;
v___y_1141_ = v_val_1157_;
v___y_1142_ = v_color_1149_;
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
v___y_1138_ = v_key_1156_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_rchild_1158_;
v___y_1141_ = v_val_1157_;
v___y_1142_ = v_color_1149_;
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
v___y_1119_ = v_key_1156_;
v___y_1120_ = v_color_1151_;
v___y_1121_ = v_rchild_1158_;
v___y_1122_ = v_val_1157_;
v___y_1123_ = v_color_1149_;
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
v___y_1138_ = v_key_1156_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_rchild_1158_;
v___y_1141_ = v_val_1157_;
v___y_1142_ = v_color_1149_;
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
v___y_1138_ = v_key_1156_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_rchild_1158_;
v___y_1141_ = v_val_1157_;
v___y_1142_ = v_color_1149_;
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
v___y_1138_ = v_key_1156_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_rchild_1158_;
v___y_1141_ = v_val_1157_;
v___y_1142_ = v_color_1149_;
v_a_1143_ = v___x_1159_;
v_kx_1144_ = v_key_1153_;
v_vx_1145_ = v_val_1154_;
v_b_1146_ = v_lchild_1155_;
goto v___jp_1137_;
}
}
else
{
v___y_1138_ = v_key_1156_;
v___y_1139_ = v_color_1151_;
v___y_1140_ = v_rchild_1158_;
v___y_1141_ = v_val_1157_;
v___y_1142_ = v_color_1149_;
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
if (lean_obj_tag(v_x_1302_) == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_h__2_1304_);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_apply_1(v_h__1_1303_, v___x_1305_);
return v___x_1306_;
}
else
{
uint8_t v_color_1307_; lean_object* v_lchild_1308_; lean_object* v_key_1309_; lean_object* v_val_1310_; lean_object* v_rchild_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec(v_h__1_1303_);
v_color_1307_ = lean_ctor_get_uint8(v_x_1302_, sizeof(void*)*4);
v_lchild_1308_ = lean_ctor_get(v_x_1302_, 0);
lean_inc(v_lchild_1308_);
v_key_1309_ = lean_ctor_get(v_x_1302_, 1);
lean_inc(v_key_1309_);
v_val_1310_ = lean_ctor_get(v_x_1302_, 2);
lean_inc(v_val_1310_);
v_rchild_1311_ = lean_ctor_get(v_x_1302_, 3);
lean_inc(v_rchild_1311_);
lean_dec_ref(v_x_1302_);
v___x_1312_ = lean_box(v_color_1307_);
v___x_1313_ = lean_apply_5(v_h__2_1304_, v___x_1312_, v_lchild_1308_, v_key_1309_, v_val_1310_, v_rchild_1311_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* v_x_1314_, lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1314_) == 0)
{
return v_x_1315_;
}
else
{
if (lean_obj_tag(v_x_1315_) == 0)
{
return v_x_1314_;
}
else
{
uint8_t v_color_1316_; lean_object* v_lchild_1317_; lean_object* v_key_1318_; lean_object* v_val_1319_; lean_object* v_rchild_1320_; uint8_t v_color_1321_; lean_object* v_lchild_1322_; lean_object* v_key_1323_; lean_object* v_val_1324_; lean_object* v_rchild_1325_; lean_object* v_bc_1327_; lean_object* v_bc_1331_; 
v_color_1316_ = lean_ctor_get_uint8(v_x_1314_, sizeof(void*)*4);
v_lchild_1317_ = lean_ctor_get(v_x_1314_, 0);
v_key_1318_ = lean_ctor_get(v_x_1314_, 1);
v_val_1319_ = lean_ctor_get(v_x_1314_, 2);
v_rchild_1320_ = lean_ctor_get(v_x_1314_, 3);
v_color_1321_ = lean_ctor_get_uint8(v_x_1315_, sizeof(void*)*4);
v_lchild_1322_ = lean_ctor_get(v_x_1315_, 0);
v_key_1323_ = lean_ctor_get(v_x_1315_, 1);
v_val_1324_ = lean_ctor_get(v_x_1315_, 2);
v_rchild_1325_ = lean_ctor_get(v_x_1315_, 3);
if (v_color_1321_ == 0)
{
lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1368_; 
lean_inc(v_rchild_1325_);
lean_inc(v_val_1324_);
lean_inc(v_key_1323_);
lean_inc(v_lchild_1322_);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1369_ = lean_ctor_get(v_x_1315_, 3);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_x_1315_, 2);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_x_1315_, 1);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_x_1315_, 0);
lean_dec(v_unused_1372_);
v___x_1335_ = v_x_1315_;
v_isShared_1336_ = v_isSharedCheck_1368_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v_x_1315_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1368_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
if (v_color_1316_ == 0)
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1359_; 
lean_inc(v_rchild_1320_);
lean_inc(v_val_1319_);
lean_inc(v_key_1318_);
lean_inc(v_lchild_1317_);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_x_1314_);
if (v_isSharedCheck_1359_ == 0)
{
lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1360_ = lean_ctor_get(v_x_1314_, 3);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_x_1314_, 2);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_x_1314_, 1);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_x_1314_, 0);
lean_dec(v_unused_1363_);
v___x_1338_ = v_x_1314_;
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v_x_1314_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1359_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1320_, v_lchild_1322_);
if (lean_obj_tag(v___x_1340_) == 1)
{
uint8_t v_color_1341_; 
v_color_1341_ = lean_ctor_get_uint8(v___x_1340_, sizeof(void*)*4);
if (v_color_1341_ == 0)
{
lean_object* v_lchild_1342_; lean_object* v_key_1343_; lean_object* v_val_1344_; lean_object* v_rchild_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1358_; 
v_lchild_1342_ = lean_ctor_get(v___x_1340_, 0);
v_key_1343_ = lean_ctor_get(v___x_1340_, 1);
v_val_1344_ = lean_ctor_get(v___x_1340_, 2);
v_rchild_1345_ = lean_ctor_get(v___x_1340_, 3);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1347_ = v___x_1340_;
v_isShared_1348_ = v_isSharedCheck_1358_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_rchild_1345_);
lean_inc(v_val_1344_);
lean_inc(v_key_1343_);
lean_inc(v_lchild_1342_);
lean_dec(v___x_1340_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1358_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 3, v_lchild_1342_);
lean_ctor_set(v___x_1347_, 2, v_val_1319_);
lean_ctor_set(v___x_1347_, 1, v_key_1318_);
lean_ctor_set(v___x_1347_, 0, v_lchild_1317_);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_lchild_1317_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_val_1319_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_lchild_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*4, v_color_1341_);
v___x_1350_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_rchild_1345_);
v___x_1352_ = v___x_1335_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_rchild_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_key_1323_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_val_1324_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_rchild_1325_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*4, v_color_1341_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 3, v___x_1352_);
lean_ctor_set(v___x_1338_, 2, v_val_1344_);
lean_ctor_set(v___x_1338_, 1, v_key_1343_);
lean_ctor_set(v___x_1338_, 0, v___x_1350_);
v___x_1354_ = v___x_1338_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_key_1343_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_val_1344_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*4, v_color_1341_);
return v___x_1354_;
}
}
}
}
}
else
{
lean_del_object(v___x_1338_);
lean_del_object(v___x_1335_);
v_bc_1331_ = v___x_1340_;
goto v___jp_1330_;
}
}
else
{
lean_del_object(v___x_1338_);
lean_del_object(v___x_1335_);
v_bc_1331_ = v___x_1340_;
goto v___jp_1330_;
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = l_Lean_RBNode_appendTrees___redArg(v_x_1314_, v_lchild_1322_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1364_);
v___x_1366_ = v___x_1335_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_key_1323_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_val_1324_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_rchild_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1367_, sizeof(void*)*4, v_color_1321_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1407_; 
lean_inc(v_rchild_1320_);
lean_inc(v_val_1319_);
lean_inc(v_key_1318_);
lean_inc(v_lchild_1317_);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_x_1314_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1408_ = lean_ctor_get(v_x_1314_, 3);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_x_1314_, 2);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_x_1314_, 1);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_x_1314_, 0);
lean_dec(v_unused_1411_);
v___x_1374_ = v_x_1314_;
v_isShared_1375_ = v_isSharedCheck_1407_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_x_1314_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1407_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
if (v_color_1316_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1320_, v_x_1315_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 3, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_lchild_1317_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_val_1319_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v___x_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, sizeof(void*)*4, v_color_1316_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
else
{
lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1402_; 
lean_inc(v_rchild_1325_);
lean_inc(v_val_1324_);
lean_inc(v_key_1323_);
lean_inc(v_lchild_1322_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_x_1315_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1403_ = lean_ctor_get(v_x_1315_, 3);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_x_1315_, 2);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_x_1315_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_x_1315_, 0);
lean_dec(v_unused_1406_);
v___x_1381_ = v_x_1315_;
v_isShared_1382_ = v_isSharedCheck_1402_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_x_1315_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1402_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1320_, v_lchild_1322_);
if (lean_obj_tag(v___x_1383_) == 1)
{
uint8_t v_color_1384_; 
v_color_1384_ = lean_ctor_get_uint8(v___x_1383_, sizeof(void*)*4);
if (v_color_1384_ == 0)
{
lean_object* v_lchild_1385_; lean_object* v_key_1386_; lean_object* v_val_1387_; lean_object* v_rchild_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v_lchild_1385_ = lean_ctor_get(v___x_1383_, 0);
v_key_1386_ = lean_ctor_get(v___x_1383_, 1);
v_val_1387_ = lean_ctor_get(v___x_1383_, 2);
v_rchild_1388_ = lean_ctor_get(v___x_1383_, 3);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1390_ = v___x_1383_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_rchild_1388_);
lean_inc(v_val_1387_);
lean_inc(v_key_1386_);
lean_inc(v_lchild_1385_);
lean_dec(v___x_1383_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 3, v_lchild_1385_);
lean_ctor_set(v___x_1390_, 2, v_val_1319_);
lean_ctor_set(v___x_1390_, 1, v_key_1318_);
lean_ctor_set(v___x_1390_, 0, v_lchild_1317_);
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_lchild_1317_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_key_1318_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_val_1319_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_lchild_1385_);
v___x_1393_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; 
lean_ctor_set_uint8(v___x_1393_, sizeof(void*)*4, v_color_1316_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_rchild_1388_);
v___x_1395_ = v___x_1381_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_rchild_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_key_1323_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_val_1324_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_rchild_1325_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*4, v_color_1316_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 3, v___x_1395_);
lean_ctor_set(v___x_1374_, 2, v_val_1387_);
lean_ctor_set(v___x_1374_, 1, v_key_1386_);
lean_ctor_set(v___x_1374_, 0, v___x_1393_);
v___x_1397_ = v___x_1374_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_key_1386_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_val_1387_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*4, v_color_1384_);
return v___x_1397_;
}
}
}
}
}
else
{
lean_del_object(v___x_1381_);
lean_del_object(v___x_1374_);
v_bc_1327_ = v___x_1383_;
goto v___jp_1326_;
}
}
else
{
lean_del_object(v___x_1381_);
lean_del_object(v___x_1374_);
v_bc_1327_ = v___x_1383_;
goto v___jp_1326_;
}
}
}
}
}
v___jp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1328_, 0, v_bc_1327_);
lean_ctor_set(v___x_1328_, 1, v_key_1323_);
lean_ctor_set(v___x_1328_, 2, v_val_1324_);
lean_ctor_set(v___x_1328_, 3, v_rchild_1325_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*4, v_color_1316_);
v___x_1329_ = l_Lean_RBNode_balLeft___redArg(v_lchild_1317_, v_key_1318_, v_val_1319_, v___x_1328_);
return v___x_1329_;
}
v___jp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1332_, 0, v_bc_1331_);
lean_ctor_set(v___x_1332_, 1, v_key_1323_);
lean_ctor_set(v___x_1332_, 2, v_val_1324_);
lean_ctor_set(v___x_1332_, 3, v_rchild_1325_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*4, v_color_1316_);
v___x_1333_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1333_, 0, v_lchild_1317_);
lean_ctor_set(v___x_1333_, 1, v_key_1318_);
lean_ctor_set(v___x_1333_, 2, v_val_1319_);
lean_ctor_set(v___x_1333_, 3, v___x_1332_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*4, v_color_1316_);
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_RBNode_appendTrees___redArg(v_x_1414_, v_x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_h__1_1419_, lean_object* v_h__2_1420_, lean_object* v_h__3_1421_, lean_object* v_h__4_1422_, lean_object* v_h__5_1423_, lean_object* v_h__6_1424_){
_start:
{
if (lean_obj_tag(v_x_1417_) == 0)
{
lean_object* v___x_1425_; 
lean_dec(v_h__6_1424_);
lean_dec(v_h__5_1423_);
lean_dec(v_h__4_1422_);
lean_dec(v_h__3_1421_);
lean_dec(v_h__2_1420_);
v___x_1425_ = lean_apply_1(v_h__1_1419_, v_x_1418_);
return v___x_1425_;
}
else
{
lean_dec(v_h__1_1419_);
if (lean_obj_tag(v_x_1418_) == 0)
{
lean_object* v___x_1426_; 
lean_dec(v_h__6_1424_);
lean_dec(v_h__5_1423_);
lean_dec(v_h__4_1422_);
lean_dec(v_h__3_1421_);
v___x_1426_ = lean_apply_2(v_h__2_1420_, v_x_1417_, lean_box(0));
return v___x_1426_;
}
else
{
uint8_t v_color_1427_; 
lean_dec(v_h__2_1420_);
v_color_1427_ = lean_ctor_get_uint8(v_x_1418_, sizeof(void*)*4);
if (v_color_1427_ == 0)
{
uint8_t v_color_1428_; 
lean_dec(v_h__6_1424_);
lean_dec(v_h__4_1422_);
v_color_1428_ = lean_ctor_get_uint8(v_x_1417_, sizeof(void*)*4);
if (v_color_1428_ == 0)
{
lean_object* v_lchild_1429_; lean_object* v_key_1430_; lean_object* v_val_1431_; lean_object* v_rchild_1432_; lean_object* v_lchild_1433_; lean_object* v_key_1434_; lean_object* v_val_1435_; lean_object* v_rchild_1436_; lean_object* v___x_1437_; 
lean_dec(v_h__5_1423_);
v_lchild_1429_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_lchild_1429_);
v_key_1430_ = lean_ctor_get(v_x_1417_, 1);
lean_inc(v_key_1430_);
v_val_1431_ = lean_ctor_get(v_x_1417_, 2);
lean_inc(v_val_1431_);
v_rchild_1432_ = lean_ctor_get(v_x_1417_, 3);
lean_inc(v_rchild_1432_);
lean_dec_ref(v_x_1417_);
v_lchild_1433_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_lchild_1433_);
v_key_1434_ = lean_ctor_get(v_x_1418_, 1);
lean_inc(v_key_1434_);
v_val_1435_ = lean_ctor_get(v_x_1418_, 2);
lean_inc(v_val_1435_);
v_rchild_1436_ = lean_ctor_get(v_x_1418_, 3);
lean_inc(v_rchild_1436_);
lean_dec_ref(v_x_1418_);
v___x_1437_ = lean_apply_8(v_h__3_1421_, v_lchild_1429_, v_key_1430_, v_val_1431_, v_rchild_1432_, v_lchild_1433_, v_key_1434_, v_val_1435_, v_rchild_1436_);
return v___x_1437_;
}
else
{
lean_object* v_lchild_1438_; lean_object* v_key_1439_; lean_object* v_val_1440_; lean_object* v_rchild_1441_; lean_object* v___x_1442_; 
lean_dec(v_h__3_1421_);
v_lchild_1438_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_lchild_1438_);
v_key_1439_ = lean_ctor_get(v_x_1418_, 1);
lean_inc(v_key_1439_);
v_val_1440_ = lean_ctor_get(v_x_1418_, 2);
lean_inc(v_val_1440_);
v_rchild_1441_ = lean_ctor_get(v_x_1418_, 3);
lean_inc(v_rchild_1441_);
lean_dec_ref(v_x_1418_);
v___x_1442_ = lean_apply_7(v_h__5_1423_, v_x_1417_, v_lchild_1438_, v_key_1439_, v_val_1440_, v_rchild_1441_, lean_box(0), lean_box(0));
return v___x_1442_;
}
}
else
{
uint8_t v_color_1443_; 
lean_dec(v_h__5_1423_);
lean_dec(v_h__3_1421_);
v_color_1443_ = lean_ctor_get_uint8(v_x_1417_, sizeof(void*)*4);
if (v_color_1443_ == 0)
{
lean_object* v_lchild_1444_; lean_object* v_key_1445_; lean_object* v_val_1446_; lean_object* v_rchild_1447_; lean_object* v___x_1448_; 
lean_dec(v_h__4_1422_);
v_lchild_1444_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_lchild_1444_);
v_key_1445_ = lean_ctor_get(v_x_1417_, 1);
lean_inc(v_key_1445_);
v_val_1446_ = lean_ctor_get(v_x_1417_, 2);
lean_inc(v_val_1446_);
v_rchild_1447_ = lean_ctor_get(v_x_1417_, 3);
lean_inc(v_rchild_1447_);
lean_dec_ref(v_x_1417_);
v___x_1448_ = lean_apply_7(v_h__6_1424_, v_lchild_1444_, v_key_1445_, v_val_1446_, v_rchild_1447_, v_x_1418_, lean_box(0), lean_box(0));
return v___x_1448_;
}
else
{
lean_object* v_lchild_1449_; lean_object* v_key_1450_; lean_object* v_val_1451_; lean_object* v_rchild_1452_; lean_object* v_lchild_1453_; lean_object* v_key_1454_; lean_object* v_val_1455_; lean_object* v_rchild_1456_; lean_object* v___x_1457_; 
lean_dec(v_h__6_1424_);
v_lchild_1449_ = lean_ctor_get(v_x_1417_, 0);
lean_inc(v_lchild_1449_);
v_key_1450_ = lean_ctor_get(v_x_1417_, 1);
lean_inc(v_key_1450_);
v_val_1451_ = lean_ctor_get(v_x_1417_, 2);
lean_inc(v_val_1451_);
v_rchild_1452_ = lean_ctor_get(v_x_1417_, 3);
lean_inc(v_rchild_1452_);
lean_dec_ref(v_x_1417_);
v_lchild_1453_ = lean_ctor_get(v_x_1418_, 0);
lean_inc(v_lchild_1453_);
v_key_1454_ = lean_ctor_get(v_x_1418_, 1);
lean_inc(v_key_1454_);
v_val_1455_ = lean_ctor_get(v_x_1418_, 2);
lean_inc(v_val_1455_);
v_rchild_1456_ = lean_ctor_get(v_x_1418_, 3);
lean_inc(v_rchild_1456_);
lean_dec_ref(v_x_1418_);
v___x_1457_ = lean_apply_8(v_h__4_1422_, v_lchild_1449_, v_key_1450_, v_val_1451_, v_rchild_1452_, v_lchild_1453_, v_key_1454_, v_val_1455_, v_rchild_1456_);
return v___x_1457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* v_00_u03b1_1458_, lean_object* v_00_u03b2_1459_, lean_object* v_motive_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_h__1_1463_, lean_object* v_h__2_1464_, lean_object* v_h__3_1465_, lean_object* v_h__4_1466_, lean_object* v_h__5_1467_, lean_object* v_h__6_1468_){
_start:
{
if (lean_obj_tag(v_x_1461_) == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
lean_dec(v_h__2_1464_);
v___x_1469_ = lean_apply_1(v_h__1_1463_, v_x_1462_);
return v___x_1469_;
}
else
{
lean_dec(v_h__1_1463_);
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v___x_1470_; 
lean_dec(v_h__6_1468_);
lean_dec(v_h__5_1467_);
lean_dec(v_h__4_1466_);
lean_dec(v_h__3_1465_);
v___x_1470_ = lean_apply_2(v_h__2_1464_, v_x_1461_, lean_box(0));
return v___x_1470_;
}
else
{
uint8_t v_color_1471_; 
lean_dec(v_h__2_1464_);
v_color_1471_ = lean_ctor_get_uint8(v_x_1462_, sizeof(void*)*4);
if (v_color_1471_ == 0)
{
uint8_t v_color_1472_; 
lean_dec(v_h__6_1468_);
lean_dec(v_h__4_1466_);
v_color_1472_ = lean_ctor_get_uint8(v_x_1461_, sizeof(void*)*4);
if (v_color_1472_ == 0)
{
lean_object* v_lchild_1473_; lean_object* v_key_1474_; lean_object* v_val_1475_; lean_object* v_rchild_1476_; lean_object* v_lchild_1477_; lean_object* v_key_1478_; lean_object* v_val_1479_; lean_object* v_rchild_1480_; lean_object* v___x_1481_; 
lean_dec(v_h__5_1467_);
v_lchild_1473_ = lean_ctor_get(v_x_1461_, 0);
lean_inc(v_lchild_1473_);
v_key_1474_ = lean_ctor_get(v_x_1461_, 1);
lean_inc(v_key_1474_);
v_val_1475_ = lean_ctor_get(v_x_1461_, 2);
lean_inc(v_val_1475_);
v_rchild_1476_ = lean_ctor_get(v_x_1461_, 3);
lean_inc(v_rchild_1476_);
lean_dec_ref(v_x_1461_);
v_lchild_1477_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_lchild_1477_);
v_key_1478_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_key_1478_);
v_val_1479_ = lean_ctor_get(v_x_1462_, 2);
lean_inc(v_val_1479_);
v_rchild_1480_ = lean_ctor_get(v_x_1462_, 3);
lean_inc(v_rchild_1480_);
lean_dec_ref(v_x_1462_);
v___x_1481_ = lean_apply_8(v_h__3_1465_, v_lchild_1473_, v_key_1474_, v_val_1475_, v_rchild_1476_, v_lchild_1477_, v_key_1478_, v_val_1479_, v_rchild_1480_);
return v___x_1481_;
}
else
{
lean_object* v_lchild_1482_; lean_object* v_key_1483_; lean_object* v_val_1484_; lean_object* v_rchild_1485_; lean_object* v___x_1486_; 
lean_dec(v_h__3_1465_);
v_lchild_1482_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_lchild_1482_);
v_key_1483_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_key_1483_);
v_val_1484_ = lean_ctor_get(v_x_1462_, 2);
lean_inc(v_val_1484_);
v_rchild_1485_ = lean_ctor_get(v_x_1462_, 3);
lean_inc(v_rchild_1485_);
lean_dec_ref(v_x_1462_);
v___x_1486_ = lean_apply_7(v_h__5_1467_, v_x_1461_, v_lchild_1482_, v_key_1483_, v_val_1484_, v_rchild_1485_, lean_box(0), lean_box(0));
return v___x_1486_;
}
}
else
{
uint8_t v_color_1487_; 
lean_dec(v_h__5_1467_);
lean_dec(v_h__3_1465_);
v_color_1487_ = lean_ctor_get_uint8(v_x_1461_, sizeof(void*)*4);
if (v_color_1487_ == 0)
{
lean_object* v_lchild_1488_; lean_object* v_key_1489_; lean_object* v_val_1490_; lean_object* v_rchild_1491_; lean_object* v___x_1492_; 
lean_dec(v_h__4_1466_);
v_lchild_1488_ = lean_ctor_get(v_x_1461_, 0);
lean_inc(v_lchild_1488_);
v_key_1489_ = lean_ctor_get(v_x_1461_, 1);
lean_inc(v_key_1489_);
v_val_1490_ = lean_ctor_get(v_x_1461_, 2);
lean_inc(v_val_1490_);
v_rchild_1491_ = lean_ctor_get(v_x_1461_, 3);
lean_inc(v_rchild_1491_);
lean_dec_ref(v_x_1461_);
v___x_1492_ = lean_apply_7(v_h__6_1468_, v_lchild_1488_, v_key_1489_, v_val_1490_, v_rchild_1491_, v_x_1462_, lean_box(0), lean_box(0));
return v___x_1492_;
}
else
{
lean_object* v_lchild_1493_; lean_object* v_key_1494_; lean_object* v_val_1495_; lean_object* v_rchild_1496_; lean_object* v_lchild_1497_; lean_object* v_key_1498_; lean_object* v_val_1499_; lean_object* v_rchild_1500_; lean_object* v___x_1501_; 
lean_dec(v_h__6_1468_);
v_lchild_1493_ = lean_ctor_get(v_x_1461_, 0);
lean_inc(v_lchild_1493_);
v_key_1494_ = lean_ctor_get(v_x_1461_, 1);
lean_inc(v_key_1494_);
v_val_1495_ = lean_ctor_get(v_x_1461_, 2);
lean_inc(v_val_1495_);
v_rchild_1496_ = lean_ctor_get(v_x_1461_, 3);
lean_inc(v_rchild_1496_);
lean_dec_ref(v_x_1461_);
v_lchild_1497_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_lchild_1497_);
v_key_1498_ = lean_ctor_get(v_x_1462_, 1);
lean_inc(v_key_1498_);
v_val_1499_ = lean_ctor_get(v_x_1462_, 2);
lean_inc(v_val_1499_);
v_rchild_1500_ = lean_ctor_get(v_x_1462_, 3);
lean_inc(v_rchild_1500_);
lean_dec_ref(v_x_1462_);
v___x_1501_ = lean_apply_8(v_h__4_1466_, v_lchild_1493_, v_key_1494_, v_val_1495_, v_rchild_1496_, v_lchild_1497_, v_key_1498_, v_val_1499_, v_rchild_1500_);
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* v_x_1502_, lean_object* v_h__1_1503_, lean_object* v_h__2_1504_){
_start:
{
if (lean_obj_tag(v_x_1502_) == 1)
{
uint8_t v_color_1505_; 
v_color_1505_ = lean_ctor_get_uint8(v_x_1502_, sizeof(void*)*4);
if (v_color_1505_ == 0)
{
lean_object* v_lchild_1506_; lean_object* v_key_1507_; lean_object* v_val_1508_; lean_object* v_rchild_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__2_1504_);
v_lchild_1506_ = lean_ctor_get(v_x_1502_, 0);
lean_inc(v_lchild_1506_);
v_key_1507_ = lean_ctor_get(v_x_1502_, 1);
lean_inc(v_key_1507_);
v_val_1508_ = lean_ctor_get(v_x_1502_, 2);
lean_inc(v_val_1508_);
v_rchild_1509_ = lean_ctor_get(v_x_1502_, 3);
lean_inc(v_rchild_1509_);
lean_dec_ref(v_x_1502_);
v___x_1510_ = lean_apply_4(v_h__1_1503_, v_lchild_1506_, v_key_1507_, v_val_1508_, v_rchild_1509_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_h__1_1503_);
v___x_1511_ = lean_apply_2(v_h__2_1504_, v_x_1502_, lean_box(0));
return v___x_1511_;
}
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_h__1_1503_);
v___x_1512_ = lean_apply_2(v_h__2_1504_, v_x_1502_, lean_box(0));
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* v_00_u03b1_1513_, lean_object* v_00_u03b2_1514_, lean_object* v_motive_1515_, lean_object* v_x_1516_, lean_object* v_h__1_1517_, lean_object* v_h__2_1518_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 1)
{
uint8_t v_color_1519_; 
v_color_1519_ = lean_ctor_get_uint8(v_x_1516_, sizeof(void*)*4);
if (v_color_1519_ == 0)
{
lean_object* v_lchild_1520_; lean_object* v_key_1521_; lean_object* v_val_1522_; lean_object* v_rchild_1523_; lean_object* v___x_1524_; 
lean_dec(v_h__2_1518_);
v_lchild_1520_ = lean_ctor_get(v_x_1516_, 0);
lean_inc(v_lchild_1520_);
v_key_1521_ = lean_ctor_get(v_x_1516_, 1);
lean_inc(v_key_1521_);
v_val_1522_ = lean_ctor_get(v_x_1516_, 2);
lean_inc(v_val_1522_);
v_rchild_1523_ = lean_ctor_get(v_x_1516_, 3);
lean_inc(v_rchild_1523_);
lean_dec_ref(v_x_1516_);
v___x_1524_ = lean_apply_4(v_h__1_1517_, v_lchild_1520_, v_key_1521_, v_val_1522_, v_rchild_1523_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_h__1_1517_);
v___x_1525_ = lean_apply_2(v_h__2_1518_, v_x_1516_, lean_box(0));
return v___x_1525_;
}
}
else
{
lean_object* v___x_1526_; 
lean_dec(v_h__1_1517_);
v___x_1526_ = lean_apply_2(v_h__2_1518_, v_x_1516_, lean_box(0));
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* v_cmp_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_dec(v_x_1528_);
lean_dec_ref(v_cmp_1527_);
return v_x_1529_;
}
else
{
lean_object* v_lchild_1530_; lean_object* v_key_1531_; lean_object* v_val_1532_; lean_object* v_rchild_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1556_; 
v_lchild_1530_ = lean_ctor_get(v_x_1529_, 0);
v_key_1531_ = lean_ctor_get(v_x_1529_, 1);
v_val_1532_ = lean_ctor_get(v_x_1529_, 2);
v_rchild_1533_ = lean_ctor_get(v_x_1529_, 3);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1535_ = v_x_1529_;
v_isShared_1536_ = v_isSharedCheck_1556_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_rchild_1533_);
lean_inc(v_val_1532_);
lean_inc(v_key_1531_);
lean_inc(v_lchild_1530_);
lean_dec(v_x_1529_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1556_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
lean_inc_ref(v_cmp_1527_);
lean_inc(v_key_1531_);
lean_inc(v_x_1528_);
v___x_1537_ = lean_apply_2(v_cmp_1527_, v_x_1528_, v_key_1531_);
v___x_1538_ = lean_unbox(v___x_1537_);
switch(v___x_1538_)
{
case 0:
{
uint8_t v___x_1539_; 
v___x_1539_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1530_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1540_ = 0;
v___x_1541_ = l_Lean_RBNode_del___redArg(v_cmp_1527_, v_x_1528_, v_lchild_1530_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1541_);
v___x_1543_ = v___x_1535_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_key_1531_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_val_1532_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_rchild_1533_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*4, v___x_1540_);
return v___x_1543_;
}
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_del_object(v___x_1535_);
v___x_1545_ = l_Lean_RBNode_del___redArg(v_cmp_1527_, v_x_1528_, v_lchild_1530_);
v___x_1546_ = l_Lean_RBNode_balLeft___redArg(v___x_1545_, v_key_1531_, v_val_1532_, v_rchild_1533_);
return v___x_1546_;
}
}
case 1:
{
lean_object* v___x_1547_; 
lean_del_object(v___x_1535_);
lean_dec(v_val_1532_);
lean_dec(v_key_1531_);
lean_dec(v_x_1528_);
lean_dec_ref(v_cmp_1527_);
v___x_1547_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_1530_, v_rchild_1533_);
return v___x_1547_;
}
default: 
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1533_);
if (v___x_1548_ == 0)
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = 0;
v___x_1550_ = l_Lean_RBNode_del___redArg(v_cmp_1527_, v_x_1528_, v_rchild_1533_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 3, v___x_1550_);
v___x_1552_ = v___x_1535_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_lchild_1530_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_key_1531_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_val_1532_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*4, v___x_1549_);
return v___x_1552_;
}
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_del_object(v___x_1535_);
v___x_1554_ = l_Lean_RBNode_del___redArg(v_cmp_1527_, v_x_1528_, v_rchild_1533_);
v___x_1555_ = l_Lean_RBNode_balRight___redArg(v_lchild_1530_, v_key_1531_, v_val_1532_, v___x_1554_);
return v___x_1555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_cmp_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_RBNode_del___redArg(v_cmp_1559_, v_x_1560_, v_x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* v_cmp_1563_, lean_object* v_x_1564_, lean_object* v_t_1565_){
_start:
{
lean_object* v_t_1566_; lean_object* v___x_1567_; 
v_t_1566_ = l_Lean_RBNode_del___redArg(v_cmp_1563_, v_x_1564_, v_t_1565_);
v___x_1567_ = l_Lean_RBNode_setBlack___redArg(v_t_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_cmp_1570_, lean_object* v_x_1571_, lean_object* v_t_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_RBNode_erase___redArg(v_cmp_1570_, v_x_1571_, v_t_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* v_cmp_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
lean_object* v___x_1577_; 
lean_dec(v_x_1576_);
lean_dec_ref(v_cmp_1574_);
v___x_1577_ = lean_box(0);
return v___x_1577_;
}
else
{
lean_object* v_lchild_1578_; lean_object* v_key_1579_; lean_object* v_val_1580_; lean_object* v_rchild_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_lchild_1578_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_lchild_1578_);
v_key_1579_ = lean_ctor_get(v_x_1575_, 1);
lean_inc_n(v_key_1579_, 2);
v_val_1580_ = lean_ctor_get(v_x_1575_, 2);
lean_inc(v_val_1580_);
v_rchild_1581_ = lean_ctor_get(v_x_1575_, 3);
lean_inc(v_rchild_1581_);
lean_dec_ref(v_x_1575_);
lean_inc_ref(v_cmp_1574_);
lean_inc(v_x_1576_);
v___x_1582_ = lean_apply_2(v_cmp_1574_, v_x_1576_, v_key_1579_);
v___x_1583_ = lean_unbox(v___x_1582_);
switch(v___x_1583_)
{
case 0:
{
lean_dec(v_rchild_1581_);
lean_dec(v_val_1580_);
lean_dec(v_key_1579_);
v_x_1575_ = v_lchild_1578_;
goto _start;
}
case 1:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v_rchild_1581_);
lean_dec(v_lchild_1578_);
lean_dec(v_x_1576_);
lean_dec_ref(v_cmp_1574_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_key_1579_);
lean_ctor_set(v___x_1585_, 1, v_val_1580_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
default: 
{
lean_dec(v_val_1580_);
lean_dec(v_key_1579_);
lean_dec(v_lchild_1578_);
v_x_1575_ = v_rchild_1581_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_cmp_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_RBNode_findCore___redArg(v_cmp_1590_, v_x_1591_, v_x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* v_cmp_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_object* v___x_1597_; 
lean_dec(v_x_1596_);
lean_dec_ref(v_cmp_1594_);
v___x_1597_ = lean_box(0);
return v___x_1597_;
}
else
{
lean_object* v_lchild_1598_; lean_object* v_key_1599_; lean_object* v_val_1600_; lean_object* v_rchild_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_lchild_1598_ = lean_ctor_get(v_x_1595_, 0);
lean_inc(v_lchild_1598_);
v_key_1599_ = lean_ctor_get(v_x_1595_, 1);
lean_inc(v_key_1599_);
v_val_1600_ = lean_ctor_get(v_x_1595_, 2);
lean_inc(v_val_1600_);
v_rchild_1601_ = lean_ctor_get(v_x_1595_, 3);
lean_inc(v_rchild_1601_);
lean_dec_ref(v_x_1595_);
lean_inc_ref(v_cmp_1594_);
lean_inc(v_x_1596_);
v___x_1602_ = lean_apply_2(v_cmp_1594_, v_x_1596_, v_key_1599_);
v___x_1603_ = lean_unbox(v___x_1602_);
switch(v___x_1603_)
{
case 0:
{
lean_dec(v_rchild_1601_);
lean_dec(v_val_1600_);
v_x_1595_ = v_lchild_1598_;
goto _start;
}
case 1:
{
lean_object* v___x_1605_; 
lean_dec(v_rchild_1601_);
lean_dec(v_lchild_1598_);
lean_dec(v_x_1596_);
lean_dec_ref(v_cmp_1594_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_val_1600_);
return v___x_1605_;
}
default: 
{
lean_dec(v_val_1600_);
lean_dec(v_lchild_1598_);
v_x_1595_ = v_rchild_1601_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* v_00_u03b1_1607_, lean_object* v_cmp_1608_, lean_object* v_00_u03b2_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_RBNode_find___redArg(v_cmp_1608_, v_x_1610_, v_x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* v_cmp_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1614_) == 0)
{
lean_dec(v_x_1615_);
lean_dec_ref(v_cmp_1613_);
return v_x_1616_;
}
else
{
lean_object* v_lchild_1617_; lean_object* v_key_1618_; lean_object* v_val_1619_; lean_object* v_rchild_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_lchild_1617_ = lean_ctor_get(v_x_1614_, 0);
lean_inc(v_lchild_1617_);
v_key_1618_ = lean_ctor_get(v_x_1614_, 1);
lean_inc_n(v_key_1618_, 2);
v_val_1619_ = lean_ctor_get(v_x_1614_, 2);
lean_inc(v_val_1619_);
v_rchild_1620_ = lean_ctor_get(v_x_1614_, 3);
lean_inc(v_rchild_1620_);
lean_dec_ref(v_x_1614_);
lean_inc_ref(v_cmp_1613_);
lean_inc(v_x_1615_);
v___x_1621_ = lean_apply_2(v_cmp_1613_, v_x_1615_, v_key_1618_);
v___x_1622_ = lean_unbox(v___x_1621_);
switch(v___x_1622_)
{
case 0:
{
lean_dec(v_rchild_1620_);
lean_dec(v_val_1619_);
lean_dec(v_key_1618_);
v_x_1614_ = v_lchild_1617_;
goto _start;
}
case 1:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v_rchild_1620_);
lean_dec(v_lchild_1617_);
lean_dec(v_x_1616_);
lean_dec(v_x_1615_);
lean_dec_ref(v_cmp_1613_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_key_1618_);
lean_ctor_set(v___x_1624_, 1, v_val_1619_);
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
default: 
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_lchild_1617_);
lean_dec(v_x_1616_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_key_1618_);
lean_ctor_set(v___x_1626_, 1, v_val_1619_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
v_x_1614_ = v_rchild_1620_;
v_x_1616_ = v___x_1627_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* v_00_u03b1_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_cmp_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_1631_, v_x_1632_, v_x_1633_, v_x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t v_color_1636_, lean_object* v_key_1637_, lean_object* v_x1_1638_, lean_object* v_x2_1639_, lean_object* v_x3_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1641_, 0, v_x1_1638_);
lean_ctor_set(v___x_1641_, 1, v_key_1637_);
lean_ctor_set(v___x_1641_, 2, v_x2_1639_);
lean_ctor_set(v___x_1641_, 3, v_x3_1640_);
lean_ctor_set_uint8(v___x_1641_, sizeof(void*)*4, v_color_1636_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* v_color_1642_, lean_object* v_key_1643_, lean_object* v_x1_1644_, lean_object* v_x2_1645_, lean_object* v_x3_1646_){
_start:
{
uint8_t v_color_88__boxed_1647_; lean_object* v_res_1648_; 
v_color_88__boxed_1647_ = lean_unbox(v_color_1642_);
v_res_1648_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_88__boxed_1647_, v_key_1643_, v_x1_1644_, v_x2_1645_, v_x3_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* v_f_1649_, lean_object* v_key_1650_, lean_object* v_val_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_apply_2(v_f_1649_, v_key_1650_, v_val_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* v_inst_1654_, lean_object* v_f_1655_, lean_object* v_lchild_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_RBNode_mapM___redArg(v_inst_1654_, v_f_1655_, v_lchild_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* v_inst_1659_, lean_object* v_f_1660_, lean_object* v_x_1661_){
_start:
{
if (lean_obj_tag(v_x_1661_) == 0)
{
lean_object* v_toPure_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec(v_f_1660_);
v_toPure_1662_ = lean_ctor_get(v_inst_1659_, 1);
lean_inc(v_toPure_1662_);
lean_dec_ref(v_inst_1659_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1663_);
return v___x_1664_;
}
else
{
lean_object* v_toPure_1665_; lean_object* v_toSeq_1666_; uint8_t v_color_1667_; lean_object* v_lchild_1668_; lean_object* v_key_1669_; lean_object* v_val_1670_; lean_object* v_rchild_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_toPure_1665_ = lean_ctor_get(v_inst_1659_, 1);
lean_inc(v_toPure_1665_);
v_toSeq_1666_ = lean_ctor_get(v_inst_1659_, 2);
lean_inc_n(v_toSeq_1666_, 3);
v_color_1667_ = lean_ctor_get_uint8(v_x_1661_, sizeof(void*)*4);
v_lchild_1668_ = lean_ctor_get(v_x_1661_, 0);
lean_inc(v_lchild_1668_);
v_key_1669_ = lean_ctor_get(v_x_1661_, 1);
lean_inc_n(v_key_1669_, 2);
v_val_1670_ = lean_ctor_get(v_x_1661_, 2);
lean_inc(v_val_1670_);
v_rchild_1671_ = lean_ctor_get(v_x_1661_, 3);
lean_inc(v_rchild_1671_);
lean_dec_ref(v_x_1661_);
lean_inc_n(v_f_1660_, 2);
lean_inc_ref(v_inst_1659_);
v___f_1672_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1672_, 0, v_inst_1659_);
lean_closure_set(v___f_1672_, 1, v_f_1660_);
lean_closure_set(v___f_1672_, 2, v_rchild_1671_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1673_, 0, v_f_1660_);
lean_closure_set(v___f_1673_, 1, v_key_1669_);
lean_closure_set(v___f_1673_, 2, v_val_1670_);
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1674_, 0, v_inst_1659_);
lean_closure_set(v___f_1674_, 1, v_f_1660_);
lean_closure_set(v___f_1674_, 2, v_lchild_1668_);
v___x_1675_ = lean_box(v_color_1667_);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1676_, 0, v___x_1675_);
lean_closure_set(v___f_1676_, 1, v_key_1669_);
v___x_1677_ = lean_apply_2(v_toPure_1665_, lean_box(0), v___f_1676_);
v___x_1678_ = lean_apply_4(v_toSeq_1666_, lean_box(0), lean_box(0), v___x_1677_, v___f_1674_);
v___x_1679_ = lean_apply_4(v_toSeq_1666_, lean_box(0), lean_box(0), v___x_1678_, v___f_1673_);
v___x_1680_ = lean_apply_4(v_toSeq_1666_, lean_box(0), lean_box(0), v___x_1679_, v___f_1672_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* v_inst_1681_, lean_object* v_f_1682_, lean_object* v_rchild_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_RBNode_mapM___redArg(v_inst_1681_, v_f_1682_, v_rchild_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* v_00_u03b1_1686_, lean_object* v_00_u03b2_1687_, lean_object* v_00_u03b3_1688_, lean_object* v_M_1689_, lean_object* v_inst_1690_, lean_object* v_f_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_RBNode_mapM___redArg(v_inst_1690_, v_f_1691_, v_x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* v_f_1694_, lean_object* v_x_1695_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
lean_object* v___x_1696_; 
lean_dec(v_f_1694_);
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
else
{
uint8_t v_color_1697_; lean_object* v_lchild_1698_; lean_object* v_key_1699_; lean_object* v_val_1700_; lean_object* v_rchild_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v_color_1697_ = lean_ctor_get_uint8(v_x_1695_, sizeof(void*)*4);
v_lchild_1698_ = lean_ctor_get(v_x_1695_, 0);
v_key_1699_ = lean_ctor_get(v_x_1695_, 1);
v_val_1700_ = lean_ctor_get(v_x_1695_, 2);
v_rchild_1701_ = lean_ctor_get(v_x_1695_, 3);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1695_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1703_ = v_x_1695_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_rchild_1701_);
lean_inc(v_val_1700_);
lean_inc(v_key_1699_);
lean_inc(v_lchild_1698_);
lean_dec(v_x_1695_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
lean_inc_n(v_f_1694_, 2);
v___x_1705_ = l_Lean_RBNode_map___redArg(v_f_1694_, v_lchild_1698_);
lean_inc(v_key_1699_);
v___x_1706_ = lean_apply_2(v_f_1694_, v_key_1699_, v_val_1700_);
v___x_1707_ = l_Lean_RBNode_map___redArg(v_f_1694_, v_rchild_1701_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 3, v___x_1707_);
lean_ctor_set(v___x_1703_, 2, v___x_1706_);
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1709_ = v___x_1703_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_key_1699_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v___x_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*4, v_color_1697_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* v_00_u03b1_1712_, lean_object* v_00_u03b2_1713_, lean_object* v_00_u03b3_1714_, lean_object* v_f_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_RBNode_map___redArg(v_f_1715_, v_x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
return v_x_1718_;
}
else
{
lean_object* v_lchild_1720_; lean_object* v_key_1721_; lean_object* v_val_1722_; lean_object* v_rchild_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_lchild_1720_ = lean_ctor_get(v_x_1719_, 0);
v_key_1721_ = lean_ctor_get(v_x_1719_, 1);
v_val_1722_ = lean_ctor_get(v_x_1719_, 2);
v_rchild_1723_ = lean_ctor_get(v_x_1719_, 3);
v___x_1724_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1718_, v_lchild_1720_);
lean_inc(v_val_1722_);
lean_inc(v_key_1721_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_key_1721_);
lean_ctor_set(v___x_1725_, 1, v_val_1722_);
v___x_1726_ = lean_array_push(v___x_1724_, v___x_1725_);
v_x_1718_ = v___x_1726_;
v_x_1719_ = v_rchild_1723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1728_, v_x_1729_);
lean_dec(v_x_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* v_n_1733_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
v___x_1735_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_1734_, v_n_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* v_n_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_RBNode_toArray___redArg(v_n_1736_);
lean_dec(v_n_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_n_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_RBNode_toArray___redArg(v_n_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_n_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_RBNode_toArray(v_00_u03b1_1742_, v_00_u03b2_1743_, v_n_1744_);
lean_dec(v_n_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1748_, v_x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* v_00_u03b1_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(v_00_u03b1_1751_, v_00_u03b2_1752_, v_x_1753_, v_x_1754_);
lean_dec(v_x_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_box(0);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_cmp_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_box(0);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_cmp_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_mkRBMap(v_00_u03b1_1763_, v_00_u03b2_1764_, v_cmp_1765_);
lean_dec_ref(v_cmp_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_RBMap_empty(v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec_ref(v___y_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* v_00_u03b1_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_cmp_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_00_u03b2_1780_, lean_object* v_cmp_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_1779_, v_00_u03b2_1780_, v_cmp_1781_);
lean_dec_ref(v_cmp_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_cmp_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_cmp_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_instInhabitedRBMap(v_00_u03b1_1787_, v_00_u03b2_1788_, v_cmp_1789_);
lean_dec_ref(v_cmp_1789_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* v_f_1791_, lean_object* v_t_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_RBNode_depth___redArg(v_f_1791_, v_t_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* v_f_1794_, lean_object* v_t_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_RBMap_depth___redArg(v_f_1794_, v_t_1795_);
lean_dec(v_t_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* v_00_u03b1_1797_, lean_object* v_00_u03b2_1798_, lean_object* v_cmp_1799_, lean_object* v_f_1800_, lean_object* v_t_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_RBNode_depth___redArg(v_f_1800_, v_t_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_cmp_1805_, lean_object* v_f_1806_, lean_object* v_t_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_RBMap_depth(v_00_u03b1_1803_, v_00_u03b2_1804_, v_cmp_1805_, v_f_1806_, v_t_1807_);
lean_dec(v_t_1807_);
lean_dec_ref(v_cmp_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* v_t_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Lean_RBNode_isSingleton___redArg(v_t_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* v_t_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Lean_RBMap_isSingleton___redArg(v_t_1811_);
lean_dec(v_t_1811_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* v_00_u03b1_1814_, lean_object* v_00_u03b2_1815_, lean_object* v_cmp_1816_, lean_object* v_t_1817_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Lean_RBNode_isSingleton___redArg(v_t_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_cmp_1821_, lean_object* v_t_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l_Lean_RBMap_isSingleton(v_00_u03b1_1819_, v_00_u03b2_1820_, v_cmp_1821_, v_t_1822_);
lean_dec(v_t_1822_);
lean_dec_ref(v_cmp_1821_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* v_f_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_RBNode_fold___redArg(v_f_1825_, v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_00_u03c3_1831_, lean_object* v_cmp_1832_, lean_object* v_f_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_RBNode_fold___redArg(v_f_1833_, v_x_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_00_u03c3_1839_, lean_object* v_cmp_1840_, lean_object* v_f_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_RBMap_fold(v_00_u03b1_1837_, v_00_u03b2_1838_, v_00_u03c3_1839_, v_cmp_1840_, v_f_1841_, v_x_1842_, v_x_1843_);
lean_dec_ref(v_cmp_1840_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* v_f_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_RBNode_revFold___redArg(v_f_1845_, v_x_1846_, v_x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* v_00_u03b1_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_00_u03c3_1851_, lean_object* v_cmp_1852_, lean_object* v_f_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_RBNode_revFold___redArg(v_f_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* v_00_u03b1_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_00_u03c3_1859_, lean_object* v_cmp_1860_, lean_object* v_f_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_RBMap_revFold(v_00_u03b1_1857_, v_00_u03b2_1858_, v_00_u03c3_1859_, v_cmp_1860_, v_f_1861_, v_x_1862_, v_x_1863_);
lean_dec_ref(v_cmp_1860_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* v_inst_1865_, lean_object* v_f_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_RBNode_foldM___redArg(v_inst_1865_, v_f_1866_, v_x_1867_, v_x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* v_00_u03b1_1870_, lean_object* v_00_u03b2_1871_, lean_object* v_00_u03c3_1872_, lean_object* v_cmp_1873_, lean_object* v_m_1874_, lean_object* v_inst_1875_, lean_object* v_f_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_RBNode_foldM___redArg(v_inst_1875_, v_f_1876_, v_x_1877_, v_x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_00_u03c3_1882_, lean_object* v_cmp_1883_, lean_object* v_m_1884_, lean_object* v_inst_1885_, lean_object* v_f_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_RBMap_foldM(v_00_u03b1_1880_, v_00_u03b2_1881_, v_00_u03c3_1882_, v_cmp_1883_, v_m_1884_, v_inst_1885_, v_f_1886_, v_x_1887_, v_x_1888_);
lean_dec_ref(v_cmp_1883_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* v_f_1890_, lean_object* v_x_1891_, lean_object* v_k_1892_, lean_object* v_v_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_apply_2(v_f_1890_, v_k_1892_, v_v_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* v_inst_1895_, lean_object* v_f_1896_, lean_object* v_t_1897_){
_start:
{
lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1898_, 0, v_f_1896_);
v___x_1899_ = lean_box(0);
v___x_1900_ = l_Lean_RBNode_foldM___redArg(v_inst_1895_, v___f_1898_, v___x_1899_, v_t_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* v_00_u03b1_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_cmp_1903_, lean_object* v_m_1904_, lean_object* v_inst_1905_, lean_object* v_f_1906_, lean_object* v_t_1907_){
_start:
{
lean_object* v___f_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___f_1908_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1908_, 0, v_f_1906_);
v___x_1909_ = lean_box(0);
v___x_1910_ = l_Lean_RBNode_foldM___redArg(v_inst_1905_, v___f_1908_, v___x_1909_, v_t_1907_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* v_00_u03b1_1911_, lean_object* v_00_u03b2_1912_, lean_object* v_cmp_1913_, lean_object* v_m_1914_, lean_object* v_inst_1915_, lean_object* v_f_1916_, lean_object* v_t_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_RBMap_forM(v_00_u03b1_1911_, v_00_u03b2_1912_, v_cmp_1913_, v_m_1914_, v_inst_1915_, v_f_1916_, v_t_1917_);
lean_dec_ref(v_cmp_1913_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* v_f_1919_, lean_object* v_a_1920_, lean_object* v_b_1921_, lean_object* v_acc_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1920_);
lean_ctor_set(v___x_1923_, 1, v_b_1921_);
v___x_1924_ = lean_apply_2(v_f_1919_, v___x_1923_, v_acc_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* v_inst_1925_, lean_object* v_t_1926_, lean_object* v_init_1927_, lean_object* v_f_1928_){
_start:
{
lean_object* v_toApplicative_1929_; lean_object* v_toBind_1930_; lean_object* v_toPure_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; 
v_toApplicative_1929_ = lean_ctor_get(v_inst_1925_, 0);
v_toBind_1930_ = lean_ctor_get(v_inst_1925_, 1);
lean_inc(v_toBind_1930_);
v_toPure_1931_ = lean_ctor_get(v_toApplicative_1929_, 1);
lean_inc(v_toPure_1931_);
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1932_, 0, v_f_1928_);
v___x_1933_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1925_, v___f_1932_, v_t_1926_, v_init_1927_);
v___f_1934_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1934_, 0, v_toPure_1931_);
v___x_1935_ = lean_apply_4(v_toBind_1930_, lean_box(0), lean_box(0), v___x_1933_, v___f_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* v_00_u03b1_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_00_u03c3_1938_, lean_object* v_cmp_1939_, lean_object* v_m_1940_, lean_object* v_inst_1941_, lean_object* v_t_1942_, lean_object* v_init_1943_, lean_object* v_f_1944_){
_start:
{
lean_object* v_toApplicative_1945_; lean_object* v_toBind_1946_; lean_object* v_toPure_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; 
v_toApplicative_1945_ = lean_ctor_get(v_inst_1941_, 0);
v_toBind_1946_ = lean_ctor_get(v_inst_1941_, 1);
lean_inc(v_toBind_1946_);
v_toPure_1947_ = lean_ctor_get(v_toApplicative_1945_, 1);
lean_inc(v_toPure_1947_);
v___f_1948_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1948_, 0, v_f_1944_);
v___x_1949_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1941_, v___f_1948_, v_t_1942_, v_init_1943_);
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1950_, 0, v_toPure_1947_);
v___x_1951_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1949_, v___f_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_00_u03b2_1953_, lean_object* v_00_u03c3_1954_, lean_object* v_cmp_1955_, lean_object* v_m_1956_, lean_object* v_inst_1957_, lean_object* v_t_1958_, lean_object* v_init_1959_, lean_object* v_f_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_RBMap_forIn(v_00_u03b1_1952_, v_00_u03b2_1953_, v_00_u03c3_1954_, v_cmp_1955_, v_m_1956_, v_inst_1957_, v_t_1958_, v_init_1959_, v_f_1960_);
lean_dec_ref(v_cmp_1955_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* v___y_1962_, lean_object* v_a_1963_, lean_object* v_b_1964_, lean_object* v_acc_1965_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_a_1963_);
lean_ctor_set(v___x_1966_, 1, v_b_1964_);
v___x_1967_ = lean_apply_2(v___y_1962_, v___x_1966_, v_acc_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1968_, lean_object* v_00_u03b2_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_toApplicative_1973_; lean_object* v_toBind_1974_; lean_object* v_toPure_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___x_1979_; 
v_toApplicative_1973_ = lean_ctor_get(v_inst_1968_, 0);
v_toBind_1974_ = lean_ctor_get(v_inst_1968_, 1);
lean_inc(v_toBind_1974_);
v_toPure_1975_ = lean_ctor_get(v_toApplicative_1973_, 1);
lean_inc(v_toPure_1975_);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1976_, 0, v___y_1972_);
v___x_1977_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1968_, v___f_1976_, v___y_1970_, v___y_1971_);
v___f_1978_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1978_, 0, v_toPure_1975_);
v___x_1979_ = lean_apply_4(v_toBind_1974_, lean_box(0), lean_box(0), v___x_1977_, v___f_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* v_inst_1980_){
_start:
{
lean_object* v___f_1981_; 
v___f_1981_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1981_, 0, v_inst_1980_);
return v___f_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* v_00_u03b1_1982_, lean_object* v_00_u03b2_1983_, lean_object* v_cmp_1984_, lean_object* v_m_1985_, lean_object* v_inst_1986_){
_start:
{
lean_object* v___f_1987_; 
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1987_, 0, v_inst_1986_);
return v___f_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1988_, lean_object* v_00_u03b2_1989_, lean_object* v_cmp_1990_, lean_object* v_m_1991_, lean_object* v_inst_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_RBMap_instForInProdOfMonad(v_00_u03b1_1988_, v_00_u03b2_1989_, v_cmp_1990_, v_m_1991_, v_inst_1992_);
lean_dec_ref(v_cmp_1990_);
return v_res_1993_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* v_x_1994_){
_start:
{
if (lean_obj_tag(v_x_1994_) == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = 1;
return v___x_1995_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = 0;
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* v_x_1997_){
_start:
{
uint8_t v_res_1998_; lean_object* v_r_1999_; 
v_res_1998_ = l_Lean_RBMap_isEmpty___redArg(v_x_1997_);
lean_dec(v_x_1997_);
v_r_1999_ = lean_box(v_res_1998_);
return v_r_1999_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object* v_00_u03b1_2000_, lean_object* v_00_u03b2_2001_, lean_object* v_cmp_2002_, lean_object* v_x_2003_){
_start:
{
if (lean_obj_tag(v_x_2003_) == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = 1;
return v___x_2004_;
}
else
{
uint8_t v___x_2005_; 
v___x_2005_ = 0;
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* v_00_u03b1_2006_, lean_object* v_00_u03b2_2007_, lean_object* v_cmp_2008_, lean_object* v_x_2009_){
_start:
{
uint8_t v_res_2010_; lean_object* v_r_2011_; 
v_res_2010_ = l_Lean_RBMap_isEmpty(v_00_u03b1_2006_, v_00_u03b2_2007_, v_cmp_2008_, v_x_2009_);
lean_dec(v_x_2009_);
lean_dec_ref(v_cmp_2008_);
v_r_2011_ = lean_box(v_res_2010_);
return v_r_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* v_ps_2012_, lean_object* v_k_2013_, lean_object* v_v_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_k_2013_);
lean_ctor_set(v___x_2015_, 1, v_v_2014_);
v___x_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v_ps_2012_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* v_x_2018_){
_start:
{
lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___f_2019_ = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Lean_RBNode_revFold___redArg(v___f_2019_, v___x_2020_, v_x_2018_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_cmp_2024_, lean_object* v_x_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_RBMap_toList___redArg(v_x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* v_00_u03b1_2027_, lean_object* v_00_u03b2_2028_, lean_object* v_cmp_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_RBMap_toList(v_00_u03b1_2027_, v_00_u03b2_2028_, v_cmp_2029_, v_x_2030_);
lean_dec_ref(v_cmp_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* v_ps_2032_, lean_object* v_k_2033_, lean_object* v_v_2034_){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_k_2033_);
lean_ctor_set(v___x_2035_, 1, v_v_2034_);
v___x_2036_ = lean_array_push(v_ps_2032_, v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* v_x_2040_){
_start:
{
lean_object* v___f_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___f_2041_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
v___x_2042_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
v___x_2043_ = l_Lean_RBNode_fold___redArg(v___f_2041_, v___x_2042_, v_x_2040_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* v_00_u03b1_2044_, lean_object* v_00_u03b2_2045_, lean_object* v_cmp_2046_, lean_object* v_x_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_RBMap_toArray___redArg(v_x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* v_00_u03b1_2049_, lean_object* v_00_u03b2_2050_, lean_object* v_cmp_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_RBMap_toArray(v_00_u03b1_2049_, v_00_u03b2_2050_, v_cmp_2051_, v_x_2052_);
lean_dec_ref(v_cmp_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* v_x_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_RBNode_min___redArg(v_x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_box(0);
return v___x_2056_;
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2073_; 
v_val_2057_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2059_ = v___x_2055_;
v_isShared_2060_ = v_isSharedCheck_2073_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_val_2057_);
lean_dec(v___x_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2073_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_fst_2061_; lean_object* v_snd_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2072_; 
v_fst_2061_ = lean_ctor_get(v_val_2057_, 0);
v_snd_2062_ = lean_ctor_get(v_val_2057_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_val_2057_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2064_ = v_val_2057_;
v_isShared_2065_ = v_isSharedCheck_2072_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_snd_2062_);
lean_inc(v_fst_2061_);
lean_dec(v_val_2057_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2072_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_fst_2061_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_snd_2062_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2067_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* v_x_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_RBMap_min___redArg(v_x_2074_);
lean_dec(v_x_2074_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* v_00_u03b1_2076_, lean_object* v_00_u03b2_2077_, lean_object* v_cmp_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_RBNode_min___redArg(v_x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_box(0);
return v___x_2081_;
}
else
{
lean_object* v_val_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2098_; 
v_val_2082_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_val_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_fst_2086_; lean_object* v_snd_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2097_; 
v_fst_2086_ = lean_ctor_get(v_val_2082_, 0);
v_snd_2087_ = lean_ctor_get(v_val_2082_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_val_2082_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2089_ = v_val_2082_;
v_isShared_2090_ = v_isSharedCheck_2097_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_snd_2087_);
lean_inc(v_fst_2086_);
lean_dec(v_val_2082_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2097_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_fst_2086_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_snd_2087_);
v___x_2092_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2092_);
v___x_2094_ = v___x_2084_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_cmp_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_RBMap_min(v_00_u03b1_2099_, v_00_u03b2_2100_, v_cmp_2101_, v_x_2102_);
lean_dec(v_x_2102_);
lean_dec_ref(v_cmp_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* v_x_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_RBNode_max___redArg(v_x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_box(0);
return v___x_2106_;
}
else
{
lean_object* v_val_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2123_; 
v_val_2107_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2109_ = v___x_2105_;
v_isShared_2110_ = v_isSharedCheck_2123_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_val_2107_);
lean_dec(v___x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2123_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_fst_2111_; lean_object* v_snd_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2122_; 
v_fst_2111_ = lean_ctor_get(v_val_2107_, 0);
v_snd_2112_ = lean_ctor_get(v_val_2107_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_val_2107_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2114_ = v_val_2107_;
v_isShared_2115_ = v_isSharedCheck_2122_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_snd_2112_);
lean_inc(v_fst_2111_);
lean_dec(v_val_2107_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2122_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_fst_2111_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_snd_2112_);
v___x_2117_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2119_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2117_);
v___x_2119_ = v___x_2109_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* v_x_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_RBMap_max___redArg(v_x_2124_);
lean_dec(v_x_2124_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* v_00_u03b1_2126_, lean_object* v_00_u03b2_2127_, lean_object* v_cmp_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_RBNode_max___redArg(v_x_2129_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_box(0);
return v___x_2131_;
}
else
{
lean_object* v_val_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2148_; 
v_val_2132_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2134_ = v___x_2130_;
v_isShared_2135_ = v_isSharedCheck_2148_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_val_2132_);
lean_dec(v___x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2148_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_fst_2136_; lean_object* v_snd_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2147_; 
v_fst_2136_ = lean_ctor_get(v_val_2132_, 0);
v_snd_2137_ = lean_ctor_get(v_val_2132_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_val_2132_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2139_ = v_val_2132_;
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_snd_2137_);
lean_inc(v_fst_2136_);
lean_dec(v_val_2132_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_fst_2136_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_snd_2137_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2142_);
v___x_2144_ = v___x_2134_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_cmp_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_RBMap_max(v_00_u03b1_2149_, v_00_u03b2_2150_, v_cmp_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_cmp_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* v___x_2157_, lean_object* v_m_2158_, lean_object* v_prec_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2160_ = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
v___x_2161_ = l_Lean_RBMap_toList___redArg(v_m_2158_);
v___x_2162_ = l_List_repr___redArg(v___x_2157_, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2160_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Repr_addAppParen(v___x_2163_, v_prec_2159_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* v___x_2165_, lean_object* v_m_2166_, lean_object* v_prec_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_2165_, v_m_2166_, v_prec_2167_);
lean_dec(v_prec_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* v_inst_2169_, lean_object* v_inst_2170_){
_start:
{
lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; 
v___f_2171_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2171_, 0, v_inst_2170_);
v___x_2172_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2172_, 0, lean_box(0));
lean_closure_set(v___x_2172_, 1, lean_box(0));
lean_closure_set(v___x_2172_, 2, v_inst_2169_);
lean_closure_set(v___x_2172_, 3, v___f_2171_);
v___f_2173_ = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2173_, 0, v___x_2172_);
return v___f_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* v_00_u03b1_2174_, lean_object* v_00_u03b2_2175_, lean_object* v_cmp_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_RBMap_instRepr___redArg(v_inst_2177_, v_inst_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_00_u03b2_2181_, lean_object* v_cmp_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_RBMap_instRepr(v_00_u03b1_2180_, v_00_u03b2_2181_, v_cmp_2182_, v_inst_2183_, v_inst_2184_);
lean_dec_ref(v_cmp_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* v_cmp_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_RBNode_insert___redArg(v_cmp_2186_, v_x_2187_, v_x_2188_, v_x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* v_00_u03b1_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_cmp_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_RBNode_insert___redArg(v_cmp_2193_, v_x_2194_, v_x_2195_, v_x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* v_cmp_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_RBNode_erase___redArg(v_cmp_2198_, v_x_2200_, v_x_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_cmp_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_RBNode_erase___redArg(v_cmp_2204_, v_x_2206_, v_x_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* v_cmp_2208_, lean_object* v_x_2209_){
_start:
{
if (lean_obj_tag(v_x_2209_) == 0)
{
lean_object* v___x_2210_; 
lean_dec_ref(v_cmp_2208_);
v___x_2210_ = lean_box(0);
return v___x_2210_;
}
else
{
lean_object* v_head_2211_; lean_object* v_tail_2212_; lean_object* v_fst_2213_; lean_object* v_snd_2214_; lean_object* v_val_2215_; lean_object* v___x_2216_; 
v_head_2211_ = lean_ctor_get(v_x_2209_, 0);
lean_inc(v_head_2211_);
v_tail_2212_ = lean_ctor_get(v_x_2209_, 1);
lean_inc(v_tail_2212_);
lean_dec_ref(v_x_2209_);
v_fst_2213_ = lean_ctor_get(v_head_2211_, 0);
lean_inc(v_fst_2213_);
v_snd_2214_ = lean_ctor_get(v_head_2211_, 1);
lean_inc(v_snd_2214_);
lean_dec(v_head_2211_);
lean_inc_ref(v_cmp_2208_);
v_val_2215_ = l_Lean_RBMap_ofList___redArg(v_cmp_2208_, v_tail_2212_);
v___x_2216_ = l_Lean_RBNode_insert___redArg(v_cmp_2208_, v_val_2215_, v_fst_2213_, v_snd_2214_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* v_00_u03b1_2217_, lean_object* v_00_u03b2_2218_, lean_object* v_cmp_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_RBMap_ofList___redArg(v_cmp_2219_, v_x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* v_cmp_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_RBNode_findCore___redArg(v_cmp_2222_, v_x_2223_, v_x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* v_00_u03b1_2226_, lean_object* v_00_u03b2_2227_, lean_object* v_cmp_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_RBNode_findCore___redArg(v_cmp_2228_, v_x_2229_, v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* v_cmp_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_RBNode_find___redArg(v_cmp_2232_, v_x_2233_, v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* v_00_u03b1_2236_, lean_object* v_00_u03b2_2237_, lean_object* v_cmp_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_RBNode_find___redArg(v_cmp_2238_, v_x_2239_, v_x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* v_cmp_2242_, lean_object* v_t_2243_, lean_object* v_k_2244_, lean_object* v_v_u2080_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_RBNode_find___redArg(v_cmp_2242_, v_t_2243_, v_k_2244_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_inc(v_v_u2080_2245_);
return v_v_u2080_2245_;
}
else
{
lean_object* v_val_2247_; 
v_val_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_val_2247_);
lean_dec_ref(v___x_2246_);
return v_val_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* v_cmp_2248_, lean_object* v_t_2249_, lean_object* v_k_2250_, lean_object* v_v_u2080_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_RBMap_findD___redArg(v_cmp_2248_, v_t_2249_, v_k_2250_, v_v_u2080_2251_);
lean_dec(v_v_u2080_2251_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* v_00_u03b1_2253_, lean_object* v_00_u03b2_2254_, lean_object* v_cmp_2255_, lean_object* v_t_2256_, lean_object* v_k_2257_, lean_object* v_v_u2080_2258_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_RBNode_find___redArg(v_cmp_2255_, v_t_2256_, v_k_2257_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_inc(v_v_u2080_2258_);
return v_v_u2080_2258_;
}
else
{
lean_object* v_val_2260_; 
v_val_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_val_2260_);
lean_dec_ref(v___x_2259_);
return v_val_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* v_00_u03b1_2261_, lean_object* v_00_u03b2_2262_, lean_object* v_cmp_2263_, lean_object* v_t_2264_, lean_object* v_k_2265_, lean_object* v_v_u2080_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_RBMap_findD(v_00_u03b1_2261_, v_00_u03b2_2262_, v_cmp_2263_, v_t_2264_, v_k_2265_, v_v_u2080_2266_);
lean_dec(v_v_u2080_2266_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* v_cmp_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2268_, v_x_2269_, v_x_2270_, v___x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* v_00_u03b1_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_cmp_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2275_, v_x_2276_, v_x_2277_, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object* v_cmp_2280_, lean_object* v_t_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_RBNode_find___redArg(v_cmp_2280_, v_t_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
uint8_t v___x_2284_; 
v___x_2284_ = 0;
return v___x_2284_;
}
else
{
uint8_t v___x_2285_; 
lean_dec_ref(v___x_2283_);
v___x_2285_ = 1;
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* v_cmp_2286_, lean_object* v_t_2287_, lean_object* v_a_2288_){
_start:
{
uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_res_2289_ = l_Lean_RBMap_contains___redArg(v_cmp_2286_, v_t_2287_, v_a_2288_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object* v_00_u03b1_2291_, lean_object* v_00_u03b2_2292_, lean_object* v_cmp_2293_, lean_object* v_t_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_RBNode_find___redArg(v_cmp_2293_, v_t_2294_, v_a_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
uint8_t v___x_2297_; 
v___x_2297_ = 0;
return v___x_2297_;
}
else
{
uint8_t v___x_2298_; 
lean_dec_ref(v___x_2296_);
v___x_2298_ = 1;
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_00_u03b2_2300_, lean_object* v_cmp_2301_, lean_object* v_t_2302_, lean_object* v_a_2303_){
_start:
{
uint8_t v_res_2304_; lean_object* v_r_2305_; 
v_res_2304_ = l_Lean_RBMap_contains(v_00_u03b1_2299_, v_00_u03b2_2300_, v_cmp_2301_, v_t_2302_, v_a_2303_);
v_r_2305_ = lean_box(v_res_2304_);
return v_r_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* v_cmp_2306_, lean_object* v_r_2307_, lean_object* v_p_2308_){
_start:
{
lean_object* v_fst_2309_; lean_object* v_snd_2310_; lean_object* v___x_2311_; 
v_fst_2309_ = lean_ctor_get(v_p_2308_, 0);
lean_inc(v_fst_2309_);
v_snd_2310_ = lean_ctor_get(v_p_2308_, 1);
lean_inc(v_snd_2310_);
lean_dec_ref(v_p_2308_);
v___x_2311_ = l_Lean_RBNode_insert___redArg(v_cmp_2306_, v_r_2307_, v_fst_2309_, v_snd_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* v_l_2312_, lean_object* v_cmp_2313_){
_start:
{
lean_object* v___f_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___f_2314_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2314_, 0, v_cmp_2313_);
v___x_2315_ = lean_box(0);
v___x_2316_ = l_List_foldl___redArg(v___f_2314_, v___x_2315_, v_l_2312_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* v_00_u03b1_2317_, lean_object* v_00_u03b2_2318_, lean_object* v_l_2319_, lean_object* v_cmp_2320_){
_start:
{
lean_object* v___f_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___f_2321_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2321_, 0, v_cmp_2320_);
v___x_2322_ = lean_box(0);
v___x_2323_ = l_List_foldl___redArg(v___f_2321_, v___x_2322_, v_l_2319_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* v_cmp_2324_, lean_object* v_x1_2325_, lean_object* v_x2_2326_){
_start:
{
lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2329_; 
v_fst_2327_ = lean_ctor_get(v_x2_2326_, 0);
lean_inc(v_fst_2327_);
v_snd_2328_ = lean_ctor_get(v_x2_2326_, 1);
lean_inc(v_snd_2328_);
lean_dec_ref(v_x2_2326_);
v___x_2329_ = l_Lean_RBNode_insert___redArg(v_cmp_2324_, v_x1_2325_, v_fst_2327_, v_snd_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* v_l_2349_, lean_object* v_cmp_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_array_get_size(v_l_2349_);
v___x_2354_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2355_ = lean_nat_dec_lt(v___x_2352_, v___x_2353_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v_cmp_2350_);
lean_dec_ref(v_l_2349_);
return v___x_2351_;
}
else
{
lean_object* v___f_2356_; uint8_t v___x_2357_; 
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2356_, 0, v_cmp_2350_);
v___x_2357_ = lean_nat_dec_le(v___x_2353_, v___x_2353_);
if (v___x_2357_ == 0)
{
if (v___x_2355_ == 0)
{
lean_dec_ref(v___f_2356_);
lean_dec_ref(v_l_2349_);
return v___x_2351_;
}
else
{
size_t v___x_2358_; size_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = ((size_t)0ULL);
v___x_2359_ = lean_usize_of_nat(v___x_2353_);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2354_, v___f_2356_, v_l_2349_, v___x_2358_, v___x_2359_, v___x_2351_);
return v___x_2360_;
}
}
else
{
size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = ((size_t)0ULL);
v___x_2362_ = lean_usize_of_nat(v___x_2353_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2354_, v___f_2356_, v_l_2349_, v___x_2361_, v___x_2362_, v___x_2351_);
return v___x_2363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* v_00_u03b1_2364_, lean_object* v_00_u03b2_2365_, lean_object* v_l_2366_, lean_object* v_cmp_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_array_get_size(v_l_2366_);
v___x_2371_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2372_ = lean_nat_dec_lt(v___x_2369_, v___x_2370_);
if (v___x_2372_ == 0)
{
lean_dec_ref(v_cmp_2367_);
lean_dec_ref(v_l_2366_);
return v___x_2368_;
}
else
{
lean_object* v___f_2373_; uint8_t v___x_2374_; 
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2373_, 0, v_cmp_2367_);
v___x_2374_ = lean_nat_dec_le(v___x_2370_, v___x_2370_);
if (v___x_2374_ == 0)
{
if (v___x_2372_ == 0)
{
lean_dec_ref(v___f_2373_);
lean_dec_ref(v_l_2366_);
return v___x_2368_;
}
else
{
size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = ((size_t)0ULL);
v___x_2376_ = lean_usize_of_nat(v___x_2370_);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2371_, v___f_2373_, v_l_2366_, v___x_2375_, v___x_2376_, v___x_2368_);
return v___x_2377_;
}
}
else
{
size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = ((size_t)0ULL);
v___x_2379_ = lean_usize_of_nat(v___x_2370_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2371_, v___f_2373_, v_l_2366_, v___x_2378_, v___x_2379_, v___x_2368_);
return v___x_2380_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Lean_RBNode_all___redArg(v_x_2382_, v_x_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_res_2386_ = l_Lean_RBMap_all___redArg(v_x_2384_, v_x_2385_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object* v_00_u03b1_2388_, lean_object* v_00_u03b2_2389_, lean_object* v_cmp_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
uint8_t v___x_2393_; 
v___x_2393_ = l_Lean_RBNode_all___redArg(v_x_2392_, v_x_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_cmp_2396_, lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
uint8_t v_res_2399_; lean_object* v_r_2400_; 
v_res_2399_ = l_Lean_RBMap_all(v_00_u03b1_2394_, v_00_u03b2_2395_, v_cmp_2396_, v_x_2397_, v_x_2398_);
lean_dec_ref(v_cmp_2396_);
v_r_2400_ = lean_box(v_res_2399_);
return v_r_2400_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Lean_RBNode_any___redArg(v_x_2402_, v_x_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* v_x_2404_, lean_object* v_x_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Lean_RBMap_any___redArg(v_x_2404_, v_x_2405_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object* v_00_u03b1_2408_, lean_object* v_00_u03b2_2409_, lean_object* v_cmp_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v___x_2413_; 
v___x_2413_ = l_Lean_RBNode_any___redArg(v_x_2412_, v_x_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_cmp_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_){
_start:
{
uint8_t v_res_2419_; lean_object* v_r_2420_; 
v_res_2419_ = l_Lean_RBMap_any(v_00_u03b1_2414_, v_00_u03b2_2415_, v_cmp_2416_, v_x_2417_, v_x_2418_);
lean_dec_ref(v_cmp_2416_);
v_r_2420_ = lean_box(v_res_2419_);
return v_r_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* v_x_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
return v_x_2421_;
}
else
{
lean_object* v_lchild_2423_; lean_object* v_rchild_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_lchild_2423_ = lean_ctor_get(v_x_2422_, 0);
v_rchild_2424_ = lean_ctor_get(v_x_2422_, 3);
v___x_2425_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2421_, v_lchild_2423_);
v___x_2426_ = lean_unsigned_to_nat(1u);
v___x_2427_ = lean_nat_add(v___x_2425_, v___x_2426_);
lean_dec(v___x_2425_);
v_x_2421_ = v___x_2427_;
v_x_2422_ = v_rchild_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2429_, v_x_2430_);
lean_dec(v_x_2430_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* v_m_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_unsigned_to_nat(0u);
v___x_2434_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_2433_, v_m_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* v_m_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_RBMap_size___redArg(v_m_2435_);
lean_dec(v_m_2435_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* v_00_u03b1_2437_, lean_object* v_00_u03b2_2438_, lean_object* v_cmp_2439_, lean_object* v_m_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_RBMap_size___redArg(v_m_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_00_u03b2_2443_, lean_object* v_cmp_2444_, lean_object* v_m_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_RBMap_size(v_00_u03b1_2442_, v_00_u03b2_2443_, v_cmp_2444_, v_m_2445_);
lean_dec(v_m_2445_);
lean_dec_ref(v_cmp_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* v_00_u03b1_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2449_, v_x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_00_u03b2_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(v_00_u03b1_2452_, v_00_u03b2_2453_, v_x_2454_, v_x_2455_);
lean_dec(v_x_2455_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = lean_nat_dec_le(v___y_2457_, v___y_2458_);
if (v___x_2459_ == 0)
{
lean_inc(v___y_2457_);
return v___y_2457_;
}
else
{
lean_inc(v___y_2458_);
return v___y_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* v_t_2464_){
_start:
{
lean_object* v___f_2465_; lean_object* v___x_2466_; 
v___f_2465_ = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
v___x_2466_ = l_Lean_RBNode_depth___redArg(v___f_2465_, v_t_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* v_t_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_RBMap_maxDepth___redArg(v_t_2467_);
lean_dec(v_t_2467_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_cmp_2471_, lean_object* v_t_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_RBMap_maxDepth___redArg(v_t_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* v_00_u03b1_2474_, lean_object* v_00_u03b2_2475_, lean_object* v_cmp_2476_, lean_object* v_t_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_RBMap_maxDepth(v_00_u03b1_2474_, v_00_u03b2_2475_, v_cmp_2476_, v_t_2477_);
lean_dec(v_t_2477_);
lean_dec_ref(v_cmp_2476_);
return v_res_2478_;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2482_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2483_ = lean_unsigned_to_nat(14u);
v___x_2484_ = lean_unsigned_to_nat(384u);
v___x_2485_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
v___x_2486_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2487_ = l_mkPanicMessageWithDecl(v___x_2486_, v___x_2485_, v___x_2484_, v___x_2483_, v___x_2482_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_t_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_RBNode_min___redArg(v_t_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v_inst_2488_);
lean_ctor_set(v___x_2492_, 1, v_inst_2489_);
v___x_2493_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2494_ = l_panic___redArg(v___x_2492_, v___x_2493_);
lean_dec_ref(v___x_2492_);
return v___x_2494_;
}
else
{
lean_object* v_val_2495_; lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_inst_2489_);
lean_dec(v_inst_2488_);
v_val_2495_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_val_2495_);
lean_dec_ref(v___x_2491_);
v_fst_2496_ = lean_ctor_get(v_val_2495_, 0);
v_snd_2497_ = lean_ctor_get(v_val_2495_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_val_2495_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v_val_2495_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_snd_2497_);
lean_inc(v_fst_2496_);
lean_dec(v_val_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_fst_2496_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_snd_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* v_inst_2505_, lean_object* v_inst_2506_, lean_object* v_t_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_RBMap_min_x21___redArg(v_inst_2505_, v_inst_2506_, v_t_2507_);
lean_dec(v_t_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* v_00_u03b1_2509_, lean_object* v_00_u03b2_2510_, lean_object* v_cmp_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_t_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_RBNode_min___redArg(v_t_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v_inst_2512_);
lean_ctor_set(v___x_2516_, 1, v_inst_2513_);
v___x_2517_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2518_ = l_panic___redArg(v___x_2516_, v___x_2517_);
lean_dec_ref(v___x_2516_);
return v___x_2518_;
}
else
{
lean_object* v_val_2519_; lean_object* v_fst_2520_; lean_object* v_snd_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_inst_2513_);
lean_dec(v_inst_2512_);
v_val_2519_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v___x_2515_);
v_fst_2520_ = lean_ctor_get(v_val_2519_, 0);
v_snd_2521_ = lean_ctor_get(v_val_2519_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_val_2519_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v_val_2519_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_snd_2521_);
lean_inc(v_fst_2520_);
lean_dec(v_val_2519_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_fst_2520_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_snd_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* v_00_u03b1_2529_, lean_object* v_00_u03b2_2530_, lean_object* v_cmp_2531_, lean_object* v_inst_2532_, lean_object* v_inst_2533_, lean_object* v_t_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_RBMap_min_x21(v_00_u03b1_2529_, v_00_u03b2_2530_, v_cmp_2531_, v_inst_2532_, v_inst_2533_, v_t_2534_);
lean_dec(v_t_2534_);
lean_dec_ref(v_cmp_2531_);
return v_res_2535_;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2537_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2538_ = lean_unsigned_to_nat(14u);
v___x_2539_ = lean_unsigned_to_nat(389u);
v___x_2540_ = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
v___x_2541_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2542_ = l_mkPanicMessageWithDecl(v___x_2541_, v___x_2540_, v___x_2539_, v___x_2538_, v___x_2537_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_t_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_RBNode_max___redArg(v_t_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_inst_2543_);
lean_ctor_set(v___x_2547_, 1, v_inst_2544_);
v___x_2548_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2549_ = l_panic___redArg(v___x_2547_, v___x_2548_);
lean_dec_ref(v___x_2547_);
return v___x_2549_;
}
else
{
lean_object* v_val_2550_; lean_object* v_fst_2551_; lean_object* v_snd_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_inst_2544_);
lean_dec(v_inst_2543_);
v_val_2550_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_val_2550_);
lean_dec_ref(v___x_2546_);
v_fst_2551_ = lean_ctor_get(v_val_2550_, 0);
v_snd_2552_ = lean_ctor_get(v_val_2550_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_val_2550_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v_val_2550_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_snd_2552_);
lean_inc(v_fst_2551_);
lean_dec(v_val_2550_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_fst_2551_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_snd_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_t_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_RBMap_max_x21___redArg(v_inst_2560_, v_inst_2561_, v_t_2562_);
lean_dec(v_t_2562_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b2_2565_, lean_object* v_cmp_2566_, lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_t_2569_){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_RBNode_max___redArg(v_t_2569_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_inst_2567_);
lean_ctor_set(v___x_2571_, 1, v_inst_2568_);
v___x_2572_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2573_ = l_panic___redArg(v___x_2571_, v___x_2572_);
lean_dec_ref(v___x_2571_);
return v___x_2573_;
}
else
{
lean_object* v_val_2574_; lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_inst_2568_);
lean_dec(v_inst_2567_);
v_val_2574_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_val_2574_);
lean_dec_ref(v___x_2570_);
v_fst_2575_ = lean_ctor_get(v_val_2574_, 0);
v_snd_2576_ = lean_ctor_get(v_val_2574_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_val_2574_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v_val_2574_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_snd_2576_);
lean_inc(v_fst_2575_);
lean_dec(v_val_2574_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_fst_2575_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_snd_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* v_00_u03b1_2584_, lean_object* v_00_u03b2_2585_, lean_object* v_cmp_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_t_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_RBMap_max_x21(v_00_u03b1_2584_, v_00_u03b2_2585_, v_cmp_2586_, v_inst_2587_, v_inst_2588_, v_t_2589_);
lean_dec(v_t_2589_);
lean_dec_ref(v_cmp_2586_);
return v_res_2590_;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2593_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
v___x_2594_ = lean_unsigned_to_nat(14u);
v___x_2595_ = lean_unsigned_to_nat(395u);
v___x_2596_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
v___x_2597_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2598_ = l_mkPanicMessageWithDecl(v___x_2597_, v___x_2596_, v___x_2595_, v___x_2594_, v___x_2593_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* v_cmp_2599_, lean_object* v_inst_2600_, lean_object* v_t_2601_, lean_object* v_k_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_RBNode_find___redArg(v_cmp_2599_, v_t_2601_, v_k_2602_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2605_ = l_panic___redArg(v_inst_2600_, v___x_2604_);
return v___x_2605_;
}
else
{
lean_object* v_val_2606_; 
v_val_2606_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_val_2606_);
lean_dec_ref(v___x_2603_);
return v_val_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg___boxed(lean_object* v_cmp_2607_, lean_object* v_inst_2608_, lean_object* v_t_2609_, lean_object* v_k_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_RBMap_find_x21___redArg(v_cmp_2607_, v_inst_2608_, v_t_2609_, v_k_2610_);
lean_dec(v_inst_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* v_00_u03b1_2612_, lean_object* v_00_u03b2_2613_, lean_object* v_cmp_2614_, lean_object* v_inst_2615_, lean_object* v_t_2616_, lean_object* v_k_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_RBNode_find___redArg(v_cmp_2614_, v_t_2616_, v_k_2617_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2620_ = l_panic___redArg(v_inst_2615_, v___x_2619_);
return v___x_2620_;
}
else
{
lean_object* v_val_2621_; 
v_val_2621_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_val_2621_);
lean_dec_ref(v___x_2618_);
return v_val_2621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_00_u03b2_2623_, lean_object* v_cmp_2624_, lean_object* v_inst_2625_, lean_object* v_t_2626_, lean_object* v_k_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_RBMap_find_x21(v_00_u03b1_2622_, v_00_u03b2_2623_, v_cmp_2624_, v_inst_2625_, v_t_2626_, v_k_2627_);
lean_dec(v_inst_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* v_cmp_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
if (lean_obj_tag(v_x_2630_) == 0)
{
uint8_t v___x_2633_; lean_object* v___x_2634_; 
lean_dec_ref(v_cmp_2629_);
v___x_2633_ = 0;
v___x_2634_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2634_, 0, v_x_2630_);
lean_ctor_set(v___x_2634_, 1, v_x_2631_);
lean_ctor_set(v___x_2634_, 2, v_x_2632_);
lean_ctor_set(v___x_2634_, 3, v_x_2630_);
lean_ctor_set_uint8(v___x_2634_, sizeof(void*)*4, v___x_2633_);
return v___x_2634_;
}
else
{
uint8_t v_color_2635_; 
v_color_2635_ = lean_ctor_get_uint8(v_x_2630_, sizeof(void*)*4);
if (v_color_2635_ == 0)
{
lean_object* v_lchild_2636_; lean_object* v_key_2637_; lean_object* v_val_2638_; lean_object* v_rchild_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2656_; 
v_lchild_2636_ = lean_ctor_get(v_x_2630_, 0);
v_key_2637_ = lean_ctor_get(v_x_2630_, 1);
v_val_2638_ = lean_ctor_get(v_x_2630_, 2);
v_rchild_2639_ = lean_ctor_get(v_x_2630_, 3);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_x_2630_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2641_ = v_x_2630_;
v_isShared_2642_ = v_isSharedCheck_2656_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_rchild_2639_);
lean_inc(v_val_2638_);
lean_inc(v_key_2637_);
lean_inc(v_lchild_2636_);
lean_dec(v_x_2630_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2656_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
lean_inc_ref(v_cmp_2629_);
lean_inc(v_key_2637_);
lean_inc(v_x_2631_);
v___x_2643_ = lean_apply_2(v_cmp_2629_, v_x_2631_, v_key_2637_);
v___x_2644_ = lean_unbox(v___x_2643_);
switch(v___x_2644_)
{
case 0:
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2645_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2629_, v_lchild_2636_, v_x_2631_, v_x_2632_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2645_);
v___x_2647_ = v___x_2641_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_rchild_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2648_, sizeof(void*)*4, v_color_2635_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
case 1:
{
lean_object* v___x_2650_; 
lean_dec(v_val_2638_);
lean_dec(v_key_2637_);
lean_dec_ref(v_cmp_2629_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 2, v_x_2632_);
lean_ctor_set(v___x_2641_, 1, v_x_2631_);
v___x_2650_ = v___x_2641_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_x_2631_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_x_2632_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_rchild_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*4, v_color_2635_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
default: 
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2652_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2629_, v_rchild_2639_, v_x_2631_, v_x_2632_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 3, v___x_2652_);
v___x_2654_ = v___x_2641_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v___x_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, sizeof(void*)*4, v_color_2635_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
else
{
lean_object* v_lchild_2657_; lean_object* v_key_2658_; lean_object* v_val_2659_; lean_object* v_rchild_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2819_; 
v_lchild_2657_ = lean_ctor_get(v_x_2630_, 0);
v_key_2658_ = lean_ctor_get(v_x_2630_, 1);
v_val_2659_ = lean_ctor_get(v_x_2630_, 2);
v_rchild_2660_ = lean_ctor_get(v_x_2630_, 3);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_x_2630_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2662_ = v_x_2630_;
v_isShared_2663_ = v_isSharedCheck_2819_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_rchild_2660_);
lean_inc(v_val_2659_);
lean_inc(v_key_2658_);
lean_inc(v_lchild_2657_);
lean_dec(v_x_2630_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2819_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
lean_inc_ref(v_cmp_2629_);
lean_inc(v_key_2658_);
lean_inc(v_x_2631_);
v___x_2664_ = lean_apply_2(v_cmp_2629_, v_x_2631_, v_key_2658_);
v___x_2665_ = lean_unbox(v___x_2664_);
switch(v___x_2665_)
{
case 0:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2629_, v_lchild_2657_, v_x_2631_, v_x_2632_);
if (lean_obj_tag(v___x_2666_) == 1)
{
uint8_t v_color_2667_; lean_object* v_lchild_2668_; lean_object* v_key_2669_; lean_object* v_val_2670_; lean_object* v_rchild_2671_; lean_object* v_a_2673_; lean_object* v_kx_2674_; lean_object* v_vx_2675_; lean_object* v_b_2676_; lean_object* v_ky_2677_; lean_object* v_vy_2678_; lean_object* v_c_2679_; lean_object* v_kz_2680_; lean_object* v_vz_2681_; lean_object* v_d_2682_; 
v_color_2667_ = lean_ctor_get_uint8(v___x_2666_, sizeof(void*)*4);
v_lchild_2668_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_lchild_2668_);
v_key_2669_ = lean_ctor_get(v___x_2666_, 1);
lean_inc(v_key_2669_);
v_val_2670_ = lean_ctor_get(v___x_2666_, 2);
lean_inc(v_val_2670_);
v_rchild_2671_ = lean_ctor_get(v___x_2666_, 3);
lean_inc(v_rchild_2671_);
if (v_color_2667_ == 0)
{
if (lean_obj_tag(v_lchild_2668_) == 1)
{
uint8_t v_color_2688_; 
v_color_2688_ = lean_ctor_get_uint8(v_lchild_2668_, sizeof(void*)*4);
if (v_color_2688_ == 0)
{
lean_object* v_lchild_2689_; lean_object* v_key_2690_; lean_object* v_val_2691_; lean_object* v_rchild_2692_; 
lean_dec_ref(v___x_2666_);
v_lchild_2689_ = lean_ctor_get(v_lchild_2668_, 0);
lean_inc(v_lchild_2689_);
v_key_2690_ = lean_ctor_get(v_lchild_2668_, 1);
lean_inc(v_key_2690_);
v_val_2691_ = lean_ctor_get(v_lchild_2668_, 2);
lean_inc(v_val_2691_);
v_rchild_2692_ = lean_ctor_get(v_lchild_2668_, 3);
lean_inc(v_rchild_2692_);
lean_dec_ref(v_lchild_2668_);
v_a_2673_ = v_lchild_2689_;
v_kx_2674_ = v_key_2690_;
v_vx_2675_ = v_val_2691_;
v_b_2676_ = v_rchild_2692_;
v_ky_2677_ = v_key_2669_;
v_vy_2678_ = v_val_2670_;
v_c_2679_ = v_rchild_2671_;
v_kz_2680_ = v_key_2658_;
v_vz_2681_ = v_val_2659_;
v_d_2682_ = v_rchild_2660_;
goto v___jp_2672_;
}
else
{
if (lean_obj_tag(v_rchild_2671_) == 1)
{
uint8_t v_color_2693_; 
v_color_2693_ = lean_ctor_get_uint8(v_rchild_2671_, sizeof(void*)*4);
if (v_color_2693_ == 0)
{
lean_object* v_lchild_2694_; lean_object* v_key_2695_; lean_object* v_val_2696_; lean_object* v_rchild_2697_; 
lean_dec_ref(v___x_2666_);
v_lchild_2694_ = lean_ctor_get(v_rchild_2671_, 0);
lean_inc(v_lchild_2694_);
v_key_2695_ = lean_ctor_get(v_rchild_2671_, 1);
lean_inc(v_key_2695_);
v_val_2696_ = lean_ctor_get(v_rchild_2671_, 2);
lean_inc(v_val_2696_);
v_rchild_2697_ = lean_ctor_get(v_rchild_2671_, 3);
lean_inc(v_rchild_2697_);
lean_dec_ref(v_rchild_2671_);
v_a_2673_ = v_lchild_2668_;
v_kx_2674_ = v_key_2669_;
v_vx_2675_ = v_val_2670_;
v_b_2676_ = v_lchild_2694_;
v_ky_2677_ = v_key_2695_;
v_vy_2678_ = v_val_2696_;
v_c_2679_ = v_rchild_2697_;
v_kz_2680_ = v_key_2658_;
v_vz_2681_ = v_val_2659_;
v_d_2682_ = v_rchild_2660_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_lchild_2668_);
lean_dec(v_val_2670_);
lean_dec(v_key_2669_);
lean_del_object(v___x_2662_);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_rchild_2671_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; lean_object* v_unused_2708_; 
v_unused_2705_ = lean_ctor_get(v_rchild_2671_, 3);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_rchild_2671_, 2);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_rchild_2671_, 1);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_rchild_2671_, 0);
lean_dec(v_unused_2708_);
v___x_2699_ = v_rchild_2671_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_dec(v_rchild_2671_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 3, v_rchild_2660_);
lean_ctor_set(v___x_2699_, 2, v_val_2659_);
lean_ctor_set(v___x_2699_, 1, v_key_2658_);
lean_ctor_set(v___x_2699_, 0, v___x_2666_);
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_rchild_2660_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*4, v_color_2635_);
return v___x_2702_;
}
}
}
}
else
{
lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v_rchild_2671_);
lean_dec(v_val_2670_);
lean_dec(v_key_2669_);
lean_del_object(v___x_2662_);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_lchild_2668_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2716_ = lean_ctor_get(v_lchild_2668_, 3);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_lchild_2668_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_lchild_2668_, 1);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_lchild_2668_, 0);
lean_dec(v_unused_2719_);
v___x_2710_ = v_lchild_2668_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_dec(v_lchild_2668_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 3, v_rchild_2660_);
lean_ctor_set(v___x_2710_, 2, v_val_2659_);
lean_ctor_set(v___x_2710_, 1, v_key_2658_);
lean_ctor_set(v___x_2710_, 0, v___x_2666_);
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2714_, 3, v_rchild_2660_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*4, v_color_2635_);
return v___x_2713_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2671_) == 1)
{
uint8_t v_color_2720_; 
v_color_2720_ = lean_ctor_get_uint8(v_rchild_2671_, sizeof(void*)*4);
if (v_color_2720_ == 0)
{
lean_object* v_lchild_2721_; lean_object* v_key_2722_; lean_object* v_val_2723_; lean_object* v_rchild_2724_; 
lean_dec_ref(v___x_2666_);
v_lchild_2721_ = lean_ctor_get(v_rchild_2671_, 0);
lean_inc(v_lchild_2721_);
v_key_2722_ = lean_ctor_get(v_rchild_2671_, 1);
lean_inc(v_key_2722_);
v_val_2723_ = lean_ctor_get(v_rchild_2671_, 2);
lean_inc(v_val_2723_);
v_rchild_2724_ = lean_ctor_get(v_rchild_2671_, 3);
lean_inc(v_rchild_2724_);
lean_dec_ref(v_rchild_2671_);
v_a_2673_ = v_lchild_2668_;
v_kx_2674_ = v_key_2669_;
v_vx_2675_ = v_val_2670_;
v_b_2676_ = v_lchild_2721_;
v_ky_2677_ = v_key_2722_;
v_vy_2678_ = v_val_2723_;
v_c_2679_ = v_rchild_2724_;
v_kz_2680_ = v_key_2658_;
v_vz_2681_ = v_val_2659_;
v_d_2682_ = v_rchild_2660_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_val_2670_);
lean_dec(v_key_2669_);
lean_dec(v_lchild_2668_);
lean_del_object(v___x_2662_);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_rchild_2671_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2732_ = lean_ctor_get(v_rchild_2671_, 3);
lean_dec(v_unused_2732_);
v_unused_2733_ = lean_ctor_get(v_rchild_2671_, 2);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_rchild_2671_, 1);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_rchild_2671_, 0);
lean_dec(v_unused_2735_);
v___x_2726_ = v_rchild_2671_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v_rchild_2671_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 3, v_rchild_2660_);
lean_ctor_set(v___x_2726_, 2, v_val_2659_);
lean_ctor_set(v___x_2726_, 1, v_key_2658_);
lean_ctor_set(v___x_2726_, 0, v___x_2666_);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_rchild_2660_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*4, v_color_2635_);
return v___x_2729_;
}
}
}
}
else
{
lean_object* v___x_2736_; 
lean_dec(v_rchild_2671_);
lean_dec(v_val_2670_);
lean_dec(v_key_2669_);
lean_dec(v_lchild_2668_);
lean_del_object(v___x_2662_);
v___x_2736_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2736_, 0, v___x_2666_);
lean_ctor_set(v___x_2736_, 1, v_key_2658_);
lean_ctor_set(v___x_2736_, 2, v_val_2659_);
lean_ctor_set(v___x_2736_, 3, v_rchild_2660_);
lean_ctor_set_uint8(v___x_2736_, sizeof(void*)*4, v_color_2635_);
return v___x_2736_;
}
}
}
else
{
lean_object* v___x_2737_; 
lean_dec(v_rchild_2671_);
lean_dec(v_val_2670_);
lean_dec(v_key_2669_);
lean_dec(v_lchild_2668_);
lean_del_object(v___x_2662_);
v___x_2737_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2737_, 0, v___x_2666_);
lean_ctor_set(v___x_2737_, 1, v_key_2658_);
lean_ctor_set(v___x_2737_, 2, v_val_2659_);
lean_ctor_set(v___x_2737_, 3, v_rchild_2660_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*4, v_color_2635_);
return v___x_2737_;
}
v___jp_2672_:
{
lean_object* v___x_2684_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 3, v_b_2676_);
lean_ctor_set(v___x_2662_, 2, v_vx_2675_);
lean_ctor_set(v___x_2662_, 1, v_kx_2674_);
lean_ctor_set(v___x_2662_, 0, v_a_2673_);
v___x_2684_ = v___x_2662_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2673_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_kx_2674_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_vx_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_b_2676_);
lean_ctor_set_uint8(v_reuseFailAlloc_2687_, sizeof(void*)*4, v_color_2635_);
v___x_2684_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2685_, 0, v_c_2679_);
lean_ctor_set(v___x_2685_, 1, v_kz_2680_);
lean_ctor_set(v___x_2685_, 2, v_vz_2681_);
lean_ctor_set(v___x_2685_, 3, v_d_2682_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*4, v_color_2635_);
v___x_2686_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v_ky_2677_);
lean_ctor_set(v___x_2686_, 2, v_vy_2678_);
lean_ctor_set(v___x_2686_, 3, v___x_2685_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*4, v_color_2667_);
return v___x_2686_;
}
}
}
else
{
lean_object* v___x_2739_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2666_);
v___x_2739_ = v___x_2662_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2740_, 3, v_rchild_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2740_, sizeof(void*)*4, v_color_2635_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
case 1:
{
lean_object* v___x_2742_; 
lean_dec(v_val_2659_);
lean_dec(v_key_2658_);
lean_dec_ref(v_cmp_2629_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 2, v_x_2632_);
lean_ctor_set(v___x_2662_, 1, v_x_2631_);
v___x_2742_ = v___x_2662_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_lchild_2657_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_x_2631_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_x_2632_);
lean_ctor_set(v_reuseFailAlloc_2743_, 3, v_rchild_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2743_, sizeof(void*)*4, v_color_2635_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
default: 
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2629_, v_rchild_2660_, v_x_2631_, v_x_2632_);
if (lean_obj_tag(v___x_2744_) == 1)
{
uint8_t v_color_2745_; lean_object* v_lchild_2746_; lean_object* v_key_2747_; lean_object* v_val_2748_; lean_object* v_rchild_2749_; lean_object* v_a_2751_; lean_object* v_kx_2752_; lean_object* v_vx_2753_; lean_object* v_b_2754_; lean_object* v_ky_2755_; lean_object* v_vy_2756_; lean_object* v_c_2757_; lean_object* v_kz_2758_; lean_object* v_vz_2759_; lean_object* v_d_2760_; 
v_color_2745_ = lean_ctor_get_uint8(v___x_2744_, sizeof(void*)*4);
v_lchild_2746_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_lchild_2746_);
v_key_2747_ = lean_ctor_get(v___x_2744_, 1);
lean_inc(v_key_2747_);
v_val_2748_ = lean_ctor_get(v___x_2744_, 2);
lean_inc(v_val_2748_);
v_rchild_2749_ = lean_ctor_get(v___x_2744_, 3);
lean_inc(v_rchild_2749_);
if (v_color_2745_ == 0)
{
if (lean_obj_tag(v_lchild_2746_) == 1)
{
uint8_t v_color_2766_; 
v_color_2766_ = lean_ctor_get_uint8(v_lchild_2746_, sizeof(void*)*4);
if (v_color_2766_ == 0)
{
lean_object* v_lchild_2767_; lean_object* v_key_2768_; lean_object* v_val_2769_; lean_object* v_rchild_2770_; 
lean_dec_ref(v___x_2744_);
v_lchild_2767_ = lean_ctor_get(v_lchild_2746_, 0);
lean_inc(v_lchild_2767_);
v_key_2768_ = lean_ctor_get(v_lchild_2746_, 1);
lean_inc(v_key_2768_);
v_val_2769_ = lean_ctor_get(v_lchild_2746_, 2);
lean_inc(v_val_2769_);
v_rchild_2770_ = lean_ctor_get(v_lchild_2746_, 3);
lean_inc(v_rchild_2770_);
lean_dec_ref(v_lchild_2746_);
v_a_2751_ = v_lchild_2657_;
v_kx_2752_ = v_key_2658_;
v_vx_2753_ = v_val_2659_;
v_b_2754_ = v_lchild_2767_;
v_ky_2755_ = v_key_2768_;
v_vy_2756_ = v_val_2769_;
v_c_2757_ = v_rchild_2770_;
v_kz_2758_ = v_key_2747_;
v_vz_2759_ = v_val_2748_;
v_d_2760_ = v_rchild_2749_;
goto v___jp_2750_;
}
else
{
if (lean_obj_tag(v_rchild_2749_) == 1)
{
uint8_t v_color_2771_; 
v_color_2771_ = lean_ctor_get_uint8(v_rchild_2749_, sizeof(void*)*4);
if (v_color_2771_ == 0)
{
lean_object* v_lchild_2772_; lean_object* v_key_2773_; lean_object* v_val_2774_; lean_object* v_rchild_2775_; 
lean_dec_ref(v___x_2744_);
v_lchild_2772_ = lean_ctor_get(v_rchild_2749_, 0);
lean_inc(v_lchild_2772_);
v_key_2773_ = lean_ctor_get(v_rchild_2749_, 1);
lean_inc(v_key_2773_);
v_val_2774_ = lean_ctor_get(v_rchild_2749_, 2);
lean_inc(v_val_2774_);
v_rchild_2775_ = lean_ctor_get(v_rchild_2749_, 3);
lean_inc(v_rchild_2775_);
lean_dec_ref(v_rchild_2749_);
v_a_2751_ = v_lchild_2657_;
v_kx_2752_ = v_key_2658_;
v_vx_2753_ = v_val_2659_;
v_b_2754_ = v_lchild_2746_;
v_ky_2755_ = v_key_2747_;
v_vy_2756_ = v_val_2748_;
v_c_2757_ = v_lchild_2772_;
v_kz_2758_ = v_key_2773_;
v_vz_2759_ = v_val_2774_;
v_d_2760_ = v_rchild_2775_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref(v_lchild_2746_);
lean_dec(v_val_2748_);
lean_dec(v_key_2747_);
lean_del_object(v___x_2662_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_rchild_2749_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; lean_object* v_unused_2785_; lean_object* v_unused_2786_; 
v_unused_2783_ = lean_ctor_get(v_rchild_2749_, 3);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_rchild_2749_, 2);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_rchild_2749_, 1);
lean_dec(v_unused_2785_);
v_unused_2786_ = lean_ctor_get(v_rchild_2749_, 0);
lean_dec(v_unused_2786_);
v___x_2777_ = v_rchild_2749_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v_rchild_2749_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 3, v___x_2744_);
lean_ctor_set(v___x_2777_, 2, v_val_2659_);
lean_ctor_set(v___x_2777_, 1, v_key_2658_);
lean_ctor_set(v___x_2777_, 0, v_lchild_2657_);
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_lchild_2657_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2781_, 3, v___x_2744_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*4, v_color_2635_);
return v___x_2780_;
}
}
}
}
else
{
lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_rchild_2749_);
lean_dec(v_val_2748_);
lean_dec(v_key_2747_);
lean_del_object(v___x_2662_);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_lchild_2746_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; lean_object* v_unused_2795_; lean_object* v_unused_2796_; lean_object* v_unused_2797_; 
v_unused_2794_ = lean_ctor_get(v_lchild_2746_, 3);
lean_dec(v_unused_2794_);
v_unused_2795_ = lean_ctor_get(v_lchild_2746_, 2);
lean_dec(v_unused_2795_);
v_unused_2796_ = lean_ctor_get(v_lchild_2746_, 1);
lean_dec(v_unused_2796_);
v_unused_2797_ = lean_ctor_get(v_lchild_2746_, 0);
lean_dec(v_unused_2797_);
v___x_2788_ = v_lchild_2746_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_dec(v_lchild_2746_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 3, v___x_2744_);
lean_ctor_set(v___x_2788_, 2, v_val_2659_);
lean_ctor_set(v___x_2788_, 1, v_key_2658_);
lean_ctor_set(v___x_2788_, 0, v_lchild_2657_);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_lchild_2657_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v___x_2744_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_ctor_set_uint8(v___x_2791_, sizeof(void*)*4, v_color_2635_);
return v___x_2791_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2749_) == 1)
{
uint8_t v_color_2798_; 
v_color_2798_ = lean_ctor_get_uint8(v_rchild_2749_, sizeof(void*)*4);
if (v_color_2798_ == 0)
{
lean_object* v_lchild_2799_; lean_object* v_key_2800_; lean_object* v_val_2801_; lean_object* v_rchild_2802_; 
lean_dec_ref(v___x_2744_);
v_lchild_2799_ = lean_ctor_get(v_rchild_2749_, 0);
lean_inc(v_lchild_2799_);
v_key_2800_ = lean_ctor_get(v_rchild_2749_, 1);
lean_inc(v_key_2800_);
v_val_2801_ = lean_ctor_get(v_rchild_2749_, 2);
lean_inc(v_val_2801_);
v_rchild_2802_ = lean_ctor_get(v_rchild_2749_, 3);
lean_inc(v_rchild_2802_);
lean_dec_ref(v_rchild_2749_);
v_a_2751_ = v_lchild_2657_;
v_kx_2752_ = v_key_2658_;
v_vx_2753_ = v_val_2659_;
v_b_2754_ = v_lchild_2746_;
v_ky_2755_ = v_key_2747_;
v_vy_2756_ = v_val_2748_;
v_c_2757_ = v_lchild_2799_;
v_kz_2758_ = v_key_2800_;
v_vz_2759_ = v_val_2801_;
v_d_2760_ = v_rchild_2802_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_val_2748_);
lean_dec(v_key_2747_);
lean_dec(v_lchild_2746_);
lean_del_object(v___x_2662_);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_rchild_2749_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; lean_object* v_unused_2813_; 
v_unused_2810_ = lean_ctor_get(v_rchild_2749_, 3);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_rchild_2749_, 2);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_rchild_2749_, 1);
lean_dec(v_unused_2812_);
v_unused_2813_ = lean_ctor_get(v_rchild_2749_, 0);
lean_dec(v_unused_2813_);
v___x_2804_ = v_rchild_2749_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_dec(v_rchild_2749_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 3, v___x_2744_);
lean_ctor_set(v___x_2804_, 2, v_val_2659_);
lean_ctor_set(v___x_2804_, 1, v_key_2658_);
lean_ctor_set(v___x_2804_, 0, v_lchild_2657_);
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_lchild_2657_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2808_, 3, v___x_2744_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_ctor_set_uint8(v___x_2807_, sizeof(void*)*4, v_color_2635_);
return v___x_2807_;
}
}
}
}
else
{
lean_object* v___x_2814_; 
lean_dec(v_rchild_2749_);
lean_dec(v_val_2748_);
lean_dec(v_key_2747_);
lean_dec(v_lchild_2746_);
lean_del_object(v___x_2662_);
v___x_2814_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2814_, 0, v_lchild_2657_);
lean_ctor_set(v___x_2814_, 1, v_key_2658_);
lean_ctor_set(v___x_2814_, 2, v_val_2659_);
lean_ctor_set(v___x_2814_, 3, v___x_2744_);
lean_ctor_set_uint8(v___x_2814_, sizeof(void*)*4, v_color_2635_);
return v___x_2814_;
}
}
}
else
{
lean_object* v___x_2815_; 
lean_dec(v_rchild_2749_);
lean_dec(v_val_2748_);
lean_dec(v_key_2747_);
lean_dec(v_lchild_2746_);
lean_del_object(v___x_2662_);
v___x_2815_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2815_, 0, v_lchild_2657_);
lean_ctor_set(v___x_2815_, 1, v_key_2658_);
lean_ctor_set(v___x_2815_, 2, v_val_2659_);
lean_ctor_set(v___x_2815_, 3, v___x_2744_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*4, v_color_2635_);
return v___x_2815_;
}
v___jp_2750_:
{
lean_object* v___x_2762_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 3, v_b_2754_);
lean_ctor_set(v___x_2662_, 2, v_vx_2753_);
lean_ctor_set(v___x_2662_, 1, v_kx_2752_);
lean_ctor_set(v___x_2662_, 0, v_a_2751_);
v___x_2762_ = v___x_2662_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2751_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_kx_2752_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_vx_2753_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_b_2754_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*4, v_color_2635_);
v___x_2762_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2763_, 0, v_c_2757_);
lean_ctor_set(v___x_2763_, 1, v_kz_2758_);
lean_ctor_set(v___x_2763_, 2, v_vz_2759_);
lean_ctor_set(v___x_2763_, 3, v_d_2760_);
lean_ctor_set_uint8(v___x_2763_, sizeof(void*)*4, v_color_2635_);
v___x_2764_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v_ky_2755_);
lean_ctor_set(v___x_2764_, 2, v_vy_2756_);
lean_ctor_set(v___x_2764_, 3, v___x_2763_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*4, v_color_2745_);
return v___x_2764_;
}
}
}
else
{
lean_object* v___x_2817_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 3, v___x_2744_);
v___x_2817_ = v___x_2662_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_lchild_2657_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_key_2658_);
lean_ctor_set(v_reuseFailAlloc_2818_, 2, v_val_2659_);
lean_ctor_set(v_reuseFailAlloc_2818_, 3, v___x_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2818_, sizeof(void*)*4, v_color_2635_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* v_cmp_2820_, lean_object* v_t_2821_, lean_object* v_k_2822_, lean_object* v_v_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = l_Lean_RBNode_isRed___redArg(v_t_2821_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2820_, v_t_2821_, v_k_2822_, v_v_2823_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2820_, v_t_2821_, v_k_2822_, v_v_2823_);
v___x_2827_ = l_Lean_RBNode_setBlack___redArg(v___x_2826_);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* v_cmp_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_){
_start:
{
if (lean_obj_tag(v_x_2829_) == 0)
{
lean_object* v___x_2831_; 
lean_dec(v_x_2830_);
lean_dec_ref(v_cmp_2828_);
v___x_2831_ = lean_box(0);
return v___x_2831_;
}
else
{
lean_object* v_lchild_2832_; lean_object* v_key_2833_; lean_object* v_val_2834_; lean_object* v_rchild_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_lchild_2832_ = lean_ctor_get(v_x_2829_, 0);
lean_inc(v_lchild_2832_);
v_key_2833_ = lean_ctor_get(v_x_2829_, 1);
lean_inc(v_key_2833_);
v_val_2834_ = lean_ctor_get(v_x_2829_, 2);
lean_inc(v_val_2834_);
v_rchild_2835_ = lean_ctor_get(v_x_2829_, 3);
lean_inc(v_rchild_2835_);
lean_dec_ref(v_x_2829_);
lean_inc_ref(v_cmp_2828_);
lean_inc(v_x_2830_);
v___x_2836_ = lean_apply_2(v_cmp_2828_, v_x_2830_, v_key_2833_);
v___x_2837_ = lean_unbox(v___x_2836_);
switch(v___x_2837_)
{
case 0:
{
lean_dec(v_rchild_2835_);
lean_dec(v_val_2834_);
v_x_2829_ = v_lchild_2832_;
goto _start;
}
case 1:
{
lean_object* v___x_2839_; 
lean_dec(v_rchild_2835_);
lean_dec(v_lchild_2832_);
lean_dec(v_x_2830_);
lean_dec_ref(v_cmp_2828_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_val_2834_);
return v___x_2839_;
}
default: 
{
lean_dec(v_val_2834_);
lean_dec(v_lchild_2832_);
v_x_2829_ = v_rchild_2835_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* v_cmp_2841_, lean_object* v_mergeFn_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
if (lean_obj_tag(v_x_2844_) == 0)
{
lean_dec(v_mergeFn_2842_);
lean_dec_ref(v_cmp_2841_);
return v_x_2843_;
}
else
{
lean_object* v_lchild_2845_; lean_object* v_key_2846_; lean_object* v_val_2847_; lean_object* v_rchild_2848_; lean_object* v_val_2849_; lean_object* v___y_2851_; lean_object* v___x_2854_; 
v_lchild_2845_ = lean_ctor_get(v_x_2844_, 0);
lean_inc(v_lchild_2845_);
v_key_2846_ = lean_ctor_get(v_x_2844_, 1);
lean_inc_n(v_key_2846_, 2);
v_val_2847_ = lean_ctor_get(v_x_2844_, 2);
lean_inc(v_val_2847_);
v_rchild_2848_ = lean_ctor_get(v_x_2844_, 3);
lean_inc(v_rchild_2848_);
lean_dec_ref(v_x_2844_);
lean_inc(v_mergeFn_2842_);
lean_inc_ref_n(v_cmp_2841_, 2);
v_val_2849_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2841_, v_mergeFn_2842_, v_x_2843_, v_lchild_2845_);
lean_inc(v_val_2849_);
v___x_2854_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2841_, v_val_2849_, v_key_2846_);
if (lean_obj_tag(v___x_2854_) == 0)
{
v___y_2851_ = v_val_2847_;
goto v___jp_2850_;
}
else
{
lean_object* v_val_2855_; lean_object* v___x_2856_; 
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref(v___x_2854_);
lean_inc(v_mergeFn_2842_);
lean_inc(v_key_2846_);
v___x_2856_ = lean_apply_3(v_mergeFn_2842_, v_key_2846_, v_val_2855_, v_val_2847_);
v___y_2851_ = v___x_2856_;
goto v___jp_2850_;
}
v___jp_2850_:
{
lean_object* v___x_2852_; 
lean_inc_ref(v_cmp_2841_);
v___x_2852_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2841_, v_val_2849_, v_key_2846_, v___y_2851_);
v_x_2843_ = v___x_2852_;
v_x_2844_ = v_rchild_2848_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* v_cmp_2857_, lean_object* v_mergeFn_2858_, lean_object* v_t_u2081_2859_, lean_object* v_t_u2082_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2857_, v_mergeFn_2858_, v_t_u2081_2859_, v_t_u2082_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* v_00_u03b1_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_cmp_2864_, lean_object* v_mergeFn_2865_, lean_object* v_t_u2081_2866_, lean_object* v_t_u2082_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2864_, v_mergeFn_2865_, v_t_u2081_2866_, v_t_u2082_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* v_00_u03b1_2869_, lean_object* v_cmp_2870_, lean_object* v_00_u03b2_2871_, lean_object* v_t_2872_, lean_object* v_k_2873_, lean_object* v_v_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2870_, v_t_2872_, v_k_2873_, v_v_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* v_00_u03b1_2876_, lean_object* v_cmp_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_x_2879_, lean_object* v_x_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2877_, v_x_2879_, v_x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* v_00_u03b1_2882_, lean_object* v_00_u03b2_2883_, lean_object* v_cmp_2884_, lean_object* v_mergeFn_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2884_, v_mergeFn_2885_, v_x_2886_, v_x_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* v_00_u03b1_2889_, lean_object* v_cmp_2890_, lean_object* v_00_u03b2_2891_, lean_object* v_x_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2890_, v_x_2892_, v_x_2893_, v_x_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* v_t_u2082_2896_, lean_object* v_cmp_2897_, lean_object* v_mergeFn_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2900_) == 0)
{
lean_dec(v_mergeFn_2898_);
lean_dec_ref(v_cmp_2897_);
lean_dec(v_t_u2082_2896_);
return v_x_2899_;
}
else
{
lean_object* v_lchild_2901_; lean_object* v_key_2902_; lean_object* v_val_2903_; lean_object* v_rchild_2904_; lean_object* v_val_2905_; lean_object* v___x_2906_; 
v_lchild_2901_ = lean_ctor_get(v_x_2900_, 0);
lean_inc(v_lchild_2901_);
v_key_2902_ = lean_ctor_get(v_x_2900_, 1);
lean_inc_n(v_key_2902_, 2);
v_val_2903_ = lean_ctor_get(v_x_2900_, 2);
lean_inc(v_val_2903_);
v_rchild_2904_ = lean_ctor_get(v_x_2900_, 3);
lean_inc(v_rchild_2904_);
lean_dec_ref(v_x_2900_);
lean_inc(v_mergeFn_2898_);
lean_inc_ref_n(v_cmp_2897_, 2);
lean_inc_n(v_t_u2082_2896_, 2);
v_val_2905_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2896_, v_cmp_2897_, v_mergeFn_2898_, v_x_2899_, v_lchild_2901_);
v___x_2906_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2897_, v_t_u2082_2896_, v_key_2902_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_dec(v_val_2903_);
lean_dec(v_key_2902_);
v_x_2899_ = v_val_2905_;
v_x_2900_ = v_rchild_2904_;
goto _start;
}
else
{
lean_object* v_val_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_val_2908_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_val_2908_);
lean_dec_ref(v___x_2906_);
lean_inc(v_mergeFn_2898_);
lean_inc(v_key_2902_);
v___x_2909_ = lean_apply_3(v_mergeFn_2898_, v_key_2902_, v_val_2903_, v_val_2908_);
lean_inc_ref(v_cmp_2897_);
v___x_2910_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2897_, v_val_2905_, v_key_2902_, v___x_2909_);
v_x_2899_ = v___x_2910_;
v_x_2900_ = v_rchild_2904_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* v_cmp_2912_, lean_object* v_mergeFn_2913_, lean_object* v_t_u2081_2914_, lean_object* v_t_u2082_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_box(0);
v___x_2917_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2915_, v_cmp_2912_, v_mergeFn_2913_, v___x_2916_, v_t_u2081_2914_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* v_00_u03b1_2918_, lean_object* v_00_u03b2_2919_, lean_object* v_cmp_2920_, lean_object* v_00_u03b3_2921_, lean_object* v_00_u03b4_2922_, lean_object* v_mergeFn_2923_, lean_object* v_t_u2081_2924_, lean_object* v_t_u2082_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_RBMap_intersectBy___redArg(v_cmp_2920_, v_mergeFn_2923_, v_t_u2081_2924_, v_t_u2082_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* v_00_u03b1_2927_, lean_object* v_00_u03b2_2928_, lean_object* v_00_u03b4_2929_, lean_object* v_00_u03b3_2930_, lean_object* v_t_u2082_2931_, lean_object* v_cmp_2932_, lean_object* v_mergeFn_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2931_, v_cmp_2932_, v_mergeFn_2933_, v_x_2934_, v_x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* v_f_2937_, lean_object* v_cmp_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_){
_start:
{
if (lean_obj_tag(v_x_2940_) == 0)
{
lean_dec_ref(v_cmp_2938_);
lean_dec_ref(v_f_2937_);
return v_x_2939_;
}
else
{
lean_object* v_lchild_2941_; lean_object* v_key_2942_; lean_object* v_val_2943_; lean_object* v_rchild_2944_; lean_object* v_val_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v_lchild_2941_ = lean_ctor_get(v_x_2940_, 0);
lean_inc(v_lchild_2941_);
v_key_2942_ = lean_ctor_get(v_x_2940_, 1);
lean_inc_n(v_key_2942_, 2);
v_val_2943_ = lean_ctor_get(v_x_2940_, 2);
lean_inc_n(v_val_2943_, 2);
v_rchild_2944_ = lean_ctor_get(v_x_2940_, 3);
lean_inc(v_rchild_2944_);
lean_dec_ref(v_x_2940_);
lean_inc_ref(v_cmp_2938_);
lean_inc_ref_n(v_f_2937_, 2);
v_val_2945_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2937_, v_cmp_2938_, v_x_2939_, v_lchild_2941_);
v___x_2946_ = lean_apply_2(v_f_2937_, v_key_2942_, v_val_2943_);
v___x_2947_ = lean_unbox(v___x_2946_);
if (v___x_2947_ == 0)
{
lean_dec(v_val_2943_);
lean_dec(v_key_2942_);
v_x_2939_ = v_val_2945_;
v_x_2940_ = v_rchild_2944_;
goto _start;
}
else
{
lean_object* v___x_2949_; 
lean_inc_ref(v_cmp_2938_);
v___x_2949_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2938_, v_val_2945_, v_key_2942_, v_val_2943_);
v_x_2939_ = v___x_2949_;
v_x_2940_ = v_rchild_2944_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* v_cmp_2951_, lean_object* v_f_2952_, lean_object* v_m_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_box(0);
v___x_2955_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2952_, v_cmp_2951_, v___x_2954_, v_m_2953_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* v_00_u03b1_2956_, lean_object* v_00_u03b2_2957_, lean_object* v_cmp_2958_, lean_object* v_f_2959_, lean_object* v_m_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_RBMap_filter___redArg(v_cmp_2958_, v_f_2959_, v_m_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* v_00_u03b1_2962_, lean_object* v_00_u03b2_2963_, lean_object* v_f_2964_, lean_object* v_cmp_2965_, lean_object* v_x_2966_, lean_object* v_x_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2964_, v_cmp_2965_, v_x_2966_, v_x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* v_f_2969_, lean_object* v_cmp_2970_, lean_object* v_x_2971_, lean_object* v_x_2972_){
_start:
{
if (lean_obj_tag(v_x_2972_) == 0)
{
lean_dec_ref(v_cmp_2970_);
lean_dec_ref(v_f_2969_);
return v_x_2971_;
}
else
{
lean_object* v_lchild_2973_; lean_object* v_key_2974_; lean_object* v_val_2975_; lean_object* v_rchild_2976_; lean_object* v_val_2977_; lean_object* v___x_2978_; 
v_lchild_2973_ = lean_ctor_get(v_x_2972_, 0);
lean_inc(v_lchild_2973_);
v_key_2974_ = lean_ctor_get(v_x_2972_, 1);
lean_inc_n(v_key_2974_, 2);
v_val_2975_ = lean_ctor_get(v_x_2972_, 2);
lean_inc(v_val_2975_);
v_rchild_2976_ = lean_ctor_get(v_x_2972_, 3);
lean_inc(v_rchild_2976_);
lean_dec_ref(v_x_2972_);
lean_inc_ref(v_cmp_2970_);
lean_inc_ref_n(v_f_2969_, 2);
v_val_2977_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2969_, v_cmp_2970_, v_x_2971_, v_lchild_2973_);
v___x_2978_ = lean_apply_2(v_f_2969_, v_key_2974_, v_val_2975_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_dec(v_key_2974_);
v_x_2971_ = v_val_2977_;
v_x_2972_ = v_rchild_2976_;
goto _start;
}
else
{
lean_object* v_val_2980_; lean_object* v___x_2981_; 
v_val_2980_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_val_2980_);
lean_dec_ref(v___x_2978_);
lean_inc_ref(v_cmp_2970_);
v___x_2981_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2970_, v_val_2977_, v_key_2974_, v_val_2980_);
v_x_2971_ = v___x_2981_;
v_x_2972_ = v_rchild_2976_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* v_cmp_2983_, lean_object* v_f_2984_, lean_object* v_m_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_box(0);
v___x_2987_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2984_, v_cmp_2983_, v___x_2986_, v_m_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* v_00_u03b1_2988_, lean_object* v_00_u03b2_2989_, lean_object* v_cmp_2990_, lean_object* v_00_u03b3_2991_, lean_object* v_f_2992_, lean_object* v_m_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Lean_RBMap_filterMap___redArg(v_cmp_2990_, v_f_2992_, v_m_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* v_00_u03b1_2995_, lean_object* v_00_u03b2_2996_, lean_object* v_00_u03b3_2997_, lean_object* v_f_2998_, lean_object* v_cmp_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2998_, v_cmp_2999_, v_x_3000_, v_x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* v_cmp_3003_, lean_object* v_x_3004_, lean_object* v_x_3005_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
lean_dec_ref(v_cmp_3003_);
return v_x_3004_;
}
else
{
lean_object* v_head_3006_; lean_object* v_tail_3007_; lean_object* v_fst_3008_; lean_object* v_snd_3009_; lean_object* v___x_3010_; 
v_head_3006_ = lean_ctor_get(v_x_3005_, 0);
lean_inc(v_head_3006_);
v_tail_3007_ = lean_ctor_get(v_x_3005_, 1);
lean_inc(v_tail_3007_);
lean_dec_ref(v_x_3005_);
v_fst_3008_ = lean_ctor_get(v_head_3006_, 0);
lean_inc(v_fst_3008_);
v_snd_3009_ = lean_ctor_get(v_head_3006_, 1);
lean_inc(v_snd_3009_);
lean_dec(v_head_3006_);
lean_inc_ref(v_cmp_3003_);
v___x_3010_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_3003_, v_x_3004_, v_fst_3008_, v_snd_3009_);
v_x_3004_ = v___x_3010_;
v_x_3005_ = v_tail_3007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* v_l_3012_, lean_object* v_cmp_3013_){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_box(0);
v___x_3015_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3013_, v___x_3014_, v_l_3012_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* v_00_u03b1_3016_, lean_object* v_00_u03b2_3017_, lean_object* v_l_3018_, lean_object* v_cmp_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_rbmapOf___redArg(v_l_3018_, v_cmp_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* v_00_u03b1_3021_, lean_object* v_00_u03b2_3022_, lean_object* v_cmp_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3023_, v_x_3024_, v_x_3025_);
return v___x_3026_;
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
