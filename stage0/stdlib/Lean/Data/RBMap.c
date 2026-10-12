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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg();
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg___boxed(lean_object*);
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
lean_object* l_Lean_RBColor_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_RBColor_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_RBColor_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_RBColor_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_RBColor_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_RBColor_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_RBColor_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_RBColor_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_RBColor_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg(lean_object* v_red_24_){
_start:
{
lean_inc(v_red_24_);
return v_red_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___redArg___boxed(lean_object* v_red_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_RBColor_red_elim___redArg(v_red_25_);
lean_dec(v_red_25_);
return v_res_26_;
}
}
lean_object* l_Lean_RBColor_red_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_red_30_){
_start:
{
lean_inc(v_red_30_);
return v_red_30_;
}
}
LEAN_EXPORT void l_Lean_RBColor_red_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_red_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_RBColor_red_elim(lean_box(0), v_t_28_, lean_box(0), v_red_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_RBColor_red_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_red_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_RBColor_red_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_red_35_);
lean_dec(v_red_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg(lean_object* v_black_38_){
_start:
{
lean_inc(v_black_38_);
return v_black_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___redArg___boxed(lean_object* v_black_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_RBColor_black_elim___redArg(v_black_39_);
lean_dec(v_black_39_);
return v_res_40_;
}
}
lean_object* l_Lean_RBColor_black_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_black_44_){
_start:
{
lean_inc(v_black_44_);
return v_black_44_;
}
}
LEAN_EXPORT void l_Lean_RBColor_black_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_black_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_RBColor_black_elim(lean_box(0), v_t_42_, lean_box(0), v_black_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_RBColor_black_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_black_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_RBColor_black_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_black_49_);
lean_dec(v_black_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___redArg(lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_tag_nat(v_x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___redArg___boxed(lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_RBNode_ctorIdx___impl___redArg(v_x_54_);
lean_dec(v_x_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_x_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_obj_tag_nat(v_x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___boxed(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_, lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_RBNode_ctorIdx___impl(v_00_u03b1_60_, v_00_u03b2_61_, v_x_62_);
lean_dec(v_x_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___redArg(lean_object* v_t_64_, lean_object* v_k_65_){
_start:
{
if (lean_obj_tag(v_t_64_) == 0)
{
return v_k_65_;
}
else
{
uint8_t v_color_66_; lean_object* v_lchild_67_; lean_object* v_key_68_; lean_object* v_val_69_; lean_object* v_rchild_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_color_66_ = lean_ctor_get_uint8(v_t_64_, sizeof(void*)*4);
v_lchild_67_ = lean_ctor_get(v_t_64_, 0);
lean_inc(v_lchild_67_);
v_key_68_ = lean_ctor_get(v_t_64_, 1);
lean_inc(v_key_68_);
v_val_69_ = lean_ctor_get(v_t_64_, 2);
lean_inc(v_val_69_);
v_rchild_70_ = lean_ctor_get(v_t_64_, 3);
lean_inc(v_rchild_70_);
lean_dec_ref_known(v_t_64_, 4);
v___x_71_ = lean_box(v_color_66_);
v___x_72_ = lean_apply_5(v_k_65_, v___x_71_, v_lchild_67_, v_key_68_, v_val_69_, v_rchild_70_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_RBNode_ctorElim___redArg(v_t_77_, v_k_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___boxed(lean_object* v_00_u03b1_81_, lean_object* v_00_u03b2_82_, lean_object* v_motive_83_, lean_object* v_ctorIdx_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_k_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_RBNode_ctorElim(v_00_u03b1_81_, v_00_u03b2_82_, v_motive_83_, v_ctorIdx_84_, v_t_85_, v_h_86_, v_k_87_);
lean_dec(v_ctorIdx_84_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim___redArg(lean_object* v_t_89_, lean_object* v_leaf_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_RBNode_ctorElim___redArg(v_t_89_, v_leaf_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_leaf_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_RBNode_ctorElim___redArg(v_t_95_, v_leaf_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim___redArg(lean_object* v_t_99_, lean_object* v_node_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_RBNode_ctorElim___redArg(v_t_99_, v_node_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b2_103_, lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_node_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_RBNode_ctorElim___redArg(v_t_105_, v_node_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object* v_f_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_f_109_);
v___x_111_ = lean_unsigned_to_nat(0u);
return v___x_111_;
}
else
{
lean_object* v_lchild_112_; lean_object* v_rchild_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_lchild_112_ = lean_ctor_get(v_x_110_, 0);
v_rchild_113_ = lean_ctor_get(v_x_110_, 3);
lean_inc_ref_n(v_f_109_, 2);
v___x_114_ = l_Lean_RBNode_depth___redArg(v_f_109_, v_lchild_112_);
v___x_115_ = l_Lean_RBNode_depth___redArg(v_f_109_, v_rchild_113_);
v___x_116_ = lean_apply_2(v_f_109_, v___x_114_, v___x_115_);
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v___x_116_, v___x_117_);
lean_dec(v___x_116_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object* v_f_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_RBNode_depth___redArg(v_f_119_, v_x_120_);
lean_dec(v_x_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_f_124_, lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_RBNode_depth___redArg(v_f_124_, v_x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object* v_00_u03b1_127_, lean_object* v_00_u03b2_128_, lean_object* v_f_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_RBNode_depth(v_00_u03b1_127_, v_00_u03b2_128_, v_f_129_, v_x_130_);
lean_dec(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
lean_object* v_lchild_134_; 
v_lchild_134_ = lean_ctor_get(v_x_132_, 0);
if (lean_obj_tag(v_lchild_134_) == 0)
{
lean_object* v_key_135_; lean_object* v_val_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_key_135_ = lean_ctor_get(v_x_132_, 1);
v_val_136_ = lean_ctor_get(v_x_132_, 2);
lean_inc(v_val_136_);
lean_inc(v_key_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_key_135_);
lean_ctor_set(v___x_137_, 1, v_val_136_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
else
{
v_x_132_ = v_lchild_134_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_RBNode_min___redArg(v_x_140_);
lean_dec(v_x_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_RBNode_min___redArg(v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_RBNode_min(v_00_u03b1_146_, v_00_u03b2_147_, v_x_148_);
lean_dec(v_x_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v_rchild_152_; 
v_rchild_152_ = lean_ctor_get(v_x_150_, 3);
if (lean_obj_tag(v_rchild_152_) == 0)
{
lean_object* v_key_153_; lean_object* v_val_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_key_153_ = lean_ctor_get(v_x_150_, 1);
v_val_154_ = lean_ctor_get(v_x_150_, 2);
lean_inc(v_val_154_);
lean_inc(v_key_153_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_key_153_);
lean_ctor_set(v___x_155_, 1, v_val_154_);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
else
{
v_x_150_ = v_rchild_152_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_RBNode_max___redArg(v_x_158_);
lean_dec(v_x_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_RBNode_max___redArg(v_x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object* v_00_u03b1_164_, lean_object* v_00_u03b2_165_, lean_object* v_x_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_RBNode_max(v_00_u03b1_164_, v_00_u03b2_165_, v_x_166_);
lean_dec(v_x_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object* v_f_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_dec(v_f_168_);
return v_x_169_;
}
else
{
lean_object* v_lchild_171_; lean_object* v_key_172_; lean_object* v_val_173_; lean_object* v_rchild_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_lchild_171_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_lchild_171_);
v_key_172_ = lean_ctor_get(v_x_170_, 1);
lean_inc(v_key_172_);
v_val_173_ = lean_ctor_get(v_x_170_, 2);
lean_inc(v_val_173_);
v_rchild_174_ = lean_ctor_get(v_x_170_, 3);
lean_inc(v_rchild_174_);
lean_dec_ref_known(v_x_170_, 4);
lean_inc_n(v_f_168_, 2);
v___x_175_ = l_Lean_RBNode_fold___redArg(v_f_168_, v_x_169_, v_lchild_171_);
v___x_176_ = lean_apply_3(v_f_168_, v___x_175_, v_key_172_, v_val_173_);
v_x_169_ = v___x_176_;
v_x_170_ = v_rchild_174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_00_u03c3_180_, lean_object* v_f_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_RBNode_fold___redArg(v_f_181_, v_x_182_, v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object* v_f_185_, lean_object* v_key_186_, lean_object* v_val_187_, lean_object* v_toBind_188_, lean_object* v___f_189_, lean_object* v_____r_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_apply_2(v_f_185_, v_key_186_, v_val_187_);
v___x_192_ = lean_apply_4(v_toBind_188_, lean_box(0), lean_box(0), v___x_191_, v___f_189_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object* v_inst_193_, lean_object* v_f_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_object* v_toApplicative_196_; lean_object* v_toPure_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_toApplicative_196_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toApplicative_196_);
lean_dec(v_f_194_);
lean_dec_ref(v_inst_193_);
v_toPure_197_ = lean_ctor_get(v_toApplicative_196_, 1);
lean_inc(v_toPure_197_);
lean_dec_ref(v_toApplicative_196_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_apply_2(v_toPure_197_, lean_box(0), v___x_198_);
return v___x_199_;
}
else
{
lean_object* v_toBind_200_; lean_object* v_lchild_201_; lean_object* v_key_202_; lean_object* v_val_203_; lean_object* v_rchild_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_toBind_200_ = lean_ctor_get(v_inst_193_, 1);
lean_inc_n(v_toBind_200_, 2);
v_lchild_201_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_lchild_201_);
v_key_202_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_key_202_);
v_val_203_ = lean_ctor_get(v_x_195_, 2);
lean_inc(v_val_203_);
v_rchild_204_ = lean_ctor_get(v_x_195_, 3);
lean_inc(v_rchild_204_);
lean_dec_ref_known(v_x_195_, 4);
lean_inc_n(v_f_194_, 2);
lean_inc_ref(v_inst_193_);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_205_, 0, v_inst_193_);
lean_closure_set(v___f_205_, 1, v_f_194_);
lean_closure_set(v___f_205_, 2, v_rchild_204_);
v___f_206_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_206_, 0, v_f_194_);
lean_closure_set(v___f_206_, 1, v_key_202_);
lean_closure_set(v___f_206_, 2, v_val_203_);
lean_closure_set(v___f_206_, 3, v_toBind_200_);
lean_closure_set(v___f_206_, 4, v___f_205_);
v___x_207_ = l_Lean_RBNode_forM___redArg(v_inst_193_, v_f_194_, v_lchild_201_);
v___x_208_ = lean_apply_4(v_toBind_200_, lean_box(0), lean_box(0), v___x_207_, v___f_206_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object* v_inst_209_, lean_object* v_f_210_, lean_object* v_rchild_211_, lean_object* v_____r_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_RBNode_forM___redArg(v_inst_209_, v_f_210_, v_rchild_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_m_216_, lean_object* v_inst_217_, lean_object* v_f_218_, lean_object* v_x_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_RBNode_forM___redArg(v_inst_217_, v_f_218_, v_x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object* v_f_221_, lean_object* v_key_222_, lean_object* v_val_223_, lean_object* v_toBind_224_, lean_object* v___f_225_, lean_object* v_b_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_apply_3(v_f_221_, v_b_226_, v_key_222_, v_val_223_);
v___x_228_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v___x_227_, v___f_225_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object* v_inst_229_, lean_object* v_f_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v_toApplicative_233_; lean_object* v_toPure_234_; lean_object* v___x_235_; 
v_toApplicative_233_ = lean_ctor_get(v_inst_229_, 0);
lean_inc_ref(v_toApplicative_233_);
lean_dec(v_f_230_);
lean_dec_ref(v_inst_229_);
v_toPure_234_ = lean_ctor_get(v_toApplicative_233_, 1);
lean_inc(v_toPure_234_);
lean_dec_ref(v_toApplicative_233_);
v___x_235_ = lean_apply_2(v_toPure_234_, lean_box(0), v_x_231_);
return v___x_235_;
}
else
{
lean_object* v_toBind_236_; lean_object* v_lchild_237_; lean_object* v_key_238_; lean_object* v_val_239_; lean_object* v_rchild_240_; lean_object* v___f_241_; lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_toBind_236_ = lean_ctor_get(v_inst_229_, 1);
lean_inc_n(v_toBind_236_, 2);
v_lchild_237_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_lchild_237_);
v_key_238_ = lean_ctor_get(v_x_232_, 1);
lean_inc(v_key_238_);
v_val_239_ = lean_ctor_get(v_x_232_, 2);
lean_inc(v_val_239_);
v_rchild_240_ = lean_ctor_get(v_x_232_, 3);
lean_inc(v_rchild_240_);
lean_dec_ref_known(v_x_232_, 4);
lean_inc_n(v_f_230_, 2);
lean_inc_ref(v_inst_229_);
v___f_241_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_241_, 0, v_inst_229_);
lean_closure_set(v___f_241_, 1, v_f_230_);
lean_closure_set(v___f_241_, 2, v_rchild_240_);
v___f_242_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_242_, 0, v_f_230_);
lean_closure_set(v___f_242_, 1, v_key_238_);
lean_closure_set(v___f_242_, 2, v_val_239_);
lean_closure_set(v___f_242_, 3, v_toBind_236_);
lean_closure_set(v___f_242_, 4, v___f_241_);
v___x_243_ = l_Lean_RBNode_foldM___redArg(v_inst_229_, v_f_230_, v_x_231_, v_lchild_237_);
v___x_244_ = lean_apply_4(v_toBind_236_, lean_box(0), lean_box(0), v___x_243_, v___f_242_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object* v_inst_245_, lean_object* v_f_246_, lean_object* v_rchild_247_, lean_object* v_b_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_RBNode_foldM___redArg(v_inst_245_, v_f_246_, v_b_248_, v_rchild_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_00_u03c3_252_, lean_object* v_m_253_, lean_object* v_inst_254_, lean_object* v_f_255_, lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_RBNode_foldM___redArg(v_inst_254_, v_f_255_, v_x_256_, v_x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object* v_toPure_259_, lean_object* v_f_260_, lean_object* v_key_261_, lean_object* v_val_262_, lean_object* v_toBind_263_, lean_object* v___f_264_, lean_object* v_____do__lift_265_){
_start:
{
if (lean_obj_tag(v_____do__lift_265_) == 0)
{
lean_object* v___x_266_; 
lean_dec(v___f_264_);
lean_dec(v_toBind_263_);
lean_dec(v_val_262_);
lean_dec(v_key_261_);
lean_dec(v_f_260_);
v___x_266_ = lean_apply_2(v_toPure_259_, lean_box(0), v_____do__lift_265_);
return v___x_266_;
}
else
{
lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_toPure_259_);
v_a_267_ = lean_ctor_get(v_____do__lift_265_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v_____do__lift_265_, 1);
v___x_268_ = lean_apply_3(v_f_260_, v_key_261_, v_val_262_, v_a_267_);
v___x_269_ = lean_apply_4(v_toBind_263_, lean_box(0), lean_box(0), v___x_268_, v___f_264_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object* v_inst_270_, lean_object* v_f_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
if (lean_obj_tag(v_a_272_) == 0)
{
lean_object* v_toApplicative_274_; lean_object* v_toPure_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_toApplicative_274_ = lean_ctor_get(v_inst_270_, 0);
lean_inc_ref(v_toApplicative_274_);
lean_dec(v_f_271_);
lean_dec_ref(v_inst_270_);
v_toPure_275_ = lean_ctor_get(v_toApplicative_274_, 1);
lean_inc(v_toPure_275_);
lean_dec_ref(v_toApplicative_274_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_a_273_);
v___x_277_ = lean_apply_2(v_toPure_275_, lean_box(0), v___x_276_);
return v___x_277_;
}
else
{
lean_object* v_toApplicative_278_; lean_object* v_toBind_279_; lean_object* v_toPure_280_; lean_object* v_lchild_281_; lean_object* v_key_282_; lean_object* v_val_283_; lean_object* v_rchild_284_; lean_object* v___f_285_; lean_object* v___f_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_toApplicative_278_ = lean_ctor_get(v_inst_270_, 0);
v_toBind_279_ = lean_ctor_get(v_inst_270_, 1);
lean_inc_n(v_toBind_279_, 2);
v_toPure_280_ = lean_ctor_get(v_toApplicative_278_, 1);
v_lchild_281_ = lean_ctor_get(v_a_272_, 0);
lean_inc(v_lchild_281_);
v_key_282_ = lean_ctor_get(v_a_272_, 1);
lean_inc(v_key_282_);
v_val_283_ = lean_ctor_get(v_a_272_, 2);
lean_inc(v_val_283_);
v_rchild_284_ = lean_ctor_get(v_a_272_, 3);
lean_inc(v_rchild_284_);
lean_dec_ref_known(v_a_272_, 4);
lean_inc_n(v_f_271_, 2);
lean_inc_ref(v_inst_270_);
lean_inc_n(v_toPure_280_, 2);
v___f_285_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0), 5, 4);
lean_closure_set(v___f_285_, 0, v_toPure_280_);
lean_closure_set(v___f_285_, 1, v_inst_270_);
lean_closure_set(v___f_285_, 2, v_f_271_);
lean_closure_set(v___f_285_, 3, v_rchild_284_);
v___f_286_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1), 7, 6);
lean_closure_set(v___f_286_, 0, v_toPure_280_);
lean_closure_set(v___f_286_, 1, v_f_271_);
lean_closure_set(v___f_286_, 2, v_key_282_);
lean_closure_set(v___f_286_, 3, v_val_283_);
lean_closure_set(v___f_286_, 4, v_toBind_279_);
lean_closure_set(v___f_286_, 5, v___f_285_);
v___x_287_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_270_, v_f_271_, v_lchild_281_, v_a_273_);
v___x_288_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v___x_287_, v___f_286_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object* v_toPure_289_, lean_object* v_inst_290_, lean_object* v_f_291_, lean_object* v_rchild_292_, lean_object* v_____do__lift_293_){
_start:
{
if (lean_obj_tag(v_____do__lift_293_) == 0)
{
lean_object* v___x_294_; 
lean_dec(v_rchild_292_);
lean_dec(v_f_291_);
lean_dec_ref(v_inst_290_);
v___x_294_ = lean_apply_2(v_toPure_289_, lean_box(0), v_____do__lift_293_);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_296_; 
lean_dec(v_toPure_289_);
v_a_295_ = lean_ctor_get(v_____do__lift_293_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v_____do__lift_293_, 1);
v___x_296_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_290_, v_f_291_, v_rchild_292_, v_a_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_00_u03c3_299_, lean_object* v_m_300_, lean_object* v_inst_301_, lean_object* v_f_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_301_, v_f_302_, v_a_303_, v_a_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object* v_toPure_306_, lean_object* v_____do__lift_307_){
_start:
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v_____do__lift_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v_____do__lift_307_);
v___x_309_ = lean_apply_2(v_toPure_306_, lean_box(0), v_a_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object* v_inst_310_, lean_object* v_as_311_, lean_object* v_init_312_, lean_object* v_f_313_){
_start:
{
lean_object* v_toApplicative_314_; lean_object* v_toBind_315_; lean_object* v_toPure_316_; lean_object* v___x_317_; lean_object* v___f_318_; lean_object* v___x_319_; 
v_toApplicative_314_ = lean_ctor_get(v_inst_310_, 0);
v_toBind_315_ = lean_ctor_get(v_inst_310_, 1);
lean_inc(v_toBind_315_);
v_toPure_316_ = lean_ctor_get(v_toApplicative_314_, 1);
lean_inc(v_toPure_316_);
v___x_317_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_310_, v_f_313_, v_as_311_, v_init_312_);
v___f_318_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_318_, 0, v_toPure_316_);
v___x_319_ = lean_apply_4(v_toBind_315_, lean_box(0), lean_box(0), v___x_317_, v___f_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_00_u03c3_322_, lean_object* v_m_323_, lean_object* v_inst_324_, lean_object* v_as_325_, lean_object* v_init_326_, lean_object* v_f_327_){
_start:
{
lean_object* v_toApplicative_328_; lean_object* v_toBind_329_; lean_object* v_toPure_330_; lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___x_333_; 
v_toApplicative_328_ = lean_ctor_get(v_inst_324_, 0);
v_toBind_329_ = lean_ctor_get(v_inst_324_, 1);
lean_inc(v_toBind_329_);
v_toPure_330_ = lean_ctor_get(v_toApplicative_328_, 1);
lean_inc(v_toPure_330_);
v___x_331_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_324_, v_f_327_, v_as_325_, v_init_326_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_332_, 0, v_toPure_330_);
v___x_333_ = lean_apply_4(v_toBind_329_, lean_box(0), lean_box(0), v___x_331_, v___f_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object* v_f_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_dec(v_f_334_);
return v_x_335_;
}
else
{
lean_object* v_lchild_337_; lean_object* v_key_338_; lean_object* v_val_339_; lean_object* v_rchild_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_lchild_337_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_lchild_337_);
v_key_338_ = lean_ctor_get(v_x_336_, 1);
lean_inc(v_key_338_);
v_val_339_ = lean_ctor_get(v_x_336_, 2);
lean_inc(v_val_339_);
v_rchild_340_ = lean_ctor_get(v_x_336_, 3);
lean_inc(v_rchild_340_);
lean_dec_ref_known(v_x_336_, 4);
lean_inc_n(v_f_334_, 2);
v___x_341_ = l_Lean_RBNode_revFold___redArg(v_f_334_, v_x_335_, v_rchild_340_);
v___x_342_ = lean_apply_3(v_f_334_, v___x_341_, v_key_338_, v_val_339_);
v_x_335_ = v___x_342_;
v_x_336_ = v_lchild_337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_00_u03c3_346_, lean_object* v_f_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_RBNode_revFold___redArg(v_f_347_, v_x_348_, v_x_349_);
return v___x_350_;
}
}
uint8_t l_Lean_RBNode_all___redArg(lean_object* v_p_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
uint8_t v___x_353_; 
lean_dec_ref(v_p_351_);
v___x_353_ = 1;
return v___x_353_;
}
else
{
lean_object* v_lchild_354_; lean_object* v_key_355_; lean_object* v_val_356_; lean_object* v_rchild_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_lchild_354_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_lchild_354_);
v_key_355_ = lean_ctor_get(v_x_352_, 1);
lean_inc(v_key_355_);
v_val_356_ = lean_ctor_get(v_x_352_, 2);
lean_inc(v_val_356_);
v_rchild_357_ = lean_ctor_get(v_x_352_, 3);
lean_inc(v_rchild_357_);
lean_dec_ref_known(v_x_352_, 4);
lean_inc_ref(v_p_351_);
v___x_358_ = lean_apply_2(v_p_351_, v_key_355_, v_val_356_);
v___x_359_ = lean_unbox(v___x_358_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
lean_dec(v_rchild_357_);
lean_dec(v_lchild_354_);
lean_dec_ref(v_p_351_);
v___x_360_ = lean_unbox(v___x_358_);
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
lean_inc_ref(v_p_351_);
v___x_361_ = l_Lean_RBNode_all___redArg(v_p_351_, v_lchild_354_);
if (v___x_361_ == 0)
{
lean_dec(v_rchild_357_);
lean_dec_ref(v_p_351_);
return v___x_361_;
}
else
{
v_x_352_ = v_rchild_357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Lean_RBNode_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_351_ = stack[0].m_obj;
lean_object* v_x_352_ = stack[1].m_obj;
uint8_t v_res_363_;
v_res_363_ = l_Lean_RBNode_all___redArg(v_p_351_, v_x_352_);
stack->m_num = v_res_363_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object* v_p_364_, lean_object* v_x_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_RBNode_all___redArg(v_p_364_, v_x_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
uint8_t l_Lean_RBNode_all(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_p_370_, lean_object* v_x_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_RBNode_all___redArg(v_p_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT void l_Lean_RBNode_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_370_ = stack[2].m_obj;
lean_object* v_x_371_ = stack[3].m_obj;
uint8_t v_res_373_;
v_res_373_ = l_Lean_RBNode_all(lean_box(0), lean_box(0), v_p_370_, v_x_371_);
stack->m_num = v_res_373_;
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
uint8_t l_Lean_RBNode_any___redArg(lean_object* v_p_380_, lean_object* v_x_381_){
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
lean_dec_ref_known(v_x_381_, 4);
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
LEAN_EXPORT void l_Lean_RBNode_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_380_ = stack[0].m_obj;
lean_object* v_x_381_ = stack[1].m_obj;
uint8_t v_res_392_;
v_res_392_ = l_Lean_RBNode_any___redArg(v_p_380_, v_x_381_);
stack->m_num = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object* v_p_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lean_RBNode_any___redArg(v_p_393_, v_x_394_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
uint8_t l_Lean_RBNode_any(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_p_399_, lean_object* v_x_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = l_Lean_RBNode_any___redArg(v_p_399_, v_x_400_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Lean_RBNode_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_399_ = stack[2].m_obj;
lean_object* v_x_400_ = stack[3].m_obj;
uint8_t v_res_402_;
v_res_402_ = l_Lean_RBNode_any(lean_box(0), lean_box(0), v_p_399_, v_x_400_);
stack->m_num = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object* v_00_u03b1_403_, lean_object* v_00_u03b2_404_, lean_object* v_p_405_, lean_object* v_x_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Lean_RBNode_any(v_00_u03b1_403_, v_00_u03b2_404_, v_p_405_, v_x_406_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object* v_k_409_, lean_object* v_v_410_){
_start:
{
uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = 0;
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_k_409_);
lean_ctor_set(v___x_413_, 2, v_v_410_);
lean_ctor_set(v___x_413_, 3, v___x_412_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*4, v___x_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_k_416_, lean_object* v_v_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_RBNode_singleton___redArg(v_k_416_, v_v_417_);
return v___x_418_;
}
}
uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 1)
{
lean_object* v_lchild_420_; 
v_lchild_420_ = lean_ctor_get(v_x_419_, 0);
if (lean_obj_tag(v_lchild_420_) == 0)
{
lean_object* v_rchild_421_; 
v_rchild_421_ = lean_ctor_get(v_x_419_, 3);
if (lean_obj_tag(v_rchild_421_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 1;
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
else
{
uint8_t v___x_424_; 
v___x_424_ = 0;
return v___x_424_;
}
}
else
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
}
}
LEAN_EXPORT void l_Lean_RBNode_isSingleton___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_419_ = stack[0].m_obj;
uint8_t v_res_426_;
v_res_426_ = l_Lean_RBNode_isSingleton___redArg(v_x_419_);
stack->m_num = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object* v_x_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_RBNode_isSingleton___redArg(v_x_427_);
lean_dec(v_x_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
uint8_t l_Lean_RBNode_isSingleton(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_x_432_){
_start:
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_RBNode_isSingleton___redArg(v_x_432_);
return v___x_433_;
}
}
LEAN_EXPORT void l_Lean_RBNode_isSingleton_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_432_ = stack[2].m_obj;
uint8_t v_res_434_;
v_res_434_ = l_Lean_RBNode_isSingleton(lean_box(0), lean_box(0), v_x_432_);
stack->m_num = v_res_434_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object* v_00_u03b1_435_, lean_object* v_00_u03b2_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_RBNode_isSingleton(v_00_u03b1_435_, v_00_u03b2_436_, v_x_437_);
lean_dec(v_x_437_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_a_445_; lean_object* v_kx_446_; lean_object* v_vx_447_; lean_object* v_b_448_; 
if (lean_obj_tag(v_x_440_) == 1)
{
uint8_t v_color_451_; lean_object* v_lchild_452_; lean_object* v_key_453_; lean_object* v_val_454_; lean_object* v_rchild_455_; lean_object* v_a_457_; lean_object* v_kx_458_; lean_object* v_vx_459_; lean_object* v_b_460_; lean_object* v_ky_461_; lean_object* v_vy_462_; lean_object* v_c_463_; lean_object* v_kz_464_; lean_object* v_vz_465_; lean_object* v_d_466_; 
v_color_451_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*4);
v_lchild_452_ = lean_ctor_get(v_x_440_, 0);
v_key_453_ = lean_ctor_get(v_x_440_, 1);
v_val_454_ = lean_ctor_get(v_x_440_, 2);
v_rchild_455_ = lean_ctor_get(v_x_440_, 3);
if (v_color_451_ == 0)
{
if (lean_obj_tag(v_lchild_452_) == 1)
{
uint8_t v_color_471_; 
v_color_471_ = lean_ctor_get_uint8(v_lchild_452_, sizeof(void*)*4);
if (v_color_471_ == 0)
{
lean_object* v_lchild_472_; lean_object* v_key_473_; lean_object* v_val_474_; lean_object* v_rchild_475_; 
lean_inc_ref(v_lchild_452_);
lean_inc(v_rchild_455_);
lean_inc(v_val_454_);
lean_inc(v_key_453_);
lean_dec_ref_known(v_x_440_, 4);
v_lchild_472_ = lean_ctor_get(v_lchild_452_, 0);
lean_inc(v_lchild_472_);
v_key_473_ = lean_ctor_get(v_lchild_452_, 1);
lean_inc(v_key_473_);
v_val_474_ = lean_ctor_get(v_lchild_452_, 2);
lean_inc(v_val_474_);
v_rchild_475_ = lean_ctor_get(v_lchild_452_, 3);
lean_inc(v_rchild_475_);
lean_dec_ref_known(v_lchild_452_, 4);
v_a_457_ = v_lchild_472_;
v_kx_458_ = v_key_473_;
v_vx_459_ = v_val_474_;
v_b_460_ = v_rchild_475_;
v_ky_461_ = v_key_453_;
v_vy_462_ = v_val_454_;
v_c_463_ = v_rchild_455_;
v_kz_464_ = v_x_441_;
v_vz_465_ = v_x_442_;
v_d_466_ = v_x_443_;
goto v___jp_456_;
}
else
{
if (lean_obj_tag(v_rchild_455_) == 1)
{
uint8_t v_color_476_; 
v_color_476_ = lean_ctor_get_uint8(v_rchild_455_, sizeof(void*)*4);
if (v_color_476_ == 0)
{
lean_object* v_lchild_477_; lean_object* v_key_478_; lean_object* v_val_479_; lean_object* v_rchild_480_; 
lean_inc_ref(v_rchild_455_);
lean_inc_ref(v_lchild_452_);
lean_inc(v_val_454_);
lean_inc(v_key_453_);
lean_dec_ref_known(v_x_440_, 4);
v_lchild_477_ = lean_ctor_get(v_rchild_455_, 0);
lean_inc(v_lchild_477_);
v_key_478_ = lean_ctor_get(v_rchild_455_, 1);
lean_inc(v_key_478_);
v_val_479_ = lean_ctor_get(v_rchild_455_, 2);
lean_inc(v_val_479_);
v_rchild_480_ = lean_ctor_get(v_rchild_455_, 3);
lean_inc(v_rchild_480_);
lean_dec_ref_known(v_rchild_455_, 4);
v_a_457_ = v_lchild_452_;
v_kx_458_ = v_key_453_;
v_vx_459_ = v_val_454_;
v_b_460_ = v_lchild_477_;
v_ky_461_ = v_key_478_;
v_vy_462_ = v_val_479_;
v_c_463_ = v_rchild_480_;
v_kz_464_ = v_x_441_;
v_vz_465_ = v_x_442_;
v_d_466_ = v_x_443_;
goto v___jp_456_;
}
else
{
v_a_445_ = v_x_440_;
v_kx_446_ = v_x_441_;
v_vx_447_ = v_x_442_;
v_b_448_ = v_x_443_;
goto v___jp_444_;
}
}
else
{
v_a_445_ = v_x_440_;
v_kx_446_ = v_x_441_;
v_vx_447_ = v_x_442_;
v_b_448_ = v_x_443_;
goto v___jp_444_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_455_) == 1)
{
uint8_t v_color_481_; 
v_color_481_ = lean_ctor_get_uint8(v_rchild_455_, sizeof(void*)*4);
if (v_color_481_ == 0)
{
lean_object* v_lchild_482_; lean_object* v_key_483_; lean_object* v_val_484_; lean_object* v_rchild_485_; 
lean_inc_ref(v_rchild_455_);
lean_inc(v_val_454_);
lean_inc(v_key_453_);
lean_inc(v_lchild_452_);
lean_dec_ref_known(v_x_440_, 4);
v_lchild_482_ = lean_ctor_get(v_rchild_455_, 0);
lean_inc(v_lchild_482_);
v_key_483_ = lean_ctor_get(v_rchild_455_, 1);
lean_inc(v_key_483_);
v_val_484_ = lean_ctor_get(v_rchild_455_, 2);
lean_inc(v_val_484_);
v_rchild_485_ = lean_ctor_get(v_rchild_455_, 3);
lean_inc(v_rchild_485_);
lean_dec_ref_known(v_rchild_455_, 4);
v_a_457_ = v_lchild_452_;
v_kx_458_ = v_key_453_;
v_vx_459_ = v_val_454_;
v_b_460_ = v_lchild_482_;
v_ky_461_ = v_key_483_;
v_vy_462_ = v_val_484_;
v_c_463_ = v_rchild_485_;
v_kz_464_ = v_x_441_;
v_vz_465_ = v_x_442_;
v_d_466_ = v_x_443_;
goto v___jp_456_;
}
else
{
v_a_445_ = v_x_440_;
v_kx_446_ = v_x_441_;
v_vx_447_ = v_x_442_;
v_b_448_ = v_x_443_;
goto v___jp_444_;
}
}
else
{
v_a_445_ = v_x_440_;
v_kx_446_ = v_x_441_;
v_vx_447_ = v_x_442_;
v_b_448_ = v_x_443_;
goto v___jp_444_;
}
}
}
else
{
v_a_445_ = v_x_440_;
v_kx_446_ = v_x_441_;
v_vx_447_ = v_x_442_;
v_b_448_ = v_x_443_;
goto v___jp_444_;
}
v___jp_456_:
{
uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = 1;
v___x_468_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_468_, 0, v_a_457_);
lean_ctor_set(v___x_468_, 1, v_kx_458_);
lean_ctor_set(v___x_468_, 2, v_vx_459_);
lean_ctor_set(v___x_468_, 3, v_b_460_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*4, v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_469_, 0, v_c_463_);
lean_ctor_set(v___x_469_, 1, v_kz_464_);
lean_ctor_set(v___x_469_, 2, v_vz_465_);
lean_ctor_set(v___x_469_, 3, v_d_466_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*4, v___x_467_);
v___x_470_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v_ky_461_);
lean_ctor_set(v___x_470_, 2, v_vy_462_);
lean_ctor_set(v___x_470_, 3, v___x_469_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*4, v_color_451_);
return v___x_470_;
}
}
else
{
v_a_445_ = v_x_440_;
v_kx_446_ = v_x_441_;
v_vx_447_ = v_x_442_;
v_b_448_ = v_x_443_;
goto v___jp_444_;
}
v___jp_444_:
{
uint8_t v___x_449_; lean_object* v___x_450_; 
v___x_449_ = 1;
v___x_450_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_450_, 0, v_a_445_);
lean_ctor_set(v___x_450_, 1, v_kx_446_);
lean_ctor_set(v___x_450_, 2, v_vx_447_);
lean_ctor_set(v___x_450_, 3, v_b_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*4, v___x_449_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
lean_object* v_a_493_; lean_object* v_kx_494_; lean_object* v_vx_495_; lean_object* v_b_496_; 
if (lean_obj_tag(v_x_488_) == 1)
{
uint8_t v_color_499_; lean_object* v_lchild_500_; lean_object* v_key_501_; lean_object* v_val_502_; lean_object* v_rchild_503_; lean_object* v_a_505_; lean_object* v_kx_506_; lean_object* v_vx_507_; lean_object* v_b_508_; lean_object* v_ky_509_; lean_object* v_vy_510_; lean_object* v_c_511_; lean_object* v_kz_512_; lean_object* v_vz_513_; lean_object* v_d_514_; 
v_color_499_ = lean_ctor_get_uint8(v_x_488_, sizeof(void*)*4);
v_lchild_500_ = lean_ctor_get(v_x_488_, 0);
v_key_501_ = lean_ctor_get(v_x_488_, 1);
v_val_502_ = lean_ctor_get(v_x_488_, 2);
v_rchild_503_ = lean_ctor_get(v_x_488_, 3);
if (v_color_499_ == 0)
{
if (lean_obj_tag(v_lchild_500_) == 1)
{
uint8_t v_color_519_; 
v_color_519_ = lean_ctor_get_uint8(v_lchild_500_, sizeof(void*)*4);
if (v_color_519_ == 0)
{
lean_object* v_lchild_520_; lean_object* v_key_521_; lean_object* v_val_522_; lean_object* v_rchild_523_; 
lean_inc_ref(v_lchild_500_);
lean_inc(v_rchild_503_);
lean_inc(v_val_502_);
lean_inc(v_key_501_);
lean_dec_ref_known(v_x_488_, 4);
v_lchild_520_ = lean_ctor_get(v_lchild_500_, 0);
lean_inc(v_lchild_520_);
v_key_521_ = lean_ctor_get(v_lchild_500_, 1);
lean_inc(v_key_521_);
v_val_522_ = lean_ctor_get(v_lchild_500_, 2);
lean_inc(v_val_522_);
v_rchild_523_ = lean_ctor_get(v_lchild_500_, 3);
lean_inc(v_rchild_523_);
lean_dec_ref_known(v_lchild_500_, 4);
v_a_505_ = v_lchild_520_;
v_kx_506_ = v_key_521_;
v_vx_507_ = v_val_522_;
v_b_508_ = v_rchild_523_;
v_ky_509_ = v_key_501_;
v_vy_510_ = v_val_502_;
v_c_511_ = v_rchild_503_;
v_kz_512_ = v_x_489_;
v_vz_513_ = v_x_490_;
v_d_514_ = v_x_491_;
goto v___jp_504_;
}
else
{
if (lean_obj_tag(v_rchild_503_) == 1)
{
uint8_t v_color_524_; 
v_color_524_ = lean_ctor_get_uint8(v_rchild_503_, sizeof(void*)*4);
if (v_color_524_ == 0)
{
lean_object* v_lchild_525_; lean_object* v_key_526_; lean_object* v_val_527_; lean_object* v_rchild_528_; 
lean_inc_ref(v_rchild_503_);
lean_inc_ref(v_lchild_500_);
lean_inc(v_val_502_);
lean_inc(v_key_501_);
lean_dec_ref_known(v_x_488_, 4);
v_lchild_525_ = lean_ctor_get(v_rchild_503_, 0);
lean_inc(v_lchild_525_);
v_key_526_ = lean_ctor_get(v_rchild_503_, 1);
lean_inc(v_key_526_);
v_val_527_ = lean_ctor_get(v_rchild_503_, 2);
lean_inc(v_val_527_);
v_rchild_528_ = lean_ctor_get(v_rchild_503_, 3);
lean_inc(v_rchild_528_);
lean_dec_ref_known(v_rchild_503_, 4);
v_a_505_ = v_lchild_500_;
v_kx_506_ = v_key_501_;
v_vx_507_ = v_val_502_;
v_b_508_ = v_lchild_525_;
v_ky_509_ = v_key_526_;
v_vy_510_ = v_val_527_;
v_c_511_ = v_rchild_528_;
v_kz_512_ = v_x_489_;
v_vz_513_ = v_x_490_;
v_d_514_ = v_x_491_;
goto v___jp_504_;
}
else
{
v_a_493_ = v_x_488_;
v_kx_494_ = v_x_489_;
v_vx_495_ = v_x_490_;
v_b_496_ = v_x_491_;
goto v___jp_492_;
}
}
else
{
v_a_493_ = v_x_488_;
v_kx_494_ = v_x_489_;
v_vx_495_ = v_x_490_;
v_b_496_ = v_x_491_;
goto v___jp_492_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_503_) == 1)
{
uint8_t v_color_529_; 
v_color_529_ = lean_ctor_get_uint8(v_rchild_503_, sizeof(void*)*4);
if (v_color_529_ == 0)
{
lean_object* v_lchild_530_; lean_object* v_key_531_; lean_object* v_val_532_; lean_object* v_rchild_533_; 
lean_inc_ref(v_rchild_503_);
lean_inc(v_val_502_);
lean_inc(v_key_501_);
lean_inc(v_lchild_500_);
lean_dec_ref_known(v_x_488_, 4);
v_lchild_530_ = lean_ctor_get(v_rchild_503_, 0);
lean_inc(v_lchild_530_);
v_key_531_ = lean_ctor_get(v_rchild_503_, 1);
lean_inc(v_key_531_);
v_val_532_ = lean_ctor_get(v_rchild_503_, 2);
lean_inc(v_val_532_);
v_rchild_533_ = lean_ctor_get(v_rchild_503_, 3);
lean_inc(v_rchild_533_);
lean_dec_ref_known(v_rchild_503_, 4);
v_a_505_ = v_lchild_500_;
v_kx_506_ = v_key_501_;
v_vx_507_ = v_val_502_;
v_b_508_ = v_lchild_530_;
v_ky_509_ = v_key_531_;
v_vy_510_ = v_val_532_;
v_c_511_ = v_rchild_533_;
v_kz_512_ = v_x_489_;
v_vz_513_ = v_x_490_;
v_d_514_ = v_x_491_;
goto v___jp_504_;
}
else
{
v_a_493_ = v_x_488_;
v_kx_494_ = v_x_489_;
v_vx_495_ = v_x_490_;
v_b_496_ = v_x_491_;
goto v___jp_492_;
}
}
else
{
v_a_493_ = v_x_488_;
v_kx_494_ = v_x_489_;
v_vx_495_ = v_x_490_;
v_b_496_ = v_x_491_;
goto v___jp_492_;
}
}
}
else
{
v_a_493_ = v_x_488_;
v_kx_494_ = v_x_489_;
v_vx_495_ = v_x_490_;
v_b_496_ = v_x_491_;
goto v___jp_492_;
}
v___jp_504_:
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = 1;
v___x_516_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_516_, 0, v_a_505_);
lean_ctor_set(v___x_516_, 1, v_kx_506_);
lean_ctor_set(v___x_516_, 2, v_vx_507_);
lean_ctor_set(v___x_516_, 3, v_b_508_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*4, v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_517_, 0, v_c_511_);
lean_ctor_set(v___x_517_, 1, v_kz_512_);
lean_ctor_set(v___x_517_, 2, v_vz_513_);
lean_ctor_set(v___x_517_, 3, v_d_514_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*4, v___x_515_);
v___x_518_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v_ky_509_);
lean_ctor_set(v___x_518_, 2, v_vy_510_);
lean_ctor_set(v___x_518_, 3, v___x_517_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*4, v_color_499_);
return v___x_518_;
}
}
else
{
v_a_493_ = v_x_488_;
v_kx_494_ = v_x_489_;
v_vx_495_ = v_x_490_;
v_b_496_ = v_x_491_;
goto v___jp_492_;
}
v___jp_492_:
{
uint8_t v___x_497_; lean_object* v___x_498_; 
v___x_497_ = 1;
v___x_498_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_498_, 0, v_a_493_);
lean_ctor_set(v___x_498_, 1, v_kx_494_);
lean_ctor_set(v___x_498_, 2, v_vx_495_);
lean_ctor_set(v___x_498_, 3, v_b_496_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*4, v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_a_539_; lean_object* v_kx_540_; lean_object* v_vx_541_; lean_object* v_b_542_; 
if (lean_obj_tag(v_x_537_) == 1)
{
uint8_t v_color_545_; lean_object* v_lchild_546_; lean_object* v_key_547_; lean_object* v_val_548_; lean_object* v_rchild_549_; lean_object* v_a_551_; lean_object* v_kx_552_; lean_object* v_vx_553_; lean_object* v_b_554_; lean_object* v_ky_555_; lean_object* v_vy_556_; lean_object* v_c_557_; lean_object* v_kz_558_; lean_object* v_vz_559_; lean_object* v_d_560_; 
v_color_545_ = lean_ctor_get_uint8(v_x_537_, sizeof(void*)*4);
v_lchild_546_ = lean_ctor_get(v_x_537_, 0);
v_key_547_ = lean_ctor_get(v_x_537_, 1);
v_val_548_ = lean_ctor_get(v_x_537_, 2);
v_rchild_549_ = lean_ctor_get(v_x_537_, 3);
if (v_color_545_ == 0)
{
if (lean_obj_tag(v_lchild_546_) == 1)
{
uint8_t v_color_565_; 
v_color_565_ = lean_ctor_get_uint8(v_lchild_546_, sizeof(void*)*4);
if (v_color_565_ == 0)
{
lean_object* v_lchild_566_; lean_object* v_key_567_; lean_object* v_val_568_; lean_object* v_rchild_569_; 
lean_inc_ref(v_lchild_546_);
lean_inc(v_rchild_549_);
lean_inc(v_val_548_);
lean_inc(v_key_547_);
lean_dec_ref_known(v_x_537_, 4);
v_lchild_566_ = lean_ctor_get(v_lchild_546_, 0);
lean_inc(v_lchild_566_);
v_key_567_ = lean_ctor_get(v_lchild_546_, 1);
lean_inc(v_key_567_);
v_val_568_ = lean_ctor_get(v_lchild_546_, 2);
lean_inc(v_val_568_);
v_rchild_569_ = lean_ctor_get(v_lchild_546_, 3);
lean_inc(v_rchild_569_);
lean_dec_ref_known(v_lchild_546_, 4);
v_a_551_ = v_x_534_;
v_kx_552_ = v_x_535_;
v_vx_553_ = v_x_536_;
v_b_554_ = v_lchild_566_;
v_ky_555_ = v_key_567_;
v_vy_556_ = v_val_568_;
v_c_557_ = v_rchild_569_;
v_kz_558_ = v_key_547_;
v_vz_559_ = v_val_548_;
v_d_560_ = v_rchild_549_;
goto v___jp_550_;
}
else
{
if (lean_obj_tag(v_rchild_549_) == 1)
{
uint8_t v_color_570_; 
v_color_570_ = lean_ctor_get_uint8(v_rchild_549_, sizeof(void*)*4);
if (v_color_570_ == 0)
{
lean_object* v_lchild_571_; lean_object* v_key_572_; lean_object* v_val_573_; lean_object* v_rchild_574_; 
lean_inc_ref(v_rchild_549_);
lean_inc_ref(v_lchild_546_);
lean_inc(v_val_548_);
lean_inc(v_key_547_);
lean_dec_ref_known(v_x_537_, 4);
v_lchild_571_ = lean_ctor_get(v_rchild_549_, 0);
lean_inc(v_lchild_571_);
v_key_572_ = lean_ctor_get(v_rchild_549_, 1);
lean_inc(v_key_572_);
v_val_573_ = lean_ctor_get(v_rchild_549_, 2);
lean_inc(v_val_573_);
v_rchild_574_ = lean_ctor_get(v_rchild_549_, 3);
lean_inc(v_rchild_574_);
lean_dec_ref_known(v_rchild_549_, 4);
v_a_551_ = v_x_534_;
v_kx_552_ = v_x_535_;
v_vx_553_ = v_x_536_;
v_b_554_ = v_lchild_546_;
v_ky_555_ = v_key_547_;
v_vy_556_ = v_val_548_;
v_c_557_ = v_lchild_571_;
v_kz_558_ = v_key_572_;
v_vz_559_ = v_val_573_;
v_d_560_ = v_rchild_574_;
goto v___jp_550_;
}
else
{
v_a_539_ = v_x_534_;
v_kx_540_ = v_x_535_;
v_vx_541_ = v_x_536_;
v_b_542_ = v_x_537_;
goto v___jp_538_;
}
}
else
{
v_a_539_ = v_x_534_;
v_kx_540_ = v_x_535_;
v_vx_541_ = v_x_536_;
v_b_542_ = v_x_537_;
goto v___jp_538_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_549_) == 1)
{
uint8_t v_color_575_; 
v_color_575_ = lean_ctor_get_uint8(v_rchild_549_, sizeof(void*)*4);
if (v_color_575_ == 0)
{
lean_object* v_lchild_576_; lean_object* v_key_577_; lean_object* v_val_578_; lean_object* v_rchild_579_; 
lean_inc_ref(v_rchild_549_);
lean_inc(v_val_548_);
lean_inc(v_key_547_);
lean_inc(v_lchild_546_);
lean_dec_ref_known(v_x_537_, 4);
v_lchild_576_ = lean_ctor_get(v_rchild_549_, 0);
lean_inc(v_lchild_576_);
v_key_577_ = lean_ctor_get(v_rchild_549_, 1);
lean_inc(v_key_577_);
v_val_578_ = lean_ctor_get(v_rchild_549_, 2);
lean_inc(v_val_578_);
v_rchild_579_ = lean_ctor_get(v_rchild_549_, 3);
lean_inc(v_rchild_579_);
lean_dec_ref_known(v_rchild_549_, 4);
v_a_551_ = v_x_534_;
v_kx_552_ = v_x_535_;
v_vx_553_ = v_x_536_;
v_b_554_ = v_lchild_546_;
v_ky_555_ = v_key_547_;
v_vy_556_ = v_val_548_;
v_c_557_ = v_lchild_576_;
v_kz_558_ = v_key_577_;
v_vz_559_ = v_val_578_;
v_d_560_ = v_rchild_579_;
goto v___jp_550_;
}
else
{
v_a_539_ = v_x_534_;
v_kx_540_ = v_x_535_;
v_vx_541_ = v_x_536_;
v_b_542_ = v_x_537_;
goto v___jp_538_;
}
}
else
{
v_a_539_ = v_x_534_;
v_kx_540_ = v_x_535_;
v_vx_541_ = v_x_536_;
v_b_542_ = v_x_537_;
goto v___jp_538_;
}
}
}
else
{
v_a_539_ = v_x_534_;
v_kx_540_ = v_x_535_;
v_vx_541_ = v_x_536_;
v_b_542_ = v_x_537_;
goto v___jp_538_;
}
v___jp_550_:
{
uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = 1;
v___x_562_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_562_, 0, v_a_551_);
lean_ctor_set(v___x_562_, 1, v_kx_552_);
lean_ctor_set(v___x_562_, 2, v_vx_553_);
lean_ctor_set(v___x_562_, 3, v_b_554_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*4, v___x_561_);
v___x_563_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_563_, 0, v_c_557_);
lean_ctor_set(v___x_563_, 1, v_kz_558_);
lean_ctor_set(v___x_563_, 2, v_vz_559_);
lean_ctor_set(v___x_563_, 3, v_d_560_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*4, v___x_561_);
v___x_564_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v_ky_555_);
lean_ctor_set(v___x_564_, 2, v_vy_556_);
lean_ctor_set(v___x_564_, 3, v___x_563_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*4, v_color_545_);
return v___x_564_;
}
}
else
{
v_a_539_ = v_x_534_;
v_kx_540_ = v_x_535_;
v_vx_541_ = v_x_536_;
v_b_542_ = v_x_537_;
goto v___jp_538_;
}
v___jp_538_:
{
uint8_t v___x_543_; lean_object* v___x_544_; 
v___x_543_ = 1;
v___x_544_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_544_, 0, v_a_539_);
lean_ctor_set(v___x_544_, 1, v_kx_540_);
lean_ctor_set(v___x_544_, 2, v_vx_541_);
lean_ctor_set(v___x_544_, 3, v_b_542_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*4, v___x_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b2_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_a_587_; lean_object* v_kx_588_; lean_object* v_vx_589_; lean_object* v_b_590_; 
if (lean_obj_tag(v_x_585_) == 1)
{
uint8_t v_color_593_; lean_object* v_lchild_594_; lean_object* v_key_595_; lean_object* v_val_596_; lean_object* v_rchild_597_; lean_object* v_a_599_; lean_object* v_kx_600_; lean_object* v_vx_601_; lean_object* v_b_602_; lean_object* v_ky_603_; lean_object* v_vy_604_; lean_object* v_c_605_; lean_object* v_kz_606_; lean_object* v_vz_607_; lean_object* v_d_608_; 
v_color_593_ = lean_ctor_get_uint8(v_x_585_, sizeof(void*)*4);
v_lchild_594_ = lean_ctor_get(v_x_585_, 0);
v_key_595_ = lean_ctor_get(v_x_585_, 1);
v_val_596_ = lean_ctor_get(v_x_585_, 2);
v_rchild_597_ = lean_ctor_get(v_x_585_, 3);
if (v_color_593_ == 0)
{
if (lean_obj_tag(v_lchild_594_) == 1)
{
uint8_t v_color_613_; 
v_color_613_ = lean_ctor_get_uint8(v_lchild_594_, sizeof(void*)*4);
if (v_color_613_ == 0)
{
lean_object* v_lchild_614_; lean_object* v_key_615_; lean_object* v_val_616_; lean_object* v_rchild_617_; 
lean_inc_ref(v_lchild_594_);
lean_inc(v_rchild_597_);
lean_inc(v_val_596_);
lean_inc(v_key_595_);
lean_dec_ref_known(v_x_585_, 4);
v_lchild_614_ = lean_ctor_get(v_lchild_594_, 0);
lean_inc(v_lchild_614_);
v_key_615_ = lean_ctor_get(v_lchild_594_, 1);
lean_inc(v_key_615_);
v_val_616_ = lean_ctor_get(v_lchild_594_, 2);
lean_inc(v_val_616_);
v_rchild_617_ = lean_ctor_get(v_lchild_594_, 3);
lean_inc(v_rchild_617_);
lean_dec_ref_known(v_lchild_594_, 4);
v_a_599_ = v_x_582_;
v_kx_600_ = v_x_583_;
v_vx_601_ = v_x_584_;
v_b_602_ = v_lchild_614_;
v_ky_603_ = v_key_615_;
v_vy_604_ = v_val_616_;
v_c_605_ = v_rchild_617_;
v_kz_606_ = v_key_595_;
v_vz_607_ = v_val_596_;
v_d_608_ = v_rchild_597_;
goto v___jp_598_;
}
else
{
if (lean_obj_tag(v_rchild_597_) == 1)
{
uint8_t v_color_618_; 
v_color_618_ = lean_ctor_get_uint8(v_rchild_597_, sizeof(void*)*4);
if (v_color_618_ == 0)
{
lean_object* v_lchild_619_; lean_object* v_key_620_; lean_object* v_val_621_; lean_object* v_rchild_622_; 
lean_inc_ref(v_rchild_597_);
lean_inc_ref(v_lchild_594_);
lean_inc(v_val_596_);
lean_inc(v_key_595_);
lean_dec_ref_known(v_x_585_, 4);
v_lchild_619_ = lean_ctor_get(v_rchild_597_, 0);
lean_inc(v_lchild_619_);
v_key_620_ = lean_ctor_get(v_rchild_597_, 1);
lean_inc(v_key_620_);
v_val_621_ = lean_ctor_get(v_rchild_597_, 2);
lean_inc(v_val_621_);
v_rchild_622_ = lean_ctor_get(v_rchild_597_, 3);
lean_inc(v_rchild_622_);
lean_dec_ref_known(v_rchild_597_, 4);
v_a_599_ = v_x_582_;
v_kx_600_ = v_x_583_;
v_vx_601_ = v_x_584_;
v_b_602_ = v_lchild_594_;
v_ky_603_ = v_key_595_;
v_vy_604_ = v_val_596_;
v_c_605_ = v_lchild_619_;
v_kz_606_ = v_key_620_;
v_vz_607_ = v_val_621_;
v_d_608_ = v_rchild_622_;
goto v___jp_598_;
}
else
{
v_a_587_ = v_x_582_;
v_kx_588_ = v_x_583_;
v_vx_589_ = v_x_584_;
v_b_590_ = v_x_585_;
goto v___jp_586_;
}
}
else
{
v_a_587_ = v_x_582_;
v_kx_588_ = v_x_583_;
v_vx_589_ = v_x_584_;
v_b_590_ = v_x_585_;
goto v___jp_586_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_597_) == 1)
{
uint8_t v_color_623_; 
v_color_623_ = lean_ctor_get_uint8(v_rchild_597_, sizeof(void*)*4);
if (v_color_623_ == 0)
{
lean_object* v_lchild_624_; lean_object* v_key_625_; lean_object* v_val_626_; lean_object* v_rchild_627_; 
lean_inc_ref(v_rchild_597_);
lean_inc(v_val_596_);
lean_inc(v_key_595_);
lean_inc(v_lchild_594_);
lean_dec_ref_known(v_x_585_, 4);
v_lchild_624_ = lean_ctor_get(v_rchild_597_, 0);
lean_inc(v_lchild_624_);
v_key_625_ = lean_ctor_get(v_rchild_597_, 1);
lean_inc(v_key_625_);
v_val_626_ = lean_ctor_get(v_rchild_597_, 2);
lean_inc(v_val_626_);
v_rchild_627_ = lean_ctor_get(v_rchild_597_, 3);
lean_inc(v_rchild_627_);
lean_dec_ref_known(v_rchild_597_, 4);
v_a_599_ = v_x_582_;
v_kx_600_ = v_x_583_;
v_vx_601_ = v_x_584_;
v_b_602_ = v_lchild_594_;
v_ky_603_ = v_key_595_;
v_vy_604_ = v_val_596_;
v_c_605_ = v_lchild_624_;
v_kz_606_ = v_key_625_;
v_vz_607_ = v_val_626_;
v_d_608_ = v_rchild_627_;
goto v___jp_598_;
}
else
{
v_a_587_ = v_x_582_;
v_kx_588_ = v_x_583_;
v_vx_589_ = v_x_584_;
v_b_590_ = v_x_585_;
goto v___jp_586_;
}
}
else
{
v_a_587_ = v_x_582_;
v_kx_588_ = v_x_583_;
v_vx_589_ = v_x_584_;
v_b_590_ = v_x_585_;
goto v___jp_586_;
}
}
}
else
{
v_a_587_ = v_x_582_;
v_kx_588_ = v_x_583_;
v_vx_589_ = v_x_584_;
v_b_590_ = v_x_585_;
goto v___jp_586_;
}
v___jp_598_:
{
uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = 1;
v___x_610_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_610_, 0, v_a_599_);
lean_ctor_set(v___x_610_, 1, v_kx_600_);
lean_ctor_set(v___x_610_, 2, v_vx_601_);
lean_ctor_set(v___x_610_, 3, v_b_602_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*4, v___x_609_);
v___x_611_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_611_, 0, v_c_605_);
lean_ctor_set(v___x_611_, 1, v_kz_606_);
lean_ctor_set(v___x_611_, 2, v_vz_607_);
lean_ctor_set(v___x_611_, 3, v_d_608_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*4, v___x_609_);
v___x_612_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v_ky_603_);
lean_ctor_set(v___x_612_, 2, v_vy_604_);
lean_ctor_set(v___x_612_, 3, v___x_611_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*4, v_color_593_);
return v___x_612_;
}
}
else
{
v_a_587_ = v_x_582_;
v_kx_588_ = v_x_583_;
v_vx_589_ = v_x_584_;
v_b_590_ = v_x_585_;
goto v___jp_586_;
}
v___jp_586_:
{
uint8_t v___x_591_; lean_object* v___x_592_; 
v___x_591_ = 1;
v___x_592_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_592_, 0, v_a_587_);
lean_ctor_set(v___x_592_, 1, v_kx_588_);
lean_ctor_set(v___x_592_, 2, v_vx_589_);
lean_ctor_set(v___x_592_, 3, v_b_590_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*4, v___x_591_);
return v___x_592_;
}
}
}
uint8_t l_Lean_RBNode_isRed___redArg(lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 1)
{
uint8_t v_color_629_; 
v_color_629_ = lean_ctor_get_uint8(v_x_628_, sizeof(void*)*4);
if (v_color_629_ == 0)
{
uint8_t v___x_630_; 
v___x_630_ = 1;
return v___x_630_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
else
{
uint8_t v___x_632_; 
v___x_632_ = 0;
return v___x_632_;
}
}
}
LEAN_EXPORT void l_Lean_RBNode_isRed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_628_ = stack[0].m_obj;
uint8_t v_res_633_;
v_res_633_ = l_Lean_RBNode_isRed___redArg(v_x_628_);
stack->m_num = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Lean_RBNode_isRed___redArg(v_x_634_);
lean_dec(v_x_634_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
uint8_t l_Lean_RBNode_isRed(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_x_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_RBNode_isRed___redArg(v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT void l_Lean_RBNode_isRed_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_639_ = stack[2].m_obj;
uint8_t v_res_641_;
v_res_641_ = l_Lean_RBNode_isRed(lean_box(0), lean_box(0), v_x_639_);
stack->m_num = v_res_641_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_x_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Lean_RBNode_isRed(v_00_u03b1_642_, v_00_u03b2_643_, v_x_644_);
lean_dec(v_x_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_647_) == 1)
{
uint8_t v_color_648_; 
v_color_648_ = lean_ctor_get_uint8(v_x_647_, sizeof(void*)*4);
if (v_color_648_ == 1)
{
uint8_t v___x_649_; 
v___x_649_ = 1;
return v___x_649_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = 0;
return v___x_650_;
}
}
else
{
uint8_t v___x_651_; 
v___x_651_ = 0;
return v___x_651_;
}
}
}
LEAN_EXPORT void l_Lean_RBNode_isBlack___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_647_ = stack[0].m_obj;
uint8_t v_res_652_;
v_res_652_ = l_Lean_RBNode_isBlack___redArg(v_x_647_);
stack->m_num = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object* v_x_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lean_RBNode_isBlack___redArg(v_x_653_);
lean_dec(v_x_653_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
uint8_t l_Lean_RBNode_isBlack(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_x_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = l_Lean_RBNode_isBlack___redArg(v_x_658_);
return v___x_659_;
}
}
LEAN_EXPORT void l_Lean_RBNode_isBlack_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_658_ = stack[2].m_obj;
uint8_t v_res_660_;
v_res_660_ = l_Lean_RBNode_isBlack(lean_box(0), lean_box(0), v_x_658_);
stack->m_num = v_res_660_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_x_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Lean_RBNode_isBlack(v_00_u03b1_661_, v_00_u03b2_662_, v_x_663_);
lean_dec(v_x_663_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object* v_cmp_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
uint8_t v___x_670_; lean_object* v___x_671_; 
lean_dec_ref(v_cmp_666_);
v___x_670_ = 0;
v___x_671_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_671_, 0, v_x_667_);
lean_ctor_set(v___x_671_, 1, v_x_668_);
lean_ctor_set(v___x_671_, 2, v_x_669_);
lean_ctor_set(v___x_671_, 3, v_x_667_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*4, v___x_670_);
return v___x_671_;
}
else
{
uint8_t v_color_672_; 
v_color_672_ = lean_ctor_get_uint8(v_x_667_, sizeof(void*)*4);
if (v_color_672_ == 0)
{
lean_object* v_lchild_673_; lean_object* v_key_674_; lean_object* v_val_675_; lean_object* v_rchild_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_693_; 
v_lchild_673_ = lean_ctor_get(v_x_667_, 0);
v_key_674_ = lean_ctor_get(v_x_667_, 1);
v_val_675_ = lean_ctor_get(v_x_667_, 2);
v_rchild_676_ = lean_ctor_get(v_x_667_, 3);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_693_ == 0)
{
v___x_678_ = v_x_667_;
v_isShared_679_ = v_isSharedCheck_693_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_rchild_676_);
lean_inc(v_val_675_);
lean_inc(v_key_674_);
lean_inc(v_lchild_673_);
lean_dec(v_x_667_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_693_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
lean_inc_ref(v_cmp_666_);
lean_inc(v_key_674_);
lean_inc(v_x_668_);
v___x_680_ = lean_apply_2(v_cmp_666_, v_x_668_, v_key_674_);
v___x_681_ = lean_unbox(v___x_680_);
switch(v___x_681_)
{
case 0:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = l_Lean_RBNode_ins___redArg(v_cmp_666_, v_lchild_673_, v_x_668_, v_x_669_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_682_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_key_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_val_675_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_rchild_676_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*4, v_color_672_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
case 1:
{
lean_object* v___x_687_; 
lean_dec(v_val_675_);
lean_dec(v_key_674_);
lean_dec_ref(v_cmp_666_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 2, v_x_669_);
lean_ctor_set(v___x_678_, 1, v_x_668_);
v___x_687_ = v___x_678_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_lchild_673_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_x_668_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_x_669_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_rchild_676_);
lean_ctor_set_uint8(v_reuseFailAlloc_688_, sizeof(void*)*4, v_color_672_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
default: 
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = l_Lean_RBNode_ins___redArg(v_cmp_666_, v_rchild_676_, v_x_668_, v_x_669_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 3, v___x_689_);
v___x_691_ = v___x_678_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_lchild_673_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_key_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_val_675_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v___x_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*4, v_color_672_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_object* v_lchild_694_; lean_object* v_key_695_; lean_object* v_val_696_; lean_object* v_rchild_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_856_; 
v_lchild_694_ = lean_ctor_get(v_x_667_, 0);
v_key_695_ = lean_ctor_get(v_x_667_, 1);
v_val_696_ = lean_ctor_get(v_x_667_, 2);
v_rchild_697_ = lean_ctor_get(v_x_667_, 3);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_856_ == 0)
{
v___x_699_ = v_x_667_;
v_isShared_700_ = v_isSharedCheck_856_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_rchild_697_);
lean_inc(v_val_696_);
lean_inc(v_key_695_);
lean_inc(v_lchild_694_);
lean_dec(v_x_667_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_856_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
lean_inc_ref(v_cmp_666_);
lean_inc(v_key_695_);
lean_inc(v_x_668_);
v___x_701_ = lean_apply_2(v_cmp_666_, v_x_668_, v_key_695_);
v___x_702_ = lean_unbox(v___x_701_);
switch(v___x_702_)
{
case 0:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_RBNode_ins___redArg(v_cmp_666_, v_lchild_694_, v_x_668_, v_x_669_);
if (lean_obj_tag(v___x_703_) == 1)
{
uint8_t v_color_704_; lean_object* v_lchild_705_; lean_object* v_key_706_; lean_object* v_val_707_; lean_object* v_rchild_708_; lean_object* v_a_710_; lean_object* v_kx_711_; lean_object* v_vx_712_; lean_object* v_b_713_; lean_object* v_ky_714_; lean_object* v_vy_715_; lean_object* v_c_716_; lean_object* v_kz_717_; lean_object* v_vz_718_; lean_object* v_d_719_; 
v_color_704_ = lean_ctor_get_uint8(v___x_703_, sizeof(void*)*4);
v_lchild_705_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_lchild_705_);
v_key_706_ = lean_ctor_get(v___x_703_, 1);
v_val_707_ = lean_ctor_get(v___x_703_, 2);
v_rchild_708_ = lean_ctor_get(v___x_703_, 3);
lean_inc(v_rchild_708_);
if (v_color_704_ == 0)
{
if (lean_obj_tag(v_lchild_705_) == 1)
{
uint8_t v_color_725_; 
v_color_725_ = lean_ctor_get_uint8(v_lchild_705_, sizeof(void*)*4);
if (v_color_725_ == 0)
{
lean_object* v_lchild_726_; lean_object* v_key_727_; lean_object* v_val_728_; lean_object* v_rchild_729_; 
lean_inc(v_val_707_);
lean_inc(v_key_706_);
lean_dec_ref_known(v___x_703_, 4);
v_lchild_726_ = lean_ctor_get(v_lchild_705_, 0);
lean_inc(v_lchild_726_);
v_key_727_ = lean_ctor_get(v_lchild_705_, 1);
lean_inc(v_key_727_);
v_val_728_ = lean_ctor_get(v_lchild_705_, 2);
lean_inc(v_val_728_);
v_rchild_729_ = lean_ctor_get(v_lchild_705_, 3);
lean_inc(v_rchild_729_);
lean_dec_ref_known(v_lchild_705_, 4);
v_a_710_ = v_lchild_726_;
v_kx_711_ = v_key_727_;
v_vx_712_ = v_val_728_;
v_b_713_ = v_rchild_729_;
v_ky_714_ = v_key_706_;
v_vy_715_ = v_val_707_;
v_c_716_ = v_rchild_708_;
v_kz_717_ = v_key_695_;
v_vz_718_ = v_val_696_;
v_d_719_ = v_rchild_697_;
goto v___jp_709_;
}
else
{
if (lean_obj_tag(v_rchild_708_) == 1)
{
uint8_t v_color_730_; 
v_color_730_ = lean_ctor_get_uint8(v_rchild_708_, sizeof(void*)*4);
if (v_color_730_ == 0)
{
lean_object* v_lchild_731_; lean_object* v_key_732_; lean_object* v_val_733_; lean_object* v_rchild_734_; 
lean_inc(v_val_707_);
lean_inc(v_key_706_);
lean_dec_ref_known(v___x_703_, 4);
v_lchild_731_ = lean_ctor_get(v_rchild_708_, 0);
lean_inc(v_lchild_731_);
v_key_732_ = lean_ctor_get(v_rchild_708_, 1);
lean_inc(v_key_732_);
v_val_733_ = lean_ctor_get(v_rchild_708_, 2);
lean_inc(v_val_733_);
v_rchild_734_ = lean_ctor_get(v_rchild_708_, 3);
lean_inc(v_rchild_734_);
lean_dec_ref_known(v_rchild_708_, 4);
v_a_710_ = v_lchild_705_;
v_kx_711_ = v_key_706_;
v_vx_712_ = v_val_707_;
v_b_713_ = v_lchild_731_;
v_ky_714_ = v_key_732_;
v_vy_715_ = v_val_733_;
v_c_716_ = v_rchild_734_;
v_kz_717_ = v_key_695_;
v_vz_718_ = v_val_696_;
v_d_719_ = v_rchild_697_;
goto v___jp_709_;
}
else
{
lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec_ref_known(v_lchild_705_, 4);
lean_del_object(v___x_699_);
v_isSharedCheck_741_ = !lean_is_exclusive(v_rchild_708_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; 
v_unused_742_ = lean_ctor_get(v_rchild_708_, 3);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_rchild_708_, 2);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_rchild_708_, 1);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_rchild_708_, 0);
lean_dec(v_unused_745_);
v___x_736_ = v_rchild_708_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_dec(v_rchild_708_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 3, v_rchild_697_);
lean_ctor_set(v___x_736_, 2, v_val_696_);
lean_ctor_set(v___x_736_, 1, v_key_695_);
lean_ctor_set(v___x_736_, 0, v___x_703_);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_rchild_697_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*4, v_color_672_);
return v___x_739_;
}
}
}
}
else
{
lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_rchild_708_);
lean_del_object(v___x_699_);
v_isSharedCheck_752_ = !lean_is_exclusive(v_lchild_705_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; lean_object* v_unused_755_; lean_object* v_unused_756_; 
v_unused_753_ = lean_ctor_get(v_lchild_705_, 3);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_lchild_705_, 2);
lean_dec(v_unused_754_);
v_unused_755_ = lean_ctor_get(v_lchild_705_, 1);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_lchild_705_, 0);
lean_dec(v_unused_756_);
v___x_747_ = v_lchild_705_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_dec(v_lchild_705_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 3, v_rchild_697_);
lean_ctor_set(v___x_747_, 2, v_val_696_);
lean_ctor_set(v___x_747_, 1, v_key_695_);
lean_ctor_set(v___x_747_, 0, v___x_703_);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_rchild_697_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*4, v_color_672_);
return v___x_750_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_708_) == 1)
{
uint8_t v_color_757_; 
v_color_757_ = lean_ctor_get_uint8(v_rchild_708_, sizeof(void*)*4);
if (v_color_757_ == 0)
{
lean_object* v_lchild_758_; lean_object* v_key_759_; lean_object* v_val_760_; lean_object* v_rchild_761_; 
lean_inc(v_val_707_);
lean_inc(v_key_706_);
lean_dec_ref_known(v___x_703_, 4);
v_lchild_758_ = lean_ctor_get(v_rchild_708_, 0);
lean_inc(v_lchild_758_);
v_key_759_ = lean_ctor_get(v_rchild_708_, 1);
lean_inc(v_key_759_);
v_val_760_ = lean_ctor_get(v_rchild_708_, 2);
lean_inc(v_val_760_);
v_rchild_761_ = lean_ctor_get(v_rchild_708_, 3);
lean_inc(v_rchild_761_);
lean_dec_ref_known(v_rchild_708_, 4);
v_a_710_ = v_lchild_705_;
v_kx_711_ = v_key_706_;
v_vx_712_ = v_val_707_;
v_b_713_ = v_lchild_758_;
v_ky_714_ = v_key_759_;
v_vy_715_ = v_val_760_;
v_c_716_ = v_rchild_761_;
v_kz_717_ = v_key_695_;
v_vz_718_ = v_val_696_;
v_d_719_ = v_rchild_697_;
goto v___jp_709_;
}
else
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_lchild_705_);
lean_del_object(v___x_699_);
v_isSharedCheck_768_ = !lean_is_exclusive(v_rchild_708_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; lean_object* v_unused_772_; 
v_unused_769_ = lean_ctor_get(v_rchild_708_, 3);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_rchild_708_, 2);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_rchild_708_, 1);
lean_dec(v_unused_771_);
v_unused_772_ = lean_ctor_get(v_rchild_708_, 0);
lean_dec(v_unused_772_);
v___x_763_ = v_rchild_708_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_rchild_708_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 3, v_rchild_697_);
lean_ctor_set(v___x_763_, 2, v_val_696_);
lean_ctor_set(v___x_763_, 1, v_key_695_);
lean_ctor_set(v___x_763_, 0, v___x_703_);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_rchild_697_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*4, v_color_672_);
return v___x_766_;
}
}
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_rchild_708_);
lean_dec(v_lchild_705_);
lean_del_object(v___x_699_);
v___x_773_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_773_, 0, v___x_703_);
lean_ctor_set(v___x_773_, 1, v_key_695_);
lean_ctor_set(v___x_773_, 2, v_val_696_);
lean_ctor_set(v___x_773_, 3, v_rchild_697_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*4, v_color_672_);
return v___x_773_;
}
}
}
else
{
lean_object* v___x_774_; 
lean_dec(v_rchild_708_);
lean_dec(v_lchild_705_);
lean_del_object(v___x_699_);
v___x_774_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_774_, 0, v___x_703_);
lean_ctor_set(v___x_774_, 1, v_key_695_);
lean_ctor_set(v___x_774_, 2, v_val_696_);
lean_ctor_set(v___x_774_, 3, v_rchild_697_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*4, v_color_672_);
return v___x_774_;
}
v___jp_709_:
{
lean_object* v___x_721_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 3, v_b_713_);
lean_ctor_set(v___x_699_, 2, v_vx_712_);
lean_ctor_set(v___x_699_, 1, v_kx_711_);
lean_ctor_set(v___x_699_, 0, v_a_710_);
v___x_721_ = v___x_699_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_710_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_kx_711_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_vx_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_b_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_724_, sizeof(void*)*4, v_color_672_);
v___x_721_ = v_reuseFailAlloc_724_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_722_, 0, v_c_716_);
lean_ctor_set(v___x_722_, 1, v_kz_717_);
lean_ctor_set(v___x_722_, 2, v_vz_718_);
lean_ctor_set(v___x_722_, 3, v_d_719_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*4, v_color_672_);
v___x_723_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v_ky_714_);
lean_ctor_set(v___x_723_, 2, v_vy_715_);
lean_ctor_set(v___x_723_, 3, v___x_722_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*4, v_color_704_);
return v___x_723_;
}
}
}
else
{
lean_object* v___x_776_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_703_);
v___x_776_ = v___x_699_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_rchild_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*4, v_color_672_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
case 1:
{
lean_object* v___x_779_; 
lean_dec(v_val_696_);
lean_dec(v_key_695_);
lean_dec_ref(v_cmp_666_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 2, v_x_669_);
lean_ctor_set(v___x_699_, 1, v_x_668_);
v___x_779_ = v___x_699_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_lchild_694_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_x_668_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_x_669_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_rchild_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_780_, sizeof(void*)*4, v_color_672_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
default: 
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_RBNode_ins___redArg(v_cmp_666_, v_rchild_697_, v_x_668_, v_x_669_);
if (lean_obj_tag(v___x_781_) == 1)
{
uint8_t v_color_782_; lean_object* v_lchild_783_; lean_object* v_key_784_; lean_object* v_val_785_; lean_object* v_rchild_786_; lean_object* v_a_788_; lean_object* v_kx_789_; lean_object* v_vx_790_; lean_object* v_b_791_; lean_object* v_ky_792_; lean_object* v_vy_793_; lean_object* v_c_794_; lean_object* v_kz_795_; lean_object* v_vz_796_; lean_object* v_d_797_; 
v_color_782_ = lean_ctor_get_uint8(v___x_781_, sizeof(void*)*4);
v_lchild_783_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_lchild_783_);
v_key_784_ = lean_ctor_get(v___x_781_, 1);
v_val_785_ = lean_ctor_get(v___x_781_, 2);
v_rchild_786_ = lean_ctor_get(v___x_781_, 3);
lean_inc(v_rchild_786_);
if (v_color_782_ == 0)
{
if (lean_obj_tag(v_lchild_783_) == 1)
{
uint8_t v_color_803_; 
v_color_803_ = lean_ctor_get_uint8(v_lchild_783_, sizeof(void*)*4);
if (v_color_803_ == 0)
{
lean_object* v_lchild_804_; lean_object* v_key_805_; lean_object* v_val_806_; lean_object* v_rchild_807_; 
lean_inc(v_val_785_);
lean_inc(v_key_784_);
lean_dec_ref_known(v___x_781_, 4);
v_lchild_804_ = lean_ctor_get(v_lchild_783_, 0);
lean_inc(v_lchild_804_);
v_key_805_ = lean_ctor_get(v_lchild_783_, 1);
lean_inc(v_key_805_);
v_val_806_ = lean_ctor_get(v_lchild_783_, 2);
lean_inc(v_val_806_);
v_rchild_807_ = lean_ctor_get(v_lchild_783_, 3);
lean_inc(v_rchild_807_);
lean_dec_ref_known(v_lchild_783_, 4);
v_a_788_ = v_lchild_694_;
v_kx_789_ = v_key_695_;
v_vx_790_ = v_val_696_;
v_b_791_ = v_lchild_804_;
v_ky_792_ = v_key_805_;
v_vy_793_ = v_val_806_;
v_c_794_ = v_rchild_807_;
v_kz_795_ = v_key_784_;
v_vz_796_ = v_val_785_;
v_d_797_ = v_rchild_786_;
goto v___jp_787_;
}
else
{
if (lean_obj_tag(v_rchild_786_) == 1)
{
uint8_t v_color_808_; 
v_color_808_ = lean_ctor_get_uint8(v_rchild_786_, sizeof(void*)*4);
if (v_color_808_ == 0)
{
lean_object* v_lchild_809_; lean_object* v_key_810_; lean_object* v_val_811_; lean_object* v_rchild_812_; 
lean_inc(v_val_785_);
lean_inc(v_key_784_);
lean_dec_ref_known(v___x_781_, 4);
v_lchild_809_ = lean_ctor_get(v_rchild_786_, 0);
lean_inc(v_lchild_809_);
v_key_810_ = lean_ctor_get(v_rchild_786_, 1);
lean_inc(v_key_810_);
v_val_811_ = lean_ctor_get(v_rchild_786_, 2);
lean_inc(v_val_811_);
v_rchild_812_ = lean_ctor_get(v_rchild_786_, 3);
lean_inc(v_rchild_812_);
lean_dec_ref_known(v_rchild_786_, 4);
v_a_788_ = v_lchild_694_;
v_kx_789_ = v_key_695_;
v_vx_790_ = v_val_696_;
v_b_791_ = v_lchild_783_;
v_ky_792_ = v_key_784_;
v_vy_793_ = v_val_785_;
v_c_794_ = v_lchild_809_;
v_kz_795_ = v_key_810_;
v_vz_796_ = v_val_811_;
v_d_797_ = v_rchild_812_;
goto v___jp_787_;
}
else
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref_known(v_lchild_783_, 4);
lean_del_object(v___x_699_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_rchild_786_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_820_ = lean_ctor_get(v_rchild_786_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_rchild_786_, 2);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_rchild_786_, 1);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_rchild_786_, 0);
lean_dec(v_unused_823_);
v___x_814_ = v_rchild_786_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_dec(v_rchild_786_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 3, v___x_781_);
lean_ctor_set(v___x_814_, 2, v_val_696_);
lean_ctor_set(v___x_814_, 1, v_key_695_);
lean_ctor_set(v___x_814_, 0, v_lchild_694_);
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_lchild_694_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___x_781_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*4, v_color_672_);
return v___x_817_;
}
}
}
}
else
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_rchild_786_);
lean_del_object(v___x_699_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_lchild_783_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; 
v_unused_831_ = lean_ctor_get(v_lchild_783_, 3);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_lchild_783_, 2);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_lchild_783_, 1);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_lchild_783_, 0);
lean_dec(v_unused_834_);
v___x_825_ = v_lchild_783_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_lchild_783_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 3, v___x_781_);
lean_ctor_set(v___x_825_, 2, v_val_696_);
lean_ctor_set(v___x_825_, 1, v_key_695_);
lean_ctor_set(v___x_825_, 0, v_lchild_694_);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_lchild_694_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v___x_781_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*4, v_color_672_);
return v___x_828_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_786_) == 1)
{
uint8_t v_color_835_; 
v_color_835_ = lean_ctor_get_uint8(v_rchild_786_, sizeof(void*)*4);
if (v_color_835_ == 0)
{
lean_object* v_lchild_836_; lean_object* v_key_837_; lean_object* v_val_838_; lean_object* v_rchild_839_; 
lean_inc(v_val_785_);
lean_inc(v_key_784_);
lean_dec_ref_known(v___x_781_, 4);
v_lchild_836_ = lean_ctor_get(v_rchild_786_, 0);
lean_inc(v_lchild_836_);
v_key_837_ = lean_ctor_get(v_rchild_786_, 1);
lean_inc(v_key_837_);
v_val_838_ = lean_ctor_get(v_rchild_786_, 2);
lean_inc(v_val_838_);
v_rchild_839_ = lean_ctor_get(v_rchild_786_, 3);
lean_inc(v_rchild_839_);
lean_dec_ref_known(v_rchild_786_, 4);
v_a_788_ = v_lchild_694_;
v_kx_789_ = v_key_695_;
v_vx_790_ = v_val_696_;
v_b_791_ = v_lchild_783_;
v_ky_792_ = v_key_784_;
v_vy_793_ = v_val_785_;
v_c_794_ = v_lchild_836_;
v_kz_795_ = v_key_837_;
v_vz_796_ = v_val_838_;
v_d_797_ = v_rchild_839_;
goto v___jp_787_;
}
else
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_lchild_783_);
lean_del_object(v___x_699_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_rchild_786_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_847_ = lean_ctor_get(v_rchild_786_, 3);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_rchild_786_, 2);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_rchild_786_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_rchild_786_, 0);
lean_dec(v_unused_850_);
v___x_841_ = v_rchild_786_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_rchild_786_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 3, v___x_781_);
lean_ctor_set(v___x_841_, 2, v_val_696_);
lean_ctor_set(v___x_841_, 1, v_key_695_);
lean_ctor_set(v___x_841_, 0, v_lchild_694_);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_lchild_694_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v___x_781_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*4, v_color_672_);
return v___x_844_;
}
}
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v_rchild_786_);
lean_dec(v_lchild_783_);
lean_del_object(v___x_699_);
v___x_851_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_851_, 0, v_lchild_694_);
lean_ctor_set(v___x_851_, 1, v_key_695_);
lean_ctor_set(v___x_851_, 2, v_val_696_);
lean_ctor_set(v___x_851_, 3, v___x_781_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*4, v_color_672_);
return v___x_851_;
}
}
}
else
{
lean_object* v___x_852_; 
lean_dec(v_rchild_786_);
lean_dec(v_lchild_783_);
lean_del_object(v___x_699_);
v___x_852_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_852_, 0, v_lchild_694_);
lean_ctor_set(v___x_852_, 1, v_key_695_);
lean_ctor_set(v___x_852_, 2, v_val_696_);
lean_ctor_set(v___x_852_, 3, v___x_781_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*4, v_color_672_);
return v___x_852_;
}
v___jp_787_:
{
lean_object* v___x_799_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 3, v_b_791_);
lean_ctor_set(v___x_699_, 2, v_vx_790_);
lean_ctor_set(v___x_699_, 1, v_kx_789_);
lean_ctor_set(v___x_699_, 0, v_a_788_);
v___x_799_ = v___x_699_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_788_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_kx_789_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_vx_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_b_791_);
lean_ctor_set_uint8(v_reuseFailAlloc_802_, sizeof(void*)*4, v_color_672_);
v___x_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_800_, 0, v_c_794_);
lean_ctor_set(v___x_800_, 1, v_kz_795_);
lean_ctor_set(v___x_800_, 2, v_vz_796_);
lean_ctor_set(v___x_800_, 3, v_d_797_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*4, v_color_672_);
v___x_801_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v_ky_792_);
lean_ctor_set(v___x_801_, 2, v_vy_793_);
lean_ctor_set(v___x_801_, 3, v___x_800_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*4, v_color_782_);
return v___x_801_;
}
}
}
else
{
lean_object* v___x_854_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 3, v___x_781_);
v___x_854_ = v___x_699_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_lchild_694_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_key_695_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_val_696_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v___x_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*4, v_color_672_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_cmp_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_RBNode_ins___redArg(v_cmp_859_, v_x_860_, v_x_861_, v_x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 1)
{
lean_object* v_lchild_865_; lean_object* v_key_866_; lean_object* v_val_867_; lean_object* v_rchild_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_lchild_865_ = lean_ctor_get(v_x_864_, 0);
v_key_866_ = lean_ctor_get(v_x_864_, 1);
v_val_867_ = lean_ctor_get(v_x_864_, 2);
v_rchild_868_ = lean_ctor_get(v_x_864_, 3);
v_isSharedCheck_876_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v_x_864_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_rchild_868_);
lean_inc(v_val_867_);
lean_inc(v_key_866_);
lean_inc(v_lchild_865_);
lean_dec(v_x_864_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; lean_object* v___x_874_; 
v___x_872_ = 1;
if (v_isShared_871_ == 0)
{
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_lchild_865_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_key_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_val_867_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_rchild_868_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*4, v___x_872_);
return v___x_874_;
}
}
}
else
{
return v_x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v_x_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_RBNode_setBlack___redArg(v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object* v_cmp_881_, lean_object* v_t_882_, lean_object* v_k_883_, lean_object* v_v_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_RBNode_isRed___redArg(v_t_882_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_RBNode_ins___redArg(v_cmp_881_, v_t_882_, v_k_883_, v_v_884_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Lean_RBNode_ins___redArg(v_cmp_881_, v_t_882_, v_k_883_, v_v_884_);
v___x_888_ = l_Lean_RBNode_setBlack___redArg(v___x_887_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_cmp_891_, lean_object* v_t_892_, lean_object* v_k_893_, lean_object* v_v_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_RBNode_insert___redArg(v_cmp_891_, v_t_892_, v_k_893_, v_v_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_896_) == 1)
{
lean_object* v_lchild_897_; lean_object* v_key_898_; lean_object* v_val_899_; lean_object* v_rchild_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_908_; 
v_lchild_897_ = lean_ctor_get(v_x_896_, 0);
v_key_898_ = lean_ctor_get(v_x_896_, 1);
v_val_899_ = lean_ctor_get(v_x_896_, 2);
v_rchild_900_ = lean_ctor_get(v_x_896_, 3);
v_isSharedCheck_908_ = !lean_is_exclusive(v_x_896_);
if (v_isSharedCheck_908_ == 0)
{
v___x_902_ = v_x_896_;
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_rchild_900_);
lean_inc(v_val_899_);
lean_inc(v_key_898_);
lean_inc(v_lchild_897_);
lean_dec(v_x_896_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v___x_904_; lean_object* v___x_906_; 
v___x_904_ = 0;
if (v_isShared_903_ == 0)
{
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_lchild_897_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_key_898_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_val_899_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_rchild_900_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*4, v___x_904_);
return v___x_906_;
}
}
}
else
{
return v_x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_RBNode_setRed___redArg(v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_a_918_; lean_object* v_kx_919_; lean_object* v_vx_920_; lean_object* v_b_921_; lean_object* v_a_925_; lean_object* v_kx_926_; lean_object* v_vx_927_; lean_object* v_b_928_; lean_object* v_ky_929_; lean_object* v_vy_930_; lean_object* v_c_931_; lean_object* v_kz_932_; lean_object* v_vz_933_; lean_object* v_d_934_; lean_object* v_l_941_; lean_object* v_k_942_; lean_object* v_v_943_; lean_object* v_a_944_; lean_object* v_ky_945_; lean_object* v_vy_946_; lean_object* v_b_947_; uint8_t v___y_966_; lean_object* v___y_967_; uint8_t v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v_a_971_; lean_object* v_kx_972_; lean_object* v_vx_973_; lean_object* v_b_974_; lean_object* v_ky_975_; lean_object* v_vy_976_; lean_object* v_c_977_; lean_object* v_kz_978_; lean_object* v_vz_979_; lean_object* v_d_980_; uint8_t v___y_986_; lean_object* v___y_987_; uint8_t v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v_a_991_; lean_object* v_kx_992_; lean_object* v_vx_993_; lean_object* v_b_994_; lean_object* v_l_998_; lean_object* v_k_999_; lean_object* v_v_1000_; lean_object* v_a_1001_; lean_object* v_ky_1002_; lean_object* v_vy_1003_; lean_object* v_b_1004_; lean_object* v_kz_1005_; lean_object* v_vz_1006_; lean_object* v_c_1007_; lean_object* v_l_1039_; lean_object* v_k_1040_; lean_object* v_v_1041_; lean_object* v_r_1042_; 
if (lean_obj_tag(v_x_913_) == 1)
{
uint8_t v_color_1045_; 
v_color_1045_ = lean_ctor_get_uint8(v_x_913_, sizeof(void*)*4);
if (v_color_1045_ == 0)
{
lean_object* v_lchild_1046_; lean_object* v_key_1047_; lean_object* v_val_1048_; lean_object* v_rchild_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
v_lchild_1046_ = lean_ctor_get(v_x_913_, 0);
v_key_1047_ = lean_ctor_get(v_x_913_, 1);
v_val_1048_ = lean_ctor_get(v_x_913_, 2);
v_rchild_1049_ = lean_ctor_get(v_x_913_, 3);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_913_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1051_ = v_x_913_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_rchild_1049_);
lean_inc(v_val_1048_);
lean_inc(v_key_1047_);
lean_inc(v_lchild_1046_);
lean_dec(v_x_913_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
uint8_t v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = 1;
if (v_isShared_1052_ == 0)
{
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_lchild_1046_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_key_1047_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_val_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_rchild_1049_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*4, v___x_1053_);
v___x_1056_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_x_914_);
lean_ctor_set(v___x_1056_, 2, v_x_915_);
lean_ctor_set(v___x_1056_, 3, v_x_916_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*4, v_color_1045_);
return v___x_1056_;
}
}
}
else
{
if (lean_obj_tag(v_x_916_) == 1)
{
uint8_t v_color_1059_; 
v_color_1059_ = lean_ctor_get_uint8(v_x_916_, sizeof(void*)*4);
if (v_color_1059_ == 0)
{
lean_object* v_lchild_1060_; 
v_lchild_1060_ = lean_ctor_get(v_x_916_, 0);
if (lean_obj_tag(v_lchild_1060_) == 1)
{
uint8_t v_color_1061_; 
v_color_1061_ = lean_ctor_get_uint8(v_lchild_1060_, sizeof(void*)*4);
if (v_color_1061_ == 1)
{
lean_object* v_key_1062_; lean_object* v_val_1063_; lean_object* v_rchild_1064_; lean_object* v_lchild_1065_; lean_object* v_key_1066_; lean_object* v_val_1067_; lean_object* v_rchild_1068_; 
lean_inc_ref(v_lchild_1060_);
v_key_1062_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_key_1062_);
v_val_1063_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_val_1063_);
v_rchild_1064_ = lean_ctor_get(v_x_916_, 3);
lean_inc(v_rchild_1064_);
lean_dec_ref_known(v_x_916_, 4);
v_lchild_1065_ = lean_ctor_get(v_lchild_1060_, 0);
lean_inc(v_lchild_1065_);
v_key_1066_ = lean_ctor_get(v_lchild_1060_, 1);
lean_inc(v_key_1066_);
v_val_1067_ = lean_ctor_get(v_lchild_1060_, 2);
lean_inc(v_val_1067_);
v_rchild_1068_ = lean_ctor_get(v_lchild_1060_, 3);
lean_inc(v_rchild_1068_);
lean_dec_ref_known(v_lchild_1060_, 4);
v_l_998_ = v_x_913_;
v_k_999_ = v_x_914_;
v_v_1000_ = v_x_915_;
v_a_1001_ = v_lchild_1065_;
v_ky_1002_ = v_key_1066_;
v_vy_1003_ = v_val_1067_;
v_b_1004_ = v_rchild_1068_;
v_kz_1005_ = v_key_1062_;
v_vz_1006_ = v_val_1063_;
v_c_1007_ = v_rchild_1064_;
goto v___jp_997_;
}
else
{
v_l_1039_ = v_x_913_;
v_k_1040_ = v_x_914_;
v_v_1041_ = v_x_915_;
v_r_1042_ = v_x_916_;
goto v___jp_1038_;
}
}
else
{
v_l_1039_ = v_x_913_;
v_k_1040_ = v_x_914_;
v_v_1041_ = v_x_915_;
v_r_1042_ = v_x_916_;
goto v___jp_1038_;
}
}
else
{
lean_object* v_lchild_1069_; lean_object* v_key_1070_; lean_object* v_val_1071_; lean_object* v_rchild_1072_; 
v_lchild_1069_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_lchild_1069_);
v_key_1070_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_key_1070_);
v_val_1071_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_val_1071_);
v_rchild_1072_ = lean_ctor_get(v_x_916_, 3);
lean_inc(v_rchild_1072_);
lean_dec_ref_known(v_x_916_, 4);
v_l_941_ = v_x_913_;
v_k_942_ = v_x_914_;
v_v_943_ = v_x_915_;
v_a_944_ = v_lchild_1069_;
v_ky_945_ = v_key_1070_;
v_vy_946_ = v_val_1071_;
v_b_947_ = v_rchild_1072_;
goto v___jp_940_;
}
}
else
{
v_l_1039_ = v_x_913_;
v_k_1040_ = v_x_914_;
v_v_1041_ = v_x_915_;
v_r_1042_ = v_x_916_;
goto v___jp_1038_;
}
}
}
else
{
if (lean_obj_tag(v_x_916_) == 1)
{
uint8_t v_color_1073_; 
v_color_1073_ = lean_ctor_get_uint8(v_x_916_, sizeof(void*)*4);
if (v_color_1073_ == 0)
{
lean_object* v_lchild_1074_; 
v_lchild_1074_ = lean_ctor_get(v_x_916_, 0);
if (lean_obj_tag(v_lchild_1074_) == 1)
{
uint8_t v_color_1075_; 
v_color_1075_ = lean_ctor_get_uint8(v_lchild_1074_, sizeof(void*)*4);
if (v_color_1075_ == 1)
{
lean_object* v_key_1076_; lean_object* v_val_1077_; lean_object* v_rchild_1078_; lean_object* v_lchild_1079_; lean_object* v_key_1080_; lean_object* v_val_1081_; lean_object* v_rchild_1082_; 
lean_inc_ref(v_lchild_1074_);
v_key_1076_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_key_1076_);
v_val_1077_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_val_1077_);
v_rchild_1078_ = lean_ctor_get(v_x_916_, 3);
lean_inc(v_rchild_1078_);
lean_dec_ref_known(v_x_916_, 4);
v_lchild_1079_ = lean_ctor_get(v_lchild_1074_, 0);
lean_inc(v_lchild_1079_);
v_key_1080_ = lean_ctor_get(v_lchild_1074_, 1);
lean_inc(v_key_1080_);
v_val_1081_ = lean_ctor_get(v_lchild_1074_, 2);
lean_inc(v_val_1081_);
v_rchild_1082_ = lean_ctor_get(v_lchild_1074_, 3);
lean_inc(v_rchild_1082_);
lean_dec_ref_known(v_lchild_1074_, 4);
v_l_998_ = v_x_913_;
v_k_999_ = v_x_914_;
v_v_1000_ = v_x_915_;
v_a_1001_ = v_lchild_1079_;
v_ky_1002_ = v_key_1080_;
v_vy_1003_ = v_val_1081_;
v_b_1004_ = v_rchild_1082_;
v_kz_1005_ = v_key_1076_;
v_vz_1006_ = v_val_1077_;
v_c_1007_ = v_rchild_1078_;
goto v___jp_997_;
}
else
{
v_l_1039_ = v_x_913_;
v_k_1040_ = v_x_914_;
v_v_1041_ = v_x_915_;
v_r_1042_ = v_x_916_;
goto v___jp_1038_;
}
}
else
{
v_l_1039_ = v_x_913_;
v_k_1040_ = v_x_914_;
v_v_1041_ = v_x_915_;
v_r_1042_ = v_x_916_;
goto v___jp_1038_;
}
}
else
{
lean_object* v_lchild_1083_; lean_object* v_key_1084_; lean_object* v_val_1085_; lean_object* v_rchild_1086_; 
v_lchild_1083_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_lchild_1083_);
v_key_1084_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_key_1084_);
v_val_1085_ = lean_ctor_get(v_x_916_, 2);
lean_inc(v_val_1085_);
v_rchild_1086_ = lean_ctor_get(v_x_916_, 3);
lean_inc(v_rchild_1086_);
lean_dec_ref_known(v_x_916_, 4);
v_l_941_ = v_x_913_;
v_k_942_ = v_x_914_;
v_v_943_ = v_x_915_;
v_a_944_ = v_lchild_1083_;
v_ky_945_ = v_key_1084_;
v_vy_946_ = v_val_1085_;
v_b_947_ = v_rchild_1086_;
goto v___jp_940_;
}
}
else
{
v_l_1039_ = v_x_913_;
v_k_1040_ = v_x_914_;
v_v_1041_ = v_x_915_;
v_r_1042_ = v_x_916_;
goto v___jp_1038_;
}
}
v___jp_917_:
{
uint8_t v___x_922_; lean_object* v___x_923_; 
v___x_922_ = 1;
v___x_923_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_923_, 0, v_a_918_);
lean_ctor_set(v___x_923_, 1, v_kx_919_);
lean_ctor_set(v___x_923_, 2, v_vx_920_);
lean_ctor_set(v___x_923_, 3, v_b_921_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*4, v___x_922_);
return v___x_923_;
}
v___jp_924_:
{
uint8_t v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_935_ = 0;
v___x_936_ = 1;
v___x_937_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_937_, 0, v_a_925_);
lean_ctor_set(v___x_937_, 1, v_kx_926_);
lean_ctor_set(v___x_937_, 2, v_vx_927_);
lean_ctor_set(v___x_937_, 3, v_b_928_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*4, v___x_936_);
v___x_938_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_938_, 0, v_c_931_);
lean_ctor_set(v___x_938_, 1, v_kz_932_);
lean_ctor_set(v___x_938_, 2, v_vz_933_);
lean_ctor_set(v___x_938_, 3, v_d_934_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*4, v___x_936_);
v___x_939_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v_ky_929_);
lean_ctor_set(v___x_939_, 2, v_vy_930_);
lean_ctor_set(v___x_939_, 3, v___x_938_);
lean_ctor_set_uint8(v___x_939_, sizeof(void*)*4, v___x_935_);
return v___x_939_;
}
v___jp_940_:
{
uint8_t v___x_948_; lean_object* v___x_949_; 
v___x_948_ = 0;
lean_inc(v_b_947_);
lean_inc(v_vy_946_);
lean_inc(v_ky_945_);
lean_inc(v_a_944_);
v___x_949_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_949_, 0, v_a_944_);
lean_ctor_set(v___x_949_, 1, v_ky_945_);
lean_ctor_set(v___x_949_, 2, v_vy_946_);
lean_ctor_set(v___x_949_, 3, v_b_947_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*4, v___x_948_);
if (lean_obj_tag(v_a_944_) == 1)
{
uint8_t v_color_950_; 
v_color_950_ = lean_ctor_get_uint8(v_a_944_, sizeof(void*)*4);
if (v_color_950_ == 0)
{
lean_object* v_lchild_951_; lean_object* v_key_952_; lean_object* v_val_953_; lean_object* v_rchild_954_; 
lean_dec_ref_known(v___x_949_, 4);
v_lchild_951_ = lean_ctor_get(v_a_944_, 0);
lean_inc(v_lchild_951_);
v_key_952_ = lean_ctor_get(v_a_944_, 1);
lean_inc(v_key_952_);
v_val_953_ = lean_ctor_get(v_a_944_, 2);
lean_inc(v_val_953_);
v_rchild_954_ = lean_ctor_get(v_a_944_, 3);
lean_inc(v_rchild_954_);
lean_dec_ref_known(v_a_944_, 4);
v_a_925_ = v_l_941_;
v_kx_926_ = v_k_942_;
v_vx_927_ = v_v_943_;
v_b_928_ = v_lchild_951_;
v_ky_929_ = v_key_952_;
v_vy_930_ = v_val_953_;
v_c_931_ = v_rchild_954_;
v_kz_932_ = v_ky_945_;
v_vz_933_ = v_vy_946_;
v_d_934_ = v_b_947_;
goto v___jp_924_;
}
else
{
if (lean_obj_tag(v_b_947_) == 1)
{
uint8_t v_color_955_; 
v_color_955_ = lean_ctor_get_uint8(v_b_947_, sizeof(void*)*4);
if (v_color_955_ == 0)
{
lean_object* v_lchild_956_; lean_object* v_key_957_; lean_object* v_val_958_; lean_object* v_rchild_959_; 
lean_dec_ref_known(v___x_949_, 4);
v_lchild_956_ = lean_ctor_get(v_b_947_, 0);
lean_inc(v_lchild_956_);
v_key_957_ = lean_ctor_get(v_b_947_, 1);
lean_inc(v_key_957_);
v_val_958_ = lean_ctor_get(v_b_947_, 2);
lean_inc(v_val_958_);
v_rchild_959_ = lean_ctor_get(v_b_947_, 3);
lean_inc(v_rchild_959_);
lean_dec_ref_known(v_b_947_, 4);
v_a_925_ = v_l_941_;
v_kx_926_ = v_k_942_;
v_vx_927_ = v_v_943_;
v_b_928_ = v_a_944_;
v_ky_929_ = v_ky_945_;
v_vy_930_ = v_vy_946_;
v_c_931_ = v_lchild_956_;
v_kz_932_ = v_key_957_;
v_vz_933_ = v_val_958_;
v_d_934_ = v_rchild_959_;
goto v___jp_924_;
}
else
{
lean_dec_ref_known(v_b_947_, 4);
lean_dec_ref_known(v_a_944_, 4);
lean_dec(v_vy_946_);
lean_dec(v_ky_945_);
v_a_918_ = v_l_941_;
v_kx_919_ = v_k_942_;
v_vx_920_ = v_v_943_;
v_b_921_ = v___x_949_;
goto v___jp_917_;
}
}
else
{
lean_dec_ref_known(v_a_944_, 4);
lean_dec(v_b_947_);
lean_dec(v_vy_946_);
lean_dec(v_ky_945_);
v_a_918_ = v_l_941_;
v_kx_919_ = v_k_942_;
v_vx_920_ = v_v_943_;
v_b_921_ = v___x_949_;
goto v___jp_917_;
}
}
}
else
{
if (lean_obj_tag(v_b_947_) == 1)
{
uint8_t v_color_960_; 
v_color_960_ = lean_ctor_get_uint8(v_b_947_, sizeof(void*)*4);
if (v_color_960_ == 0)
{
lean_object* v_lchild_961_; lean_object* v_key_962_; lean_object* v_val_963_; lean_object* v_rchild_964_; 
lean_dec_ref_known(v___x_949_, 4);
v_lchild_961_ = lean_ctor_get(v_b_947_, 0);
lean_inc(v_lchild_961_);
v_key_962_ = lean_ctor_get(v_b_947_, 1);
lean_inc(v_key_962_);
v_val_963_ = lean_ctor_get(v_b_947_, 2);
lean_inc(v_val_963_);
v_rchild_964_ = lean_ctor_get(v_b_947_, 3);
lean_inc(v_rchild_964_);
lean_dec_ref_known(v_b_947_, 4);
v_a_925_ = v_l_941_;
v_kx_926_ = v_k_942_;
v_vx_927_ = v_v_943_;
v_b_928_ = v_a_944_;
v_ky_929_ = v_ky_945_;
v_vy_930_ = v_vy_946_;
v_c_931_ = v_lchild_961_;
v_kz_932_ = v_key_962_;
v_vz_933_ = v_val_963_;
v_d_934_ = v_rchild_964_;
goto v___jp_924_;
}
else
{
lean_dec_ref_known(v_b_947_, 4);
lean_dec(v_vy_946_);
lean_dec(v_ky_945_);
lean_dec(v_a_944_);
v_a_918_ = v_l_941_;
v_kx_919_ = v_k_942_;
v_vx_920_ = v_v_943_;
v_b_921_ = v___x_949_;
goto v___jp_917_;
}
}
else
{
lean_dec(v_b_947_);
lean_dec(v_vy_946_);
lean_dec(v_ky_945_);
lean_dec(v_a_944_);
v_a_918_ = v_l_941_;
v_kx_919_ = v_k_942_;
v_vx_920_ = v_v_943_;
v_b_921_ = v___x_949_;
goto v___jp_917_;
}
}
}
v___jp_965_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_981_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_981_, 0, v_a_971_);
lean_ctor_set(v___x_981_, 1, v_kx_972_);
lean_ctor_set(v___x_981_, 2, v_vx_973_);
lean_ctor_set(v___x_981_, 3, v_b_974_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*4, v___y_966_);
v___x_982_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_982_, 0, v_c_977_);
lean_ctor_set(v___x_982_, 1, v_kz_978_);
lean_ctor_set(v___x_982_, 2, v_vz_979_);
lean_ctor_set(v___x_982_, 3, v_d_980_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*4, v___y_966_);
v___x_983_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v_ky_975_);
lean_ctor_set(v___x_983_, 2, v_vy_976_);
lean_ctor_set(v___x_983_, 3, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*4, v___y_968_);
v___x_984_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_984_, 0, v___y_967_);
lean_ctor_set(v___x_984_, 1, v___y_970_);
lean_ctor_set(v___x_984_, 2, v___y_969_);
lean_ctor_set(v___x_984_, 3, v___x_983_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*4, v___y_968_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_995_, 0, v_a_991_);
lean_ctor_set(v___x_995_, 1, v_kx_992_);
lean_ctor_set(v___x_995_, 2, v_vx_993_);
lean_ctor_set(v___x_995_, 3, v_b_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*4, v___y_986_);
v___x_996_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_996_, 0, v___y_987_);
lean_ctor_set(v___x_996_, 1, v___y_990_);
lean_ctor_set(v___x_996_, 2, v___y_989_);
lean_ctor_set(v___x_996_, 3, v___x_995_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*4, v___y_988_);
return v___x_996_;
}
v___jp_997_:
{
uint8_t v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1008_ = 0;
v___x_1009_ = 1;
v___x_1010_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1010_, 0, v_l_998_);
lean_ctor_set(v___x_1010_, 1, v_k_999_);
lean_ctor_set(v___x_1010_, 2, v_v_1000_);
lean_ctor_set(v___x_1010_, 3, v_a_1001_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*4, v___x_1009_);
v___x_1011_ = l_Lean_RBNode_setRed___redArg(v_c_1007_);
if (lean_obj_tag(v___x_1011_) == 1)
{
uint8_t v_color_1012_; 
v_color_1012_ = lean_ctor_get_uint8(v___x_1011_, sizeof(void*)*4);
if (v_color_1012_ == 0)
{
lean_object* v_lchild_1013_; 
v_lchild_1013_ = lean_ctor_get(v___x_1011_, 0);
if (lean_obj_tag(v_lchild_1013_) == 1)
{
uint8_t v_color_1014_; 
v_color_1014_ = lean_ctor_get_uint8(v_lchild_1013_, sizeof(void*)*4);
if (v_color_1014_ == 0)
{
lean_object* v_key_1015_; lean_object* v_val_1016_; lean_object* v_rchild_1017_; lean_object* v_lchild_1018_; lean_object* v_key_1019_; lean_object* v_val_1020_; lean_object* v_rchild_1021_; 
lean_inc_ref(v_lchild_1013_);
v_key_1015_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_key_1015_);
v_val_1016_ = lean_ctor_get(v___x_1011_, 2);
lean_inc(v_val_1016_);
v_rchild_1017_ = lean_ctor_get(v___x_1011_, 3);
lean_inc(v_rchild_1017_);
lean_dec_ref_known(v___x_1011_, 4);
v_lchild_1018_ = lean_ctor_get(v_lchild_1013_, 0);
lean_inc(v_lchild_1018_);
v_key_1019_ = lean_ctor_get(v_lchild_1013_, 1);
lean_inc(v_key_1019_);
v_val_1020_ = lean_ctor_get(v_lchild_1013_, 2);
lean_inc(v_val_1020_);
v_rchild_1021_ = lean_ctor_get(v_lchild_1013_, 3);
lean_inc(v_rchild_1021_);
lean_dec_ref_known(v_lchild_1013_, 4);
v___y_966_ = v___x_1009_;
v___y_967_ = v___x_1010_;
v___y_968_ = v___x_1008_;
v___y_969_ = v_vy_1003_;
v___y_970_ = v_ky_1002_;
v_a_971_ = v_b_1004_;
v_kx_972_ = v_kz_1005_;
v_vx_973_ = v_vz_1006_;
v_b_974_ = v_lchild_1018_;
v_ky_975_ = v_key_1019_;
v_vy_976_ = v_val_1020_;
v_c_977_ = v_rchild_1021_;
v_kz_978_ = v_key_1015_;
v_vz_979_ = v_val_1016_;
v_d_980_ = v_rchild_1017_;
goto v___jp_965_;
}
else
{
lean_object* v_rchild_1022_; 
v_rchild_1022_ = lean_ctor_get(v___x_1011_, 3);
if (lean_obj_tag(v_rchild_1022_) == 1)
{
uint8_t v_color_1023_; 
v_color_1023_ = lean_ctor_get_uint8(v_rchild_1022_, sizeof(void*)*4);
if (v_color_1023_ == 0)
{
lean_object* v_key_1024_; lean_object* v_val_1025_; lean_object* v_lchild_1026_; lean_object* v_key_1027_; lean_object* v_val_1028_; lean_object* v_rchild_1029_; 
lean_inc_ref(v_rchild_1022_);
lean_inc_ref(v_lchild_1013_);
v_key_1024_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_key_1024_);
v_val_1025_ = lean_ctor_get(v___x_1011_, 2);
lean_inc(v_val_1025_);
lean_dec_ref_known(v___x_1011_, 4);
v_lchild_1026_ = lean_ctor_get(v_rchild_1022_, 0);
lean_inc(v_lchild_1026_);
v_key_1027_ = lean_ctor_get(v_rchild_1022_, 1);
lean_inc(v_key_1027_);
v_val_1028_ = lean_ctor_get(v_rchild_1022_, 2);
lean_inc(v_val_1028_);
v_rchild_1029_ = lean_ctor_get(v_rchild_1022_, 3);
lean_inc(v_rchild_1029_);
lean_dec_ref_known(v_rchild_1022_, 4);
v___y_966_ = v___x_1009_;
v___y_967_ = v___x_1010_;
v___y_968_ = v___x_1008_;
v___y_969_ = v_vy_1003_;
v___y_970_ = v_ky_1002_;
v_a_971_ = v_b_1004_;
v_kx_972_ = v_kz_1005_;
v_vx_973_ = v_vz_1006_;
v_b_974_ = v_lchild_1013_;
v_ky_975_ = v_key_1024_;
v_vy_976_ = v_val_1025_;
v_c_977_ = v_lchild_1026_;
v_kz_978_ = v_key_1027_;
v_vz_979_ = v_val_1028_;
v_d_980_ = v_rchild_1029_;
goto v___jp_965_;
}
else
{
v___y_986_ = v___x_1009_;
v___y_987_ = v___x_1010_;
v___y_988_ = v___x_1008_;
v___y_989_ = v_vy_1003_;
v___y_990_ = v_ky_1002_;
v_a_991_ = v_b_1004_;
v_kx_992_ = v_kz_1005_;
v_vx_993_ = v_vz_1006_;
v_b_994_ = v___x_1011_;
goto v___jp_985_;
}
}
else
{
v___y_986_ = v___x_1009_;
v___y_987_ = v___x_1010_;
v___y_988_ = v___x_1008_;
v___y_989_ = v_vy_1003_;
v___y_990_ = v_ky_1002_;
v_a_991_ = v_b_1004_;
v_kx_992_ = v_kz_1005_;
v_vx_993_ = v_vz_1006_;
v_b_994_ = v___x_1011_;
goto v___jp_985_;
}
}
}
else
{
lean_object* v_rchild_1030_; 
v_rchild_1030_ = lean_ctor_get(v___x_1011_, 3);
if (lean_obj_tag(v_rchild_1030_) == 1)
{
uint8_t v_color_1031_; 
v_color_1031_ = lean_ctor_get_uint8(v_rchild_1030_, sizeof(void*)*4);
if (v_color_1031_ == 0)
{
lean_object* v_key_1032_; lean_object* v_val_1033_; lean_object* v_lchild_1034_; lean_object* v_key_1035_; lean_object* v_val_1036_; lean_object* v_rchild_1037_; 
lean_inc_ref(v_rchild_1030_);
lean_inc(v_lchild_1013_);
v_key_1032_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_key_1032_);
v_val_1033_ = lean_ctor_get(v___x_1011_, 2);
lean_inc(v_val_1033_);
lean_dec_ref_known(v___x_1011_, 4);
v_lchild_1034_ = lean_ctor_get(v_rchild_1030_, 0);
lean_inc(v_lchild_1034_);
v_key_1035_ = lean_ctor_get(v_rchild_1030_, 1);
lean_inc(v_key_1035_);
v_val_1036_ = lean_ctor_get(v_rchild_1030_, 2);
lean_inc(v_val_1036_);
v_rchild_1037_ = lean_ctor_get(v_rchild_1030_, 3);
lean_inc(v_rchild_1037_);
lean_dec_ref_known(v_rchild_1030_, 4);
v___y_966_ = v___x_1009_;
v___y_967_ = v___x_1010_;
v___y_968_ = v___x_1008_;
v___y_969_ = v_vy_1003_;
v___y_970_ = v_ky_1002_;
v_a_971_ = v_b_1004_;
v_kx_972_ = v_kz_1005_;
v_vx_973_ = v_vz_1006_;
v_b_974_ = v_lchild_1013_;
v_ky_975_ = v_key_1032_;
v_vy_976_ = v_val_1033_;
v_c_977_ = v_lchild_1034_;
v_kz_978_ = v_key_1035_;
v_vz_979_ = v_val_1036_;
v_d_980_ = v_rchild_1037_;
goto v___jp_965_;
}
else
{
v___y_986_ = v___x_1009_;
v___y_987_ = v___x_1010_;
v___y_988_ = v___x_1008_;
v___y_989_ = v_vy_1003_;
v___y_990_ = v_ky_1002_;
v_a_991_ = v_b_1004_;
v_kx_992_ = v_kz_1005_;
v_vx_993_ = v_vz_1006_;
v_b_994_ = v___x_1011_;
goto v___jp_985_;
}
}
else
{
v___y_986_ = v___x_1009_;
v___y_987_ = v___x_1010_;
v___y_988_ = v___x_1008_;
v___y_989_ = v_vy_1003_;
v___y_990_ = v_ky_1002_;
v_a_991_ = v_b_1004_;
v_kx_992_ = v_kz_1005_;
v_vx_993_ = v_vz_1006_;
v_b_994_ = v___x_1011_;
goto v___jp_985_;
}
}
}
else
{
v___y_986_ = v___x_1009_;
v___y_987_ = v___x_1010_;
v___y_988_ = v___x_1008_;
v___y_989_ = v_vy_1003_;
v___y_990_ = v_ky_1002_;
v_a_991_ = v_b_1004_;
v_kx_992_ = v_kz_1005_;
v_vx_993_ = v_vz_1006_;
v_b_994_ = v___x_1011_;
goto v___jp_985_;
}
}
else
{
v___y_986_ = v___x_1009_;
v___y_987_ = v___x_1010_;
v___y_988_ = v___x_1008_;
v___y_989_ = v_vy_1003_;
v___y_990_ = v_ky_1002_;
v_a_991_ = v_b_1004_;
v_kx_992_ = v_kz_1005_;
v_vx_993_ = v_vz_1006_;
v_b_994_ = v___x_1011_;
goto v___jp_985_;
}
}
v___jp_1038_:
{
uint8_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = 0;
v___x_1044_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1044_, 0, v_l_1039_);
lean_ctor_set(v___x_1044_, 1, v_k_1040_);
lean_ctor_set(v___x_1044_, 2, v_v_1041_);
lean_ctor_set(v___x_1044_, 3, v_r_1042_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*4, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object* v_00_u03b1_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_RBNode_balLeft___redArg(v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object* v_l_1094_, lean_object* v_k_1095_, lean_object* v_v_1096_, lean_object* v_r_1097_){
_start:
{
uint8_t v___y_1102_; lean_object* v_a_1103_; lean_object* v_kx_1104_; lean_object* v_vx_1105_; lean_object* v_b_1106_; lean_object* v_ky_1107_; lean_object* v_vy_1108_; lean_object* v_c_1109_; lean_object* v_kz_1110_; lean_object* v_vz_1111_; lean_object* v_d_1112_; uint8_t v___y_1118_; uint8_t v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; uint8_t v___y_1127_; uint8_t v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v_a_1132_; lean_object* v_kx_1133_; lean_object* v_vx_1134_; lean_object* v_b_1135_; lean_object* v_ky_1136_; lean_object* v_vy_1137_; lean_object* v_c_1138_; lean_object* v_kz_1139_; lean_object* v_vz_1140_; lean_object* v_d_1141_; uint8_t v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v_a_1151_; lean_object* v_kx_1152_; lean_object* v_vx_1153_; lean_object* v_b_1154_; 
if (lean_obj_tag(v_r_1097_) == 1)
{
uint8_t v_color_1255_; 
v_color_1255_ = lean_ctor_get_uint8(v_r_1097_, sizeof(void*)*4);
if (v_color_1255_ == 0)
{
lean_object* v_lchild_1256_; lean_object* v_key_1257_; lean_object* v_val_1258_; lean_object* v_rchild_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v_lchild_1256_ = lean_ctor_get(v_r_1097_, 0);
v_key_1257_ = lean_ctor_get(v_r_1097_, 1);
v_val_1258_ = lean_ctor_get(v_r_1097_, 2);
v_rchild_1259_ = lean_ctor_get(v_r_1097_, 3);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_r_1097_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1261_ = v_r_1097_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_rchild_1259_);
lean_inc(v_val_1258_);
lean_inc(v_key_1257_);
lean_inc(v_lchild_1256_);
lean_dec(v_r_1097_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = 1;
if (v_isShared_1262_ == 0)
{
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_lchild_1256_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_key_1257_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_val_1258_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_rchild_1259_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*4, v___x_1263_);
v___x_1266_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1266_, 0, v_l_1094_);
lean_ctor_set(v___x_1266_, 1, v_k_1095_);
lean_ctor_set(v___x_1266_, 2, v_v_1096_);
lean_ctor_set(v___x_1266_, 3, v___x_1265_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*4, v_color_1255_);
return v___x_1266_;
}
}
}
else
{
goto v___jp_1156_;
}
}
else
{
goto v___jp_1156_;
}
v___jp_1098_:
{
uint8_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = 0;
v___x_1100_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1100_, 0, v_l_1094_);
lean_ctor_set(v___x_1100_, 1, v_k_1095_);
lean_ctor_set(v___x_1100_, 2, v_v_1096_);
lean_ctor_set(v___x_1100_, 3, v_r_1097_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*4, v___x_1099_);
return v___x_1100_;
}
v___jp_1101_:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = 0;
v___x_1114_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1114_, 0, v_a_1103_);
lean_ctor_set(v___x_1114_, 1, v_kx_1104_);
lean_ctor_set(v___x_1114_, 2, v_vx_1105_);
lean_ctor_set(v___x_1114_, 3, v_b_1106_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*4, v___y_1102_);
v___x_1115_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1115_, 0, v_c_1109_);
lean_ctor_set(v___x_1115_, 1, v_kz_1110_);
lean_ctor_set(v___x_1115_, 2, v_vz_1111_);
lean_ctor_set(v___x_1115_, 3, v_d_1112_);
lean_ctor_set_uint8(v___x_1115_, sizeof(void*)*4, v___y_1102_);
v___x_1116_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v_ky_1107_);
lean_ctor_set(v___x_1116_, 2, v_vy_1108_);
lean_ctor_set(v___x_1116_, 3, v___x_1115_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*4, v___x_1113_);
return v___x_1116_;
}
v___jp_1117_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1124_, 0, v___y_1122_);
lean_ctor_set(v___x_1124_, 1, v_k_1095_);
lean_ctor_set(v___x_1124_, 2, v_v_1096_);
lean_ctor_set(v___x_1124_, 3, v_r_1097_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*4, v___y_1118_);
v___x_1125_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1125_, 0, v___y_1123_);
lean_ctor_set(v___x_1125_, 1, v___y_1121_);
lean_ctor_set(v___x_1125_, 2, v___y_1120_);
lean_ctor_set(v___x_1125_, 3, v___x_1124_);
lean_ctor_set_uint8(v___x_1125_, sizeof(void*)*4, v___y_1119_);
return v___x_1125_;
}
v___jp_1126_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1142_, 0, v_a_1132_);
lean_ctor_set(v___x_1142_, 1, v_kx_1133_);
lean_ctor_set(v___x_1142_, 2, v_vx_1134_);
lean_ctor_set(v___x_1142_, 3, v_b_1135_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*4, v___y_1127_);
v___x_1143_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1143_, 0, v_c_1138_);
lean_ctor_set(v___x_1143_, 1, v_kz_1139_);
lean_ctor_set(v___x_1143_, 2, v_vz_1140_);
lean_ctor_set(v___x_1143_, 3, v_d_1141_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*4, v___y_1127_);
v___x_1144_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v_ky_1136_);
lean_ctor_set(v___x_1144_, 2, v_vy_1137_);
lean_ctor_set(v___x_1144_, 3, v___x_1143_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*4, v___y_1128_);
v___y_1118_ = v___y_1127_;
v___y_1119_ = v___y_1128_;
v___y_1120_ = v___y_1129_;
v___y_1121_ = v___y_1131_;
v___y_1122_ = v___y_1130_;
v___y_1123_ = v___x_1144_;
goto v___jp_1117_;
}
v___jp_1145_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1155_, 0, v_a_1151_);
lean_ctor_set(v___x_1155_, 1, v_kx_1152_);
lean_ctor_set(v___x_1155_, 2, v_vx_1153_);
lean_ctor_set(v___x_1155_, 3, v_b_1154_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*4, v___y_1146_);
v___y_1118_ = v___y_1146_;
v___y_1119_ = v___y_1147_;
v___y_1120_ = v___y_1148_;
v___y_1121_ = v___y_1150_;
v___y_1122_ = v___y_1149_;
v___y_1123_ = v___x_1155_;
goto v___jp_1117_;
}
v___jp_1156_:
{
if (lean_obj_tag(v_l_1094_) == 1)
{
uint8_t v_color_1157_; 
v_color_1157_ = lean_ctor_get_uint8(v_l_1094_, sizeof(void*)*4);
if (v_color_1157_ == 0)
{
lean_object* v_rchild_1158_; 
v_rchild_1158_ = lean_ctor_get(v_l_1094_, 3);
if (lean_obj_tag(v_rchild_1158_) == 1)
{
uint8_t v_color_1159_; 
v_color_1159_ = lean_ctor_get_uint8(v_rchild_1158_, sizeof(void*)*4);
if (v_color_1159_ == 1)
{
lean_object* v_lchild_1160_; lean_object* v_key_1161_; lean_object* v_val_1162_; lean_object* v_lchild_1163_; lean_object* v_key_1164_; lean_object* v_val_1165_; lean_object* v_rchild_1166_; lean_object* v___x_1167_; 
lean_inc_ref(v_rchild_1158_);
v_lchild_1160_ = lean_ctor_get(v_l_1094_, 0);
lean_inc(v_lchild_1160_);
v_key_1161_ = lean_ctor_get(v_l_1094_, 1);
lean_inc(v_key_1161_);
v_val_1162_ = lean_ctor_get(v_l_1094_, 2);
lean_inc(v_val_1162_);
lean_dec_ref_known(v_l_1094_, 4);
v_lchild_1163_ = lean_ctor_get(v_rchild_1158_, 0);
lean_inc(v_lchild_1163_);
v_key_1164_ = lean_ctor_get(v_rchild_1158_, 1);
lean_inc(v_key_1164_);
v_val_1165_ = lean_ctor_get(v_rchild_1158_, 2);
lean_inc(v_val_1165_);
v_rchild_1166_ = lean_ctor_get(v_rchild_1158_, 3);
lean_inc(v_rchild_1166_);
lean_dec_ref_known(v_rchild_1158_, 4);
v___x_1167_ = l_Lean_RBNode_setRed___redArg(v_lchild_1160_);
if (lean_obj_tag(v___x_1167_) == 1)
{
uint8_t v_color_1168_; 
v_color_1168_ = lean_ctor_get_uint8(v___x_1167_, sizeof(void*)*4);
if (v_color_1168_ == 0)
{
lean_object* v_lchild_1169_; 
v_lchild_1169_ = lean_ctor_get(v___x_1167_, 0);
if (lean_obj_tag(v_lchild_1169_) == 1)
{
uint8_t v_color_1170_; 
v_color_1170_ = lean_ctor_get_uint8(v_lchild_1169_, sizeof(void*)*4);
if (v_color_1170_ == 0)
{
lean_object* v_key_1171_; lean_object* v_val_1172_; lean_object* v_rchild_1173_; lean_object* v_lchild_1174_; lean_object* v_key_1175_; lean_object* v_val_1176_; lean_object* v_rchild_1177_; 
lean_inc_ref(v_lchild_1169_);
v_key_1171_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_key_1171_);
v_val_1172_ = lean_ctor_get(v___x_1167_, 2);
lean_inc(v_val_1172_);
v_rchild_1173_ = lean_ctor_get(v___x_1167_, 3);
lean_inc(v_rchild_1173_);
lean_dec_ref_known(v___x_1167_, 4);
v_lchild_1174_ = lean_ctor_get(v_lchild_1169_, 0);
lean_inc(v_lchild_1174_);
v_key_1175_ = lean_ctor_get(v_lchild_1169_, 1);
lean_inc(v_key_1175_);
v_val_1176_ = lean_ctor_get(v_lchild_1169_, 2);
lean_inc(v_val_1176_);
v_rchild_1177_ = lean_ctor_get(v_lchild_1169_, 3);
lean_inc(v_rchild_1177_);
lean_dec_ref_known(v_lchild_1169_, 4);
v___y_1127_ = v_color_1159_;
v___y_1128_ = v_color_1157_;
v___y_1129_ = v_val_1165_;
v___y_1130_ = v_rchild_1166_;
v___y_1131_ = v_key_1164_;
v_a_1132_ = v_lchild_1174_;
v_kx_1133_ = v_key_1175_;
v_vx_1134_ = v_val_1176_;
v_b_1135_ = v_rchild_1177_;
v_ky_1136_ = v_key_1171_;
v_vy_1137_ = v_val_1172_;
v_c_1138_ = v_rchild_1173_;
v_kz_1139_ = v_key_1161_;
v_vz_1140_ = v_val_1162_;
v_d_1141_ = v_lchild_1163_;
goto v___jp_1126_;
}
else
{
lean_object* v_rchild_1178_; 
v_rchild_1178_ = lean_ctor_get(v___x_1167_, 3);
if (lean_obj_tag(v_rchild_1178_) == 1)
{
uint8_t v_color_1179_; 
v_color_1179_ = lean_ctor_get_uint8(v_rchild_1178_, sizeof(void*)*4);
if (v_color_1179_ == 0)
{
lean_object* v_key_1180_; lean_object* v_val_1181_; lean_object* v_lchild_1182_; lean_object* v_key_1183_; lean_object* v_val_1184_; lean_object* v_rchild_1185_; 
lean_inc_ref(v_rchild_1178_);
lean_inc_ref(v_lchild_1169_);
v_key_1180_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_key_1180_);
v_val_1181_ = lean_ctor_get(v___x_1167_, 2);
lean_inc(v_val_1181_);
lean_dec_ref_known(v___x_1167_, 4);
v_lchild_1182_ = lean_ctor_get(v_rchild_1178_, 0);
lean_inc(v_lchild_1182_);
v_key_1183_ = lean_ctor_get(v_rchild_1178_, 1);
lean_inc(v_key_1183_);
v_val_1184_ = lean_ctor_get(v_rchild_1178_, 2);
lean_inc(v_val_1184_);
v_rchild_1185_ = lean_ctor_get(v_rchild_1178_, 3);
lean_inc(v_rchild_1185_);
lean_dec_ref_known(v_rchild_1178_, 4);
v___y_1127_ = v_color_1159_;
v___y_1128_ = v_color_1157_;
v___y_1129_ = v_val_1165_;
v___y_1130_ = v_rchild_1166_;
v___y_1131_ = v_key_1164_;
v_a_1132_ = v_lchild_1169_;
v_kx_1133_ = v_key_1180_;
v_vx_1134_ = v_val_1181_;
v_b_1135_ = v_lchild_1182_;
v_ky_1136_ = v_key_1183_;
v_vy_1137_ = v_val_1184_;
v_c_1138_ = v_rchild_1185_;
v_kz_1139_ = v_key_1161_;
v_vz_1140_ = v_val_1162_;
v_d_1141_ = v_lchild_1163_;
goto v___jp_1126_;
}
else
{
v___y_1146_ = v_color_1159_;
v___y_1147_ = v_color_1157_;
v___y_1148_ = v_val_1165_;
v___y_1149_ = v_rchild_1166_;
v___y_1150_ = v_key_1164_;
v_a_1151_ = v___x_1167_;
v_kx_1152_ = v_key_1161_;
v_vx_1153_ = v_val_1162_;
v_b_1154_ = v_lchild_1163_;
goto v___jp_1145_;
}
}
else
{
v___y_1146_ = v_color_1159_;
v___y_1147_ = v_color_1157_;
v___y_1148_ = v_val_1165_;
v___y_1149_ = v_rchild_1166_;
v___y_1150_ = v_key_1164_;
v_a_1151_ = v___x_1167_;
v_kx_1152_ = v_key_1161_;
v_vx_1153_ = v_val_1162_;
v_b_1154_ = v_lchild_1163_;
goto v___jp_1145_;
}
}
}
else
{
lean_object* v_rchild_1186_; 
v_rchild_1186_ = lean_ctor_get(v___x_1167_, 3);
if (lean_obj_tag(v_rchild_1186_) == 1)
{
uint8_t v_color_1187_; 
v_color_1187_ = lean_ctor_get_uint8(v_rchild_1186_, sizeof(void*)*4);
if (v_color_1187_ == 0)
{
lean_object* v_key_1188_; lean_object* v_val_1189_; lean_object* v_lchild_1190_; lean_object* v_key_1191_; lean_object* v_val_1192_; lean_object* v_rchild_1193_; 
lean_inc_ref(v_rchild_1186_);
lean_inc(v_lchild_1169_);
v_key_1188_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_key_1188_);
v_val_1189_ = lean_ctor_get(v___x_1167_, 2);
lean_inc(v_val_1189_);
lean_dec_ref_known(v___x_1167_, 4);
v_lchild_1190_ = lean_ctor_get(v_rchild_1186_, 0);
lean_inc(v_lchild_1190_);
v_key_1191_ = lean_ctor_get(v_rchild_1186_, 1);
lean_inc(v_key_1191_);
v_val_1192_ = lean_ctor_get(v_rchild_1186_, 2);
lean_inc(v_val_1192_);
v_rchild_1193_ = lean_ctor_get(v_rchild_1186_, 3);
lean_inc(v_rchild_1193_);
lean_dec_ref_known(v_rchild_1186_, 4);
v___y_1127_ = v_color_1159_;
v___y_1128_ = v_color_1157_;
v___y_1129_ = v_val_1165_;
v___y_1130_ = v_rchild_1166_;
v___y_1131_ = v_key_1164_;
v_a_1132_ = v_lchild_1169_;
v_kx_1133_ = v_key_1188_;
v_vx_1134_ = v_val_1189_;
v_b_1135_ = v_lchild_1190_;
v_ky_1136_ = v_key_1191_;
v_vy_1137_ = v_val_1192_;
v_c_1138_ = v_rchild_1193_;
v_kz_1139_ = v_key_1161_;
v_vz_1140_ = v_val_1162_;
v_d_1141_ = v_lchild_1163_;
goto v___jp_1126_;
}
else
{
v___y_1146_ = v_color_1159_;
v___y_1147_ = v_color_1157_;
v___y_1148_ = v_val_1165_;
v___y_1149_ = v_rchild_1166_;
v___y_1150_ = v_key_1164_;
v_a_1151_ = v___x_1167_;
v_kx_1152_ = v_key_1161_;
v_vx_1153_ = v_val_1162_;
v_b_1154_ = v_lchild_1163_;
goto v___jp_1145_;
}
}
else
{
v___y_1146_ = v_color_1159_;
v___y_1147_ = v_color_1157_;
v___y_1148_ = v_val_1165_;
v___y_1149_ = v_rchild_1166_;
v___y_1150_ = v_key_1164_;
v_a_1151_ = v___x_1167_;
v_kx_1152_ = v_key_1161_;
v_vx_1153_ = v_val_1162_;
v_b_1154_ = v_lchild_1163_;
goto v___jp_1145_;
}
}
}
else
{
v___y_1146_ = v_color_1159_;
v___y_1147_ = v_color_1157_;
v___y_1148_ = v_val_1165_;
v___y_1149_ = v_rchild_1166_;
v___y_1150_ = v_key_1164_;
v_a_1151_ = v___x_1167_;
v_kx_1152_ = v_key_1161_;
v_vx_1153_ = v_val_1162_;
v_b_1154_ = v_lchild_1163_;
goto v___jp_1145_;
}
}
else
{
v___y_1146_ = v_color_1159_;
v___y_1147_ = v_color_1157_;
v___y_1148_ = v_val_1165_;
v___y_1149_ = v_rchild_1166_;
v___y_1150_ = v_key_1164_;
v_a_1151_ = v___x_1167_;
v_kx_1152_ = v_key_1161_;
v_vx_1153_ = v_val_1162_;
v_b_1154_ = v_lchild_1163_;
goto v___jp_1145_;
}
}
else
{
goto v___jp_1098_;
}
}
else
{
goto v___jp_1098_;
}
}
else
{
lean_object* v_lchild_1194_; lean_object* v_key_1195_; lean_object* v_val_1196_; lean_object* v_rchild_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1254_; 
v_lchild_1194_ = lean_ctor_get(v_l_1094_, 0);
v_key_1195_ = lean_ctor_get(v_l_1094_, 1);
v_val_1196_ = lean_ctor_get(v_l_1094_, 2);
v_rchild_1197_ = lean_ctor_get(v_l_1094_, 3);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_l_1094_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1199_ = v_l_1094_;
v_isShared_1200_ = v_isSharedCheck_1254_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_rchild_1197_);
lean_inc(v_val_1196_);
lean_inc(v_key_1195_);
lean_inc(v_lchild_1194_);
lean_dec(v_l_1094_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1254_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint8_t v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = 0;
lean_inc(v_rchild_1197_);
lean_inc(v_val_1196_);
lean_inc(v_key_1195_);
lean_inc(v_lchild_1194_);
if (v_isShared_1200_ == 0)
{
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_lchild_1194_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_key_1195_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_val_1196_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_rchild_1197_);
v___x_1203_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*4, v___x_1201_);
if (lean_obj_tag(v_lchild_1194_) == 1)
{
uint8_t v_color_1204_; 
v_color_1204_ = lean_ctor_get_uint8(v_lchild_1194_, sizeof(void*)*4);
if (v_color_1204_ == 0)
{
lean_object* v_lchild_1205_; lean_object* v_key_1206_; lean_object* v_val_1207_; lean_object* v_rchild_1208_; 
lean_dec_ref(v___x_1203_);
v_lchild_1205_ = lean_ctor_get(v_lchild_1194_, 0);
lean_inc(v_lchild_1205_);
v_key_1206_ = lean_ctor_get(v_lchild_1194_, 1);
lean_inc(v_key_1206_);
v_val_1207_ = lean_ctor_get(v_lchild_1194_, 2);
lean_inc(v_val_1207_);
v_rchild_1208_ = lean_ctor_get(v_lchild_1194_, 3);
lean_inc(v_rchild_1208_);
lean_dec_ref_known(v_lchild_1194_, 4);
v___y_1102_ = v_color_1157_;
v_a_1103_ = v_lchild_1205_;
v_kx_1104_ = v_key_1206_;
v_vx_1105_ = v_val_1207_;
v_b_1106_ = v_rchild_1208_;
v_ky_1107_ = v_key_1195_;
v_vy_1108_ = v_val_1196_;
v_c_1109_ = v_rchild_1197_;
v_kz_1110_ = v_k_1095_;
v_vz_1111_ = v_v_1096_;
v_d_1112_ = v_r_1097_;
goto v___jp_1101_;
}
else
{
if (lean_obj_tag(v_rchild_1197_) == 1)
{
uint8_t v_color_1209_; 
v_color_1209_ = lean_ctor_get_uint8(v_rchild_1197_, sizeof(void*)*4);
if (v_color_1209_ == 0)
{
lean_object* v_lchild_1210_; lean_object* v_key_1211_; lean_object* v_val_1212_; lean_object* v_rchild_1213_; 
lean_dec_ref(v___x_1203_);
v_lchild_1210_ = lean_ctor_get(v_rchild_1197_, 0);
lean_inc(v_lchild_1210_);
v_key_1211_ = lean_ctor_get(v_rchild_1197_, 1);
lean_inc(v_key_1211_);
v_val_1212_ = lean_ctor_get(v_rchild_1197_, 2);
lean_inc(v_val_1212_);
v_rchild_1213_ = lean_ctor_get(v_rchild_1197_, 3);
lean_inc(v_rchild_1213_);
lean_dec_ref_known(v_rchild_1197_, 4);
v___y_1102_ = v_color_1157_;
v_a_1103_ = v_lchild_1194_;
v_kx_1104_ = v_key_1195_;
v_vx_1105_ = v_val_1196_;
v_b_1106_ = v_lchild_1210_;
v_ky_1107_ = v_key_1211_;
v_vy_1108_ = v_val_1212_;
v_c_1109_ = v_rchild_1213_;
v_kz_1110_ = v_k_1095_;
v_vz_1111_ = v_v_1096_;
v_d_1112_ = v_r_1097_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref_known(v_lchild_1194_, 4);
lean_dec(v_val_1196_);
lean_dec(v_key_1195_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_rchild_1197_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; lean_object* v_unused_1224_; 
v_unused_1221_ = lean_ctor_get(v_rchild_1197_, 3);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_rchild_1197_, 2);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_rchild_1197_, 1);
lean_dec(v_unused_1223_);
v_unused_1224_ = lean_ctor_get(v_rchild_1197_, 0);
lean_dec(v_unused_1224_);
v___x_1215_ = v_rchild_1197_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v_rchild_1197_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 3, v_r_1097_);
lean_ctor_set(v___x_1215_, 2, v_v_1096_);
lean_ctor_set(v___x_1215_, 1, v_k_1095_);
lean_ctor_set(v___x_1215_, 0, v___x_1203_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_r_1097_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*4, v_color_1157_);
return v___x_1218_;
}
}
}
}
else
{
lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_rchild_1197_);
lean_dec(v_val_1196_);
lean_dec(v_key_1195_);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_lchild_1194_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1232_ = lean_ctor_get(v_lchild_1194_, 3);
lean_dec(v_unused_1232_);
v_unused_1233_ = lean_ctor_get(v_lchild_1194_, 2);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_lchild_1194_, 1);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_lchild_1194_, 0);
lean_dec(v_unused_1235_);
v___x_1226_ = v_lchild_1194_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_dec(v_lchild_1194_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 3, v_r_1097_);
lean_ctor_set(v___x_1226_, 2, v_v_1096_);
lean_ctor_set(v___x_1226_, 1, v_k_1095_);
lean_ctor_set(v___x_1226_, 0, v___x_1203_);
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_r_1097_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*4, v_color_1157_);
return v___x_1229_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_1197_) == 1)
{
uint8_t v_color_1236_; 
v_color_1236_ = lean_ctor_get_uint8(v_rchild_1197_, sizeof(void*)*4);
if (v_color_1236_ == 0)
{
lean_object* v_lchild_1237_; lean_object* v_key_1238_; lean_object* v_val_1239_; lean_object* v_rchild_1240_; 
lean_dec_ref(v___x_1203_);
v_lchild_1237_ = lean_ctor_get(v_rchild_1197_, 0);
lean_inc(v_lchild_1237_);
v_key_1238_ = lean_ctor_get(v_rchild_1197_, 1);
lean_inc(v_key_1238_);
v_val_1239_ = lean_ctor_get(v_rchild_1197_, 2);
lean_inc(v_val_1239_);
v_rchild_1240_ = lean_ctor_get(v_rchild_1197_, 3);
lean_inc(v_rchild_1240_);
lean_dec_ref_known(v_rchild_1197_, 4);
v___y_1102_ = v_color_1157_;
v_a_1103_ = v_lchild_1194_;
v_kx_1104_ = v_key_1195_;
v_vx_1105_ = v_val_1196_;
v_b_1106_ = v_lchild_1237_;
v_ky_1107_ = v_key_1238_;
v_vy_1108_ = v_val_1239_;
v_c_1109_ = v_rchild_1240_;
v_kz_1110_ = v_k_1095_;
v_vz_1111_ = v_v_1096_;
v_d_1112_ = v_r_1097_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_val_1196_);
lean_dec(v_key_1195_);
lean_dec(v_lchild_1194_);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_rchild_1197_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; lean_object* v_unused_1249_; lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1248_ = lean_ctor_get(v_rchild_1197_, 3);
lean_dec(v_unused_1248_);
v_unused_1249_ = lean_ctor_get(v_rchild_1197_, 2);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_rchild_1197_, 1);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_rchild_1197_, 0);
lean_dec(v_unused_1251_);
v___x_1242_ = v_rchild_1197_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_rchild_1197_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 3, v_r_1097_);
lean_ctor_set(v___x_1242_, 2, v_v_1096_);
lean_ctor_set(v___x_1242_, 1, v_k_1095_);
lean_ctor_set(v___x_1242_, 0, v___x_1203_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1095_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1096_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_r_1097_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*4, v_color_1157_);
return v___x_1245_;
}
}
}
}
else
{
lean_object* v___x_1252_; 
lean_dec(v_rchild_1197_);
lean_dec(v_val_1196_);
lean_dec(v_key_1195_);
lean_dec(v_lchild_1194_);
v___x_1252_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1252_, 0, v___x_1203_);
lean_ctor_set(v___x_1252_, 1, v_k_1095_);
lean_ctor_set(v___x_1252_, 2, v_v_1096_);
lean_ctor_set(v___x_1252_, 3, v_r_1097_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*4, v_color_1157_);
return v___x_1252_;
}
}
}
}
}
}
else
{
goto v___jp_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object* v_00_u03b1_1269_, lean_object* v_00_u03b2_1270_, lean_object* v_l_1271_, lean_object* v_k_1272_, lean_object* v_v_1273_, lean_object* v_r_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_RBNode_balRight___redArg(v_l_1271_, v_k_1272_, v_v_1273_, v_r_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object* v_x_1276_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
return v___x_1277_;
}
else
{
lean_object* v_lchild_1278_; lean_object* v_rchild_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_lchild_1278_ = lean_ctor_get(v_x_1276_, 0);
v_rchild_1279_ = lean_ctor_get(v_x_1276_, 3);
v___x_1280_ = l_Lean_RBNode_size___redArg(v_lchild_1278_);
v___x_1281_ = l_Lean_RBNode_size___redArg(v_rchild_1279_);
v___x_1282_ = lean_nat_add(v___x_1280_, v___x_1281_);
lean_dec(v___x_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_add(v___x_1282_, v___x_1283_);
lean_dec(v___x_1282_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object* v_x_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_RBNode_size___redArg(v_x_1285_);
lean_dec(v_x_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Lean_RBNode_size___redArg(v_x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_RBNode_size(v_00_u03b1_1291_, v_00_u03b2_1292_, v_x_1293_);
lean_dec(v_x_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
if (lean_obj_tag(v_x_1295_) == 0)
{
return v_x_1296_;
}
else
{
if (lean_obj_tag(v_x_1296_) == 0)
{
return v_x_1295_;
}
else
{
uint8_t v_color_1297_; lean_object* v_lchild_1298_; lean_object* v_key_1299_; lean_object* v_val_1300_; lean_object* v_rchild_1301_; uint8_t v_color_1302_; lean_object* v_lchild_1303_; lean_object* v_key_1304_; lean_object* v_val_1305_; lean_object* v_rchild_1306_; lean_object* v_bc_1308_; lean_object* v_bc_1312_; 
v_color_1297_ = lean_ctor_get_uint8(v_x_1295_, sizeof(void*)*4);
v_lchild_1298_ = lean_ctor_get(v_x_1295_, 0);
v_key_1299_ = lean_ctor_get(v_x_1295_, 1);
v_val_1300_ = lean_ctor_get(v_x_1295_, 2);
v_rchild_1301_ = lean_ctor_get(v_x_1295_, 3);
v_color_1302_ = lean_ctor_get_uint8(v_x_1296_, sizeof(void*)*4);
v_lchild_1303_ = lean_ctor_get(v_x_1296_, 0);
v_key_1304_ = lean_ctor_get(v_x_1296_, 1);
v_val_1305_ = lean_ctor_get(v_x_1296_, 2);
v_rchild_1306_ = lean_ctor_get(v_x_1296_, 3);
if (v_color_1302_ == 0)
{
lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1349_; 
lean_inc(v_rchild_1306_);
lean_inc(v_val_1305_);
lean_inc(v_key_1304_);
lean_inc(v_lchild_1303_);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_x_1296_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; 
v_unused_1350_ = lean_ctor_get(v_x_1296_, 3);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_x_1296_, 2);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_x_1296_, 1);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_x_1296_, 0);
lean_dec(v_unused_1353_);
v___x_1316_ = v_x_1296_;
v_isShared_1317_ = v_isSharedCheck_1349_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v_x_1296_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1349_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
if (v_color_1297_ == 0)
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1340_; 
lean_inc(v_rchild_1301_);
lean_inc(v_val_1300_);
lean_inc(v_key_1299_);
lean_inc(v_lchild_1298_);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1295_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; lean_object* v_unused_1342_; lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1341_ = lean_ctor_get(v_x_1295_, 3);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_x_1295_, 2);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v_x_1295_, 1);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_x_1295_, 0);
lean_dec(v_unused_1344_);
v___x_1319_ = v_x_1295_;
v_isShared_1320_ = v_isSharedCheck_1340_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v_x_1295_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1340_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1301_, v_lchild_1303_);
if (lean_obj_tag(v___x_1321_) == 1)
{
uint8_t v_color_1322_; 
v_color_1322_ = lean_ctor_get_uint8(v___x_1321_, sizeof(void*)*4);
if (v_color_1322_ == 0)
{
lean_object* v_lchild_1323_; lean_object* v_key_1324_; lean_object* v_val_1325_; lean_object* v_rchild_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1339_; 
v_lchild_1323_ = lean_ctor_get(v___x_1321_, 0);
v_key_1324_ = lean_ctor_get(v___x_1321_, 1);
v_val_1325_ = lean_ctor_get(v___x_1321_, 2);
v_rchild_1326_ = lean_ctor_get(v___x_1321_, 3);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1328_ = v___x_1321_;
v_isShared_1329_ = v_isSharedCheck_1339_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_rchild_1326_);
lean_inc(v_val_1325_);
lean_inc(v_key_1324_);
lean_inc(v_lchild_1323_);
lean_dec(v___x_1321_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1339_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 3, v_lchild_1323_);
lean_ctor_set(v___x_1328_, 2, v_val_1300_);
lean_ctor_set(v___x_1328_, 1, v_key_1299_);
lean_ctor_set(v___x_1328_, 0, v_lchild_1298_);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_lchild_1298_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_key_1299_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_val_1300_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v_lchild_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*4, v_color_1322_);
v___x_1331_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_rchild_1326_);
v___x_1333_ = v___x_1316_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_rchild_1326_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_key_1304_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_val_1305_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_rchild_1306_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*4, v_color_1322_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 3, v___x_1333_);
lean_ctor_set(v___x_1319_, 2, v_val_1325_);
lean_ctor_set(v___x_1319_, 1, v_key_1324_);
lean_ctor_set(v___x_1319_, 0, v___x_1331_);
v___x_1335_ = v___x_1319_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_key_1324_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_val_1325_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*4, v_color_1322_);
return v___x_1335_;
}
}
}
}
}
else
{
lean_del_object(v___x_1319_);
lean_del_object(v___x_1316_);
v_bc_1312_ = v___x_1321_;
goto v___jp_1311_;
}
}
else
{
lean_del_object(v___x_1319_);
lean_del_object(v___x_1316_);
v_bc_1312_ = v___x_1321_;
goto v___jp_1311_;
}
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = l_Lean_RBNode_appendTrees___redArg(v_x_1295_, v_lchild_1303_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1345_);
v___x_1347_ = v___x_1316_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_key_1304_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_val_1305_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_rchild_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1348_, sizeof(void*)*4, v_color_1302_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1388_; 
lean_inc(v_rchild_1301_);
lean_inc(v_val_1300_);
lean_inc(v_key_1299_);
lean_inc(v_lchild_1298_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1295_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; lean_object* v_unused_1390_; lean_object* v_unused_1391_; lean_object* v_unused_1392_; 
v_unused_1389_ = lean_ctor_get(v_x_1295_, 3);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_x_1295_, 2);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_x_1295_, 1);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_x_1295_, 0);
lean_dec(v_unused_1392_);
v___x_1355_ = v_x_1295_;
v_isShared_1356_ = v_isSharedCheck_1388_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_x_1295_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1388_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
if (v_color_1297_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1301_, v_x_1296_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 3, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_lchild_1298_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_key_1299_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_val_1300_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v___x_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, sizeof(void*)*4, v_color_1297_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
else
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1383_; 
lean_inc(v_rchild_1306_);
lean_inc(v_val_1305_);
lean_inc(v_key_1304_);
lean_inc(v_lchild_1303_);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1296_);
if (v_isSharedCheck_1383_ == 0)
{
lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1384_ = lean_ctor_get(v_x_1296_, 3);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_x_1296_, 2);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_x_1296_, 1);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_x_1296_, 0);
lean_dec(v_unused_1387_);
v___x_1362_ = v_x_1296_;
v_isShared_1363_ = v_isSharedCheck_1383_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v_x_1296_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1383_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1301_, v_lchild_1303_);
if (lean_obj_tag(v___x_1364_) == 1)
{
uint8_t v_color_1365_; 
v_color_1365_ = lean_ctor_get_uint8(v___x_1364_, sizeof(void*)*4);
if (v_color_1365_ == 0)
{
lean_object* v_lchild_1366_; lean_object* v_key_1367_; lean_object* v_val_1368_; lean_object* v_rchild_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1382_; 
v_lchild_1366_ = lean_ctor_get(v___x_1364_, 0);
v_key_1367_ = lean_ctor_get(v___x_1364_, 1);
v_val_1368_ = lean_ctor_get(v___x_1364_, 2);
v_rchild_1369_ = lean_ctor_get(v___x_1364_, 3);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1371_ = v___x_1364_;
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_rchild_1369_);
lean_inc(v_val_1368_);
lean_inc(v_key_1367_);
lean_inc(v_lchild_1366_);
lean_dec(v___x_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 3, v_lchild_1366_);
lean_ctor_set(v___x_1371_, 2, v_val_1300_);
lean_ctor_set(v___x_1371_, 1, v_key_1299_);
lean_ctor_set(v___x_1371_, 0, v_lchild_1298_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_lchild_1298_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_key_1299_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_val_1300_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v_lchild_1366_);
v___x_1374_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*4, v_color_1297_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_rchild_1369_);
v___x_1376_ = v___x_1362_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_rchild_1369_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_key_1304_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_val_1305_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_rchild_1306_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*4, v_color_1297_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 3, v___x_1376_);
lean_ctor_set(v___x_1355_, 2, v_val_1368_);
lean_ctor_set(v___x_1355_, 1, v_key_1367_);
lean_ctor_set(v___x_1355_, 0, v___x_1374_);
v___x_1378_ = v___x_1355_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_key_1367_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_val_1368_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*4, v_color_1365_);
return v___x_1378_;
}
}
}
}
}
else
{
lean_del_object(v___x_1362_);
lean_del_object(v___x_1355_);
v_bc_1308_ = v___x_1364_;
goto v___jp_1307_;
}
}
else
{
lean_del_object(v___x_1362_);
lean_del_object(v___x_1355_);
v_bc_1308_ = v___x_1364_;
goto v___jp_1307_;
}
}
}
}
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1309_, 0, v_bc_1308_);
lean_ctor_set(v___x_1309_, 1, v_key_1304_);
lean_ctor_set(v___x_1309_, 2, v_val_1305_);
lean_ctor_set(v___x_1309_, 3, v_rchild_1306_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*4, v_color_1297_);
v___x_1310_ = l_Lean_RBNode_balLeft___redArg(v_lchild_1298_, v_key_1299_, v_val_1300_, v___x_1309_);
return v___x_1310_;
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1313_, 0, v_bc_1312_);
lean_ctor_set(v___x_1313_, 1, v_key_1304_);
lean_ctor_set(v___x_1313_, 2, v_val_1305_);
lean_ctor_set(v___x_1313_, 3, v_rchild_1306_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*4, v_color_1297_);
v___x_1314_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1314_, 0, v_lchild_1298_);
lean_ctor_set(v___x_1314_, 1, v_key_1299_);
lean_ctor_set(v___x_1314_, 2, v_val_1300_);
lean_ctor_set(v___x_1314_, 3, v___x_1313_);
lean_ctor_set_uint8(v___x_1314_, sizeof(void*)*4, v_color_1297_);
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* v_00_u03b1_1393_, lean_object* v_00_u03b2_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_RBNode_appendTrees___redArg(v_x_1395_, v_x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_h__1_1400_, lean_object* v_h__2_1401_, lean_object* v_h__3_1402_, lean_object* v_h__4_1403_, lean_object* v_h__5_1404_, lean_object* v_h__6_1405_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v___x_1406_; 
lean_dec(v_h__6_1405_);
lean_dec(v_h__5_1404_);
lean_dec(v_h__4_1403_);
lean_dec(v_h__3_1402_);
lean_dec(v_h__2_1401_);
v___x_1406_ = lean_apply_1(v_h__1_1400_, v_x_1399_);
return v___x_1406_;
}
else
{
lean_dec(v_h__1_1400_);
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_h__6_1405_);
lean_dec(v_h__5_1404_);
lean_dec(v_h__4_1403_);
lean_dec(v_h__3_1402_);
v___x_1407_ = lean_apply_2(v_h__2_1401_, v_x_1398_, lean_box(0));
return v___x_1407_;
}
else
{
uint8_t v_color_1408_; 
lean_dec(v_h__2_1401_);
v_color_1408_ = lean_ctor_get_uint8(v_x_1399_, sizeof(void*)*4);
if (v_color_1408_ == 0)
{
uint8_t v_color_1409_; 
lean_dec(v_h__6_1405_);
lean_dec(v_h__4_1403_);
v_color_1409_ = lean_ctor_get_uint8(v_x_1398_, sizeof(void*)*4);
if (v_color_1409_ == 0)
{
lean_object* v_lchild_1410_; lean_object* v_key_1411_; lean_object* v_val_1412_; lean_object* v_rchild_1413_; lean_object* v_lchild_1414_; lean_object* v_key_1415_; lean_object* v_val_1416_; lean_object* v_rchild_1417_; lean_object* v___x_1418_; 
lean_dec(v_h__5_1404_);
v_lchild_1410_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_lchild_1410_);
v_key_1411_ = lean_ctor_get(v_x_1398_, 1);
lean_inc(v_key_1411_);
v_val_1412_ = lean_ctor_get(v_x_1398_, 2);
lean_inc(v_val_1412_);
v_rchild_1413_ = lean_ctor_get(v_x_1398_, 3);
lean_inc(v_rchild_1413_);
lean_dec_ref_known(v_x_1398_, 4);
v_lchild_1414_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_lchild_1414_);
v_key_1415_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_key_1415_);
v_val_1416_ = lean_ctor_get(v_x_1399_, 2);
lean_inc(v_val_1416_);
v_rchild_1417_ = lean_ctor_get(v_x_1399_, 3);
lean_inc(v_rchild_1417_);
lean_dec_ref_known(v_x_1399_, 4);
v___x_1418_ = lean_apply_8(v_h__3_1402_, v_lchild_1410_, v_key_1411_, v_val_1412_, v_rchild_1413_, v_lchild_1414_, v_key_1415_, v_val_1416_, v_rchild_1417_);
return v___x_1418_;
}
else
{
lean_object* v_lchild_1419_; lean_object* v_key_1420_; lean_object* v_val_1421_; lean_object* v_rchild_1422_; lean_object* v___x_1423_; 
lean_dec(v_h__3_1402_);
v_lchild_1419_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_lchild_1419_);
v_key_1420_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_key_1420_);
v_val_1421_ = lean_ctor_get(v_x_1399_, 2);
lean_inc(v_val_1421_);
v_rchild_1422_ = lean_ctor_get(v_x_1399_, 3);
lean_inc(v_rchild_1422_);
lean_dec_ref_known(v_x_1399_, 4);
v___x_1423_ = lean_apply_7(v_h__5_1404_, v_x_1398_, v_lchild_1419_, v_key_1420_, v_val_1421_, v_rchild_1422_, lean_box(0), lean_box(0));
return v___x_1423_;
}
}
else
{
uint8_t v_color_1424_; 
lean_dec(v_h__5_1404_);
lean_dec(v_h__3_1402_);
v_color_1424_ = lean_ctor_get_uint8(v_x_1398_, sizeof(void*)*4);
if (v_color_1424_ == 0)
{
lean_object* v_lchild_1425_; lean_object* v_key_1426_; lean_object* v_val_1427_; lean_object* v_rchild_1428_; lean_object* v___x_1429_; 
lean_dec(v_h__4_1403_);
v_lchild_1425_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_lchild_1425_);
v_key_1426_ = lean_ctor_get(v_x_1398_, 1);
lean_inc(v_key_1426_);
v_val_1427_ = lean_ctor_get(v_x_1398_, 2);
lean_inc(v_val_1427_);
v_rchild_1428_ = lean_ctor_get(v_x_1398_, 3);
lean_inc(v_rchild_1428_);
lean_dec_ref_known(v_x_1398_, 4);
v___x_1429_ = lean_apply_7(v_h__6_1405_, v_lchild_1425_, v_key_1426_, v_val_1427_, v_rchild_1428_, v_x_1399_, lean_box(0), lean_box(0));
return v___x_1429_;
}
else
{
lean_object* v_lchild_1430_; lean_object* v_key_1431_; lean_object* v_val_1432_; lean_object* v_rchild_1433_; lean_object* v_lchild_1434_; lean_object* v_key_1435_; lean_object* v_val_1436_; lean_object* v_rchild_1437_; lean_object* v___x_1438_; 
lean_dec(v_h__6_1405_);
v_lchild_1430_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_lchild_1430_);
v_key_1431_ = lean_ctor_get(v_x_1398_, 1);
lean_inc(v_key_1431_);
v_val_1432_ = lean_ctor_get(v_x_1398_, 2);
lean_inc(v_val_1432_);
v_rchild_1433_ = lean_ctor_get(v_x_1398_, 3);
lean_inc(v_rchild_1433_);
lean_dec_ref_known(v_x_1398_, 4);
v_lchild_1434_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_lchild_1434_);
v_key_1435_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_key_1435_);
v_val_1436_ = lean_ctor_get(v_x_1399_, 2);
lean_inc(v_val_1436_);
v_rchild_1437_ = lean_ctor_get(v_x_1399_, 3);
lean_inc(v_rchild_1437_);
lean_dec_ref_known(v_x_1399_, 4);
v___x_1438_ = lean_apply_8(v_h__4_1403_, v_lchild_1430_, v_key_1431_, v_val_1432_, v_rchild_1433_, v_lchild_1434_, v_key_1435_, v_val_1436_, v_rchild_1437_);
return v___x_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* v_00_u03b1_1439_, lean_object* v_00_u03b2_1440_, lean_object* v_motive_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_h__1_1444_, lean_object* v_h__2_1445_, lean_object* v_h__3_1446_, lean_object* v_h__4_1447_, lean_object* v_h__5_1448_, lean_object* v_h__6_1449_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_object* v___x_1450_; 
lean_dec(v_h__6_1449_);
lean_dec(v_h__5_1448_);
lean_dec(v_h__4_1447_);
lean_dec(v_h__3_1446_);
lean_dec(v_h__2_1445_);
v___x_1450_ = lean_apply_1(v_h__1_1444_, v_x_1443_);
return v___x_1450_;
}
else
{
lean_dec(v_h__1_1444_);
if (lean_obj_tag(v_x_1443_) == 0)
{
lean_object* v___x_1451_; 
lean_dec(v_h__6_1449_);
lean_dec(v_h__5_1448_);
lean_dec(v_h__4_1447_);
lean_dec(v_h__3_1446_);
v___x_1451_ = lean_apply_2(v_h__2_1445_, v_x_1442_, lean_box(0));
return v___x_1451_;
}
else
{
uint8_t v_color_1452_; 
lean_dec(v_h__2_1445_);
v_color_1452_ = lean_ctor_get_uint8(v_x_1443_, sizeof(void*)*4);
if (v_color_1452_ == 0)
{
uint8_t v_color_1453_; 
lean_dec(v_h__6_1449_);
lean_dec(v_h__4_1447_);
v_color_1453_ = lean_ctor_get_uint8(v_x_1442_, sizeof(void*)*4);
if (v_color_1453_ == 0)
{
lean_object* v_lchild_1454_; lean_object* v_key_1455_; lean_object* v_val_1456_; lean_object* v_rchild_1457_; lean_object* v_lchild_1458_; lean_object* v_key_1459_; lean_object* v_val_1460_; lean_object* v_rchild_1461_; lean_object* v___x_1462_; 
lean_dec(v_h__5_1448_);
v_lchild_1454_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_lchild_1454_);
v_key_1455_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_key_1455_);
v_val_1456_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_val_1456_);
v_rchild_1457_ = lean_ctor_get(v_x_1442_, 3);
lean_inc(v_rchild_1457_);
lean_dec_ref_known(v_x_1442_, 4);
v_lchild_1458_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_lchild_1458_);
v_key_1459_ = lean_ctor_get(v_x_1443_, 1);
lean_inc(v_key_1459_);
v_val_1460_ = lean_ctor_get(v_x_1443_, 2);
lean_inc(v_val_1460_);
v_rchild_1461_ = lean_ctor_get(v_x_1443_, 3);
lean_inc(v_rchild_1461_);
lean_dec_ref_known(v_x_1443_, 4);
v___x_1462_ = lean_apply_8(v_h__3_1446_, v_lchild_1454_, v_key_1455_, v_val_1456_, v_rchild_1457_, v_lchild_1458_, v_key_1459_, v_val_1460_, v_rchild_1461_);
return v___x_1462_;
}
else
{
lean_object* v_lchild_1463_; lean_object* v_key_1464_; lean_object* v_val_1465_; lean_object* v_rchild_1466_; lean_object* v___x_1467_; 
lean_dec(v_h__3_1446_);
v_lchild_1463_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_lchild_1463_);
v_key_1464_ = lean_ctor_get(v_x_1443_, 1);
lean_inc(v_key_1464_);
v_val_1465_ = lean_ctor_get(v_x_1443_, 2);
lean_inc(v_val_1465_);
v_rchild_1466_ = lean_ctor_get(v_x_1443_, 3);
lean_inc(v_rchild_1466_);
lean_dec_ref_known(v_x_1443_, 4);
v___x_1467_ = lean_apply_7(v_h__5_1448_, v_x_1442_, v_lchild_1463_, v_key_1464_, v_val_1465_, v_rchild_1466_, lean_box(0), lean_box(0));
return v___x_1467_;
}
}
else
{
uint8_t v_color_1468_; 
lean_dec(v_h__5_1448_);
lean_dec(v_h__3_1446_);
v_color_1468_ = lean_ctor_get_uint8(v_x_1442_, sizeof(void*)*4);
if (v_color_1468_ == 0)
{
lean_object* v_lchild_1469_; lean_object* v_key_1470_; lean_object* v_val_1471_; lean_object* v_rchild_1472_; lean_object* v___x_1473_; 
lean_dec(v_h__4_1447_);
v_lchild_1469_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_lchild_1469_);
v_key_1470_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_key_1470_);
v_val_1471_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_val_1471_);
v_rchild_1472_ = lean_ctor_get(v_x_1442_, 3);
lean_inc(v_rchild_1472_);
lean_dec_ref_known(v_x_1442_, 4);
v___x_1473_ = lean_apply_7(v_h__6_1449_, v_lchild_1469_, v_key_1470_, v_val_1471_, v_rchild_1472_, v_x_1443_, lean_box(0), lean_box(0));
return v___x_1473_;
}
else
{
lean_object* v_lchild_1474_; lean_object* v_key_1475_; lean_object* v_val_1476_; lean_object* v_rchild_1477_; lean_object* v_lchild_1478_; lean_object* v_key_1479_; lean_object* v_val_1480_; lean_object* v_rchild_1481_; lean_object* v___x_1482_; 
lean_dec(v_h__6_1449_);
v_lchild_1474_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_lchild_1474_);
v_key_1475_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_key_1475_);
v_val_1476_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_val_1476_);
v_rchild_1477_ = lean_ctor_get(v_x_1442_, 3);
lean_inc(v_rchild_1477_);
lean_dec_ref_known(v_x_1442_, 4);
v_lchild_1478_ = lean_ctor_get(v_x_1443_, 0);
lean_inc(v_lchild_1478_);
v_key_1479_ = lean_ctor_get(v_x_1443_, 1);
lean_inc(v_key_1479_);
v_val_1480_ = lean_ctor_get(v_x_1443_, 2);
lean_inc(v_val_1480_);
v_rchild_1481_ = lean_ctor_get(v_x_1443_, 3);
lean_inc(v_rchild_1481_);
lean_dec_ref_known(v_x_1443_, 4);
v___x_1482_ = lean_apply_8(v_h__4_1447_, v_lchild_1474_, v_key_1475_, v_val_1476_, v_rchild_1477_, v_lchild_1478_, v_key_1479_, v_val_1480_, v_rchild_1481_);
return v___x_1482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* v_x_1483_, lean_object* v_h__1_1484_, lean_object* v_h__2_1485_){
_start:
{
if (lean_obj_tag(v_x_1483_) == 1)
{
uint8_t v_color_1486_; 
v_color_1486_ = lean_ctor_get_uint8(v_x_1483_, sizeof(void*)*4);
if (v_color_1486_ == 0)
{
lean_object* v_lchild_1487_; lean_object* v_key_1488_; lean_object* v_val_1489_; lean_object* v_rchild_1490_; lean_object* v___x_1491_; 
lean_dec(v_h__2_1485_);
v_lchild_1487_ = lean_ctor_get(v_x_1483_, 0);
lean_inc(v_lchild_1487_);
v_key_1488_ = lean_ctor_get(v_x_1483_, 1);
lean_inc(v_key_1488_);
v_val_1489_ = lean_ctor_get(v_x_1483_, 2);
lean_inc(v_val_1489_);
v_rchild_1490_ = lean_ctor_get(v_x_1483_, 3);
lean_inc(v_rchild_1490_);
lean_dec_ref_known(v_x_1483_, 4);
v___x_1491_ = lean_apply_4(v_h__1_1484_, v_lchild_1487_, v_key_1488_, v_val_1489_, v_rchild_1490_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_h__1_1484_);
v___x_1492_ = lean_apply_2(v_h__2_1485_, v_x_1483_, lean_box(0));
return v___x_1492_;
}
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_h__1_1484_);
v___x_1493_ = lean_apply_2(v_h__2_1485_, v_x_1483_, lean_box(0));
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* v_00_u03b1_1494_, lean_object* v_00_u03b2_1495_, lean_object* v_motive_1496_, lean_object* v_x_1497_, lean_object* v_h__1_1498_, lean_object* v_h__2_1499_){
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
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* v_cmp_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 0)
{
lean_dec(v_x_1509_);
lean_dec_ref(v_cmp_1508_);
return v_x_1510_;
}
else
{
lean_object* v_lchild_1511_; lean_object* v_key_1512_; lean_object* v_val_1513_; lean_object* v_rchild_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1537_; 
v_lchild_1511_ = lean_ctor_get(v_x_1510_, 0);
v_key_1512_ = lean_ctor_get(v_x_1510_, 1);
v_val_1513_ = lean_ctor_get(v_x_1510_, 2);
v_rchild_1514_ = lean_ctor_get(v_x_1510_, 3);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1510_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1516_ = v_x_1510_;
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_rchild_1514_);
lean_inc(v_val_1513_);
lean_inc(v_key_1512_);
lean_inc(v_lchild_1511_);
lean_dec(v_x_1510_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
lean_inc_ref(v_cmp_1508_);
lean_inc(v_key_1512_);
lean_inc(v_x_1509_);
v___x_1518_ = lean_apply_2(v_cmp_1508_, v_x_1509_, v_key_1512_);
v___x_1519_ = lean_unbox(v___x_1518_);
switch(v___x_1519_)
{
case 0:
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1511_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1521_ = 0;
v___x_1522_ = l_Lean_RBNode_del___redArg(v_cmp_1508_, v_x_1509_, v_lchild_1511_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1522_);
v___x_1524_ = v___x_1516_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_key_1512_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_val_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_rchild_1514_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_ctor_set_uint8(v___x_1524_, sizeof(void*)*4, v___x_1521_);
return v___x_1524_;
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_del_object(v___x_1516_);
v___x_1526_ = l_Lean_RBNode_del___redArg(v_cmp_1508_, v_x_1509_, v_lchild_1511_);
v___x_1527_ = l_Lean_RBNode_balLeft___redArg(v___x_1526_, v_key_1512_, v_val_1513_, v_rchild_1514_);
return v___x_1527_;
}
}
case 1:
{
lean_object* v___x_1528_; 
lean_del_object(v___x_1516_);
lean_dec(v_val_1513_);
lean_dec(v_key_1512_);
lean_dec(v_x_1509_);
lean_dec_ref(v_cmp_1508_);
v___x_1528_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_1511_, v_rchild_1514_);
return v___x_1528_;
}
default: 
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1514_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1530_ = 0;
v___x_1531_ = l_Lean_RBNode_del___redArg(v_cmp_1508_, v_x_1509_, v_rchild_1514_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 3, v___x_1531_);
v___x_1533_ = v___x_1516_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_lchild_1511_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_key_1512_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_val_1513_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_ctor_set_uint8(v___x_1533_, sizeof(void*)*4, v___x_1530_);
return v___x_1533_;
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_del_object(v___x_1516_);
v___x_1535_ = l_Lean_RBNode_del___redArg(v_cmp_1508_, v_x_1509_, v_rchild_1514_);
v___x_1536_ = l_Lean_RBNode_balRight___redArg(v_lchild_1511_, v_key_1512_, v_val_1513_, v___x_1535_);
return v___x_1536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* v_00_u03b1_1538_, lean_object* v_00_u03b2_1539_, lean_object* v_cmp_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_RBNode_del___redArg(v_cmp_1540_, v_x_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* v_cmp_1544_, lean_object* v_x_1545_, lean_object* v_t_1546_){
_start:
{
lean_object* v_t_1547_; lean_object* v___x_1548_; 
v_t_1547_ = l_Lean_RBNode_del___redArg(v_cmp_1544_, v_x_1545_, v_t_1546_);
v___x_1548_ = l_Lean_RBNode_setBlack___redArg(v_t_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* v_00_u03b1_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_cmp_1551_, lean_object* v_x_1552_, lean_object* v_t_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_RBNode_erase___redArg(v_cmp_1551_, v_x_1552_, v_t_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* v_cmp_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1556_) == 0)
{
lean_object* v___x_1558_; 
lean_dec(v_x_1557_);
lean_dec_ref(v_cmp_1555_);
v___x_1558_ = lean_box(0);
return v___x_1558_;
}
else
{
lean_object* v_lchild_1559_; lean_object* v_key_1560_; lean_object* v_val_1561_; lean_object* v_rchild_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_lchild_1559_ = lean_ctor_get(v_x_1556_, 0);
lean_inc(v_lchild_1559_);
v_key_1560_ = lean_ctor_get(v_x_1556_, 1);
lean_inc_n(v_key_1560_, 2);
v_val_1561_ = lean_ctor_get(v_x_1556_, 2);
lean_inc(v_val_1561_);
v_rchild_1562_ = lean_ctor_get(v_x_1556_, 3);
lean_inc(v_rchild_1562_);
lean_dec_ref_known(v_x_1556_, 4);
lean_inc_ref(v_cmp_1555_);
lean_inc(v_x_1557_);
v___x_1563_ = lean_apply_2(v_cmp_1555_, v_x_1557_, v_key_1560_);
v___x_1564_ = lean_unbox(v___x_1563_);
switch(v___x_1564_)
{
case 0:
{
lean_dec(v_rchild_1562_);
lean_dec(v_val_1561_);
lean_dec(v_key_1560_);
v_x_1556_ = v_lchild_1559_;
goto _start;
}
case 1:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec(v_rchild_1562_);
lean_dec(v_lchild_1559_);
lean_dec(v_x_1557_);
lean_dec_ref(v_cmp_1555_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_key_1560_);
lean_ctor_set(v___x_1566_, 1, v_val_1561_);
v___x_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
default: 
{
lean_dec(v_val_1561_);
lean_dec(v_key_1560_);
lean_dec(v_lchild_1559_);
v_x_1556_ = v_rchild_1562_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_cmp_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_RBNode_findCore___redArg(v_cmp_1571_, v_x_1572_, v_x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* v_cmp_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
if (lean_obj_tag(v_x_1576_) == 0)
{
lean_object* v___x_1578_; 
lean_dec(v_x_1577_);
lean_dec_ref(v_cmp_1575_);
v___x_1578_ = lean_box(0);
return v___x_1578_;
}
else
{
lean_object* v_lchild_1579_; lean_object* v_key_1580_; lean_object* v_val_1581_; lean_object* v_rchild_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_lchild_1579_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_lchild_1579_);
v_key_1580_ = lean_ctor_get(v_x_1576_, 1);
lean_inc(v_key_1580_);
v_val_1581_ = lean_ctor_get(v_x_1576_, 2);
lean_inc(v_val_1581_);
v_rchild_1582_ = lean_ctor_get(v_x_1576_, 3);
lean_inc(v_rchild_1582_);
lean_dec_ref_known(v_x_1576_, 4);
lean_inc_ref(v_cmp_1575_);
lean_inc(v_x_1577_);
v___x_1583_ = lean_apply_2(v_cmp_1575_, v_x_1577_, v_key_1580_);
v___x_1584_ = lean_unbox(v___x_1583_);
switch(v___x_1584_)
{
case 0:
{
lean_dec(v_rchild_1582_);
lean_dec(v_val_1581_);
v_x_1576_ = v_lchild_1579_;
goto _start;
}
case 1:
{
lean_object* v___x_1586_; 
lean_dec(v_rchild_1582_);
lean_dec(v_lchild_1579_);
lean_dec(v_x_1577_);
lean_dec_ref(v_cmp_1575_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_val_1581_);
return v___x_1586_;
}
default: 
{
lean_dec(v_val_1581_);
lean_dec(v_lchild_1579_);
v_x_1576_ = v_rchild_1582_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* v_00_u03b1_1588_, lean_object* v_cmp_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_RBNode_find___redArg(v_cmp_1589_, v_x_1591_, v_x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* v_cmp_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_dec(v_x_1596_);
lean_dec_ref(v_cmp_1594_);
return v_x_1597_;
}
else
{
lean_object* v_lchild_1598_; lean_object* v_key_1599_; lean_object* v_val_1600_; lean_object* v_rchild_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_lchild_1598_ = lean_ctor_get(v_x_1595_, 0);
lean_inc(v_lchild_1598_);
v_key_1599_ = lean_ctor_get(v_x_1595_, 1);
lean_inc_n(v_key_1599_, 2);
v_val_1600_ = lean_ctor_get(v_x_1595_, 2);
lean_inc(v_val_1600_);
v_rchild_1601_ = lean_ctor_get(v_x_1595_, 3);
lean_inc(v_rchild_1601_);
lean_dec_ref_known(v_x_1595_, 4);
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
lean_dec(v_key_1599_);
v_x_1595_ = v_lchild_1598_;
goto _start;
}
case 1:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_rchild_1601_);
lean_dec(v_lchild_1598_);
lean_dec(v_x_1597_);
lean_dec(v_x_1596_);
lean_dec_ref(v_cmp_1594_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_key_1599_);
lean_ctor_set(v___x_1605_, 1, v_val_1600_);
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1605_);
return v___x_1606_;
}
default: 
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_lchild_1598_);
lean_dec(v_x_1597_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_key_1599_);
lean_ctor_set(v___x_1607_, 1, v_val_1600_);
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
v_x_1595_ = v_rchild_1601_;
v_x_1597_ = v___x_1608_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* v_00_u03b1_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_cmp_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_1612_, v_x_1613_, v_x_1614_, v_x_1615_);
return v___x_1616_;
}
}
lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t v_color_1617_, lean_object* v_key_1618_, lean_object* v_x1_1619_, lean_object* v_x2_1620_, lean_object* v_x3_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1622_, 0, v_x1_1619_);
lean_ctor_set(v___x_1622_, 1, v_key_1618_);
lean_ctor_set(v___x_1622_, 2, v_x2_1620_);
lean_ctor_set(v___x_1622_, 3, v_x3_1621_);
lean_ctor_set_uint8(v___x_1622_, sizeof(void*)*4, v_color_1617_);
return v___x_1622_;
}
}
LEAN_EXPORT void l_Lean_RBNode_mapM___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_color_1617_ = stack[0].m_num;
lean_object* v_key_1618_ = stack[1].m_obj;
lean_object* v_x1_1619_ = stack[2].m_obj;
lean_object* v_x2_1620_ = stack[3].m_obj;
lean_object* v_x3_1621_ = stack[4].m_obj;
lean_object* v_res_1623_;
v_res_1623_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_1617_, v_key_1618_, v_x1_1619_, v_x2_1620_, v_x3_1621_);
stack->m_obj
 = v_res_1623_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* v_color_1624_, lean_object* v_key_1625_, lean_object* v_x1_1626_, lean_object* v_x2_1627_, lean_object* v_x3_1628_){
_start:
{
uint8_t v_color_88__boxed_1629_; lean_object* v_res_1630_; 
v_color_88__boxed_1629_ = lean_unbox(v_color_1624_);
v_res_1630_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_88__boxed_1629_, v_key_1625_, v_x1_1626_, v_x2_1627_, v_x3_1628_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* v_f_1631_, lean_object* v_key_1632_, lean_object* v_val_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_apply_2(v_f_1631_, v_key_1632_, v_val_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* v_inst_1636_, lean_object* v_f_1637_, lean_object* v_lchild_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_RBNode_mapM___redArg(v_inst_1636_, v_f_1637_, v_lchild_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* v_inst_1641_, lean_object* v_f_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_toPure_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_f_1642_);
v_toPure_1644_ = lean_ctor_get(v_inst_1641_, 1);
lean_inc(v_toPure_1644_);
lean_dec_ref(v_inst_1641_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_apply_2(v_toPure_1644_, lean_box(0), v___x_1645_);
return v___x_1646_;
}
else
{
lean_object* v_toPure_1647_; lean_object* v_toSeq_1648_; uint8_t v_color_1649_; lean_object* v_lchild_1650_; lean_object* v_key_1651_; lean_object* v_val_1652_; lean_object* v_rchild_1653_; lean_object* v___f_1654_; lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_toPure_1647_ = lean_ctor_get(v_inst_1641_, 1);
lean_inc(v_toPure_1647_);
v_toSeq_1648_ = lean_ctor_get(v_inst_1641_, 2);
lean_inc_n(v_toSeq_1648_, 3);
v_color_1649_ = lean_ctor_get_uint8(v_x_1643_, sizeof(void*)*4);
v_lchild_1650_ = lean_ctor_get(v_x_1643_, 0);
lean_inc(v_lchild_1650_);
v_key_1651_ = lean_ctor_get(v_x_1643_, 1);
lean_inc_n(v_key_1651_, 2);
v_val_1652_ = lean_ctor_get(v_x_1643_, 2);
lean_inc(v_val_1652_);
v_rchild_1653_ = lean_ctor_get(v_x_1643_, 3);
lean_inc(v_rchild_1653_);
lean_dec_ref_known(v_x_1643_, 4);
lean_inc_n(v_f_1642_, 2);
lean_inc_ref(v_inst_1641_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1654_, 0, v_inst_1641_);
lean_closure_set(v___f_1654_, 1, v_f_1642_);
lean_closure_set(v___f_1654_, 2, v_rchild_1653_);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1655_, 0, v_f_1642_);
lean_closure_set(v___f_1655_, 1, v_key_1651_);
lean_closure_set(v___f_1655_, 2, v_val_1652_);
v___f_1656_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1656_, 0, v_inst_1641_);
lean_closure_set(v___f_1656_, 1, v_f_1642_);
lean_closure_set(v___f_1656_, 2, v_lchild_1650_);
v___x_1657_ = lean_box(v_color_1649_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1658_, 0, v___x_1657_);
lean_closure_set(v___f_1658_, 1, v_key_1651_);
v___x_1659_ = lean_apply_2(v_toPure_1647_, lean_box(0), v___f_1658_);
v___x_1660_ = lean_apply_4(v_toSeq_1648_, lean_box(0), lean_box(0), v___x_1659_, v___f_1656_);
v___x_1661_ = lean_apply_4(v_toSeq_1648_, lean_box(0), lean_box(0), v___x_1660_, v___f_1655_);
v___x_1662_ = lean_apply_4(v_toSeq_1648_, lean_box(0), lean_box(0), v___x_1661_, v___f_1654_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* v_inst_1663_, lean_object* v_f_1664_, lean_object* v_rchild_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_RBNode_mapM___redArg(v_inst_1663_, v_f_1664_, v_rchild_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_00_u03b3_1670_, lean_object* v_M_1671_, lean_object* v_inst_1672_, lean_object* v_f_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_RBNode_mapM___redArg(v_inst_1672_, v_f_1673_, v_x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* v_f_1676_, lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v___x_1678_; 
lean_dec(v_f_1676_);
v___x_1678_ = lean_box(0);
return v___x_1678_;
}
else
{
uint8_t v_color_1679_; lean_object* v_lchild_1680_; lean_object* v_key_1681_; lean_object* v_val_1682_; lean_object* v_rchild_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1693_; 
v_color_1679_ = lean_ctor_get_uint8(v_x_1677_, sizeof(void*)*4);
v_lchild_1680_ = lean_ctor_get(v_x_1677_, 0);
v_key_1681_ = lean_ctor_get(v_x_1677_, 1);
v_val_1682_ = lean_ctor_get(v_x_1677_, 2);
v_rchild_1683_ = lean_ctor_get(v_x_1677_, 3);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1677_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1685_ = v_x_1677_;
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_rchild_1683_);
lean_inc(v_val_1682_);
lean_inc(v_key_1681_);
lean_inc(v_lchild_1680_);
lean_dec(v_x_1677_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_inc_n(v_f_1676_, 2);
v___x_1687_ = l_Lean_RBNode_map___redArg(v_f_1676_, v_lchild_1680_);
lean_inc(v_key_1681_);
v___x_1688_ = lean_apply_2(v_f_1676_, v_key_1681_, v_val_1682_);
v___x_1689_ = l_Lean_RBNode_map___redArg(v_f_1676_, v_rchild_1683_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 3, v___x_1689_);
lean_ctor_set(v___x_1685_, 2, v___x_1688_);
lean_ctor_set(v___x_1685_, 0, v___x_1687_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_key_1681_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v___x_1689_);
lean_ctor_set_uint8(v_reuseFailAlloc_1692_, sizeof(void*)*4, v_color_1679_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* v_00_u03b1_1694_, lean_object* v_00_u03b2_1695_, lean_object* v_00_u03b3_1696_, lean_object* v_f_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_RBNode_map___redArg(v_f_1697_, v_x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
if (lean_obj_tag(v_x_1701_) == 0)
{
return v_x_1700_;
}
else
{
lean_object* v_lchild_1702_; lean_object* v_key_1703_; lean_object* v_val_1704_; lean_object* v_rchild_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_lchild_1702_ = lean_ctor_get(v_x_1701_, 0);
v_key_1703_ = lean_ctor_get(v_x_1701_, 1);
v_val_1704_ = lean_ctor_get(v_x_1701_, 2);
v_rchild_1705_ = lean_ctor_get(v_x_1701_, 3);
v___x_1706_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1700_, v_lchild_1702_);
lean_inc(v_val_1704_);
lean_inc(v_key_1703_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_key_1703_);
lean_ctor_set(v___x_1707_, 1, v_val_1704_);
v___x_1708_ = lean_array_push(v___x_1706_, v___x_1707_);
v_x_1700_ = v___x_1708_;
v_x_1701_ = v_rchild_1705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1710_, v_x_1711_);
lean_dec(v_x_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* v_n_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
v___x_1717_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_1716_, v_n_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* v_n_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_RBNode_toArray___redArg(v_n_1718_);
lean_dec(v_n_1718_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_n_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_RBNode_toArray___redArg(v_n_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_n_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_RBNode_toArray(v_00_u03b1_1724_, v_00_u03b2_1725_, v_n_1726_);
lean_dec(v_n_1726_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1730_, v_x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* v_00_u03b1_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(v_00_u03b1_1733_, v_00_u03b2_1734_, v_x_1735_, v_x_1736_);
lean_dec(v_x_1736_);
return v_res_1737_;
}
}
lean_object* l_Lean_RBNode_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_box(0);
return v___x_1739_;
}
}
LEAN_EXPORT void l_Lean_RBNode_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1740_;
v_res_1740_ = l_Lean_RBNode_instEmptyCollection___redArg();
stack->m_obj
 = v_res_1740_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg___boxed(lean_object* v___dummy_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_RBNode_instEmptyCollection___redArg();
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b2_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_box(0);
return v___x_1745_;
}
}
lean_object* l_Lean_mkRBMap___redArg(){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_box(0);
return v___x_1747_;
}
}
LEAN_EXPORT void l_Lean_mkRBMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1748_;
v_res_1748_ = l_Lean_mkRBMap___redArg();
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg___boxed(lean_object* v___dummy_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_mkRBMap___redArg();
return v_res_1750_;
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
lean_object* l_Lean_RBMap_empty___redArg(){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_box(0);
return v___x_1760_;
}
}
LEAN_EXPORT void l_Lean_RBMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1761_;
v_res_1761_ = l_Lean_RBMap_empty___redArg();
stack->m_obj
 = v_res_1761_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg___boxed(lean_object* v___dummy_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_RBMap_empty___redArg();
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_box(0);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_RBMap_empty(v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec_ref(v___y_1770_);
return v_res_1771_;
}
}
lean_object* l_Lean_instEmptyCollectionRBMap___redArg(){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_box(0);
return v___x_1773_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionRBMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1774_;
v_res_1774_ = l_Lean_instEmptyCollectionRBMap___redArg();
stack->m_obj
 = v_res_1774_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg___boxed(lean_object* v___dummy_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_instEmptyCollectionRBMap___redArg();
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* v_00_u03b1_1777_, lean_object* v_00_u03b2_1778_, lean_object* v_cmp_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_box(0);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_00_u03b2_1782_, lean_object* v_cmp_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_1781_, v_00_u03b2_1782_, v_cmp_1783_);
lean_dec_ref(v_cmp_1783_);
return v_res_1784_;
}
}
lean_object* l_Lean_instInhabitedRBMap___redArg(){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedRBMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1787_;
v_res_1787_ = l_Lean_instInhabitedRBMap___redArg();
stack->m_obj
 = v_res_1787_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg___boxed(lean_object* v___dummy_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_instInhabitedRBMap___redArg();
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_cmp_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_box(0);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_00_u03b2_1795_, lean_object* v_cmp_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_instInhabitedRBMap(v_00_u03b1_1794_, v_00_u03b2_1795_, v_cmp_1796_);
lean_dec_ref(v_cmp_1796_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* v_f_1798_, lean_object* v_t_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_RBNode_depth___redArg(v_f_1798_, v_t_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* v_f_1801_, lean_object* v_t_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_RBMap_depth___redArg(v_f_1801_, v_t_1802_);
lean_dec(v_t_1802_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* v_00_u03b1_1804_, lean_object* v_00_u03b2_1805_, lean_object* v_cmp_1806_, lean_object* v_f_1807_, lean_object* v_t_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_RBNode_depth___redArg(v_f_1807_, v_t_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* v_00_u03b1_1810_, lean_object* v_00_u03b2_1811_, lean_object* v_cmp_1812_, lean_object* v_f_1813_, lean_object* v_t_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_RBMap_depth(v_00_u03b1_1810_, v_00_u03b2_1811_, v_cmp_1812_, v_f_1813_, v_t_1814_);
lean_dec(v_t_1814_);
lean_dec_ref(v_cmp_1812_);
return v_res_1815_;
}
}
uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* v_t_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Lean_RBNode_isSingleton___redArg(v_t_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT void l_Lean_RBMap_isSingleton___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1816_ = stack[0].m_obj;
uint8_t v_res_1818_;
v_res_1818_ = l_Lean_RBMap_isSingleton___redArg(v_t_1816_);
stack->m_num = v_res_1818_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* v_t_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_Lean_RBMap_isSingleton___redArg(v_t_1819_);
lean_dec(v_t_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
uint8_t l_Lean_RBMap_isSingleton(lean_object* v_00_u03b1_1822_, lean_object* v_00_u03b2_1823_, lean_object* v_cmp_1824_, lean_object* v_t_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = l_Lean_RBNode_isSingleton___redArg(v_t_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT void l_Lean_RBMap_isSingleton_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1824_ = stack[2].m_obj;
lean_object* v_t_1825_ = stack[3].m_obj;
uint8_t v_res_1827_;
v_res_1827_ = l_Lean_RBMap_isSingleton(lean_box(0), lean_box(0), v_cmp_1824_, v_t_1825_);
stack->m_num = v_res_1827_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_00_u03b2_1829_, lean_object* v_cmp_1830_, lean_object* v_t_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l_Lean_RBMap_isSingleton(v_00_u03b1_1828_, v_00_u03b2_1829_, v_cmp_1830_, v_t_1831_);
lean_dec(v_t_1831_);
lean_dec_ref(v_cmp_1830_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* v_f_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_RBNode_fold___redArg(v_f_1834_, v_x_1835_, v_x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* v_00_u03b1_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_00_u03c3_1840_, lean_object* v_cmp_1841_, lean_object* v_f_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_RBNode_fold___redArg(v_f_1842_, v_x_1843_, v_x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_00_u03c3_1848_, lean_object* v_cmp_1849_, lean_object* v_f_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_RBMap_fold(v_00_u03b1_1846_, v_00_u03b2_1847_, v_00_u03c3_1848_, v_cmp_1849_, v_f_1850_, v_x_1851_, v_x_1852_);
lean_dec_ref(v_cmp_1849_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* v_f_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_RBNode_revFold___redArg(v_f_1854_, v_x_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_00_u03c3_1860_, lean_object* v_cmp_1861_, lean_object* v_f_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_RBNode_revFold___redArg(v_f_1862_, v_x_1863_, v_x_1864_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_00_u03c3_1868_, lean_object* v_cmp_1869_, lean_object* v_f_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_RBMap_revFold(v_00_u03b1_1866_, v_00_u03b2_1867_, v_00_u03c3_1868_, v_cmp_1869_, v_f_1870_, v_x_1871_, v_x_1872_);
lean_dec_ref(v_cmp_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* v_inst_1874_, lean_object* v_f_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_RBNode_foldM___redArg(v_inst_1874_, v_f_1875_, v_x_1876_, v_x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* v_00_u03b1_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_00_u03c3_1881_, lean_object* v_cmp_1882_, lean_object* v_m_1883_, lean_object* v_inst_1884_, lean_object* v_f_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_RBNode_foldM___redArg(v_inst_1884_, v_f_1885_, v_x_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_00_u03b2_1890_, lean_object* v_00_u03c3_1891_, lean_object* v_cmp_1892_, lean_object* v_m_1893_, lean_object* v_inst_1894_, lean_object* v_f_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_RBMap_foldM(v_00_u03b1_1889_, v_00_u03b2_1890_, v_00_u03c3_1891_, v_cmp_1892_, v_m_1893_, v_inst_1894_, v_f_1895_, v_x_1896_, v_x_1897_);
lean_dec_ref(v_cmp_1892_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* v_f_1899_, lean_object* v_x_1900_, lean_object* v_k_1901_, lean_object* v_v_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_apply_2(v_f_1899_, v_k_1901_, v_v_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* v_inst_1904_, lean_object* v_f_1905_, lean_object* v_t_1906_){
_start:
{
lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1907_, 0, v_f_1905_);
v___x_1908_ = lean_box(0);
v___x_1909_ = l_Lean_RBNode_foldM___redArg(v_inst_1904_, v___f_1907_, v___x_1908_, v_t_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_cmp_1912_, lean_object* v_m_1913_, lean_object* v_inst_1914_, lean_object* v_f_1915_, lean_object* v_t_1916_){
_start:
{
lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1917_, 0, v_f_1915_);
v___x_1918_ = lean_box(0);
v___x_1919_ = l_Lean_RBNode_foldM___redArg(v_inst_1914_, v___f_1917_, v___x_1918_, v_t_1916_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* v_00_u03b1_1920_, lean_object* v_00_u03b2_1921_, lean_object* v_cmp_1922_, lean_object* v_m_1923_, lean_object* v_inst_1924_, lean_object* v_f_1925_, lean_object* v_t_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_RBMap_forM(v_00_u03b1_1920_, v_00_u03b2_1921_, v_cmp_1922_, v_m_1923_, v_inst_1924_, v_f_1925_, v_t_1926_);
lean_dec_ref(v_cmp_1922_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* v_f_1928_, lean_object* v_a_1929_, lean_object* v_b_1930_, lean_object* v_acc_1931_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1929_);
lean_ctor_set(v___x_1932_, 1, v_b_1930_);
v___x_1933_ = lean_apply_2(v_f_1928_, v___x_1932_, v_acc_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* v_inst_1934_, lean_object* v_t_1935_, lean_object* v_init_1936_, lean_object* v_f_1937_){
_start:
{
lean_object* v_toApplicative_1938_; lean_object* v_toBind_1939_; lean_object* v_toPure_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; 
v_toApplicative_1938_ = lean_ctor_get(v_inst_1934_, 0);
v_toBind_1939_ = lean_ctor_get(v_inst_1934_, 1);
lean_inc(v_toBind_1939_);
v_toPure_1940_ = lean_ctor_get(v_toApplicative_1938_, 1);
lean_inc(v_toPure_1940_);
v___f_1941_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1941_, 0, v_f_1937_);
v___x_1942_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1934_, v___f_1941_, v_t_1935_, v_init_1936_);
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1943_, 0, v_toPure_1940_);
v___x_1944_ = lean_apply_4(v_toBind_1939_, lean_box(0), lean_box(0), v___x_1942_, v___f_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* v_00_u03b1_1945_, lean_object* v_00_u03b2_1946_, lean_object* v_00_u03c3_1947_, lean_object* v_cmp_1948_, lean_object* v_m_1949_, lean_object* v_inst_1950_, lean_object* v_t_1951_, lean_object* v_init_1952_, lean_object* v_f_1953_){
_start:
{
lean_object* v_toApplicative_1954_; lean_object* v_toBind_1955_; lean_object* v_toPure_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___f_1959_; lean_object* v___x_1960_; 
v_toApplicative_1954_ = lean_ctor_get(v_inst_1950_, 0);
v_toBind_1955_ = lean_ctor_get(v_inst_1950_, 1);
lean_inc(v_toBind_1955_);
v_toPure_1956_ = lean_ctor_get(v_toApplicative_1954_, 1);
lean_inc(v_toPure_1956_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1957_, 0, v_f_1953_);
v___x_1958_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1950_, v___f_1957_, v_t_1951_, v_init_1952_);
v___f_1959_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1959_, 0, v_toPure_1956_);
v___x_1960_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1958_, v___f_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_00_u03b2_1962_, lean_object* v_00_u03c3_1963_, lean_object* v_cmp_1964_, lean_object* v_m_1965_, lean_object* v_inst_1966_, lean_object* v_t_1967_, lean_object* v_init_1968_, lean_object* v_f_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_RBMap_forIn(v_00_u03b1_1961_, v_00_u03b2_1962_, v_00_u03c3_1963_, v_cmp_1964_, v_m_1965_, v_inst_1966_, v_t_1967_, v_init_1968_, v_f_1969_);
lean_dec_ref(v_cmp_1964_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* v___y_1971_, lean_object* v_a_1972_, lean_object* v_b_1973_, lean_object* v_acc_1974_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_a_1972_);
lean_ctor_set(v___x_1975_, 1, v_b_1973_);
v___x_1976_ = lean_apply_2(v___y_1971_, v___x_1975_, v_acc_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1977_, lean_object* v_00_u03b2_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_toApplicative_1982_; lean_object* v_toBind_1983_; lean_object* v_toPure_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; lean_object* v___f_1987_; lean_object* v___x_1988_; 
v_toApplicative_1982_ = lean_ctor_get(v_inst_1977_, 0);
v_toBind_1983_ = lean_ctor_get(v_inst_1977_, 1);
lean_inc(v_toBind_1983_);
v_toPure_1984_ = lean_ctor_get(v_toApplicative_1982_, 1);
lean_inc(v_toPure_1984_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1985_, 0, v___y_1981_);
v___x_1986_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1977_, v___f_1985_, v___y_1979_, v___y_1980_);
v___f_1987_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1987_, 0, v_toPure_1984_);
v___x_1988_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_1986_, v___f_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* v_inst_1989_){
_start:
{
lean_object* v___f_1990_; 
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1990_, 0, v_inst_1989_);
return v___f_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* v_00_u03b1_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_cmp_1993_, lean_object* v_m_1994_, lean_object* v_inst_1995_){
_start:
{
lean_object* v___f_1996_; 
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1996_, 0, v_inst_1995_);
return v___f_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1997_, lean_object* v_00_u03b2_1998_, lean_object* v_cmp_1999_, lean_object* v_m_2000_, lean_object* v_inst_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_RBMap_instForInProdOfMonad(v_00_u03b1_1997_, v_00_u03b2_1998_, v_cmp_1999_, v_m_2000_, v_inst_2001_);
lean_dec_ref(v_cmp_1999_);
return v_res_2002_;
}
}
uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* v_x_2003_){
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
LEAN_EXPORT void l_Lean_RBMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2003_ = stack[0].m_obj;
uint8_t v_res_2006_;
v_res_2006_ = l_Lean_RBMap_isEmpty___redArg(v_x_2003_);
stack->m_num = v_res_2006_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* v_x_2007_){
_start:
{
uint8_t v_res_2008_; lean_object* v_r_2009_; 
v_res_2008_ = l_Lean_RBMap_isEmpty___redArg(v_x_2007_);
lean_dec(v_x_2007_);
v_r_2009_ = lean_box(v_res_2008_);
return v_r_2009_;
}
}
uint8_t l_Lean_RBMap_isEmpty(lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_cmp_2012_, lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2013_) == 0)
{
uint8_t v___x_2014_; 
v___x_2014_ = 1;
return v___x_2014_;
}
else
{
uint8_t v___x_2015_; 
v___x_2015_ = 0;
return v___x_2015_;
}
}
}
LEAN_EXPORT void l_Lean_RBMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2012_ = stack[2].m_obj;
lean_object* v_x_2013_ = stack[3].m_obj;
uint8_t v_res_2016_;
v_res_2016_ = l_Lean_RBMap_isEmpty(lean_box(0), lean_box(0), v_cmp_2012_, v_x_2013_);
stack->m_num = v_res_2016_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_cmp_2019_, lean_object* v_x_2020_){
_start:
{
uint8_t v_res_2021_; lean_object* v_r_2022_; 
v_res_2021_ = l_Lean_RBMap_isEmpty(v_00_u03b1_2017_, v_00_u03b2_2018_, v_cmp_2019_, v_x_2020_);
lean_dec(v_x_2020_);
lean_dec_ref(v_cmp_2019_);
v_r_2022_ = lean_box(v_res_2021_);
return v_r_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* v_ps_2023_, lean_object* v_k_2024_, lean_object* v_v_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_k_2024_);
lean_ctor_set(v___x_2026_, 1, v_v_2025_);
v___x_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v_ps_2023_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* v_x_2029_){
_start:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___f_2030_ = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
v___x_2031_ = lean_box(0);
v___x_2032_ = l_Lean_RBNode_revFold___redArg(v___f_2030_, v___x_2031_, v_x_2029_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* v_00_u03b1_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_cmp_2035_, lean_object* v_x_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_RBMap_toList___redArg(v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_00_u03b2_2039_, lean_object* v_cmp_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_RBMap_toList(v_00_u03b1_2038_, v_00_u03b2_2039_, v_cmp_2040_, v_x_2041_);
lean_dec_ref(v_cmp_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* v_ps_2043_, lean_object* v_k_2044_, lean_object* v_v_2045_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_k_2044_);
lean_ctor_set(v___x_2046_, 1, v_v_2045_);
v___x_2047_ = lean_array_push(v_ps_2043_, v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* v_x_2051_){
_start:
{
lean_object* v___f_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___f_2052_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
v___x_2053_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
v___x_2054_ = l_Lean_RBNode_fold___redArg(v___f_2052_, v___x_2053_, v_x_2051_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_cmp_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_RBMap_toArray___redArg(v_x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_cmp_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Lean_RBMap_toArray(v_00_u03b1_2060_, v_00_u03b2_2061_, v_cmp_2062_, v_x_2063_);
lean_dec_ref(v_cmp_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* v_x_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_RBNode_min___redArg(v_x_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_box(0);
return v___x_2067_;
}
else
{
lean_object* v_val_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2084_; 
v_val_2068_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2070_ = v___x_2066_;
v_isShared_2071_ = v_isSharedCheck_2084_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_val_2068_);
lean_dec(v___x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2084_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2083_; 
v_fst_2072_ = lean_ctor_get(v_val_2068_, 0);
v_snd_2073_ = lean_ctor_get(v_val_2068_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_val_2068_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2075_ = v_val_2068_;
v_isShared_2076_ = v_isSharedCheck_2083_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snd_2073_);
lean_inc(v_fst_2072_);
lean_dec(v_val_2068_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2083_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_fst_2072_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_snd_2073_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2078_);
v___x_2080_ = v___x_2070_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* v_x_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_RBMap_min___redArg(v_x_2085_);
lean_dec(v_x_2085_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_cmp_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_RBNode_min___redArg(v_x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_box(0);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2109_; 
v_val_2093_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2095_ = v___x_2091_;
v_isShared_2096_ = v_isSharedCheck_2109_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_val_2093_);
lean_dec(v___x_2091_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2109_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_fst_2097_; lean_object* v_snd_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2108_; 
v_fst_2097_ = lean_ctor_get(v_val_2093_, 0);
v_snd_2098_ = lean_ctor_get(v_val_2093_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_val_2093_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2100_ = v_val_2093_;
v_isShared_2101_ = v_isSharedCheck_2108_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_snd_2098_);
lean_inc(v_fst_2097_);
lean_dec(v_val_2093_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2108_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_fst_2097_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_snd_2098_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2103_);
v___x_2105_ = v___x_2095_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* v_00_u03b1_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_cmp_2112_, lean_object* v_x_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_RBMap_min(v_00_u03b1_2110_, v_00_u03b2_2111_, v_cmp_2112_, v_x_2113_);
lean_dec(v_x_2113_);
lean_dec_ref(v_cmp_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* v_x_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_RBNode_max___redArg(v_x_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_box(0);
return v___x_2117_;
}
else
{
lean_object* v_val_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2134_; 
v_val_2118_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2120_ = v___x_2116_;
v_isShared_2121_ = v_isSharedCheck_2134_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_val_2118_);
lean_dec(v___x_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2134_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_fst_2122_; lean_object* v_snd_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2133_; 
v_fst_2122_ = lean_ctor_get(v_val_2118_, 0);
v_snd_2123_ = lean_ctor_get(v_val_2118_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_val_2118_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2125_ = v_val_2118_;
v_isShared_2126_ = v_isSharedCheck_2133_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_snd_2123_);
lean_inc(v_fst_2122_);
lean_dec(v_val_2118_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2133_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_fst_2122_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_snd_2123_);
v___x_2128_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2128_);
v___x_2130_ = v___x_2120_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* v_x_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_RBMap_max___redArg(v_x_2135_);
lean_dec(v_x_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* v_00_u03b1_2137_, lean_object* v_00_u03b2_2138_, lean_object* v_cmp_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_RBNode_max___redArg(v_x_2140_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_box(0);
return v___x_2142_;
}
else
{
lean_object* v_val_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2159_; 
v_val_2143_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2145_ = v___x_2141_;
v_isShared_2146_ = v_isSharedCheck_2159_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_val_2143_);
lean_dec(v___x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2159_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_fst_2147_; lean_object* v_snd_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2158_; 
v_fst_2147_ = lean_ctor_get(v_val_2143_, 0);
v_snd_2148_ = lean_ctor_get(v_val_2143_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_val_2143_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2150_ = v_val_2143_;
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_snd_2148_);
lean_inc(v_fst_2147_);
lean_dec(v_val_2143_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_fst_2147_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_snd_2148_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2153_);
v___x_2155_ = v___x_2145_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_00_u03b2_2161_, lean_object* v_cmp_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_RBMap_max(v_00_u03b1_2160_, v_00_u03b2_2161_, v_cmp_2162_, v_x_2163_);
lean_dec(v_x_2163_);
lean_dec_ref(v_cmp_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* v___x_2168_, lean_object* v_m_2169_, lean_object* v_prec_2170_){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2171_ = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
v___x_2172_ = l_Lean_RBMap_toList___redArg(v_m_2169_);
v___x_2173_ = l_List_repr___redArg(v___x_2168_, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2171_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = l_Repr_addAppParen(v___x_2174_, v_prec_2170_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* v___x_2176_, lean_object* v_m_2177_, lean_object* v_prec_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_2176_, v_m_2177_, v_prec_2178_);
lean_dec(v_prec_2178_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* v_inst_2180_, lean_object* v_inst_2181_){
_start:
{
lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___f_2184_; 
v___f_2182_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2182_, 0, v_inst_2181_);
v___x_2183_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2183_, 0, lean_box(0));
lean_closure_set(v___x_2183_, 1, lean_box(0));
lean_closure_set(v___x_2183_, 2, v_inst_2180_);
lean_closure_set(v___x_2183_, 3, v___f_2182_);
v___f_2184_ = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2184_, 0, v___x_2183_);
return v___f_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* v_00_u03b1_2185_, lean_object* v_00_u03b2_2186_, lean_object* v_cmp_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_RBMap_instRepr___redArg(v_inst_2188_, v_inst_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_cmp_2193_, lean_object* v_inst_2194_, lean_object* v_inst_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_RBMap_instRepr(v_00_u03b1_2191_, v_00_u03b2_2192_, v_cmp_2193_, v_inst_2194_, v_inst_2195_);
lean_dec_ref(v_cmp_2193_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* v_cmp_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_RBNode_insert___redArg(v_cmp_2197_, v_x_2198_, v_x_2199_, v_x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_cmp_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_RBNode_insert___redArg(v_cmp_2204_, v_x_2205_, v_x_2206_, v_x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* v_cmp_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_RBNode_erase___redArg(v_cmp_2209_, v_x_2211_, v_x_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* v_00_u03b1_2213_, lean_object* v_00_u03b2_2214_, lean_object* v_cmp_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_RBNode_erase___redArg(v_cmp_2215_, v_x_2217_, v_x_2216_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* v_cmp_2219_, lean_object* v_x_2220_){
_start:
{
if (lean_obj_tag(v_x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref(v_cmp_2219_);
v___x_2221_ = lean_box(0);
return v___x_2221_;
}
else
{
lean_object* v_head_2222_; lean_object* v_tail_2223_; lean_object* v_fst_2224_; lean_object* v_snd_2225_; lean_object* v_val_2226_; lean_object* v___x_2227_; 
v_head_2222_ = lean_ctor_get(v_x_2220_, 0);
lean_inc(v_head_2222_);
v_tail_2223_ = lean_ctor_get(v_x_2220_, 1);
lean_inc(v_tail_2223_);
lean_dec_ref_known(v_x_2220_, 2);
v_fst_2224_ = lean_ctor_get(v_head_2222_, 0);
lean_inc(v_fst_2224_);
v_snd_2225_ = lean_ctor_get(v_head_2222_, 1);
lean_inc(v_snd_2225_);
lean_dec(v_head_2222_);
lean_inc_ref(v_cmp_2219_);
v_val_2226_ = l_Lean_RBMap_ofList___redArg(v_cmp_2219_, v_tail_2223_);
v___x_2227_ = l_Lean_RBNode_insert___redArg(v_cmp_2219_, v_val_2226_, v_fst_2224_, v_snd_2225_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* v_00_u03b1_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_cmp_2230_, lean_object* v_x_2231_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_RBMap_ofList___redArg(v_cmp_2230_, v_x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* v_cmp_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_RBNode_findCore___redArg(v_cmp_2233_, v_x_2234_, v_x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* v_00_u03b1_2237_, lean_object* v_00_u03b2_2238_, lean_object* v_cmp_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_RBNode_findCore___redArg(v_cmp_2239_, v_x_2240_, v_x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* v_cmp_2243_, lean_object* v_x_2244_, lean_object* v_x_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_RBNode_find___redArg(v_cmp_2243_, v_x_2244_, v_x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* v_00_u03b1_2247_, lean_object* v_00_u03b2_2248_, lean_object* v_cmp_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_RBNode_find___redArg(v_cmp_2249_, v_x_2250_, v_x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* v_cmp_2253_, lean_object* v_t_2254_, lean_object* v_k_2255_, lean_object* v_v_u2080_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_RBNode_find___redArg(v_cmp_2253_, v_t_2254_, v_k_2255_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_inc(v_v_u2080_2256_);
return v_v_u2080_2256_;
}
else
{
lean_object* v_val_2258_; 
v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v___x_2257_, 1);
return v_val_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* v_cmp_2259_, lean_object* v_t_2260_, lean_object* v_k_2261_, lean_object* v_v_u2080_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_RBMap_findD___redArg(v_cmp_2259_, v_t_2260_, v_k_2261_, v_v_u2080_2262_);
lean_dec(v_v_u2080_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* v_00_u03b1_2264_, lean_object* v_00_u03b2_2265_, lean_object* v_cmp_2266_, lean_object* v_t_2267_, lean_object* v_k_2268_, lean_object* v_v_u2080_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_RBNode_find___redArg(v_cmp_2266_, v_t_2267_, v_k_2268_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_inc(v_v_u2080_2269_);
return v_v_u2080_2269_;
}
else
{
lean_object* v_val_2271_; 
v_val_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v___x_2270_, 1);
return v_val_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_00_u03b2_2273_, lean_object* v_cmp_2274_, lean_object* v_t_2275_, lean_object* v_k_2276_, lean_object* v_v_u2080_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_RBMap_findD(v_00_u03b1_2272_, v_00_u03b2_2273_, v_cmp_2274_, v_t_2275_, v_k_2276_, v_v_u2080_2277_);
lean_dec(v_v_u2080_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* v_cmp_2279_, lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2279_, v_x_2280_, v_x_2281_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* v_00_u03b1_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_cmp_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2286_, v_x_2287_, v_x_2288_, v___x_2289_);
return v___x_2290_;
}
}
uint8_t l_Lean_RBMap_contains___redArg(lean_object* v_cmp_2291_, lean_object* v_t_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_RBNode_find___redArg(v_cmp_2291_, v_t_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
uint8_t v___x_2295_; 
v___x_2295_ = 0;
return v___x_2295_;
}
else
{
uint8_t v___x_2296_; 
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = 1;
return v___x_2296_;
}
}
}
LEAN_EXPORT void l_Lean_RBMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2291_ = stack[0].m_obj;
lean_object* v_t_2292_ = stack[1].m_obj;
lean_object* v_a_2293_ = stack[2].m_obj;
uint8_t v_res_2297_;
v_res_2297_ = l_Lean_RBMap_contains___redArg(v_cmp_2291_, v_t_2292_, v_a_2293_);
stack->m_num = v_res_2297_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* v_cmp_2298_, lean_object* v_t_2299_, lean_object* v_a_2300_){
_start:
{
uint8_t v_res_2301_; lean_object* v_r_2302_; 
v_res_2301_ = l_Lean_RBMap_contains___redArg(v_cmp_2298_, v_t_2299_, v_a_2300_);
v_r_2302_ = lean_box(v_res_2301_);
return v_r_2302_;
}
}
uint8_t l_Lean_RBMap_contains(lean_object* v_00_u03b1_2303_, lean_object* v_00_u03b2_2304_, lean_object* v_cmp_2305_, lean_object* v_t_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_RBNode_find___redArg(v_cmp_2305_, v_t_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2308_) == 0)
{
uint8_t v___x_2309_; 
v___x_2309_ = 0;
return v___x_2309_;
}
else
{
uint8_t v___x_2310_; 
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = 1;
return v___x_2310_;
}
}
}
LEAN_EXPORT void l_Lean_RBMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2305_ = stack[2].m_obj;
lean_object* v_t_2306_ = stack[3].m_obj;
lean_object* v_a_2307_ = stack[4].m_obj;
uint8_t v_res_2311_;
v_res_2311_ = l_Lean_RBMap_contains(lean_box(0), lean_box(0), v_cmp_2305_, v_t_2306_, v_a_2307_);
stack->m_num = v_res_2311_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_cmp_2314_, lean_object* v_t_2315_, lean_object* v_a_2316_){
_start:
{
uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_res_2317_ = l_Lean_RBMap_contains(v_00_u03b1_2312_, v_00_u03b2_2313_, v_cmp_2314_, v_t_2315_, v_a_2316_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* v_cmp_2319_, lean_object* v_r_2320_, lean_object* v_p_2321_){
_start:
{
lean_object* v_fst_2322_; lean_object* v_snd_2323_; lean_object* v___x_2324_; 
v_fst_2322_ = lean_ctor_get(v_p_2321_, 0);
lean_inc(v_fst_2322_);
v_snd_2323_ = lean_ctor_get(v_p_2321_, 1);
lean_inc(v_snd_2323_);
lean_dec_ref(v_p_2321_);
v___x_2324_ = l_Lean_RBNode_insert___redArg(v_cmp_2319_, v_r_2320_, v_fst_2322_, v_snd_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* v_l_2325_, lean_object* v_cmp_2326_){
_start:
{
lean_object* v___f_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___f_2327_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2327_, 0, v_cmp_2326_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l_List_foldl___redArg(v___f_2327_, v___x_2328_, v_l_2325_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* v_00_u03b1_2330_, lean_object* v_00_u03b2_2331_, lean_object* v_l_2332_, lean_object* v_cmp_2333_){
_start:
{
lean_object* v___f_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2334_, 0, v_cmp_2333_);
v___x_2335_ = lean_box(0);
v___x_2336_ = l_List_foldl___redArg(v___f_2334_, v___x_2335_, v_l_2332_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* v_cmp_2337_, lean_object* v_x1_2338_, lean_object* v_x2_2339_){
_start:
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v___x_2342_; 
v_fst_2340_ = lean_ctor_get(v_x2_2339_, 0);
lean_inc(v_fst_2340_);
v_snd_2341_ = lean_ctor_get(v_x2_2339_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v_x2_2339_);
v___x_2342_ = l_Lean_RBNode_insert___redArg(v_cmp_2337_, v_x1_2338_, v_fst_2340_, v_snd_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* v_l_2362_, lean_object* v_cmp_2363_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_unsigned_to_nat(0u);
v___x_2366_ = lean_array_get_size(v_l_2362_);
v___x_2367_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2368_ = lean_nat_dec_lt(v___x_2365_, v___x_2366_);
if (v___x_2368_ == 0)
{
lean_dec_ref(v_cmp_2363_);
lean_dec_ref(v_l_2362_);
return v___x_2364_;
}
else
{
lean_object* v___f_2369_; uint8_t v___x_2370_; 
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2369_, 0, v_cmp_2363_);
v___x_2370_ = lean_nat_dec_le(v___x_2366_, v___x_2366_);
if (v___x_2370_ == 0)
{
if (v___x_2368_ == 0)
{
lean_dec_ref(v___f_2369_);
lean_dec_ref(v_l_2362_);
return v___x_2364_;
}
else
{
size_t v___x_2371_; size_t v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = ((size_t)0ULL);
v___x_2372_ = lean_usize_of_nat(v___x_2366_);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2367_, v___f_2369_, v_l_2362_, v___x_2371_, v___x_2372_, v___x_2364_);
return v___x_2373_;
}
}
else
{
size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((size_t)0ULL);
v___x_2375_ = lean_usize_of_nat(v___x_2366_);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2367_, v___f_2369_, v_l_2362_, v___x_2374_, v___x_2375_, v___x_2364_);
return v___x_2376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* v_00_u03b1_2377_, lean_object* v_00_u03b2_2378_, lean_object* v_l_2379_, lean_object* v_cmp_2380_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = lean_array_get_size(v_l_2379_);
v___x_2384_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2385_ = lean_nat_dec_lt(v___x_2382_, v___x_2383_);
if (v___x_2385_ == 0)
{
lean_dec_ref(v_cmp_2380_);
lean_dec_ref(v_l_2379_);
return v___x_2381_;
}
else
{
lean_object* v___f_2386_; uint8_t v___x_2387_; 
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2386_, 0, v_cmp_2380_);
v___x_2387_ = lean_nat_dec_le(v___x_2383_, v___x_2383_);
if (v___x_2387_ == 0)
{
if (v___x_2385_ == 0)
{
lean_dec_ref(v___f_2386_);
lean_dec_ref(v_l_2379_);
return v___x_2381_;
}
else
{
size_t v___x_2388_; size_t v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = ((size_t)0ULL);
v___x_2389_ = lean_usize_of_nat(v___x_2383_);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2384_, v___f_2386_, v_l_2379_, v___x_2388_, v___x_2389_, v___x_2381_);
return v___x_2390_;
}
}
else
{
size_t v___x_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = lean_usize_of_nat(v___x_2383_);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2384_, v___f_2386_, v_l_2379_, v___x_2391_, v___x_2392_, v___x_2381_);
return v___x_2393_;
}
}
}
}
uint8_t l_Lean_RBMap_all___redArg(lean_object* v_x_2394_, lean_object* v_x_2395_){
_start:
{
uint8_t v___x_2396_; 
v___x_2396_ = l_Lean_RBNode_all___redArg(v_x_2395_, v_x_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT void l_Lean_RBMap_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2394_ = stack[0].m_obj;
lean_object* v_x_2395_ = stack[1].m_obj;
uint8_t v_res_2397_;
v_res_2397_ = l_Lean_RBMap_all___redArg(v_x_2394_, v_x_2395_);
stack->m_num = v_res_2397_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_Lean_RBMap_all___redArg(v_x_2398_, v_x_2399_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
uint8_t l_Lean_RBMap_all(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_cmp_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_RBNode_all___redArg(v_x_2406_, v_x_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT void l_Lean_RBMap_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2404_ = stack[2].m_obj;
lean_object* v_x_2405_ = stack[3].m_obj;
lean_object* v_x_2406_ = stack[4].m_obj;
uint8_t v_res_2408_;
v_res_2408_ = l_Lean_RBMap_all(lean_box(0), lean_box(0), v_cmp_2404_, v_x_2405_, v_x_2406_);
stack->m_num = v_res_2408_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_00_u03b2_2410_, lean_object* v_cmp_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Lean_RBMap_all(v_00_u03b1_2409_, v_00_u03b2_2410_, v_cmp_2411_, v_x_2412_, v_x_2413_);
lean_dec_ref(v_cmp_2411_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
uint8_t l_Lean_RBMap_any___redArg(lean_object* v_x_2416_, lean_object* v_x_2417_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = l_Lean_RBNode_any___redArg(v_x_2417_, v_x_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT void l_Lean_RBMap_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2416_ = stack[0].m_obj;
lean_object* v_x_2417_ = stack[1].m_obj;
uint8_t v_res_2419_;
v_res_2419_ = l_Lean_RBMap_any___redArg(v_x_2416_, v_x_2417_);
stack->m_num = v_res_2419_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* v_x_2420_, lean_object* v_x_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_Lean_RBMap_any___redArg(v_x_2420_, v_x_2421_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
uint8_t l_Lean_RBMap_any(lean_object* v_00_u03b1_2424_, lean_object* v_00_u03b2_2425_, lean_object* v_cmp_2426_, lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = l_Lean_RBNode_any___redArg(v_x_2428_, v_x_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT void l_Lean_RBMap_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_2426_ = stack[2].m_obj;
lean_object* v_x_2427_ = stack[3].m_obj;
lean_object* v_x_2428_ = stack[4].m_obj;
uint8_t v_res_2430_;
v_res_2430_ = l_Lean_RBMap_any(lean_box(0), lean_box(0), v_cmp_2426_, v_x_2427_, v_x_2428_);
stack->m_num = v_res_2430_;
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_cmp_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
uint8_t v_res_2436_; lean_object* v_r_2437_; 
v_res_2436_ = l_Lean_RBMap_any(v_00_u03b1_2431_, v_00_u03b2_2432_, v_cmp_2433_, v_x_2434_, v_x_2435_);
lean_dec_ref(v_cmp_2433_);
v_r_2437_ = lean_box(v_res_2436_);
return v_r_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
if (lean_obj_tag(v_x_2439_) == 0)
{
return v_x_2438_;
}
else
{
lean_object* v_lchild_2440_; lean_object* v_rchild_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_lchild_2440_ = lean_ctor_get(v_x_2439_, 0);
v_rchild_2441_ = lean_ctor_get(v_x_2439_, 3);
v___x_2442_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2438_, v_lchild_2440_);
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = lean_nat_add(v___x_2442_, v___x_2443_);
lean_dec(v___x_2442_);
v_x_2438_ = v___x_2444_;
v_x_2439_ = v_rchild_2441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2446_, v_x_2447_);
lean_dec(v_x_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* v_m_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_unsigned_to_nat(0u);
v___x_2451_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_2450_, v_m_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* v_m_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_RBMap_size___redArg(v_m_2452_);
lean_dec(v_m_2452_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* v_00_u03b1_2454_, lean_object* v_00_u03b2_2455_, lean_object* v_cmp_2456_, lean_object* v_m_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_RBMap_size___redArg(v_m_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_00_u03b2_2460_, lean_object* v_cmp_2461_, lean_object* v_m_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_RBMap_size(v_00_u03b1_2459_, v_00_u03b2_2460_, v_cmp_2461_, v_m_2462_);
lean_dec(v_m_2462_);
lean_dec_ref(v_cmp_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* v_00_u03b1_2464_, lean_object* v_00_u03b2_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2466_, v_x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_00_u03b2_2470_, lean_object* v_x_2471_, lean_object* v_x_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(v_00_u03b1_2469_, v_00_u03b2_2470_, v_x_2471_, v_x_2472_);
lean_dec(v_x_2472_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_nat_dec_le(v___y_2474_, v___y_2475_);
if (v___x_2476_ == 0)
{
lean_inc(v___y_2474_);
return v___y_2474_;
}
else
{
lean_inc(v___y_2475_);
return v___y_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec(v___y_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* v_t_2481_){
_start:
{
lean_object* v___f_2482_; lean_object* v___x_2483_; 
v___f_2482_ = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
v___x_2483_ = l_Lean_RBNode_depth___redArg(v___f_2482_, v_t_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* v_t_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_RBMap_maxDepth___redArg(v_t_2484_);
lean_dec(v_t_2484_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* v_00_u03b1_2486_, lean_object* v_00_u03b2_2487_, lean_object* v_cmp_2488_, lean_object* v_t_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_RBMap_maxDepth___redArg(v_t_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* v_00_u03b1_2491_, lean_object* v_00_u03b2_2492_, lean_object* v_cmp_2493_, lean_object* v_t_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_RBMap_maxDepth(v_00_u03b1_2491_, v_00_u03b2_2492_, v_cmp_2493_, v_t_2494_);
lean_dec(v_t_2494_);
lean_dec_ref(v_cmp_2493_);
return v_res_2495_;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2499_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2500_ = lean_unsigned_to_nat(14u);
v___x_2501_ = lean_unsigned_to_nat(386u);
v___x_2502_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
v___x_2503_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2504_ = l_mkPanicMessageWithDecl(v___x_2503_, v___x_2502_, v___x_2501_, v___x_2500_, v___x_2499_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* v_inst_2505_, lean_object* v_inst_2506_, lean_object* v_t_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_RBNode_min___redArg(v_t_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_inst_2505_);
lean_ctor_set(v___x_2509_, 1, v_inst_2506_);
v___x_2510_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2511_ = l_panic___redArg(v___x_2509_, v___x_2510_);
lean_dec_ref_known(v___x_2509_, 2);
return v___x_2511_;
}
else
{
lean_object* v_val_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_inst_2506_);
lean_dec(v_inst_2505_);
v_val_2512_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v___x_2508_, 1);
v_fst_2513_ = lean_ctor_get(v_val_2512_, 0);
v_snd_2514_ = lean_ctor_get(v_val_2512_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_val_2512_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v_val_2512_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snd_2514_);
lean_inc(v_fst_2513_);
lean_dec(v_val_2512_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_fst_2513_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_snd_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_t_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_RBMap_min_x21___redArg(v_inst_2522_, v_inst_2523_, v_t_2524_);
lean_dec(v_t_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* v_00_u03b1_2526_, lean_object* v_00_u03b2_2527_, lean_object* v_cmp_2528_, lean_object* v_inst_2529_, lean_object* v_inst_2530_, lean_object* v_t_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_RBNode_min___redArg(v_t_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v_inst_2529_);
lean_ctor_set(v___x_2533_, 1, v_inst_2530_);
v___x_2534_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2535_ = l_panic___redArg(v___x_2533_, v___x_2534_);
lean_dec_ref_known(v___x_2533_, 2);
return v___x_2535_;
}
else
{
lean_object* v_val_2536_; lean_object* v_fst_2537_; lean_object* v_snd_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_inst_2530_);
lean_dec(v_inst_2529_);
v_val_2536_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v___x_2532_, 1);
v_fst_2537_ = lean_ctor_get(v_val_2536_, 0);
v_snd_2538_ = lean_ctor_get(v_val_2536_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_val_2536_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v_val_2536_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_snd_2538_);
lean_inc(v_fst_2537_);
lean_dec(v_val_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_fst_2537_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_snd_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* v_00_u03b1_2546_, lean_object* v_00_u03b2_2547_, lean_object* v_cmp_2548_, lean_object* v_inst_2549_, lean_object* v_inst_2550_, lean_object* v_t_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_RBMap_min_x21(v_00_u03b1_2546_, v_00_u03b2_2547_, v_cmp_2548_, v_inst_2549_, v_inst_2550_, v_t_2551_);
lean_dec(v_t_2551_);
lean_dec_ref(v_cmp_2548_);
return v_res_2552_;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2554_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2555_ = lean_unsigned_to_nat(14u);
v___x_2556_ = lean_unsigned_to_nat(391u);
v___x_2557_ = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
v___x_2558_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2559_ = l_mkPanicMessageWithDecl(v___x_2558_, v___x_2557_, v___x_2556_, v___x_2555_, v___x_2554_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_t_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_RBNode_max___redArg(v_t_2562_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_inst_2560_);
lean_ctor_set(v___x_2564_, 1, v_inst_2561_);
v___x_2565_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2566_ = l_panic___redArg(v___x_2564_, v___x_2565_);
lean_dec_ref_known(v___x_2564_, 2);
return v___x_2566_;
}
else
{
lean_object* v_val_2567_; lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_inst_2561_);
lean_dec(v_inst_2560_);
v_val_2567_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_val_2567_);
lean_dec_ref_known(v___x_2563_, 1);
v_fst_2568_ = lean_ctor_get(v_val_2567_, 0);
v_snd_2569_ = lean_ctor_get(v_val_2567_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_val_2567_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v_val_2567_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_snd_2569_);
lean_inc(v_fst_2568_);
lean_dec(v_val_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fst_2568_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_snd_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_t_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_RBMap_max_x21___redArg(v_inst_2577_, v_inst_2578_, v_t_2579_);
lean_dec(v_t_2579_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* v_00_u03b1_2581_, lean_object* v_00_u03b2_2582_, lean_object* v_cmp_2583_, lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_t_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_RBNode_max___redArg(v_t_2586_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_inst_2584_);
lean_ctor_set(v___x_2588_, 1, v_inst_2585_);
v___x_2589_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2590_ = l_panic___redArg(v___x_2588_, v___x_2589_);
lean_dec_ref_known(v___x_2588_, 2);
return v___x_2590_;
}
else
{
lean_object* v_val_2591_; lean_object* v_fst_2592_; lean_object* v_snd_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_inst_2585_);
lean_dec(v_inst_2584_);
v_val_2591_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v___x_2587_, 1);
v_fst_2592_ = lean_ctor_get(v_val_2591_, 0);
v_snd_2593_ = lean_ctor_get(v_val_2591_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_val_2591_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v_val_2591_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snd_2593_);
lean_inc(v_fst_2592_);
lean_dec(v_val_2591_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_fst_2592_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_snd_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* v_00_u03b1_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_cmp_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_t_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_RBMap_max_x21(v_00_u03b1_2601_, v_00_u03b2_2602_, v_cmp_2603_, v_inst_2604_, v_inst_2605_, v_t_2606_);
lean_dec(v_t_2606_);
lean_dec_ref(v_cmp_2603_);
return v_res_2607_;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2610_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
v___x_2611_ = lean_unsigned_to_nat(14u);
v___x_2612_ = lean_unsigned_to_nat(397u);
v___x_2613_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
v___x_2614_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2615_ = l_mkPanicMessageWithDecl(v___x_2614_, v___x_2613_, v___x_2612_, v___x_2611_, v___x_2610_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* v_cmp_2616_, lean_object* v_inst_2617_, lean_object* v_t_2618_, lean_object* v_k_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_RBNode_find___redArg(v_cmp_2616_, v_t_2618_, v_k_2619_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2622_ = l_panic___redArg(v_inst_2617_, v___x_2621_);
return v___x_2622_;
}
else
{
lean_object* v_val_2623_; 
v_val_2623_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v___x_2620_, 1);
return v_val_2623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg___boxed(lean_object* v_cmp_2624_, lean_object* v_inst_2625_, lean_object* v_t_2626_, lean_object* v_k_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_RBMap_find_x21___redArg(v_cmp_2624_, v_inst_2625_, v_t_2626_, v_k_2627_);
lean_dec(v_inst_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* v_00_u03b1_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_cmp_2631_, lean_object* v_inst_2632_, lean_object* v_t_2633_, lean_object* v_k_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_RBNode_find___redArg(v_cmp_2631_, v_t_2633_, v_k_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2637_ = l_panic___redArg(v_inst_2632_, v___x_2636_);
return v___x_2637_;
}
else
{
lean_object* v_val_2638_; 
v_val_2638_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_val_2638_);
lean_dec_ref_known(v___x_2635_, 1);
return v_val_2638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___boxed(lean_object* v_00_u03b1_2639_, lean_object* v_00_u03b2_2640_, lean_object* v_cmp_2641_, lean_object* v_inst_2642_, lean_object* v_t_2643_, lean_object* v_k_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_RBMap_find_x21(v_00_u03b1_2639_, v_00_u03b2_2640_, v_cmp_2641_, v_inst_2642_, v_t_2643_, v_k_2644_);
lean_dec(v_inst_2642_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* v_cmp_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_, lean_object* v_x_2649_){
_start:
{
if (lean_obj_tag(v_x_2647_) == 0)
{
uint8_t v___x_2650_; lean_object* v___x_2651_; 
lean_dec_ref(v_cmp_2646_);
v___x_2650_ = 0;
v___x_2651_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2651_, 0, v_x_2647_);
lean_ctor_set(v___x_2651_, 1, v_x_2648_);
lean_ctor_set(v___x_2651_, 2, v_x_2649_);
lean_ctor_set(v___x_2651_, 3, v_x_2647_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*4, v___x_2650_);
return v___x_2651_;
}
else
{
uint8_t v_color_2652_; 
v_color_2652_ = lean_ctor_get_uint8(v_x_2647_, sizeof(void*)*4);
if (v_color_2652_ == 0)
{
lean_object* v_lchild_2653_; lean_object* v_key_2654_; lean_object* v_val_2655_; lean_object* v_rchild_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2673_; 
v_lchild_2653_ = lean_ctor_get(v_x_2647_, 0);
v_key_2654_ = lean_ctor_get(v_x_2647_, 1);
v_val_2655_ = lean_ctor_get(v_x_2647_, 2);
v_rchild_2656_ = lean_ctor_get(v_x_2647_, 3);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_x_2647_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2658_ = v_x_2647_;
v_isShared_2659_ = v_isSharedCheck_2673_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_rchild_2656_);
lean_inc(v_val_2655_);
lean_inc(v_key_2654_);
lean_inc(v_lchild_2653_);
lean_dec(v_x_2647_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2673_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
lean_inc_ref(v_cmp_2646_);
lean_inc(v_key_2654_);
lean_inc(v_x_2648_);
v___x_2660_ = lean_apply_2(v_cmp_2646_, v_x_2648_, v_key_2654_);
v___x_2661_ = lean_unbox(v___x_2660_);
switch(v___x_2661_)
{
case 0:
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2646_, v_lchild_2653_, v_x_2648_, v_x_2649_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2662_);
v___x_2664_ = v___x_2658_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_key_2654_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_val_2655_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v_rchild_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2665_, sizeof(void*)*4, v_color_2652_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
case 1:
{
lean_object* v___x_2667_; 
lean_dec(v_val_2655_);
lean_dec(v_key_2654_);
lean_dec_ref(v_cmp_2646_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 2, v_x_2649_);
lean_ctor_set(v___x_2658_, 1, v_x_2648_);
v___x_2667_ = v___x_2658_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_lchild_2653_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_x_2648_);
lean_ctor_set(v_reuseFailAlloc_2668_, 2, v_x_2649_);
lean_ctor_set(v_reuseFailAlloc_2668_, 3, v_rchild_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2668_, sizeof(void*)*4, v_color_2652_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
default: 
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2646_, v_rchild_2656_, v_x_2648_, v_x_2649_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 3, v___x_2669_);
v___x_2671_ = v___x_2658_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_lchild_2653_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_key_2654_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_val_2655_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v___x_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*4, v_color_2652_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
else
{
lean_object* v_lchild_2674_; lean_object* v_key_2675_; lean_object* v_val_2676_; lean_object* v_rchild_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2836_; 
v_lchild_2674_ = lean_ctor_get(v_x_2647_, 0);
v_key_2675_ = lean_ctor_get(v_x_2647_, 1);
v_val_2676_ = lean_ctor_get(v_x_2647_, 2);
v_rchild_2677_ = lean_ctor_get(v_x_2647_, 3);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_x_2647_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2679_ = v_x_2647_;
v_isShared_2680_ = v_isSharedCheck_2836_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_rchild_2677_);
lean_inc(v_val_2676_);
lean_inc(v_key_2675_);
lean_inc(v_lchild_2674_);
lean_dec(v_x_2647_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2836_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
lean_inc_ref(v_cmp_2646_);
lean_inc(v_key_2675_);
lean_inc(v_x_2648_);
v___x_2681_ = lean_apply_2(v_cmp_2646_, v_x_2648_, v_key_2675_);
v___x_2682_ = lean_unbox(v___x_2681_);
switch(v___x_2682_)
{
case 0:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2646_, v_lchild_2674_, v_x_2648_, v_x_2649_);
if (lean_obj_tag(v___x_2683_) == 1)
{
uint8_t v_color_2684_; lean_object* v_lchild_2685_; lean_object* v_key_2686_; lean_object* v_val_2687_; lean_object* v_rchild_2688_; lean_object* v_a_2690_; lean_object* v_kx_2691_; lean_object* v_vx_2692_; lean_object* v_b_2693_; lean_object* v_ky_2694_; lean_object* v_vy_2695_; lean_object* v_c_2696_; lean_object* v_kz_2697_; lean_object* v_vz_2698_; lean_object* v_d_2699_; 
v_color_2684_ = lean_ctor_get_uint8(v___x_2683_, sizeof(void*)*4);
v_lchild_2685_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_lchild_2685_);
v_key_2686_ = lean_ctor_get(v___x_2683_, 1);
v_val_2687_ = lean_ctor_get(v___x_2683_, 2);
v_rchild_2688_ = lean_ctor_get(v___x_2683_, 3);
lean_inc(v_rchild_2688_);
if (v_color_2684_ == 0)
{
if (lean_obj_tag(v_lchild_2685_) == 1)
{
uint8_t v_color_2705_; 
v_color_2705_ = lean_ctor_get_uint8(v_lchild_2685_, sizeof(void*)*4);
if (v_color_2705_ == 0)
{
lean_object* v_lchild_2706_; lean_object* v_key_2707_; lean_object* v_val_2708_; lean_object* v_rchild_2709_; 
lean_inc(v_val_2687_);
lean_inc(v_key_2686_);
lean_dec_ref_known(v___x_2683_, 4);
v_lchild_2706_ = lean_ctor_get(v_lchild_2685_, 0);
lean_inc(v_lchild_2706_);
v_key_2707_ = lean_ctor_get(v_lchild_2685_, 1);
lean_inc(v_key_2707_);
v_val_2708_ = lean_ctor_get(v_lchild_2685_, 2);
lean_inc(v_val_2708_);
v_rchild_2709_ = lean_ctor_get(v_lchild_2685_, 3);
lean_inc(v_rchild_2709_);
lean_dec_ref_known(v_lchild_2685_, 4);
v_a_2690_ = v_lchild_2706_;
v_kx_2691_ = v_key_2707_;
v_vx_2692_ = v_val_2708_;
v_b_2693_ = v_rchild_2709_;
v_ky_2694_ = v_key_2686_;
v_vy_2695_ = v_val_2687_;
v_c_2696_ = v_rchild_2688_;
v_kz_2697_ = v_key_2675_;
v_vz_2698_ = v_val_2676_;
v_d_2699_ = v_rchild_2677_;
goto v___jp_2689_;
}
else
{
if (lean_obj_tag(v_rchild_2688_) == 1)
{
uint8_t v_color_2710_; 
v_color_2710_ = lean_ctor_get_uint8(v_rchild_2688_, sizeof(void*)*4);
if (v_color_2710_ == 0)
{
lean_object* v_lchild_2711_; lean_object* v_key_2712_; lean_object* v_val_2713_; lean_object* v_rchild_2714_; 
lean_inc(v_val_2687_);
lean_inc(v_key_2686_);
lean_dec_ref_known(v___x_2683_, 4);
v_lchild_2711_ = lean_ctor_get(v_rchild_2688_, 0);
lean_inc(v_lchild_2711_);
v_key_2712_ = lean_ctor_get(v_rchild_2688_, 1);
lean_inc(v_key_2712_);
v_val_2713_ = lean_ctor_get(v_rchild_2688_, 2);
lean_inc(v_val_2713_);
v_rchild_2714_ = lean_ctor_get(v_rchild_2688_, 3);
lean_inc(v_rchild_2714_);
lean_dec_ref_known(v_rchild_2688_, 4);
v_a_2690_ = v_lchild_2685_;
v_kx_2691_ = v_key_2686_;
v_vx_2692_ = v_val_2687_;
v_b_2693_ = v_lchild_2711_;
v_ky_2694_ = v_key_2712_;
v_vy_2695_ = v_val_2713_;
v_c_2696_ = v_rchild_2714_;
v_kz_2697_ = v_key_2675_;
v_vz_2698_ = v_val_2676_;
v_d_2699_ = v_rchild_2677_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec_ref_known(v_lchild_2685_, 4);
lean_del_object(v___x_2679_);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_rchild_2688_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; lean_object* v_unused_2723_; lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2722_ = lean_ctor_get(v_rchild_2688_, 3);
lean_dec(v_unused_2722_);
v_unused_2723_ = lean_ctor_get(v_rchild_2688_, 2);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_rchild_2688_, 1);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_rchild_2688_, 0);
lean_dec(v_unused_2725_);
v___x_2716_ = v_rchild_2688_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_dec(v_rchild_2688_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 3, v_rchild_2677_);
lean_ctor_set(v___x_2716_, 2, v_val_2676_);
lean_ctor_set(v___x_2716_, 1, v_key_2675_);
lean_ctor_set(v___x_2716_, 0, v___x_2683_);
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2720_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2720_, 3, v_rchild_2677_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*4, v_color_2652_);
return v___x_2719_;
}
}
}
}
else
{
lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_rchild_2688_);
lean_del_object(v___x_2679_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_lchild_2685_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2733_ = lean_ctor_get(v_lchild_2685_, 3);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_lchild_2685_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_lchild_2685_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_lchild_2685_, 0);
lean_dec(v_unused_2736_);
v___x_2727_ = v_lchild_2685_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_dec(v_lchild_2685_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 3, v_rchild_2677_);
lean_ctor_set(v___x_2727_, 2, v_val_2676_);
lean_ctor_set(v___x_2727_, 1, v_key_2675_);
lean_ctor_set(v___x_2727_, 0, v___x_2683_);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2731_, 3, v_rchild_2677_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*4, v_color_2652_);
return v___x_2730_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2688_) == 1)
{
uint8_t v_color_2737_; 
v_color_2737_ = lean_ctor_get_uint8(v_rchild_2688_, sizeof(void*)*4);
if (v_color_2737_ == 0)
{
lean_object* v_lchild_2738_; lean_object* v_key_2739_; lean_object* v_val_2740_; lean_object* v_rchild_2741_; 
lean_inc(v_val_2687_);
lean_inc(v_key_2686_);
lean_dec_ref_known(v___x_2683_, 4);
v_lchild_2738_ = lean_ctor_get(v_rchild_2688_, 0);
lean_inc(v_lchild_2738_);
v_key_2739_ = lean_ctor_get(v_rchild_2688_, 1);
lean_inc(v_key_2739_);
v_val_2740_ = lean_ctor_get(v_rchild_2688_, 2);
lean_inc(v_val_2740_);
v_rchild_2741_ = lean_ctor_get(v_rchild_2688_, 3);
lean_inc(v_rchild_2741_);
lean_dec_ref_known(v_rchild_2688_, 4);
v_a_2690_ = v_lchild_2685_;
v_kx_2691_ = v_key_2686_;
v_vx_2692_ = v_val_2687_;
v_b_2693_ = v_lchild_2738_;
v_ky_2694_ = v_key_2739_;
v_vy_2695_ = v_val_2740_;
v_c_2696_ = v_rchild_2741_;
v_kz_2697_ = v_key_2675_;
v_vz_2698_ = v_val_2676_;
v_d_2699_ = v_rchild_2677_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_lchild_2685_);
lean_del_object(v___x_2679_);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_rchild_2688_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2749_ = lean_ctor_get(v_rchild_2688_, 3);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_rchild_2688_, 2);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_rchild_2688_, 1);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_rchild_2688_, 0);
lean_dec(v_unused_2752_);
v___x_2743_ = v_rchild_2688_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_dec(v_rchild_2688_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 3, v_rchild_2677_);
lean_ctor_set(v___x_2743_, 2, v_val_2676_);
lean_ctor_set(v___x_2743_, 1, v_key_2675_);
lean_ctor_set(v___x_2743_, 0, v___x_2683_);
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_rchild_2677_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*4, v_color_2652_);
return v___x_2746_;
}
}
}
}
else
{
lean_object* v___x_2753_; 
lean_dec(v_rchild_2688_);
lean_dec(v_lchild_2685_);
lean_del_object(v___x_2679_);
v___x_2753_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2753_, 0, v___x_2683_);
lean_ctor_set(v___x_2753_, 1, v_key_2675_);
lean_ctor_set(v___x_2753_, 2, v_val_2676_);
lean_ctor_set(v___x_2753_, 3, v_rchild_2677_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*4, v_color_2652_);
return v___x_2753_;
}
}
}
else
{
lean_object* v___x_2754_; 
lean_dec(v_rchild_2688_);
lean_dec(v_lchild_2685_);
lean_del_object(v___x_2679_);
v___x_2754_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2754_, 0, v___x_2683_);
lean_ctor_set(v___x_2754_, 1, v_key_2675_);
lean_ctor_set(v___x_2754_, 2, v_val_2676_);
lean_ctor_set(v___x_2754_, 3, v_rchild_2677_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*4, v_color_2652_);
return v___x_2754_;
}
v___jp_2689_:
{
lean_object* v___x_2701_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 3, v_b_2693_);
lean_ctor_set(v___x_2679_, 2, v_vx_2692_);
lean_ctor_set(v___x_2679_, 1, v_kx_2691_);
lean_ctor_set(v___x_2679_, 0, v_a_2690_);
v___x_2701_ = v___x_2679_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2690_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_kx_2691_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_vx_2692_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_b_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, sizeof(void*)*4, v_color_2652_);
v___x_2701_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2702_, 0, v_c_2696_);
lean_ctor_set(v___x_2702_, 1, v_kz_2697_);
lean_ctor_set(v___x_2702_, 2, v_vz_2698_);
lean_ctor_set(v___x_2702_, 3, v_d_2699_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*4, v_color_2652_);
v___x_2703_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v_ky_2694_);
lean_ctor_set(v___x_2703_, 2, v_vy_2695_);
lean_ctor_set(v___x_2703_, 3, v___x_2702_);
lean_ctor_set_uint8(v___x_2703_, sizeof(void*)*4, v_color_2684_);
return v___x_2703_;
}
}
}
else
{
lean_object* v___x_2756_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v___x_2683_);
v___x_2756_ = v___x_2679_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_rchild_2677_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*4, v_color_2652_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
case 1:
{
lean_object* v___x_2759_; 
lean_dec(v_val_2676_);
lean_dec(v_key_2675_);
lean_dec_ref(v_cmp_2646_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 2, v_x_2649_);
lean_ctor_set(v___x_2679_, 1, v_x_2648_);
v___x_2759_ = v___x_2679_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_lchild_2674_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_x_2648_);
lean_ctor_set(v_reuseFailAlloc_2760_, 2, v_x_2649_);
lean_ctor_set(v_reuseFailAlloc_2760_, 3, v_rchild_2677_);
lean_ctor_set_uint8(v_reuseFailAlloc_2760_, sizeof(void*)*4, v_color_2652_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
default: 
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2646_, v_rchild_2677_, v_x_2648_, v_x_2649_);
if (lean_obj_tag(v___x_2761_) == 1)
{
uint8_t v_color_2762_; lean_object* v_lchild_2763_; lean_object* v_key_2764_; lean_object* v_val_2765_; lean_object* v_rchild_2766_; lean_object* v_a_2768_; lean_object* v_kx_2769_; lean_object* v_vx_2770_; lean_object* v_b_2771_; lean_object* v_ky_2772_; lean_object* v_vy_2773_; lean_object* v_c_2774_; lean_object* v_kz_2775_; lean_object* v_vz_2776_; lean_object* v_d_2777_; 
v_color_2762_ = lean_ctor_get_uint8(v___x_2761_, sizeof(void*)*4);
v_lchild_2763_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_lchild_2763_);
v_key_2764_ = lean_ctor_get(v___x_2761_, 1);
v_val_2765_ = lean_ctor_get(v___x_2761_, 2);
v_rchild_2766_ = lean_ctor_get(v___x_2761_, 3);
lean_inc(v_rchild_2766_);
if (v_color_2762_ == 0)
{
if (lean_obj_tag(v_lchild_2763_) == 1)
{
uint8_t v_color_2783_; 
v_color_2783_ = lean_ctor_get_uint8(v_lchild_2763_, sizeof(void*)*4);
if (v_color_2783_ == 0)
{
lean_object* v_lchild_2784_; lean_object* v_key_2785_; lean_object* v_val_2786_; lean_object* v_rchild_2787_; 
lean_inc(v_val_2765_);
lean_inc(v_key_2764_);
lean_dec_ref_known(v___x_2761_, 4);
v_lchild_2784_ = lean_ctor_get(v_lchild_2763_, 0);
lean_inc(v_lchild_2784_);
v_key_2785_ = lean_ctor_get(v_lchild_2763_, 1);
lean_inc(v_key_2785_);
v_val_2786_ = lean_ctor_get(v_lchild_2763_, 2);
lean_inc(v_val_2786_);
v_rchild_2787_ = lean_ctor_get(v_lchild_2763_, 3);
lean_inc(v_rchild_2787_);
lean_dec_ref_known(v_lchild_2763_, 4);
v_a_2768_ = v_lchild_2674_;
v_kx_2769_ = v_key_2675_;
v_vx_2770_ = v_val_2676_;
v_b_2771_ = v_lchild_2784_;
v_ky_2772_ = v_key_2785_;
v_vy_2773_ = v_val_2786_;
v_c_2774_ = v_rchild_2787_;
v_kz_2775_ = v_key_2764_;
v_vz_2776_ = v_val_2765_;
v_d_2777_ = v_rchild_2766_;
goto v___jp_2767_;
}
else
{
if (lean_obj_tag(v_rchild_2766_) == 1)
{
uint8_t v_color_2788_; 
v_color_2788_ = lean_ctor_get_uint8(v_rchild_2766_, sizeof(void*)*4);
if (v_color_2788_ == 0)
{
lean_object* v_lchild_2789_; lean_object* v_key_2790_; lean_object* v_val_2791_; lean_object* v_rchild_2792_; 
lean_inc(v_val_2765_);
lean_inc(v_key_2764_);
lean_dec_ref_known(v___x_2761_, 4);
v_lchild_2789_ = lean_ctor_get(v_rchild_2766_, 0);
lean_inc(v_lchild_2789_);
v_key_2790_ = lean_ctor_get(v_rchild_2766_, 1);
lean_inc(v_key_2790_);
v_val_2791_ = lean_ctor_get(v_rchild_2766_, 2);
lean_inc(v_val_2791_);
v_rchild_2792_ = lean_ctor_get(v_rchild_2766_, 3);
lean_inc(v_rchild_2792_);
lean_dec_ref_known(v_rchild_2766_, 4);
v_a_2768_ = v_lchild_2674_;
v_kx_2769_ = v_key_2675_;
v_vx_2770_ = v_val_2676_;
v_b_2771_ = v_lchild_2763_;
v_ky_2772_ = v_key_2764_;
v_vy_2773_ = v_val_2765_;
v_c_2774_ = v_lchild_2789_;
v_kz_2775_ = v_key_2790_;
v_vz_2776_ = v_val_2791_;
v_d_2777_ = v_rchild_2792_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref_known(v_lchild_2763_, 4);
lean_del_object(v___x_2679_);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_rchild_2766_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; 
v_unused_2800_ = lean_ctor_get(v_rchild_2766_, 3);
lean_dec(v_unused_2800_);
v_unused_2801_ = lean_ctor_get(v_rchild_2766_, 2);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_rchild_2766_, 1);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_rchild_2766_, 0);
lean_dec(v_unused_2803_);
v___x_2794_ = v_rchild_2766_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v_rchild_2766_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 3, v___x_2761_);
lean_ctor_set(v___x_2794_, 2, v_val_2676_);
lean_ctor_set(v___x_2794_, 1, v_key_2675_);
lean_ctor_set(v___x_2794_, 0, v_lchild_2674_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_lchild_2674_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v___x_2761_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_ctor_set_uint8(v___x_2797_, sizeof(void*)*4, v_color_2652_);
return v___x_2797_;
}
}
}
}
else
{
lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_rchild_2766_);
lean_del_object(v___x_2679_);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_lchild_2763_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; lean_object* v_unused_2812_; lean_object* v_unused_2813_; lean_object* v_unused_2814_; 
v_unused_2811_ = lean_ctor_get(v_lchild_2763_, 3);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_lchild_2763_, 2);
lean_dec(v_unused_2812_);
v_unused_2813_ = lean_ctor_get(v_lchild_2763_, 1);
lean_dec(v_unused_2813_);
v_unused_2814_ = lean_ctor_get(v_lchild_2763_, 0);
lean_dec(v_unused_2814_);
v___x_2805_ = v_lchild_2763_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_dec(v_lchild_2763_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 3, v___x_2761_);
lean_ctor_set(v___x_2805_, 2, v_val_2676_);
lean_ctor_set(v___x_2805_, 1, v_key_2675_);
lean_ctor_set(v___x_2805_, 0, v_lchild_2674_);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_lchild_2674_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2809_, 3, v___x_2761_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_ctor_set_uint8(v___x_2808_, sizeof(void*)*4, v_color_2652_);
return v___x_2808_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2766_) == 1)
{
uint8_t v_color_2815_; 
v_color_2815_ = lean_ctor_get_uint8(v_rchild_2766_, sizeof(void*)*4);
if (v_color_2815_ == 0)
{
lean_object* v_lchild_2816_; lean_object* v_key_2817_; lean_object* v_val_2818_; lean_object* v_rchild_2819_; 
lean_inc(v_val_2765_);
lean_inc(v_key_2764_);
lean_dec_ref_known(v___x_2761_, 4);
v_lchild_2816_ = lean_ctor_get(v_rchild_2766_, 0);
lean_inc(v_lchild_2816_);
v_key_2817_ = lean_ctor_get(v_rchild_2766_, 1);
lean_inc(v_key_2817_);
v_val_2818_ = lean_ctor_get(v_rchild_2766_, 2);
lean_inc(v_val_2818_);
v_rchild_2819_ = lean_ctor_get(v_rchild_2766_, 3);
lean_inc(v_rchild_2819_);
lean_dec_ref_known(v_rchild_2766_, 4);
v_a_2768_ = v_lchild_2674_;
v_kx_2769_ = v_key_2675_;
v_vx_2770_ = v_val_2676_;
v_b_2771_ = v_lchild_2763_;
v_ky_2772_ = v_key_2764_;
v_vy_2773_ = v_val_2765_;
v_c_2774_ = v_lchild_2816_;
v_kz_2775_ = v_key_2817_;
v_vz_2776_ = v_val_2818_;
v_d_2777_ = v_rchild_2819_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_lchild_2763_);
lean_del_object(v___x_2679_);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_rchild_2766_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; 
v_unused_2827_ = lean_ctor_get(v_rchild_2766_, 3);
lean_dec(v_unused_2827_);
v_unused_2828_ = lean_ctor_get(v_rchild_2766_, 2);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_rchild_2766_, 1);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_rchild_2766_, 0);
lean_dec(v_unused_2830_);
v___x_2821_ = v_rchild_2766_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v_rchild_2766_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 3, v___x_2761_);
lean_ctor_set(v___x_2821_, 2, v_val_2676_);
lean_ctor_set(v___x_2821_, 1, v_key_2675_);
lean_ctor_set(v___x_2821_, 0, v_lchild_2674_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_lchild_2674_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v___x_2761_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*4, v_color_2652_);
return v___x_2824_;
}
}
}
}
else
{
lean_object* v___x_2831_; 
lean_dec(v_rchild_2766_);
lean_dec(v_lchild_2763_);
lean_del_object(v___x_2679_);
v___x_2831_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2831_, 0, v_lchild_2674_);
lean_ctor_set(v___x_2831_, 1, v_key_2675_);
lean_ctor_set(v___x_2831_, 2, v_val_2676_);
lean_ctor_set(v___x_2831_, 3, v___x_2761_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*4, v_color_2652_);
return v___x_2831_;
}
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v_rchild_2766_);
lean_dec(v_lchild_2763_);
lean_del_object(v___x_2679_);
v___x_2832_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2832_, 0, v_lchild_2674_);
lean_ctor_set(v___x_2832_, 1, v_key_2675_);
lean_ctor_set(v___x_2832_, 2, v_val_2676_);
lean_ctor_set(v___x_2832_, 3, v___x_2761_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*4, v_color_2652_);
return v___x_2832_;
}
v___jp_2767_:
{
lean_object* v___x_2779_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 3, v_b_2771_);
lean_ctor_set(v___x_2679_, 2, v_vx_2770_);
lean_ctor_set(v___x_2679_, 1, v_kx_2769_);
lean_ctor_set(v___x_2679_, 0, v_a_2768_);
v___x_2779_ = v___x_2679_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2768_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_kx_2769_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_vx_2770_);
lean_ctor_set(v_reuseFailAlloc_2782_, 3, v_b_2771_);
lean_ctor_set_uint8(v_reuseFailAlloc_2782_, sizeof(void*)*4, v_color_2652_);
v___x_2779_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2780_, 0, v_c_2774_);
lean_ctor_set(v___x_2780_, 1, v_kz_2775_);
lean_ctor_set(v___x_2780_, 2, v_vz_2776_);
lean_ctor_set(v___x_2780_, 3, v_d_2777_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*4, v_color_2652_);
v___x_2781_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v_ky_2772_);
lean_ctor_set(v___x_2781_, 2, v_vy_2773_);
lean_ctor_set(v___x_2781_, 3, v___x_2780_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*4, v_color_2762_);
return v___x_2781_;
}
}
}
else
{
lean_object* v___x_2834_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 3, v___x_2761_);
v___x_2834_ = v___x_2679_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_lchild_2674_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_key_2675_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2835_, 3, v___x_2761_);
lean_ctor_set_uint8(v_reuseFailAlloc_2835_, sizeof(void*)*4, v_color_2652_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* v_cmp_2837_, lean_object* v_t_2838_, lean_object* v_k_2839_, lean_object* v_v_2840_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = l_Lean_RBNode_isRed___redArg(v_t_2838_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2837_, v_t_2838_, v_k_2839_, v_v_2840_);
return v___x_2842_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2837_, v_t_2838_, v_k_2839_, v_v_2840_);
v___x_2844_ = l_Lean_RBNode_setBlack___redArg(v___x_2843_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* v_cmp_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_){
_start:
{
if (lean_obj_tag(v_x_2846_) == 0)
{
lean_object* v___x_2848_; 
lean_dec(v_x_2847_);
lean_dec_ref(v_cmp_2845_);
v___x_2848_ = lean_box(0);
return v___x_2848_;
}
else
{
lean_object* v_lchild_2849_; lean_object* v_key_2850_; lean_object* v_val_2851_; lean_object* v_rchild_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_lchild_2849_ = lean_ctor_get(v_x_2846_, 0);
lean_inc(v_lchild_2849_);
v_key_2850_ = lean_ctor_get(v_x_2846_, 1);
lean_inc(v_key_2850_);
v_val_2851_ = lean_ctor_get(v_x_2846_, 2);
lean_inc(v_val_2851_);
v_rchild_2852_ = lean_ctor_get(v_x_2846_, 3);
lean_inc(v_rchild_2852_);
lean_dec_ref_known(v_x_2846_, 4);
lean_inc_ref(v_cmp_2845_);
lean_inc(v_x_2847_);
v___x_2853_ = lean_apply_2(v_cmp_2845_, v_x_2847_, v_key_2850_);
v___x_2854_ = lean_unbox(v___x_2853_);
switch(v___x_2854_)
{
case 0:
{
lean_dec(v_rchild_2852_);
lean_dec(v_val_2851_);
v_x_2846_ = v_lchild_2849_;
goto _start;
}
case 1:
{
lean_object* v___x_2856_; 
lean_dec(v_rchild_2852_);
lean_dec(v_lchild_2849_);
lean_dec(v_x_2847_);
lean_dec_ref(v_cmp_2845_);
v___x_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_val_2851_);
return v___x_2856_;
}
default: 
{
lean_dec(v_val_2851_);
lean_dec(v_lchild_2849_);
v_x_2846_ = v_rchild_2852_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* v_cmp_2858_, lean_object* v_mergeFn_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 0)
{
lean_dec(v_mergeFn_2859_);
lean_dec_ref(v_cmp_2858_);
return v_x_2860_;
}
else
{
lean_object* v_lchild_2862_; lean_object* v_key_2863_; lean_object* v_val_2864_; lean_object* v_rchild_2865_; lean_object* v_val_2866_; lean_object* v___y_2868_; lean_object* v___x_2871_; 
v_lchild_2862_ = lean_ctor_get(v_x_2861_, 0);
lean_inc(v_lchild_2862_);
v_key_2863_ = lean_ctor_get(v_x_2861_, 1);
lean_inc_n(v_key_2863_, 2);
v_val_2864_ = lean_ctor_get(v_x_2861_, 2);
lean_inc(v_val_2864_);
v_rchild_2865_ = lean_ctor_get(v_x_2861_, 3);
lean_inc(v_rchild_2865_);
lean_dec_ref_known(v_x_2861_, 4);
lean_inc(v_mergeFn_2859_);
lean_inc_ref_n(v_cmp_2858_, 2);
v_val_2866_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2858_, v_mergeFn_2859_, v_x_2860_, v_lchild_2862_);
lean_inc(v_val_2866_);
v___x_2871_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2858_, v_val_2866_, v_key_2863_);
if (lean_obj_tag(v___x_2871_) == 0)
{
v___y_2868_ = v_val_2864_;
goto v___jp_2867_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2873_; 
v_val_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_val_2872_);
lean_dec_ref_known(v___x_2871_, 1);
lean_inc(v_mergeFn_2859_);
lean_inc(v_key_2863_);
v___x_2873_ = lean_apply_3(v_mergeFn_2859_, v_key_2863_, v_val_2872_, v_val_2864_);
v___y_2868_ = v___x_2873_;
goto v___jp_2867_;
}
v___jp_2867_:
{
lean_object* v___x_2869_; 
lean_inc_ref(v_cmp_2858_);
v___x_2869_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2858_, v_val_2866_, v_key_2863_, v___y_2868_);
v_x_2860_ = v___x_2869_;
v_x_2861_ = v_rchild_2865_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* v_cmp_2874_, lean_object* v_mergeFn_2875_, lean_object* v_t_u2081_2876_, lean_object* v_t_u2082_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2874_, v_mergeFn_2875_, v_t_u2081_2876_, v_t_u2082_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_cmp_2881_, lean_object* v_mergeFn_2882_, lean_object* v_t_u2081_2883_, lean_object* v_t_u2082_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2881_, v_mergeFn_2882_, v_t_u2081_2883_, v_t_u2082_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* v_00_u03b1_2886_, lean_object* v_cmp_2887_, lean_object* v_00_u03b2_2888_, lean_object* v_t_2889_, lean_object* v_k_2890_, lean_object* v_v_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2887_, v_t_2889_, v_k_2890_, v_v_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* v_00_u03b1_2893_, lean_object* v_cmp_2894_, lean_object* v_00_u03b2_2895_, lean_object* v_x_2896_, lean_object* v_x_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2894_, v_x_2896_, v_x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* v_00_u03b1_2899_, lean_object* v_00_u03b2_2900_, lean_object* v_cmp_2901_, lean_object* v_mergeFn_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2901_, v_mergeFn_2902_, v_x_2903_, v_x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* v_00_u03b1_2906_, lean_object* v_cmp_2907_, lean_object* v_00_u03b2_2908_, lean_object* v_x_2909_, lean_object* v_x_2910_, lean_object* v_x_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2907_, v_x_2909_, v_x_2910_, v_x_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* v_t_u2082_2913_, lean_object* v_cmp_2914_, lean_object* v_mergeFn_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
if (lean_obj_tag(v_x_2917_) == 0)
{
lean_dec(v_mergeFn_2915_);
lean_dec_ref(v_cmp_2914_);
lean_dec(v_t_u2082_2913_);
return v_x_2916_;
}
else
{
lean_object* v_lchild_2918_; lean_object* v_key_2919_; lean_object* v_val_2920_; lean_object* v_rchild_2921_; lean_object* v_val_2922_; lean_object* v___x_2923_; 
v_lchild_2918_ = lean_ctor_get(v_x_2917_, 0);
lean_inc(v_lchild_2918_);
v_key_2919_ = lean_ctor_get(v_x_2917_, 1);
lean_inc_n(v_key_2919_, 2);
v_val_2920_ = lean_ctor_get(v_x_2917_, 2);
lean_inc(v_val_2920_);
v_rchild_2921_ = lean_ctor_get(v_x_2917_, 3);
lean_inc(v_rchild_2921_);
lean_dec_ref_known(v_x_2917_, 4);
lean_inc(v_mergeFn_2915_);
lean_inc_ref_n(v_cmp_2914_, 2);
lean_inc_n(v_t_u2082_2913_, 2);
v_val_2922_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2913_, v_cmp_2914_, v_mergeFn_2915_, v_x_2916_, v_lchild_2918_);
v___x_2923_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2914_, v_t_u2082_2913_, v_key_2919_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_dec(v_val_2920_);
lean_dec(v_key_2919_);
v_x_2916_ = v_val_2922_;
v_x_2917_ = v_rchild_2921_;
goto _start;
}
else
{
lean_object* v_val_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_val_2925_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_val_2925_);
lean_dec_ref_known(v___x_2923_, 1);
lean_inc(v_mergeFn_2915_);
lean_inc(v_key_2919_);
v___x_2926_ = lean_apply_3(v_mergeFn_2915_, v_key_2919_, v_val_2920_, v_val_2925_);
lean_inc_ref(v_cmp_2914_);
v___x_2927_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2914_, v_val_2922_, v_key_2919_, v___x_2926_);
v_x_2916_ = v___x_2927_;
v_x_2917_ = v_rchild_2921_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* v_cmp_2929_, lean_object* v_mergeFn_2930_, lean_object* v_t_u2081_2931_, lean_object* v_t_u2082_2932_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_box(0);
v___x_2934_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2932_, v_cmp_2929_, v_mergeFn_2930_, v___x_2933_, v_t_u2081_2931_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* v_00_u03b1_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_cmp_2937_, lean_object* v_00_u03b3_2938_, lean_object* v_00_u03b4_2939_, lean_object* v_mergeFn_2940_, lean_object* v_t_u2081_2941_, lean_object* v_t_u2082_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_RBMap_intersectBy___redArg(v_cmp_2937_, v_mergeFn_2940_, v_t_u2081_2941_, v_t_u2082_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* v_00_u03b1_2944_, lean_object* v_00_u03b2_2945_, lean_object* v_00_u03b4_2946_, lean_object* v_00_u03b3_2947_, lean_object* v_t_u2082_2948_, lean_object* v_cmp_2949_, lean_object* v_mergeFn_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2948_, v_cmp_2949_, v_mergeFn_2950_, v_x_2951_, v_x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* v_f_2954_, lean_object* v_cmp_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
lean_dec_ref(v_cmp_2955_);
lean_dec_ref(v_f_2954_);
return v_x_2956_;
}
else
{
lean_object* v_lchild_2958_; lean_object* v_key_2959_; lean_object* v_val_2960_; lean_object* v_rchild_2961_; lean_object* v_val_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_lchild_2958_ = lean_ctor_get(v_x_2957_, 0);
lean_inc(v_lchild_2958_);
v_key_2959_ = lean_ctor_get(v_x_2957_, 1);
lean_inc_n(v_key_2959_, 2);
v_val_2960_ = lean_ctor_get(v_x_2957_, 2);
lean_inc_n(v_val_2960_, 2);
v_rchild_2961_ = lean_ctor_get(v_x_2957_, 3);
lean_inc(v_rchild_2961_);
lean_dec_ref_known(v_x_2957_, 4);
lean_inc_ref(v_cmp_2955_);
lean_inc_ref_n(v_f_2954_, 2);
v_val_2962_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2954_, v_cmp_2955_, v_x_2956_, v_lchild_2958_);
v___x_2963_ = lean_apply_2(v_f_2954_, v_key_2959_, v_val_2960_);
v___x_2964_ = lean_unbox(v___x_2963_);
if (v___x_2964_ == 0)
{
lean_dec(v_val_2960_);
lean_dec(v_key_2959_);
v_x_2956_ = v_val_2962_;
v_x_2957_ = v_rchild_2961_;
goto _start;
}
else
{
lean_object* v___x_2966_; 
lean_inc_ref(v_cmp_2955_);
v___x_2966_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2955_, v_val_2962_, v_key_2959_, v_val_2960_);
v_x_2956_ = v___x_2966_;
v_x_2957_ = v_rchild_2961_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* v_cmp_2968_, lean_object* v_f_2969_, lean_object* v_m_2970_){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_box(0);
v___x_2972_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2969_, v_cmp_2968_, v___x_2971_, v_m_2970_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* v_00_u03b1_2973_, lean_object* v_00_u03b2_2974_, lean_object* v_cmp_2975_, lean_object* v_f_2976_, lean_object* v_m_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_RBMap_filter___redArg(v_cmp_2975_, v_f_2976_, v_m_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* v_00_u03b1_2979_, lean_object* v_00_u03b2_2980_, lean_object* v_f_2981_, lean_object* v_cmp_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2981_, v_cmp_2982_, v_x_2983_, v_x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* v_f_2986_, lean_object* v_cmp_2987_, lean_object* v_x_2988_, lean_object* v_x_2989_){
_start:
{
if (lean_obj_tag(v_x_2989_) == 0)
{
lean_dec_ref(v_cmp_2987_);
lean_dec_ref(v_f_2986_);
return v_x_2988_;
}
else
{
lean_object* v_lchild_2990_; lean_object* v_key_2991_; lean_object* v_val_2992_; lean_object* v_rchild_2993_; lean_object* v_val_2994_; lean_object* v___x_2995_; 
v_lchild_2990_ = lean_ctor_get(v_x_2989_, 0);
lean_inc(v_lchild_2990_);
v_key_2991_ = lean_ctor_get(v_x_2989_, 1);
lean_inc_n(v_key_2991_, 2);
v_val_2992_ = lean_ctor_get(v_x_2989_, 2);
lean_inc(v_val_2992_);
v_rchild_2993_ = lean_ctor_get(v_x_2989_, 3);
lean_inc(v_rchild_2993_);
lean_dec_ref_known(v_x_2989_, 4);
lean_inc_ref(v_cmp_2987_);
lean_inc_ref_n(v_f_2986_, 2);
v_val_2994_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2986_, v_cmp_2987_, v_x_2988_, v_lchild_2990_);
v___x_2995_ = lean_apply_2(v_f_2986_, v_key_2991_, v_val_2992_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec(v_key_2991_);
v_x_2988_ = v_val_2994_;
v_x_2989_ = v_rchild_2993_;
goto _start;
}
else
{
lean_object* v_val_2997_; lean_object* v___x_2998_; 
v_val_2997_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2997_);
lean_dec_ref_known(v___x_2995_, 1);
lean_inc_ref(v_cmp_2987_);
v___x_2998_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2987_, v_val_2994_, v_key_2991_, v_val_2997_);
v_x_2988_ = v___x_2998_;
v_x_2989_ = v_rchild_2993_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* v_cmp_3000_, lean_object* v_f_3001_, lean_object* v_m_3002_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_box(0);
v___x_3004_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_3001_, v_cmp_3000_, v___x_3003_, v_m_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* v_00_u03b1_3005_, lean_object* v_00_u03b2_3006_, lean_object* v_cmp_3007_, lean_object* v_00_u03b3_3008_, lean_object* v_f_3009_, lean_object* v_m_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_RBMap_filterMap___redArg(v_cmp_3007_, v_f_3009_, v_m_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* v_00_u03b1_3012_, lean_object* v_00_u03b2_3013_, lean_object* v_00_u03b3_3014_, lean_object* v_f_3015_, lean_object* v_cmp_3016_, lean_object* v_x_3017_, lean_object* v_x_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_3015_, v_cmp_3016_, v_x_3017_, v_x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* v_cmp_3020_, lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
if (lean_obj_tag(v_x_3022_) == 0)
{
lean_dec_ref(v_cmp_3020_);
return v_x_3021_;
}
else
{
lean_object* v_head_3023_; lean_object* v_tail_3024_; lean_object* v_fst_3025_; lean_object* v_snd_3026_; lean_object* v___x_3027_; 
v_head_3023_ = lean_ctor_get(v_x_3022_, 0);
lean_inc(v_head_3023_);
v_tail_3024_ = lean_ctor_get(v_x_3022_, 1);
lean_inc(v_tail_3024_);
lean_dec_ref_known(v_x_3022_, 2);
v_fst_3025_ = lean_ctor_get(v_head_3023_, 0);
lean_inc(v_fst_3025_);
v_snd_3026_ = lean_ctor_get(v_head_3023_, 1);
lean_inc(v_snd_3026_);
lean_dec(v_head_3023_);
lean_inc_ref(v_cmp_3020_);
v___x_3027_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_3020_, v_x_3021_, v_fst_3025_, v_snd_3026_);
v_x_3021_ = v___x_3027_;
v_x_3022_ = v_tail_3024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* v_l_3029_, lean_object* v_cmp_3030_){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_box(0);
v___x_3032_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3030_, v___x_3031_, v_l_3029_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* v_00_u03b1_3033_, lean_object* v_00_u03b2_3034_, lean_object* v_l_3035_, lean_object* v_cmp_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_rbmapOf___redArg(v_l_3035_, v_cmp_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* v_00_u03b1_3038_, lean_object* v_00_u03b2_3039_, lean_object* v_cmp_3040_, lean_object* v_x_3041_, lean_object* v_x_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3040_, v_x_3041_, v_x_3042_);
return v___x_3043_;
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
