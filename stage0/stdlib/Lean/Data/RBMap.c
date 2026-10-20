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
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBColor_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_RBColor_ctorIdx___impl(v_x_4__boxed_5_);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___redArg(lean_object* v_x_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_tag_nat(v_x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___redArg___boxed(lean_object* v_x_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_RBNode_ctorIdx___impl___redArg(v_x_50_);
lean_dec(v_x_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_tag_nat(v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorIdx___impl___boxed(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_RBNode_ctorIdx___impl(v_00_u03b1_56_, v_00_u03b2_57_, v_x_58_);
lean_dec(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___redArg(lean_object* v_t_60_, lean_object* v_k_61_){
_start:
{
if (lean_obj_tag(v_t_60_) == 0)
{
return v_k_61_;
}
else
{
uint8_t v_color_62_; lean_object* v_lchild_63_; lean_object* v_key_64_; lean_object* v_val_65_; lean_object* v_rchild_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_color_62_ = lean_ctor_get_uint8(v_t_60_, sizeof(void*)*4);
v_lchild_63_ = lean_ctor_get(v_t_60_, 0);
lean_inc(v_lchild_63_);
v_key_64_ = lean_ctor_get(v_t_60_, 1);
lean_inc(v_key_64_);
v_val_65_ = lean_ctor_get(v_t_60_, 2);
lean_inc(v_val_65_);
v_rchild_66_ = lean_ctor_get(v_t_60_, 3);
lean_inc(v_rchild_66_);
lean_dec_ref_known(v_t_60_, 4);
v___x_67_ = lean_box(v_color_62_);
v___x_68_ = lean_apply_5(v_k_61_, v___x_67_, v_lchild_63_, v_key_64_, v_val_65_, v_rchild_66_);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim(lean_object* v_00_u03b1_69_, lean_object* v_00_u03b2_70_, lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_RBNode_ctorElim___redArg(v_t_73_, v_k_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ctorElim___boxed(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_motive_79_, lean_object* v_ctorIdx_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_k_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_RBNode_ctorElim(v_00_u03b1_77_, v_00_u03b2_78_, v_motive_79_, v_ctorIdx_80_, v_t_81_, v_h_82_, v_k_83_);
lean_dec(v_ctorIdx_80_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim___redArg(lean_object* v_t_85_, lean_object* v_leaf_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_RBNode_ctorElim___redArg(v_t_85_, v_leaf_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_leaf_elim(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_leaf_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_RBNode_ctorElim___redArg(v_t_91_, v_leaf_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim___redArg(lean_object* v_t_95_, lean_object* v_node_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_RBNode_ctorElim___redArg(v_t_95_, v_node_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_node_elim(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_node_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_RBNode_ctorElim___redArg(v_t_101_, v_node_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg(lean_object* v_f_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v___x_107_; 
lean_dec_ref(v_f_105_);
v___x_107_ = lean_unsigned_to_nat(0u);
return v___x_107_;
}
else
{
lean_object* v_lchild_108_; lean_object* v_rchild_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_lchild_108_ = lean_ctor_get(v_x_106_, 0);
v_rchild_109_ = lean_ctor_get(v_x_106_, 3);
lean_inc_ref_n(v_f_105_, 2);
v___x_110_ = l_Lean_RBNode_depth___redArg(v_f_105_, v_lchild_108_);
v___x_111_ = l_Lean_RBNode_depth___redArg(v_f_105_, v_rchild_109_);
v___x_112_ = lean_apply_2(v_f_105_, v___x_110_, v___x_111_);
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___redArg___boxed(lean_object* v_f_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_RBNode_depth___redArg(v_f_115_, v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_f_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_RBNode_depth___redArg(v_f_120_, v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_depth___boxed(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_f_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_RBNode_depth(v_00_u03b1_123_, v_00_u03b2_124_, v_f_125_, v_x_126_);
lean_dec(v_x_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg(lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_lchild_130_; 
v_lchild_130_ = lean_ctor_get(v_x_128_, 0);
if (lean_obj_tag(v_lchild_130_) == 0)
{
lean_object* v_key_131_; lean_object* v_val_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_key_131_ = lean_ctor_get(v_x_128_, 1);
v_val_132_ = lean_ctor_get(v_x_128_, 2);
lean_inc(v_val_132_);
lean_inc(v_key_131_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_key_131_);
lean_ctor_set(v___x_133_, 1, v_val_132_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
else
{
v_x_128_ = v_lchild_130_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___redArg___boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_RBNode_min___redArg(v_x_136_);
lean_dec(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min(lean_object* v_00_u03b1_138_, lean_object* v_00_u03b2_139_, lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_RBNode_min___redArg(v_x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_min___boxed(lean_object* v_00_u03b1_142_, lean_object* v_00_u03b2_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_RBNode_min(v_00_u03b1_142_, v_00_u03b2_143_, v_x_144_);
lean_dec(v_x_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg(lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v___x_147_; 
v___x_147_ = lean_box(0);
return v___x_147_;
}
else
{
lean_object* v_rchild_148_; 
v_rchild_148_ = lean_ctor_get(v_x_146_, 3);
if (lean_obj_tag(v_rchild_148_) == 0)
{
lean_object* v_key_149_; lean_object* v_val_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_key_149_ = lean_ctor_get(v_x_146_, 1);
v_val_150_ = lean_ctor_get(v_x_146_, 2);
lean_inc(v_val_150_);
lean_inc(v_key_149_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v_key_149_);
lean_ctor_set(v___x_151_, 1, v_val_150_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
else
{
v_x_146_ = v_rchild_148_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___redArg___boxed(lean_object* v_x_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_RBNode_max___redArg(v_x_154_);
lean_dec(v_x_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_RBNode_max___redArg(v_x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_max___boxed(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_RBNode_max(v_00_u03b1_160_, v_00_u03b2_161_, v_x_162_);
lean_dec(v_x_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___redArg(lean_object* v_f_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_dec(v_f_164_);
return v_x_165_;
}
else
{
lean_object* v_lchild_167_; lean_object* v_key_168_; lean_object* v_val_169_; lean_object* v_rchild_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_lchild_167_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_lchild_167_);
v_key_168_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_key_168_);
v_val_169_ = lean_ctor_get(v_x_166_, 2);
lean_inc(v_val_169_);
v_rchild_170_ = lean_ctor_get(v_x_166_, 3);
lean_inc(v_rchild_170_);
lean_dec_ref_known(v_x_166_, 4);
lean_inc_n(v_f_164_, 2);
v___x_171_ = l_Lean_RBNode_fold___redArg(v_f_164_, v_x_165_, v_lchild_167_);
v___x_172_ = lean_apply_3(v_f_164_, v___x_171_, v_key_168_, v_val_169_);
v_x_165_ = v___x_172_;
v_x_166_ = v_rchild_170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_00_u03c3_176_, lean_object* v_f_177_, lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_RBNode_fold___redArg(v_f_177_, v_x_178_, v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__1(lean_object* v_f_181_, lean_object* v_key_182_, lean_object* v_val_183_, lean_object* v_toBind_184_, lean_object* v___f_185_, lean_object* v_____r_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_apply_2(v_f_181_, v_key_182_, v_val_183_);
v___x_188_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_187_, v___f_185_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg(lean_object* v_inst_189_, lean_object* v_f_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v_toApplicative_192_; lean_object* v_toPure_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_toApplicative_192_ = lean_ctor_get(v_inst_189_, 0);
lean_inc_ref(v_toApplicative_192_);
lean_dec(v_f_190_);
lean_dec_ref(v_inst_189_);
v_toPure_193_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc(v_toPure_193_);
lean_dec_ref(v_toApplicative_192_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_apply_2(v_toPure_193_, lean_box(0), v___x_194_);
return v___x_195_;
}
else
{
lean_object* v_toBind_196_; lean_object* v_lchild_197_; lean_object* v_key_198_; lean_object* v_val_199_; lean_object* v_rchild_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_toBind_196_ = lean_ctor_get(v_inst_189_, 1);
lean_inc_n(v_toBind_196_, 2);
v_lchild_197_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_lchild_197_);
v_key_198_ = lean_ctor_get(v_x_191_, 1);
lean_inc(v_key_198_);
v_val_199_ = lean_ctor_get(v_x_191_, 2);
lean_inc(v_val_199_);
v_rchild_200_ = lean_ctor_get(v_x_191_, 3);
lean_inc(v_rchild_200_);
lean_dec_ref_known(v_x_191_, 4);
lean_inc_n(v_f_190_, 2);
lean_inc_ref(v_inst_189_);
v___f_201_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_201_, 0, v_inst_189_);
lean_closure_set(v___f_201_, 1, v_f_190_);
lean_closure_set(v___f_201_, 2, v_rchild_200_);
v___f_202_ = lean_alloc_closure((void*)(l_Lean_RBNode_forM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_202_, 0, v_f_190_);
lean_closure_set(v___f_202_, 1, v_key_198_);
lean_closure_set(v___f_202_, 2, v_val_199_);
lean_closure_set(v___f_202_, 3, v_toBind_196_);
lean_closure_set(v___f_202_, 4, v___f_201_);
v___x_203_ = l_Lean_RBNode_forM___redArg(v_inst_189_, v_f_190_, v_lchild_197_);
v___x_204_ = lean_apply_4(v_toBind_196_, lean_box(0), lean_box(0), v___x_203_, v___f_202_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM___redArg___lam__0(lean_object* v_inst_205_, lean_object* v_f_206_, lean_object* v_rchild_207_, lean_object* v_____r_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_RBNode_forM___redArg(v_inst_205_, v_f_206_, v_rchild_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forM(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_m_212_, lean_object* v_inst_213_, lean_object* v_f_214_, lean_object* v_x_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_RBNode_forM___redArg(v_inst_213_, v_f_214_, v_x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__1(lean_object* v_f_217_, lean_object* v_key_218_, lean_object* v_val_219_, lean_object* v_toBind_220_, lean_object* v___f_221_, lean_object* v_b_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_apply_3(v_f_217_, v_b_222_, v_key_218_, v_val_219_);
v___x_224_ = lean_apply_4(v_toBind_220_, lean_box(0), lean_box(0), v___x_223_, v___f_221_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg(lean_object* v_inst_225_, lean_object* v_f_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_toApplicative_229_; lean_object* v_toPure_230_; lean_object* v___x_231_; 
v_toApplicative_229_ = lean_ctor_get(v_inst_225_, 0);
lean_inc_ref(v_toApplicative_229_);
lean_dec(v_f_226_);
lean_dec_ref(v_inst_225_);
v_toPure_230_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_inc(v_toPure_230_);
lean_dec_ref(v_toApplicative_229_);
v___x_231_ = lean_apply_2(v_toPure_230_, lean_box(0), v_x_227_);
return v___x_231_;
}
else
{
lean_object* v_toBind_232_; lean_object* v_lchild_233_; lean_object* v_key_234_; lean_object* v_val_235_; lean_object* v_rchild_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_toBind_232_ = lean_ctor_get(v_inst_225_, 1);
lean_inc_n(v_toBind_232_, 2);
v_lchild_233_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_lchild_233_);
v_key_234_ = lean_ctor_get(v_x_228_, 1);
lean_inc(v_key_234_);
v_val_235_ = lean_ctor_get(v_x_228_, 2);
lean_inc(v_val_235_);
v_rchild_236_ = lean_ctor_get(v_x_228_, 3);
lean_inc(v_rchild_236_);
lean_dec_ref_known(v_x_228_, 4);
lean_inc_n(v_f_226_, 2);
lean_inc_ref(v_inst_225_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_237_, 0, v_inst_225_);
lean_closure_set(v___f_237_, 1, v_f_226_);
lean_closure_set(v___f_237_, 2, v_rchild_236_);
v___f_238_ = lean_alloc_closure((void*)(l_Lean_RBNode_foldM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_238_, 0, v_f_226_);
lean_closure_set(v___f_238_, 1, v_key_234_);
lean_closure_set(v___f_238_, 2, v_val_235_);
lean_closure_set(v___f_238_, 3, v_toBind_232_);
lean_closure_set(v___f_238_, 4, v___f_237_);
v___x_239_ = l_Lean_RBNode_foldM___redArg(v_inst_225_, v_f_226_, v_x_227_, v_lchild_233_);
v___x_240_ = lean_apply_4(v_toBind_232_, lean_box(0), lean_box(0), v___x_239_, v___f_238_);
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___redArg___lam__0(lean_object* v_inst_241_, lean_object* v_f_242_, lean_object* v_rchild_243_, lean_object* v_b_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_RBNode_foldM___redArg(v_inst_241_, v_f_242_, v_b_244_, v_rchild_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_00_u03c3_248_, lean_object* v_m_249_, lean_object* v_inst_250_, lean_object* v_f_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_RBNode_foldM___redArg(v_inst_250_, v_f_251_, v_x_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1(lean_object* v_toPure_255_, lean_object* v_f_256_, lean_object* v_key_257_, lean_object* v_val_258_, lean_object* v_toBind_259_, lean_object* v___f_260_, lean_object* v_____do__lift_261_){
_start:
{
if (lean_obj_tag(v_____do__lift_261_) == 0)
{
lean_object* v___x_262_; 
lean_dec(v___f_260_);
lean_dec(v_toBind_259_);
lean_dec(v_val_258_);
lean_dec(v_key_257_);
lean_dec(v_f_256_);
v___x_262_ = lean_apply_2(v_toPure_255_, lean_box(0), v_____do__lift_261_);
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_toPure_255_);
v_a_263_ = lean_ctor_get(v_____do__lift_261_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_____do__lift_261_, 1);
v___x_264_ = lean_apply_3(v_f_256_, v_key_257_, v_val_258_, v_a_263_);
v___x_265_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_264_, v___f_260_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(lean_object* v_inst_266_, lean_object* v_f_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
if (lean_obj_tag(v_a_268_) == 0)
{
lean_object* v_toApplicative_270_; lean_object* v_toPure_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_toApplicative_270_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_270_);
lean_dec(v_f_267_);
lean_dec_ref(v_inst_266_);
v_toPure_271_ = lean_ctor_get(v_toApplicative_270_, 1);
lean_inc(v_toPure_271_);
lean_dec_ref(v_toApplicative_270_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_a_269_);
v___x_273_ = lean_apply_2(v_toPure_271_, lean_box(0), v___x_272_);
return v___x_273_;
}
else
{
lean_object* v_toApplicative_274_; lean_object* v_toBind_275_; lean_object* v_toPure_276_; lean_object* v_lchild_277_; lean_object* v_key_278_; lean_object* v_val_279_; lean_object* v_rchild_280_; lean_object* v___f_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_toApplicative_274_ = lean_ctor_get(v_inst_266_, 0);
v_toBind_275_ = lean_ctor_get(v_inst_266_, 1);
lean_inc_n(v_toBind_275_, 2);
v_toPure_276_ = lean_ctor_get(v_toApplicative_274_, 1);
v_lchild_277_ = lean_ctor_get(v_a_268_, 0);
lean_inc(v_lchild_277_);
v_key_278_ = lean_ctor_get(v_a_268_, 1);
lean_inc(v_key_278_);
v_val_279_ = lean_ctor_get(v_a_268_, 2);
lean_inc(v_val_279_);
v_rchild_280_ = lean_ctor_get(v_a_268_, 3);
lean_inc(v_rchild_280_);
lean_dec_ref_known(v_a_268_, 4);
lean_inc_n(v_f_267_, 2);
lean_inc_ref(v_inst_266_);
lean_inc_n(v_toPure_276_, 2);
v___f_281_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0), 5, 4);
lean_closure_set(v___f_281_, 0, v_toPure_276_);
lean_closure_set(v___f_281_, 1, v_inst_266_);
lean_closure_set(v___f_281_, 2, v_f_267_);
lean_closure_set(v___f_281_, 3, v_rchild_280_);
v___f_282_ = lean_alloc_closure((void*)(l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__1), 7, 6);
lean_closure_set(v___f_282_, 0, v_toPure_276_);
lean_closure_set(v___f_282_, 1, v_f_267_);
lean_closure_set(v___f_282_, 2, v_key_278_);
lean_closure_set(v___f_282_, 3, v_val_279_);
lean_closure_set(v___f_282_, 4, v_toBind_275_);
lean_closure_set(v___f_282_, 5, v___f_281_);
v___x_283_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_266_, v_f_267_, v_lchild_277_, v_a_269_);
v___x_284_ = lean_apply_4(v_toBind_275_, lean_box(0), lean_box(0), v___x_283_, v___f_282_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg___lam__0(lean_object* v_toPure_285_, lean_object* v_inst_286_, lean_object* v_f_287_, lean_object* v_rchild_288_, lean_object* v_____do__lift_289_){
_start:
{
if (lean_obj_tag(v_____do__lift_289_) == 0)
{
lean_object* v___x_290_; 
lean_dec(v_rchild_288_);
lean_dec(v_f_287_);
lean_dec_ref(v_inst_286_);
v___x_290_ = lean_apply_2(v_toPure_285_, lean_box(0), v_____do__lift_289_);
return v___x_290_;
}
else
{
lean_object* v_a_291_; lean_object* v___x_292_; 
lean_dec(v_toPure_285_);
v_a_291_ = lean_ctor_get(v_____do__lift_289_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v_____do__lift_289_, 1);
v___x_292_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_286_, v_f_287_, v_rchild_288_, v_a_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object* v_00_u03b1_293_, lean_object* v_00_u03b2_294_, lean_object* v_00_u03c3_295_, lean_object* v_m_296_, lean_object* v_inst_297_, lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_297_, v_f_298_, v_a_299_, v_a_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg___lam__0(lean_object* v_toPure_302_, lean_object* v_____do__lift_303_){
_start:
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v_____do__lift_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v_____do__lift_303_);
v___x_305_ = lean_apply_2(v_toPure_302_, lean_box(0), v_a_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn___redArg(lean_object* v_inst_306_, lean_object* v_as_307_, lean_object* v_init_308_, lean_object* v_f_309_){
_start:
{
lean_object* v_toApplicative_310_; lean_object* v_toBind_311_; lean_object* v_toPure_312_; lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v_toApplicative_310_ = lean_ctor_get(v_inst_306_, 0);
v_toBind_311_ = lean_ctor_get(v_inst_306_, 1);
lean_inc(v_toBind_311_);
v_toPure_312_ = lean_ctor_get(v_toApplicative_310_, 1);
lean_inc(v_toPure_312_);
v___x_313_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_306_, v_f_309_, v_as_307_, v_init_308_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_314_, 0, v_toPure_312_);
v___x_315_ = lean_apply_4(v_toBind_311_, lean_box(0), lean_box(0), v___x_313_, v___f_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn(lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_00_u03c3_318_, lean_object* v_m_319_, lean_object* v_inst_320_, lean_object* v_as_321_, lean_object* v_init_322_, lean_object* v_f_323_){
_start:
{
lean_object* v_toApplicative_324_; lean_object* v_toBind_325_; lean_object* v_toPure_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___x_329_; 
v_toApplicative_324_ = lean_ctor_get(v_inst_320_, 0);
v_toBind_325_ = lean_ctor_get(v_inst_320_, 1);
lean_inc(v_toBind_325_);
v_toPure_326_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_inc(v_toPure_326_);
v___x_327_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_320_, v_f_323_, v_as_321_, v_init_322_);
v___f_328_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_328_, 0, v_toPure_326_);
v___x_329_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v___x_327_, v___f_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___redArg(lean_object* v_f_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_dec(v_f_330_);
return v_x_331_;
}
else
{
lean_object* v_lchild_333_; lean_object* v_key_334_; lean_object* v_val_335_; lean_object* v_rchild_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_lchild_333_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_lchild_333_);
v_key_334_ = lean_ctor_get(v_x_332_, 1);
lean_inc(v_key_334_);
v_val_335_ = lean_ctor_get(v_x_332_, 2);
lean_inc(v_val_335_);
v_rchild_336_ = lean_ctor_get(v_x_332_, 3);
lean_inc(v_rchild_336_);
lean_dec_ref_known(v_x_332_, 4);
lean_inc_n(v_f_330_, 2);
v___x_337_ = l_Lean_RBNode_revFold___redArg(v_f_330_, v_x_331_, v_rchild_336_);
v___x_338_ = lean_apply_3(v_f_330_, v___x_337_, v_key_334_, v_val_335_);
v_x_331_ = v___x_338_;
v_x_332_ = v_lchild_333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold(lean_object* v_00_u03b1_340_, lean_object* v_00_u03b2_341_, lean_object* v_00_u03c3_342_, lean_object* v_f_343_, lean_object* v_x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_RBNode_revFold___redArg(v_f_343_, v_x_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___redArg(lean_object* v_p_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
uint8_t v___x_349_; 
lean_dec_ref(v_p_347_);
v___x_349_ = 1;
return v___x_349_;
}
else
{
lean_object* v_lchild_350_; lean_object* v_key_351_; lean_object* v_val_352_; lean_object* v_rchild_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_lchild_350_ = lean_ctor_get(v_x_348_, 0);
lean_inc(v_lchild_350_);
v_key_351_ = lean_ctor_get(v_x_348_, 1);
lean_inc(v_key_351_);
v_val_352_ = lean_ctor_get(v_x_348_, 2);
lean_inc(v_val_352_);
v_rchild_353_ = lean_ctor_get(v_x_348_, 3);
lean_inc(v_rchild_353_);
lean_dec_ref_known(v_x_348_, 4);
lean_inc_ref(v_p_347_);
v___x_354_ = lean_apply_2(v_p_347_, v_key_351_, v_val_352_);
v___x_355_ = lean_unbox(v___x_354_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
lean_dec(v_rchild_353_);
lean_dec(v_lchild_350_);
lean_dec_ref(v_p_347_);
v___x_356_ = lean_unbox(v___x_354_);
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
lean_inc_ref(v_p_347_);
v___x_357_ = l_Lean_RBNode_all___redArg(v_p_347_, v_lchild_350_);
if (v___x_357_ == 0)
{
lean_dec(v_rchild_353_);
lean_dec_ref(v_p_347_);
return v___x_357_;
}
else
{
v_x_348_ = v_rchild_353_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___redArg___boxed(lean_object* v_p_359_, lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_RBNode_all___redArg(v_p_359_, v_x_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all(lean_object* v_00_u03b1_363_, lean_object* v_00_u03b2_364_, lean_object* v_p_365_, lean_object* v_x_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = l_Lean_RBNode_all___redArg(v_p_365_, v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___boxed(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_p_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_RBNode_all(v_00_u03b1_368_, v_00_u03b2_369_, v_p_370_, v_x_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any___redArg(lean_object* v_p_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
uint8_t v___x_376_; 
lean_dec_ref(v_p_374_);
v___x_376_ = 0;
return v___x_376_;
}
else
{
lean_object* v_lchild_377_; lean_object* v_key_378_; lean_object* v_val_379_; lean_object* v_rchild_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_lchild_377_ = lean_ctor_get(v_x_375_, 0);
lean_inc(v_lchild_377_);
v_key_378_ = lean_ctor_get(v_x_375_, 1);
lean_inc(v_key_378_);
v_val_379_ = lean_ctor_get(v_x_375_, 2);
lean_inc(v_val_379_);
v_rchild_380_ = lean_ctor_get(v_x_375_, 3);
lean_inc(v_rchild_380_);
lean_dec_ref_known(v_x_375_, 4);
lean_inc_ref(v_p_374_);
v___x_381_ = lean_apply_2(v_p_374_, v_key_378_, v_val_379_);
v___x_382_ = lean_unbox(v___x_381_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
lean_inc_ref(v_p_374_);
v___x_383_ = l_Lean_RBNode_any___redArg(v_p_374_, v_lchild_377_);
if (v___x_383_ == 0)
{
v_x_375_ = v_rchild_380_;
goto _start;
}
else
{
lean_dec(v_rchild_380_);
lean_dec_ref(v_p_374_);
return v___x_383_;
}
}
else
{
uint8_t v___x_385_; 
lean_dec(v_rchild_380_);
lean_dec(v_lchild_377_);
lean_dec_ref(v_p_374_);
v___x_385_ = lean_unbox(v___x_381_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___redArg___boxed(lean_object* v_p_386_, lean_object* v_x_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_RBNode_any___redArg(v_p_386_, v_x_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_p_392_, lean_object* v_x_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_RBNode_any___redArg(v_p_392_, v_x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_p_397_, lean_object* v_x_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Lean_RBNode_any(v_00_u03b1_395_, v_00_u03b2_396_, v_p_397_, v_x_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton___redArg(lean_object* v_k_401_, lean_object* v_v_402_){
_start:
{
uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = 0;
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_k_401_);
lean_ctor_set(v___x_405_, 2, v_v_402_);
lean_ctor_set(v___x_405_, 3, v___x_404_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*4, v___x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_singleton(lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_k_408_, lean_object* v_v_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_RBNode_singleton___redArg(v_k_408_, v_v_409_);
return v___x_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton___redArg(lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 1)
{
lean_object* v_lchild_412_; 
v_lchild_412_ = lean_ctor_get(v_x_411_, 0);
if (lean_obj_tag(v_lchild_412_) == 0)
{
lean_object* v_rchild_413_; 
v_rchild_413_ = lean_ctor_get(v_x_411_, 3);
if (lean_obj_tag(v_rchild_413_) == 0)
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
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
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___redArg___boxed(lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Lean_RBNode_isSingleton___redArg(v_x_418_);
lean_dec(v_x_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isSingleton(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_x_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_RBNode_isSingleton___redArg(v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isSingleton___boxed(lean_object* v_00_u03b1_425_, lean_object* v_00_u03b2_426_, lean_object* v_x_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_RBNode_isSingleton(v_00_u03b1_425_, v_00_u03b2_426_, v_x_427_);
lean_dec(v_x_427_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1___redArg(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_a_435_; lean_object* v_kx_436_; lean_object* v_vx_437_; lean_object* v_b_438_; 
if (lean_obj_tag(v_x_430_) == 1)
{
uint8_t v_color_441_; lean_object* v_lchild_442_; lean_object* v_key_443_; lean_object* v_val_444_; lean_object* v_rchild_445_; lean_object* v_a_447_; lean_object* v_kx_448_; lean_object* v_vx_449_; lean_object* v_b_450_; lean_object* v_ky_451_; lean_object* v_vy_452_; lean_object* v_c_453_; lean_object* v_kz_454_; lean_object* v_vz_455_; lean_object* v_d_456_; 
v_color_441_ = lean_ctor_get_uint8(v_x_430_, sizeof(void*)*4);
v_lchild_442_ = lean_ctor_get(v_x_430_, 0);
v_key_443_ = lean_ctor_get(v_x_430_, 1);
v_val_444_ = lean_ctor_get(v_x_430_, 2);
v_rchild_445_ = lean_ctor_get(v_x_430_, 3);
if (v_color_441_ == 0)
{
if (lean_obj_tag(v_lchild_442_) == 1)
{
uint8_t v_color_461_; 
v_color_461_ = lean_ctor_get_uint8(v_lchild_442_, sizeof(void*)*4);
if (v_color_461_ == 0)
{
lean_object* v_lchild_462_; lean_object* v_key_463_; lean_object* v_val_464_; lean_object* v_rchild_465_; 
lean_inc_ref(v_lchild_442_);
lean_inc(v_rchild_445_);
lean_inc(v_val_444_);
lean_inc(v_key_443_);
lean_dec_ref_known(v_x_430_, 4);
v_lchild_462_ = lean_ctor_get(v_lchild_442_, 0);
lean_inc(v_lchild_462_);
v_key_463_ = lean_ctor_get(v_lchild_442_, 1);
lean_inc(v_key_463_);
v_val_464_ = lean_ctor_get(v_lchild_442_, 2);
lean_inc(v_val_464_);
v_rchild_465_ = lean_ctor_get(v_lchild_442_, 3);
lean_inc(v_rchild_465_);
lean_dec_ref_known(v_lchild_442_, 4);
v_a_447_ = v_lchild_462_;
v_kx_448_ = v_key_463_;
v_vx_449_ = v_val_464_;
v_b_450_ = v_rchild_465_;
v_ky_451_ = v_key_443_;
v_vy_452_ = v_val_444_;
v_c_453_ = v_rchild_445_;
v_kz_454_ = v_x_431_;
v_vz_455_ = v_x_432_;
v_d_456_ = v_x_433_;
goto v___jp_446_;
}
else
{
if (lean_obj_tag(v_rchild_445_) == 1)
{
uint8_t v_color_466_; 
v_color_466_ = lean_ctor_get_uint8(v_rchild_445_, sizeof(void*)*4);
if (v_color_466_ == 0)
{
lean_object* v_lchild_467_; lean_object* v_key_468_; lean_object* v_val_469_; lean_object* v_rchild_470_; 
lean_inc_ref(v_rchild_445_);
lean_inc_ref(v_lchild_442_);
lean_inc(v_val_444_);
lean_inc(v_key_443_);
lean_dec_ref_known(v_x_430_, 4);
v_lchild_467_ = lean_ctor_get(v_rchild_445_, 0);
lean_inc(v_lchild_467_);
v_key_468_ = lean_ctor_get(v_rchild_445_, 1);
lean_inc(v_key_468_);
v_val_469_ = lean_ctor_get(v_rchild_445_, 2);
lean_inc(v_val_469_);
v_rchild_470_ = lean_ctor_get(v_rchild_445_, 3);
lean_inc(v_rchild_470_);
lean_dec_ref_known(v_rchild_445_, 4);
v_a_447_ = v_lchild_442_;
v_kx_448_ = v_key_443_;
v_vx_449_ = v_val_444_;
v_b_450_ = v_lchild_467_;
v_ky_451_ = v_key_468_;
v_vy_452_ = v_val_469_;
v_c_453_ = v_rchild_470_;
v_kz_454_ = v_x_431_;
v_vz_455_ = v_x_432_;
v_d_456_ = v_x_433_;
goto v___jp_446_;
}
else
{
v_a_435_ = v_x_430_;
v_kx_436_ = v_x_431_;
v_vx_437_ = v_x_432_;
v_b_438_ = v_x_433_;
goto v___jp_434_;
}
}
else
{
v_a_435_ = v_x_430_;
v_kx_436_ = v_x_431_;
v_vx_437_ = v_x_432_;
v_b_438_ = v_x_433_;
goto v___jp_434_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_445_) == 1)
{
uint8_t v_color_471_; 
v_color_471_ = lean_ctor_get_uint8(v_rchild_445_, sizeof(void*)*4);
if (v_color_471_ == 0)
{
lean_object* v_lchild_472_; lean_object* v_key_473_; lean_object* v_val_474_; lean_object* v_rchild_475_; 
lean_inc_ref(v_rchild_445_);
lean_inc(v_val_444_);
lean_inc(v_key_443_);
lean_inc(v_lchild_442_);
lean_dec_ref_known(v_x_430_, 4);
v_lchild_472_ = lean_ctor_get(v_rchild_445_, 0);
lean_inc(v_lchild_472_);
v_key_473_ = lean_ctor_get(v_rchild_445_, 1);
lean_inc(v_key_473_);
v_val_474_ = lean_ctor_get(v_rchild_445_, 2);
lean_inc(v_val_474_);
v_rchild_475_ = lean_ctor_get(v_rchild_445_, 3);
lean_inc(v_rchild_475_);
lean_dec_ref_known(v_rchild_445_, 4);
v_a_447_ = v_lchild_442_;
v_kx_448_ = v_key_443_;
v_vx_449_ = v_val_444_;
v_b_450_ = v_lchild_472_;
v_ky_451_ = v_key_473_;
v_vy_452_ = v_val_474_;
v_c_453_ = v_rchild_475_;
v_kz_454_ = v_x_431_;
v_vz_455_ = v_x_432_;
v_d_456_ = v_x_433_;
goto v___jp_446_;
}
else
{
v_a_435_ = v_x_430_;
v_kx_436_ = v_x_431_;
v_vx_437_ = v_x_432_;
v_b_438_ = v_x_433_;
goto v___jp_434_;
}
}
else
{
v_a_435_ = v_x_430_;
v_kx_436_ = v_x_431_;
v_vx_437_ = v_x_432_;
v_b_438_ = v_x_433_;
goto v___jp_434_;
}
}
}
else
{
v_a_435_ = v_x_430_;
v_kx_436_ = v_x_431_;
v_vx_437_ = v_x_432_;
v_b_438_ = v_x_433_;
goto v___jp_434_;
}
v___jp_446_:
{
uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = 1;
v___x_458_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_458_, 0, v_a_447_);
lean_ctor_set(v___x_458_, 1, v_kx_448_);
lean_ctor_set(v___x_458_, 2, v_vx_449_);
lean_ctor_set(v___x_458_, 3, v_b_450_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*4, v___x_457_);
v___x_459_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_459_, 0, v_c_453_);
lean_ctor_set(v___x_459_, 1, v_kz_454_);
lean_ctor_set(v___x_459_, 2, v_vz_455_);
lean_ctor_set(v___x_459_, 3, v_d_456_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*4, v___x_457_);
v___x_460_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v_ky_451_);
lean_ctor_set(v___x_460_, 2, v_vy_452_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*4, v_color_441_);
return v___x_460_;
}
}
else
{
v_a_435_ = v_x_430_;
v_kx_436_ = v_x_431_;
v_vx_437_ = v_x_432_;
v_b_438_ = v_x_433_;
goto v___jp_434_;
}
v___jp_434_:
{
uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_439_ = 1;
v___x_440_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_440_, 0, v_a_435_);
lean_ctor_set(v___x_440_, 1, v_kx_436_);
lean_ctor_set(v___x_440_, 2, v_vx_437_);
lean_ctor_set(v___x_440_, 3, v_b_438_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*4, v___x_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance1(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_a_483_; lean_object* v_kx_484_; lean_object* v_vx_485_; lean_object* v_b_486_; 
if (lean_obj_tag(v_x_478_) == 1)
{
uint8_t v_color_489_; lean_object* v_lchild_490_; lean_object* v_key_491_; lean_object* v_val_492_; lean_object* v_rchild_493_; lean_object* v_a_495_; lean_object* v_kx_496_; lean_object* v_vx_497_; lean_object* v_b_498_; lean_object* v_ky_499_; lean_object* v_vy_500_; lean_object* v_c_501_; lean_object* v_kz_502_; lean_object* v_vz_503_; lean_object* v_d_504_; 
v_color_489_ = lean_ctor_get_uint8(v_x_478_, sizeof(void*)*4);
v_lchild_490_ = lean_ctor_get(v_x_478_, 0);
v_key_491_ = lean_ctor_get(v_x_478_, 1);
v_val_492_ = lean_ctor_get(v_x_478_, 2);
v_rchild_493_ = lean_ctor_get(v_x_478_, 3);
if (v_color_489_ == 0)
{
if (lean_obj_tag(v_lchild_490_) == 1)
{
uint8_t v_color_509_; 
v_color_509_ = lean_ctor_get_uint8(v_lchild_490_, sizeof(void*)*4);
if (v_color_509_ == 0)
{
lean_object* v_lchild_510_; lean_object* v_key_511_; lean_object* v_val_512_; lean_object* v_rchild_513_; 
lean_inc_ref(v_lchild_490_);
lean_inc(v_rchild_493_);
lean_inc(v_val_492_);
lean_inc(v_key_491_);
lean_dec_ref_known(v_x_478_, 4);
v_lchild_510_ = lean_ctor_get(v_lchild_490_, 0);
lean_inc(v_lchild_510_);
v_key_511_ = lean_ctor_get(v_lchild_490_, 1);
lean_inc(v_key_511_);
v_val_512_ = lean_ctor_get(v_lchild_490_, 2);
lean_inc(v_val_512_);
v_rchild_513_ = lean_ctor_get(v_lchild_490_, 3);
lean_inc(v_rchild_513_);
lean_dec_ref_known(v_lchild_490_, 4);
v_a_495_ = v_lchild_510_;
v_kx_496_ = v_key_511_;
v_vx_497_ = v_val_512_;
v_b_498_ = v_rchild_513_;
v_ky_499_ = v_key_491_;
v_vy_500_ = v_val_492_;
v_c_501_ = v_rchild_493_;
v_kz_502_ = v_x_479_;
v_vz_503_ = v_x_480_;
v_d_504_ = v_x_481_;
goto v___jp_494_;
}
else
{
if (lean_obj_tag(v_rchild_493_) == 1)
{
uint8_t v_color_514_; 
v_color_514_ = lean_ctor_get_uint8(v_rchild_493_, sizeof(void*)*4);
if (v_color_514_ == 0)
{
lean_object* v_lchild_515_; lean_object* v_key_516_; lean_object* v_val_517_; lean_object* v_rchild_518_; 
lean_inc_ref(v_rchild_493_);
lean_inc_ref(v_lchild_490_);
lean_inc(v_val_492_);
lean_inc(v_key_491_);
lean_dec_ref_known(v_x_478_, 4);
v_lchild_515_ = lean_ctor_get(v_rchild_493_, 0);
lean_inc(v_lchild_515_);
v_key_516_ = lean_ctor_get(v_rchild_493_, 1);
lean_inc(v_key_516_);
v_val_517_ = lean_ctor_get(v_rchild_493_, 2);
lean_inc(v_val_517_);
v_rchild_518_ = lean_ctor_get(v_rchild_493_, 3);
lean_inc(v_rchild_518_);
lean_dec_ref_known(v_rchild_493_, 4);
v_a_495_ = v_lchild_490_;
v_kx_496_ = v_key_491_;
v_vx_497_ = v_val_492_;
v_b_498_ = v_lchild_515_;
v_ky_499_ = v_key_516_;
v_vy_500_ = v_val_517_;
v_c_501_ = v_rchild_518_;
v_kz_502_ = v_x_479_;
v_vz_503_ = v_x_480_;
v_d_504_ = v_x_481_;
goto v___jp_494_;
}
else
{
v_a_483_ = v_x_478_;
v_kx_484_ = v_x_479_;
v_vx_485_ = v_x_480_;
v_b_486_ = v_x_481_;
goto v___jp_482_;
}
}
else
{
v_a_483_ = v_x_478_;
v_kx_484_ = v_x_479_;
v_vx_485_ = v_x_480_;
v_b_486_ = v_x_481_;
goto v___jp_482_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_493_) == 1)
{
uint8_t v_color_519_; 
v_color_519_ = lean_ctor_get_uint8(v_rchild_493_, sizeof(void*)*4);
if (v_color_519_ == 0)
{
lean_object* v_lchild_520_; lean_object* v_key_521_; lean_object* v_val_522_; lean_object* v_rchild_523_; 
lean_inc_ref(v_rchild_493_);
lean_inc(v_val_492_);
lean_inc(v_key_491_);
lean_inc(v_lchild_490_);
lean_dec_ref_known(v_x_478_, 4);
v_lchild_520_ = lean_ctor_get(v_rchild_493_, 0);
lean_inc(v_lchild_520_);
v_key_521_ = lean_ctor_get(v_rchild_493_, 1);
lean_inc(v_key_521_);
v_val_522_ = lean_ctor_get(v_rchild_493_, 2);
lean_inc(v_val_522_);
v_rchild_523_ = lean_ctor_get(v_rchild_493_, 3);
lean_inc(v_rchild_523_);
lean_dec_ref_known(v_rchild_493_, 4);
v_a_495_ = v_lchild_490_;
v_kx_496_ = v_key_491_;
v_vx_497_ = v_val_492_;
v_b_498_ = v_lchild_520_;
v_ky_499_ = v_key_521_;
v_vy_500_ = v_val_522_;
v_c_501_ = v_rchild_523_;
v_kz_502_ = v_x_479_;
v_vz_503_ = v_x_480_;
v_d_504_ = v_x_481_;
goto v___jp_494_;
}
else
{
v_a_483_ = v_x_478_;
v_kx_484_ = v_x_479_;
v_vx_485_ = v_x_480_;
v_b_486_ = v_x_481_;
goto v___jp_482_;
}
}
else
{
v_a_483_ = v_x_478_;
v_kx_484_ = v_x_479_;
v_vx_485_ = v_x_480_;
v_b_486_ = v_x_481_;
goto v___jp_482_;
}
}
}
else
{
v_a_483_ = v_x_478_;
v_kx_484_ = v_x_479_;
v_vx_485_ = v_x_480_;
v_b_486_ = v_x_481_;
goto v___jp_482_;
}
v___jp_494_:
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = 1;
v___x_506_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_506_, 0, v_a_495_);
lean_ctor_set(v___x_506_, 1, v_kx_496_);
lean_ctor_set(v___x_506_, 2, v_vx_497_);
lean_ctor_set(v___x_506_, 3, v_b_498_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*4, v___x_505_);
v___x_507_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_507_, 0, v_c_501_);
lean_ctor_set(v___x_507_, 1, v_kz_502_);
lean_ctor_set(v___x_507_, 2, v_vz_503_);
lean_ctor_set(v___x_507_, 3, v_d_504_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*4, v___x_505_);
v___x_508_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v_ky_499_);
lean_ctor_set(v___x_508_, 2, v_vy_500_);
lean_ctor_set(v___x_508_, 3, v___x_507_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*4, v_color_489_);
return v___x_508_;
}
}
else
{
v_a_483_ = v_x_478_;
v_kx_484_ = v_x_479_;
v_vx_485_ = v_x_480_;
v_b_486_ = v_x_481_;
goto v___jp_482_;
}
v___jp_482_:
{
uint8_t v___x_487_; lean_object* v___x_488_; 
v___x_487_ = 1;
v___x_488_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_488_, 0, v_a_483_);
lean_ctor_set(v___x_488_, 1, v_kx_484_);
lean_ctor_set(v___x_488_, 2, v_vx_485_);
lean_ctor_set(v___x_488_, 3, v_b_486_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*4, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2___redArg(lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_a_529_; lean_object* v_kx_530_; lean_object* v_vx_531_; lean_object* v_b_532_; 
if (lean_obj_tag(v_x_527_) == 1)
{
uint8_t v_color_535_; lean_object* v_lchild_536_; lean_object* v_key_537_; lean_object* v_val_538_; lean_object* v_rchild_539_; lean_object* v_a_541_; lean_object* v_kx_542_; lean_object* v_vx_543_; lean_object* v_b_544_; lean_object* v_ky_545_; lean_object* v_vy_546_; lean_object* v_c_547_; lean_object* v_kz_548_; lean_object* v_vz_549_; lean_object* v_d_550_; 
v_color_535_ = lean_ctor_get_uint8(v_x_527_, sizeof(void*)*4);
v_lchild_536_ = lean_ctor_get(v_x_527_, 0);
v_key_537_ = lean_ctor_get(v_x_527_, 1);
v_val_538_ = lean_ctor_get(v_x_527_, 2);
v_rchild_539_ = lean_ctor_get(v_x_527_, 3);
if (v_color_535_ == 0)
{
if (lean_obj_tag(v_lchild_536_) == 1)
{
uint8_t v_color_555_; 
v_color_555_ = lean_ctor_get_uint8(v_lchild_536_, sizeof(void*)*4);
if (v_color_555_ == 0)
{
lean_object* v_lchild_556_; lean_object* v_key_557_; lean_object* v_val_558_; lean_object* v_rchild_559_; 
lean_inc_ref(v_lchild_536_);
lean_inc(v_rchild_539_);
lean_inc(v_val_538_);
lean_inc(v_key_537_);
lean_dec_ref_known(v_x_527_, 4);
v_lchild_556_ = lean_ctor_get(v_lchild_536_, 0);
lean_inc(v_lchild_556_);
v_key_557_ = lean_ctor_get(v_lchild_536_, 1);
lean_inc(v_key_557_);
v_val_558_ = lean_ctor_get(v_lchild_536_, 2);
lean_inc(v_val_558_);
v_rchild_559_ = lean_ctor_get(v_lchild_536_, 3);
lean_inc(v_rchild_559_);
lean_dec_ref_known(v_lchild_536_, 4);
v_a_541_ = v_x_524_;
v_kx_542_ = v_x_525_;
v_vx_543_ = v_x_526_;
v_b_544_ = v_lchild_556_;
v_ky_545_ = v_key_557_;
v_vy_546_ = v_val_558_;
v_c_547_ = v_rchild_559_;
v_kz_548_ = v_key_537_;
v_vz_549_ = v_val_538_;
v_d_550_ = v_rchild_539_;
goto v___jp_540_;
}
else
{
if (lean_obj_tag(v_rchild_539_) == 1)
{
uint8_t v_color_560_; 
v_color_560_ = lean_ctor_get_uint8(v_rchild_539_, sizeof(void*)*4);
if (v_color_560_ == 0)
{
lean_object* v_lchild_561_; lean_object* v_key_562_; lean_object* v_val_563_; lean_object* v_rchild_564_; 
lean_inc_ref(v_rchild_539_);
lean_inc_ref(v_lchild_536_);
lean_inc(v_val_538_);
lean_inc(v_key_537_);
lean_dec_ref_known(v_x_527_, 4);
v_lchild_561_ = lean_ctor_get(v_rchild_539_, 0);
lean_inc(v_lchild_561_);
v_key_562_ = lean_ctor_get(v_rchild_539_, 1);
lean_inc(v_key_562_);
v_val_563_ = lean_ctor_get(v_rchild_539_, 2);
lean_inc(v_val_563_);
v_rchild_564_ = lean_ctor_get(v_rchild_539_, 3);
lean_inc(v_rchild_564_);
lean_dec_ref_known(v_rchild_539_, 4);
v_a_541_ = v_x_524_;
v_kx_542_ = v_x_525_;
v_vx_543_ = v_x_526_;
v_b_544_ = v_lchild_536_;
v_ky_545_ = v_key_537_;
v_vy_546_ = v_val_538_;
v_c_547_ = v_lchild_561_;
v_kz_548_ = v_key_562_;
v_vz_549_ = v_val_563_;
v_d_550_ = v_rchild_564_;
goto v___jp_540_;
}
else
{
v_a_529_ = v_x_524_;
v_kx_530_ = v_x_525_;
v_vx_531_ = v_x_526_;
v_b_532_ = v_x_527_;
goto v___jp_528_;
}
}
else
{
v_a_529_ = v_x_524_;
v_kx_530_ = v_x_525_;
v_vx_531_ = v_x_526_;
v_b_532_ = v_x_527_;
goto v___jp_528_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_539_) == 1)
{
uint8_t v_color_565_; 
v_color_565_ = lean_ctor_get_uint8(v_rchild_539_, sizeof(void*)*4);
if (v_color_565_ == 0)
{
lean_object* v_lchild_566_; lean_object* v_key_567_; lean_object* v_val_568_; lean_object* v_rchild_569_; 
lean_inc_ref(v_rchild_539_);
lean_inc(v_val_538_);
lean_inc(v_key_537_);
lean_inc(v_lchild_536_);
lean_dec_ref_known(v_x_527_, 4);
v_lchild_566_ = lean_ctor_get(v_rchild_539_, 0);
lean_inc(v_lchild_566_);
v_key_567_ = lean_ctor_get(v_rchild_539_, 1);
lean_inc(v_key_567_);
v_val_568_ = lean_ctor_get(v_rchild_539_, 2);
lean_inc(v_val_568_);
v_rchild_569_ = lean_ctor_get(v_rchild_539_, 3);
lean_inc(v_rchild_569_);
lean_dec_ref_known(v_rchild_539_, 4);
v_a_541_ = v_x_524_;
v_kx_542_ = v_x_525_;
v_vx_543_ = v_x_526_;
v_b_544_ = v_lchild_536_;
v_ky_545_ = v_key_537_;
v_vy_546_ = v_val_538_;
v_c_547_ = v_lchild_566_;
v_kz_548_ = v_key_567_;
v_vz_549_ = v_val_568_;
v_d_550_ = v_rchild_569_;
goto v___jp_540_;
}
else
{
v_a_529_ = v_x_524_;
v_kx_530_ = v_x_525_;
v_vx_531_ = v_x_526_;
v_b_532_ = v_x_527_;
goto v___jp_528_;
}
}
else
{
v_a_529_ = v_x_524_;
v_kx_530_ = v_x_525_;
v_vx_531_ = v_x_526_;
v_b_532_ = v_x_527_;
goto v___jp_528_;
}
}
}
else
{
v_a_529_ = v_x_524_;
v_kx_530_ = v_x_525_;
v_vx_531_ = v_x_526_;
v_b_532_ = v_x_527_;
goto v___jp_528_;
}
v___jp_540_:
{
uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_551_ = 1;
v___x_552_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_552_, 0, v_a_541_);
lean_ctor_set(v___x_552_, 1, v_kx_542_);
lean_ctor_set(v___x_552_, 2, v_vx_543_);
lean_ctor_set(v___x_552_, 3, v_b_544_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*4, v___x_551_);
v___x_553_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_553_, 0, v_c_547_);
lean_ctor_set(v___x_553_, 1, v_kz_548_);
lean_ctor_set(v___x_553_, 2, v_vz_549_);
lean_ctor_set(v___x_553_, 3, v_d_550_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*4, v___x_551_);
v___x_554_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v_ky_545_);
lean_ctor_set(v___x_554_, 2, v_vy_546_);
lean_ctor_set(v___x_554_, 3, v___x_553_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*4, v_color_535_);
return v___x_554_;
}
}
else
{
v_a_529_ = v_x_524_;
v_kx_530_ = v_x_525_;
v_vx_531_ = v_x_526_;
v_b_532_ = v_x_527_;
goto v___jp_528_;
}
v___jp_528_:
{
uint8_t v___x_533_; lean_object* v___x_534_; 
v___x_533_ = 1;
v___x_534_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_534_, 0, v_a_529_);
lean_ctor_set(v___x_534_, 1, v_kx_530_);
lean_ctor_set(v___x_534_, 2, v_vx_531_);
lean_ctor_set(v___x_534_, 3, v_b_532_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*4, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balance2(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_a_577_; lean_object* v_kx_578_; lean_object* v_vx_579_; lean_object* v_b_580_; 
if (lean_obj_tag(v_x_575_) == 1)
{
uint8_t v_color_583_; lean_object* v_lchild_584_; lean_object* v_key_585_; lean_object* v_val_586_; lean_object* v_rchild_587_; lean_object* v_a_589_; lean_object* v_kx_590_; lean_object* v_vx_591_; lean_object* v_b_592_; lean_object* v_ky_593_; lean_object* v_vy_594_; lean_object* v_c_595_; lean_object* v_kz_596_; lean_object* v_vz_597_; lean_object* v_d_598_; 
v_color_583_ = lean_ctor_get_uint8(v_x_575_, sizeof(void*)*4);
v_lchild_584_ = lean_ctor_get(v_x_575_, 0);
v_key_585_ = lean_ctor_get(v_x_575_, 1);
v_val_586_ = lean_ctor_get(v_x_575_, 2);
v_rchild_587_ = lean_ctor_get(v_x_575_, 3);
if (v_color_583_ == 0)
{
if (lean_obj_tag(v_lchild_584_) == 1)
{
uint8_t v_color_603_; 
v_color_603_ = lean_ctor_get_uint8(v_lchild_584_, sizeof(void*)*4);
if (v_color_603_ == 0)
{
lean_object* v_lchild_604_; lean_object* v_key_605_; lean_object* v_val_606_; lean_object* v_rchild_607_; 
lean_inc_ref(v_lchild_584_);
lean_inc(v_rchild_587_);
lean_inc(v_val_586_);
lean_inc(v_key_585_);
lean_dec_ref_known(v_x_575_, 4);
v_lchild_604_ = lean_ctor_get(v_lchild_584_, 0);
lean_inc(v_lchild_604_);
v_key_605_ = lean_ctor_get(v_lchild_584_, 1);
lean_inc(v_key_605_);
v_val_606_ = lean_ctor_get(v_lchild_584_, 2);
lean_inc(v_val_606_);
v_rchild_607_ = lean_ctor_get(v_lchild_584_, 3);
lean_inc(v_rchild_607_);
lean_dec_ref_known(v_lchild_584_, 4);
v_a_589_ = v_x_572_;
v_kx_590_ = v_x_573_;
v_vx_591_ = v_x_574_;
v_b_592_ = v_lchild_604_;
v_ky_593_ = v_key_605_;
v_vy_594_ = v_val_606_;
v_c_595_ = v_rchild_607_;
v_kz_596_ = v_key_585_;
v_vz_597_ = v_val_586_;
v_d_598_ = v_rchild_587_;
goto v___jp_588_;
}
else
{
if (lean_obj_tag(v_rchild_587_) == 1)
{
uint8_t v_color_608_; 
v_color_608_ = lean_ctor_get_uint8(v_rchild_587_, sizeof(void*)*4);
if (v_color_608_ == 0)
{
lean_object* v_lchild_609_; lean_object* v_key_610_; lean_object* v_val_611_; lean_object* v_rchild_612_; 
lean_inc_ref(v_rchild_587_);
lean_inc_ref(v_lchild_584_);
lean_inc(v_val_586_);
lean_inc(v_key_585_);
lean_dec_ref_known(v_x_575_, 4);
v_lchild_609_ = lean_ctor_get(v_rchild_587_, 0);
lean_inc(v_lchild_609_);
v_key_610_ = lean_ctor_get(v_rchild_587_, 1);
lean_inc(v_key_610_);
v_val_611_ = lean_ctor_get(v_rchild_587_, 2);
lean_inc(v_val_611_);
v_rchild_612_ = lean_ctor_get(v_rchild_587_, 3);
lean_inc(v_rchild_612_);
lean_dec_ref_known(v_rchild_587_, 4);
v_a_589_ = v_x_572_;
v_kx_590_ = v_x_573_;
v_vx_591_ = v_x_574_;
v_b_592_ = v_lchild_584_;
v_ky_593_ = v_key_585_;
v_vy_594_ = v_val_586_;
v_c_595_ = v_lchild_609_;
v_kz_596_ = v_key_610_;
v_vz_597_ = v_val_611_;
v_d_598_ = v_rchild_612_;
goto v___jp_588_;
}
else
{
v_a_577_ = v_x_572_;
v_kx_578_ = v_x_573_;
v_vx_579_ = v_x_574_;
v_b_580_ = v_x_575_;
goto v___jp_576_;
}
}
else
{
v_a_577_ = v_x_572_;
v_kx_578_ = v_x_573_;
v_vx_579_ = v_x_574_;
v_b_580_ = v_x_575_;
goto v___jp_576_;
}
}
}
else
{
if (lean_obj_tag(v_rchild_587_) == 1)
{
uint8_t v_color_613_; 
v_color_613_ = lean_ctor_get_uint8(v_rchild_587_, sizeof(void*)*4);
if (v_color_613_ == 0)
{
lean_object* v_lchild_614_; lean_object* v_key_615_; lean_object* v_val_616_; lean_object* v_rchild_617_; 
lean_inc_ref(v_rchild_587_);
lean_inc(v_val_586_);
lean_inc(v_key_585_);
lean_inc(v_lchild_584_);
lean_dec_ref_known(v_x_575_, 4);
v_lchild_614_ = lean_ctor_get(v_rchild_587_, 0);
lean_inc(v_lchild_614_);
v_key_615_ = lean_ctor_get(v_rchild_587_, 1);
lean_inc(v_key_615_);
v_val_616_ = lean_ctor_get(v_rchild_587_, 2);
lean_inc(v_val_616_);
v_rchild_617_ = lean_ctor_get(v_rchild_587_, 3);
lean_inc(v_rchild_617_);
lean_dec_ref_known(v_rchild_587_, 4);
v_a_589_ = v_x_572_;
v_kx_590_ = v_x_573_;
v_vx_591_ = v_x_574_;
v_b_592_ = v_lchild_584_;
v_ky_593_ = v_key_585_;
v_vy_594_ = v_val_586_;
v_c_595_ = v_lchild_614_;
v_kz_596_ = v_key_615_;
v_vz_597_ = v_val_616_;
v_d_598_ = v_rchild_617_;
goto v___jp_588_;
}
else
{
v_a_577_ = v_x_572_;
v_kx_578_ = v_x_573_;
v_vx_579_ = v_x_574_;
v_b_580_ = v_x_575_;
goto v___jp_576_;
}
}
else
{
v_a_577_ = v_x_572_;
v_kx_578_ = v_x_573_;
v_vx_579_ = v_x_574_;
v_b_580_ = v_x_575_;
goto v___jp_576_;
}
}
}
else
{
v_a_577_ = v_x_572_;
v_kx_578_ = v_x_573_;
v_vx_579_ = v_x_574_;
v_b_580_ = v_x_575_;
goto v___jp_576_;
}
v___jp_588_:
{
uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = 1;
v___x_600_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_600_, 0, v_a_589_);
lean_ctor_set(v___x_600_, 1, v_kx_590_);
lean_ctor_set(v___x_600_, 2, v_vx_591_);
lean_ctor_set(v___x_600_, 3, v_b_592_);
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*4, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_601_, 0, v_c_595_);
lean_ctor_set(v___x_601_, 1, v_kz_596_);
lean_ctor_set(v___x_601_, 2, v_vz_597_);
lean_ctor_set(v___x_601_, 3, v_d_598_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*4, v___x_599_);
v___x_602_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v_ky_593_);
lean_ctor_set(v___x_602_, 2, v_vy_594_);
lean_ctor_set(v___x_602_, 3, v___x_601_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*4, v_color_583_);
return v___x_602_;
}
}
else
{
v_a_577_ = v_x_572_;
v_kx_578_ = v_x_573_;
v_vx_579_ = v_x_574_;
v_b_580_ = v_x_575_;
goto v___jp_576_;
}
v___jp_576_:
{
uint8_t v___x_581_; lean_object* v___x_582_; 
v___x_581_ = 1;
v___x_582_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_582_, 0, v_a_577_);
lean_ctor_set(v___x_582_, 1, v_kx_578_);
lean_ctor_set(v___x_582_, 2, v_vx_579_);
lean_ctor_set(v___x_582_, 3, v_b_580_);
lean_ctor_set_uint8(v___x_582_, sizeof(void*)*4, v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed___redArg(lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 1)
{
uint8_t v_color_619_; 
v_color_619_ = lean_ctor_get_uint8(v_x_618_, sizeof(void*)*4);
if (v_color_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = 1;
return v___x_620_;
}
else
{
uint8_t v___x_621_; 
v___x_621_ = 0;
return v___x_621_;
}
}
else
{
uint8_t v___x_622_; 
v___x_622_ = 0;
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___redArg___boxed(lean_object* v_x_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Lean_RBNode_isRed___redArg(v_x_623_);
lean_dec(v_x_623_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isRed(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_x_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = l_Lean_RBNode_isRed___redArg(v_x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isRed___boxed(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Lean_RBNode_isRed(v_00_u03b1_630_, v_00_u03b2_631_, v_x_632_);
lean_dec(v_x_632_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack___redArg(lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 1)
{
uint8_t v_color_636_; 
v_color_636_ = lean_ctor_get_uint8(v_x_635_, sizeof(void*)*4);
if (v_color_636_ == 1)
{
uint8_t v___x_637_; 
v___x_637_ = 1;
return v___x_637_;
}
else
{
uint8_t v___x_638_; 
v___x_638_ = 0;
return v___x_638_;
}
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 0;
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___redArg___boxed(lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_Lean_RBNode_isBlack___redArg(v_x_640_);
lean_dec(v_x_640_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_isBlack(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_x_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_RBNode_isBlack___redArg(v_x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_isBlack___boxed(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_x_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_RBNode_isBlack(v_00_u03b1_647_, v_00_u03b2_648_, v_x_649_);
lean_dec(v_x_649_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___redArg(lean_object* v_cmp_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
uint8_t v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v_cmp_652_);
v___x_656_ = 0;
v___x_657_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_657_, 0, v_x_653_);
lean_ctor_set(v___x_657_, 1, v_x_654_);
lean_ctor_set(v___x_657_, 2, v_x_655_);
lean_ctor_set(v___x_657_, 3, v_x_653_);
lean_ctor_set_uint8(v___x_657_, sizeof(void*)*4, v___x_656_);
return v___x_657_;
}
else
{
uint8_t v_color_658_; 
v_color_658_ = lean_ctor_get_uint8(v_x_653_, sizeof(void*)*4);
if (v_color_658_ == 0)
{
lean_object* v_lchild_659_; lean_object* v_key_660_; lean_object* v_val_661_; lean_object* v_rchild_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_679_; 
v_lchild_659_ = lean_ctor_get(v_x_653_, 0);
v_key_660_ = lean_ctor_get(v_x_653_, 1);
v_val_661_ = lean_ctor_get(v_x_653_, 2);
v_rchild_662_ = lean_ctor_get(v_x_653_, 3);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_679_ == 0)
{
v___x_664_ = v_x_653_;
v_isShared_665_ = v_isSharedCheck_679_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_rchild_662_);
lean_inc(v_val_661_);
lean_inc(v_key_660_);
lean_inc(v_lchild_659_);
lean_dec(v_x_653_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_679_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
lean_inc_ref(v_cmp_652_);
lean_inc(v_key_660_);
lean_inc(v_x_654_);
v___x_666_ = lean_apply_2(v_cmp_652_, v_x_654_, v_key_660_);
v___x_667_ = lean_unbox(v___x_666_);
switch(v___x_667_)
{
case 0:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_RBNode_ins___redArg(v_cmp_652_, v_lchild_659_, v_x_654_, v_x_655_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_668_);
v___x_670_ = v___x_664_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_key_660_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_val_661_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_rchild_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*4, v_color_658_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
case 1:
{
lean_object* v___x_673_; 
lean_dec(v_val_661_);
lean_dec(v_key_660_);
lean_dec_ref(v_cmp_652_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 2, v_x_655_);
lean_ctor_set(v___x_664_, 1, v_x_654_);
v___x_673_ = v___x_664_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_lchild_659_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_x_654_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_x_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_rchild_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_674_, sizeof(void*)*4, v_color_658_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
default: 
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_RBNode_ins___redArg(v_cmp_652_, v_rchild_662_, v_x_654_, v_x_655_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 3, v___x_675_);
v___x_677_ = v___x_664_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_lchild_659_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_key_660_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_val_661_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v___x_675_);
lean_ctor_set_uint8(v_reuseFailAlloc_678_, sizeof(void*)*4, v_color_658_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
else
{
lean_object* v_lchild_680_; lean_object* v_key_681_; lean_object* v_val_682_; lean_object* v_rchild_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_842_; 
v_lchild_680_ = lean_ctor_get(v_x_653_, 0);
v_key_681_ = lean_ctor_get(v_x_653_, 1);
v_val_682_ = lean_ctor_get(v_x_653_, 2);
v_rchild_683_ = lean_ctor_get(v_x_653_, 3);
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_842_ == 0)
{
v___x_685_ = v_x_653_;
v_isShared_686_ = v_isSharedCheck_842_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_rchild_683_);
lean_inc(v_val_682_);
lean_inc(v_key_681_);
lean_inc(v_lchild_680_);
lean_dec(v_x_653_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_842_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
lean_inc_ref(v_cmp_652_);
lean_inc(v_key_681_);
lean_inc(v_x_654_);
v___x_687_ = lean_apply_2(v_cmp_652_, v_x_654_, v_key_681_);
v___x_688_ = lean_unbox(v___x_687_);
switch(v___x_688_)
{
case 0:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_RBNode_ins___redArg(v_cmp_652_, v_lchild_680_, v_x_654_, v_x_655_);
if (lean_obj_tag(v___x_689_) == 1)
{
uint8_t v_color_690_; lean_object* v_lchild_691_; lean_object* v_key_692_; lean_object* v_val_693_; lean_object* v_rchild_694_; lean_object* v_a_696_; lean_object* v_kx_697_; lean_object* v_vx_698_; lean_object* v_b_699_; lean_object* v_ky_700_; lean_object* v_vy_701_; lean_object* v_c_702_; lean_object* v_kz_703_; lean_object* v_vz_704_; lean_object* v_d_705_; 
v_color_690_ = lean_ctor_get_uint8(v___x_689_, sizeof(void*)*4);
v_lchild_691_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_lchild_691_);
v_key_692_ = lean_ctor_get(v___x_689_, 1);
v_val_693_ = lean_ctor_get(v___x_689_, 2);
v_rchild_694_ = lean_ctor_get(v___x_689_, 3);
lean_inc(v_rchild_694_);
if (v_color_690_ == 0)
{
if (lean_obj_tag(v_lchild_691_) == 1)
{
uint8_t v_color_711_; 
v_color_711_ = lean_ctor_get_uint8(v_lchild_691_, sizeof(void*)*4);
if (v_color_711_ == 0)
{
lean_object* v_lchild_712_; lean_object* v_key_713_; lean_object* v_val_714_; lean_object* v_rchild_715_; 
lean_inc(v_val_693_);
lean_inc(v_key_692_);
lean_dec_ref_known(v___x_689_, 4);
v_lchild_712_ = lean_ctor_get(v_lchild_691_, 0);
lean_inc(v_lchild_712_);
v_key_713_ = lean_ctor_get(v_lchild_691_, 1);
lean_inc(v_key_713_);
v_val_714_ = lean_ctor_get(v_lchild_691_, 2);
lean_inc(v_val_714_);
v_rchild_715_ = lean_ctor_get(v_lchild_691_, 3);
lean_inc(v_rchild_715_);
lean_dec_ref_known(v_lchild_691_, 4);
v_a_696_ = v_lchild_712_;
v_kx_697_ = v_key_713_;
v_vx_698_ = v_val_714_;
v_b_699_ = v_rchild_715_;
v_ky_700_ = v_key_692_;
v_vy_701_ = v_val_693_;
v_c_702_ = v_rchild_694_;
v_kz_703_ = v_key_681_;
v_vz_704_ = v_val_682_;
v_d_705_ = v_rchild_683_;
goto v___jp_695_;
}
else
{
if (lean_obj_tag(v_rchild_694_) == 1)
{
uint8_t v_color_716_; 
v_color_716_ = lean_ctor_get_uint8(v_rchild_694_, sizeof(void*)*4);
if (v_color_716_ == 0)
{
lean_object* v_lchild_717_; lean_object* v_key_718_; lean_object* v_val_719_; lean_object* v_rchild_720_; 
lean_inc(v_val_693_);
lean_inc(v_key_692_);
lean_dec_ref_known(v___x_689_, 4);
v_lchild_717_ = lean_ctor_get(v_rchild_694_, 0);
lean_inc(v_lchild_717_);
v_key_718_ = lean_ctor_get(v_rchild_694_, 1);
lean_inc(v_key_718_);
v_val_719_ = lean_ctor_get(v_rchild_694_, 2);
lean_inc(v_val_719_);
v_rchild_720_ = lean_ctor_get(v_rchild_694_, 3);
lean_inc(v_rchild_720_);
lean_dec_ref_known(v_rchild_694_, 4);
v_a_696_ = v_lchild_691_;
v_kx_697_ = v_key_692_;
v_vx_698_ = v_val_693_;
v_b_699_ = v_lchild_717_;
v_ky_700_ = v_key_718_;
v_vy_701_ = v_val_719_;
v_c_702_ = v_rchild_720_;
v_kz_703_ = v_key_681_;
v_vz_704_ = v_val_682_;
v_d_705_ = v_rchild_683_;
goto v___jp_695_;
}
else
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref_known(v_lchild_691_, 4);
lean_del_object(v___x_685_);
v_isSharedCheck_727_ = !lean_is_exclusive(v_rchild_694_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; 
v_unused_728_ = lean_ctor_get(v_rchild_694_, 3);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_rchild_694_, 2);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_rchild_694_, 1);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_rchild_694_, 0);
lean_dec(v_unused_731_);
v___x_722_ = v_rchild_694_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_rchild_694_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 3, v_rchild_683_);
lean_ctor_set(v___x_722_, 2, v_val_682_);
lean_ctor_set(v___x_722_, 1, v_key_681_);
lean_ctor_set(v___x_722_, 0, v___x_689_);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_rchild_683_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*4, v_color_658_);
return v___x_725_;
}
}
}
}
else
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_rchild_694_);
lean_del_object(v___x_685_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_lchild_691_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; lean_object* v_unused_742_; 
v_unused_739_ = lean_ctor_get(v_lchild_691_, 3);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_lchild_691_, 2);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_lchild_691_, 1);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_lchild_691_, 0);
lean_dec(v_unused_742_);
v___x_733_ = v_lchild_691_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_lchild_691_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 3, v_rchild_683_);
lean_ctor_set(v___x_733_, 2, v_val_682_);
lean_ctor_set(v___x_733_, 1, v_key_681_);
lean_ctor_set(v___x_733_, 0, v___x_689_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_rchild_683_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*4, v_color_658_);
return v___x_736_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_694_) == 1)
{
uint8_t v_color_743_; 
v_color_743_ = lean_ctor_get_uint8(v_rchild_694_, sizeof(void*)*4);
if (v_color_743_ == 0)
{
lean_object* v_lchild_744_; lean_object* v_key_745_; lean_object* v_val_746_; lean_object* v_rchild_747_; 
lean_inc(v_val_693_);
lean_inc(v_key_692_);
lean_dec_ref_known(v___x_689_, 4);
v_lchild_744_ = lean_ctor_get(v_rchild_694_, 0);
lean_inc(v_lchild_744_);
v_key_745_ = lean_ctor_get(v_rchild_694_, 1);
lean_inc(v_key_745_);
v_val_746_ = lean_ctor_get(v_rchild_694_, 2);
lean_inc(v_val_746_);
v_rchild_747_ = lean_ctor_get(v_rchild_694_, 3);
lean_inc(v_rchild_747_);
lean_dec_ref_known(v_rchild_694_, 4);
v_a_696_ = v_lchild_691_;
v_kx_697_ = v_key_692_;
v_vx_698_ = v_val_693_;
v_b_699_ = v_lchild_744_;
v_ky_700_ = v_key_745_;
v_vy_701_ = v_val_746_;
v_c_702_ = v_rchild_747_;
v_kz_703_ = v_key_681_;
v_vz_704_ = v_val_682_;
v_d_705_ = v_rchild_683_;
goto v___jp_695_;
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_lchild_691_);
lean_del_object(v___x_685_);
v_isSharedCheck_754_ = !lean_is_exclusive(v_rchild_694_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; 
v_unused_755_ = lean_ctor_get(v_rchild_694_, 3);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_rchild_694_, 2);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_rchild_694_, 1);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_rchild_694_, 0);
lean_dec(v_unused_758_);
v___x_749_ = v_rchild_694_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_rchild_694_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 3, v_rchild_683_);
lean_ctor_set(v___x_749_, 2, v_val_682_);
lean_ctor_set(v___x_749_, 1, v_key_681_);
lean_ctor_set(v___x_749_, 0, v___x_689_);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_rchild_683_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*4, v_color_658_);
return v___x_752_;
}
}
}
}
else
{
lean_object* v___x_759_; 
lean_dec(v_rchild_694_);
lean_dec(v_lchild_691_);
lean_del_object(v___x_685_);
v___x_759_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_759_, 0, v___x_689_);
lean_ctor_set(v___x_759_, 1, v_key_681_);
lean_ctor_set(v___x_759_, 2, v_val_682_);
lean_ctor_set(v___x_759_, 3, v_rchild_683_);
lean_ctor_set_uint8(v___x_759_, sizeof(void*)*4, v_color_658_);
return v___x_759_;
}
}
}
else
{
lean_object* v___x_760_; 
lean_dec(v_rchild_694_);
lean_dec(v_lchild_691_);
lean_del_object(v___x_685_);
v___x_760_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_760_, 0, v___x_689_);
lean_ctor_set(v___x_760_, 1, v_key_681_);
lean_ctor_set(v___x_760_, 2, v_val_682_);
lean_ctor_set(v___x_760_, 3, v_rchild_683_);
lean_ctor_set_uint8(v___x_760_, sizeof(void*)*4, v_color_658_);
return v___x_760_;
}
v___jp_695_:
{
lean_object* v___x_707_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 3, v_b_699_);
lean_ctor_set(v___x_685_, 2, v_vx_698_);
lean_ctor_set(v___x_685_, 1, v_kx_697_);
lean_ctor_set(v___x_685_, 0, v_a_696_);
v___x_707_ = v___x_685_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_kx_697_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_vx_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_b_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_710_, sizeof(void*)*4, v_color_658_);
v___x_707_ = v_reuseFailAlloc_710_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_708_, 0, v_c_702_);
lean_ctor_set(v___x_708_, 1, v_kz_703_);
lean_ctor_set(v___x_708_, 2, v_vz_704_);
lean_ctor_set(v___x_708_, 3, v_d_705_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*4, v_color_658_);
v___x_709_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v_ky_700_);
lean_ctor_set(v___x_709_, 2, v_vy_701_);
lean_ctor_set(v___x_709_, 3, v___x_708_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*4, v_color_690_);
return v___x_709_;
}
}
}
else
{
lean_object* v___x_762_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_689_);
v___x_762_ = v___x_685_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_rchild_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_763_, sizeof(void*)*4, v_color_658_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
case 1:
{
lean_object* v___x_765_; 
lean_dec(v_val_682_);
lean_dec(v_key_681_);
lean_dec_ref(v_cmp_652_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v_x_655_);
lean_ctor_set(v___x_685_, 1, v_x_654_);
v___x_765_ = v___x_685_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_lchild_680_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_x_654_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_x_655_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v_rchild_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_766_, sizeof(void*)*4, v_color_658_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
default: 
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_RBNode_ins___redArg(v_cmp_652_, v_rchild_683_, v_x_654_, v_x_655_);
if (lean_obj_tag(v___x_767_) == 1)
{
uint8_t v_color_768_; lean_object* v_lchild_769_; lean_object* v_key_770_; lean_object* v_val_771_; lean_object* v_rchild_772_; lean_object* v_a_774_; lean_object* v_kx_775_; lean_object* v_vx_776_; lean_object* v_b_777_; lean_object* v_ky_778_; lean_object* v_vy_779_; lean_object* v_c_780_; lean_object* v_kz_781_; lean_object* v_vz_782_; lean_object* v_d_783_; 
v_color_768_ = lean_ctor_get_uint8(v___x_767_, sizeof(void*)*4);
v_lchild_769_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_lchild_769_);
v_key_770_ = lean_ctor_get(v___x_767_, 1);
v_val_771_ = lean_ctor_get(v___x_767_, 2);
v_rchild_772_ = lean_ctor_get(v___x_767_, 3);
lean_inc(v_rchild_772_);
if (v_color_768_ == 0)
{
if (lean_obj_tag(v_lchild_769_) == 1)
{
uint8_t v_color_789_; 
v_color_789_ = lean_ctor_get_uint8(v_lchild_769_, sizeof(void*)*4);
if (v_color_789_ == 0)
{
lean_object* v_lchild_790_; lean_object* v_key_791_; lean_object* v_val_792_; lean_object* v_rchild_793_; 
lean_inc(v_val_771_);
lean_inc(v_key_770_);
lean_dec_ref_known(v___x_767_, 4);
v_lchild_790_ = lean_ctor_get(v_lchild_769_, 0);
lean_inc(v_lchild_790_);
v_key_791_ = lean_ctor_get(v_lchild_769_, 1);
lean_inc(v_key_791_);
v_val_792_ = lean_ctor_get(v_lchild_769_, 2);
lean_inc(v_val_792_);
v_rchild_793_ = lean_ctor_get(v_lchild_769_, 3);
lean_inc(v_rchild_793_);
lean_dec_ref_known(v_lchild_769_, 4);
v_a_774_ = v_lchild_680_;
v_kx_775_ = v_key_681_;
v_vx_776_ = v_val_682_;
v_b_777_ = v_lchild_790_;
v_ky_778_ = v_key_791_;
v_vy_779_ = v_val_792_;
v_c_780_ = v_rchild_793_;
v_kz_781_ = v_key_770_;
v_vz_782_ = v_val_771_;
v_d_783_ = v_rchild_772_;
goto v___jp_773_;
}
else
{
if (lean_obj_tag(v_rchild_772_) == 1)
{
uint8_t v_color_794_; 
v_color_794_ = lean_ctor_get_uint8(v_rchild_772_, sizeof(void*)*4);
if (v_color_794_ == 0)
{
lean_object* v_lchild_795_; lean_object* v_key_796_; lean_object* v_val_797_; lean_object* v_rchild_798_; 
lean_inc(v_val_771_);
lean_inc(v_key_770_);
lean_dec_ref_known(v___x_767_, 4);
v_lchild_795_ = lean_ctor_get(v_rchild_772_, 0);
lean_inc(v_lchild_795_);
v_key_796_ = lean_ctor_get(v_rchild_772_, 1);
lean_inc(v_key_796_);
v_val_797_ = lean_ctor_get(v_rchild_772_, 2);
lean_inc(v_val_797_);
v_rchild_798_ = lean_ctor_get(v_rchild_772_, 3);
lean_inc(v_rchild_798_);
lean_dec_ref_known(v_rchild_772_, 4);
v_a_774_ = v_lchild_680_;
v_kx_775_ = v_key_681_;
v_vx_776_ = v_val_682_;
v_b_777_ = v_lchild_769_;
v_ky_778_ = v_key_770_;
v_vy_779_ = v_val_771_;
v_c_780_ = v_lchild_795_;
v_kz_781_ = v_key_796_;
v_vz_782_ = v_val_797_;
v_d_783_ = v_rchild_798_;
goto v___jp_773_;
}
else
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref_known(v_lchild_769_, 4);
lean_del_object(v___x_685_);
v_isSharedCheck_805_ = !lean_is_exclusive(v_rchild_772_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; 
v_unused_806_ = lean_ctor_get(v_rchild_772_, 3);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_rchild_772_, 2);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_rchild_772_, 1);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_rchild_772_, 0);
lean_dec(v_unused_809_);
v___x_800_ = v_rchild_772_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_dec(v_rchild_772_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 3, v___x_767_);
lean_ctor_set(v___x_800_, 2, v_val_682_);
lean_ctor_set(v___x_800_, 1, v_key_681_);
lean_ctor_set(v___x_800_, 0, v_lchild_680_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_lchild_680_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v___x_767_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*4, v_color_658_);
return v___x_803_;
}
}
}
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_rchild_772_);
lean_del_object(v___x_685_);
v_isSharedCheck_816_ = !lean_is_exclusive(v_lchild_769_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_817_ = lean_ctor_get(v_lchild_769_, 3);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_lchild_769_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_lchild_769_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_lchild_769_, 0);
lean_dec(v_unused_820_);
v___x_811_ = v_lchild_769_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_lchild_769_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 3, v___x_767_);
lean_ctor_set(v___x_811_, 2, v_val_682_);
lean_ctor_set(v___x_811_, 1, v_key_681_);
lean_ctor_set(v___x_811_, 0, v_lchild_680_);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_lchild_680_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v___x_767_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_ctor_set_uint8(v___x_814_, sizeof(void*)*4, v_color_658_);
return v___x_814_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_772_) == 1)
{
uint8_t v_color_821_; 
v_color_821_ = lean_ctor_get_uint8(v_rchild_772_, sizeof(void*)*4);
if (v_color_821_ == 0)
{
lean_object* v_lchild_822_; lean_object* v_key_823_; lean_object* v_val_824_; lean_object* v_rchild_825_; 
lean_inc(v_val_771_);
lean_inc(v_key_770_);
lean_dec_ref_known(v___x_767_, 4);
v_lchild_822_ = lean_ctor_get(v_rchild_772_, 0);
lean_inc(v_lchild_822_);
v_key_823_ = lean_ctor_get(v_rchild_772_, 1);
lean_inc(v_key_823_);
v_val_824_ = lean_ctor_get(v_rchild_772_, 2);
lean_inc(v_val_824_);
v_rchild_825_ = lean_ctor_get(v_rchild_772_, 3);
lean_inc(v_rchild_825_);
lean_dec_ref_known(v_rchild_772_, 4);
v_a_774_ = v_lchild_680_;
v_kx_775_ = v_key_681_;
v_vx_776_ = v_val_682_;
v_b_777_ = v_lchild_769_;
v_ky_778_ = v_key_770_;
v_vy_779_ = v_val_771_;
v_c_780_ = v_lchild_822_;
v_kz_781_ = v_key_823_;
v_vz_782_ = v_val_824_;
v_d_783_ = v_rchild_825_;
goto v___jp_773_;
}
else
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_lchild_769_);
lean_del_object(v___x_685_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_rchild_772_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_833_ = lean_ctor_get(v_rchild_772_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_rchild_772_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_rchild_772_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_rchild_772_, 0);
lean_dec(v_unused_836_);
v___x_827_ = v_rchild_772_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_rchild_772_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 3, v___x_767_);
lean_ctor_set(v___x_827_, 2, v_val_682_);
lean_ctor_set(v___x_827_, 1, v_key_681_);
lean_ctor_set(v___x_827_, 0, v_lchild_680_);
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_lchild_680_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v___x_767_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_ctor_set_uint8(v___x_830_, sizeof(void*)*4, v_color_658_);
return v___x_830_;
}
}
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_rchild_772_);
lean_dec(v_lchild_769_);
lean_del_object(v___x_685_);
v___x_837_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_837_, 0, v_lchild_680_);
lean_ctor_set(v___x_837_, 1, v_key_681_);
lean_ctor_set(v___x_837_, 2, v_val_682_);
lean_ctor_set(v___x_837_, 3, v___x_767_);
lean_ctor_set_uint8(v___x_837_, sizeof(void*)*4, v_color_658_);
return v___x_837_;
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v_rchild_772_);
lean_dec(v_lchild_769_);
lean_del_object(v___x_685_);
v___x_838_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_838_, 0, v_lchild_680_);
lean_ctor_set(v___x_838_, 1, v_key_681_);
lean_ctor_set(v___x_838_, 2, v_val_682_);
lean_ctor_set(v___x_838_, 3, v___x_767_);
lean_ctor_set_uint8(v___x_838_, sizeof(void*)*4, v_color_658_);
return v___x_838_;
}
v___jp_773_:
{
lean_object* v___x_785_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 3, v_b_777_);
lean_ctor_set(v___x_685_, 2, v_vx_776_);
lean_ctor_set(v___x_685_, 1, v_kx_775_);
lean_ctor_set(v___x_685_, 0, v_a_774_);
v___x_785_ = v___x_685_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_774_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_kx_775_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_vx_776_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_b_777_);
lean_ctor_set_uint8(v_reuseFailAlloc_788_, sizeof(void*)*4, v_color_658_);
v___x_785_ = v_reuseFailAlloc_788_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_786_, 0, v_c_780_);
lean_ctor_set(v___x_786_, 1, v_kz_781_);
lean_ctor_set(v___x_786_, 2, v_vz_782_);
lean_ctor_set(v___x_786_, 3, v_d_783_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*4, v_color_658_);
v___x_787_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v_ky_778_);
lean_ctor_set(v___x_787_, 2, v_vy_779_);
lean_ctor_set(v___x_787_, 3, v___x_786_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*4, v_color_768_);
return v___x_787_;
}
}
}
else
{
lean_object* v___x_840_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 3, v___x_767_);
v___x_840_ = v___x_685_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_lchild_680_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_key_681_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_val_682_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v___x_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_841_, sizeof(void*)*4, v_color_658_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_cmp_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_RBNode_ins___redArg(v_cmp_845_, v_x_846_, v_x_847_, v_x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack___redArg(lean_object* v_x_850_){
_start:
{
if (lean_obj_tag(v_x_850_) == 1)
{
lean_object* v_lchild_851_; lean_object* v_key_852_; lean_object* v_val_853_; lean_object* v_rchild_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_lchild_851_ = lean_ctor_get(v_x_850_, 0);
v_key_852_ = lean_ctor_get(v_x_850_, 1);
v_val_853_ = lean_ctor_get(v_x_850_, 2);
v_rchild_854_ = lean_ctor_get(v_x_850_, 3);
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_850_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v_x_850_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_rchild_854_);
lean_inc(v_val_853_);
lean_inc(v_key_852_);
lean_inc(v_lchild_851_);
lean_dec(v_x_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; lean_object* v___x_860_; 
v___x_858_ = 1;
if (v_isShared_857_ == 0)
{
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_lchild_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_key_852_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_val_853_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_rchild_854_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*4, v___x_858_);
return v___x_860_;
}
}
}
else
{
return v_x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setBlack(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_RBNode_setBlack___redArg(v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___redArg(lean_object* v_cmp_867_, lean_object* v_t_868_, lean_object* v_k_869_, lean_object* v_v_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_RBNode_isRed___redArg(v_t_868_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_RBNode_ins___redArg(v_cmp_867_, v_t_868_, v_k_869_, v_v_870_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = l_Lean_RBNode_ins___redArg(v_cmp_867_, v_t_868_, v_k_869_, v_v_870_);
v___x_874_ = l_Lean_RBNode_setBlack___redArg(v___x_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_cmp_877_, lean_object* v_t_878_, lean_object* v_k_879_, lean_object* v_v_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_RBNode_insert___redArg(v_cmp_877_, v_t_878_, v_k_879_, v_v_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed___redArg(lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 1)
{
lean_object* v_lchild_883_; lean_object* v_key_884_; lean_object* v_val_885_; lean_object* v_rchild_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_lchild_883_ = lean_ctor_get(v_x_882_, 0);
v_key_884_ = lean_ctor_get(v_x_882_, 1);
v_val_885_ = lean_ctor_get(v_x_882_, 2);
v_rchild_886_ = lean_ctor_get(v_x_882_, 3);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_882_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v_x_882_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_rchild_886_);
lean_inc(v_val_885_);
lean_inc(v_key_884_);
lean_inc(v_lchild_883_);
lean_dec(v_x_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
uint8_t v___x_890_; lean_object* v___x_892_; 
v___x_890_ = 0;
if (v_isShared_889_ == 0)
{
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_lchild_883_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_key_884_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_val_885_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_rchild_886_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*4, v___x_890_);
return v___x_892_;
}
}
}
else
{
return v_x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_setRed(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_RBNode_setRed___redArg(v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft___redArg(lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v_a_904_; lean_object* v_kx_905_; lean_object* v_vx_906_; lean_object* v_b_907_; lean_object* v_a_911_; lean_object* v_kx_912_; lean_object* v_vx_913_; lean_object* v_b_914_; lean_object* v_ky_915_; lean_object* v_vy_916_; lean_object* v_c_917_; lean_object* v_kz_918_; lean_object* v_vz_919_; lean_object* v_d_920_; lean_object* v_l_927_; lean_object* v_k_928_; lean_object* v_v_929_; lean_object* v_a_930_; lean_object* v_ky_931_; lean_object* v_vy_932_; lean_object* v_b_933_; uint8_t v___y_952_; lean_object* v___y_953_; uint8_t v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v_a_957_; lean_object* v_kx_958_; lean_object* v_vx_959_; lean_object* v_b_960_; lean_object* v_ky_961_; lean_object* v_vy_962_; lean_object* v_c_963_; lean_object* v_kz_964_; lean_object* v_vz_965_; lean_object* v_d_966_; uint8_t v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v_a_977_; lean_object* v_kx_978_; lean_object* v_vx_979_; lean_object* v_b_980_; lean_object* v_l_984_; lean_object* v_k_985_; lean_object* v_v_986_; lean_object* v_a_987_; lean_object* v_ky_988_; lean_object* v_vy_989_; lean_object* v_b_990_; lean_object* v_kz_991_; lean_object* v_vz_992_; lean_object* v_c_993_; lean_object* v_l_1025_; lean_object* v_k_1026_; lean_object* v_v_1027_; lean_object* v_r_1028_; 
if (lean_obj_tag(v_x_899_) == 1)
{
uint8_t v_color_1031_; 
v_color_1031_ = lean_ctor_get_uint8(v_x_899_, sizeof(void*)*4);
if (v_color_1031_ == 0)
{
lean_object* v_lchild_1032_; lean_object* v_key_1033_; lean_object* v_val_1034_; lean_object* v_rchild_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1044_; 
v_lchild_1032_ = lean_ctor_get(v_x_899_, 0);
v_key_1033_ = lean_ctor_get(v_x_899_, 1);
v_val_1034_ = lean_ctor_get(v_x_899_, 2);
v_rchild_1035_ = lean_ctor_get(v_x_899_, 3);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_x_899_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1037_ = v_x_899_;
v_isShared_1038_ = v_isSharedCheck_1044_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_rchild_1035_);
lean_inc(v_val_1034_);
lean_inc(v_key_1033_);
lean_inc(v_lchild_1032_);
lean_dec(v_x_899_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1044_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
uint8_t v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = 1;
if (v_isShared_1038_ == 0)
{
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_lchild_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_key_1033_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_val_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_rchild_1035_);
v___x_1041_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*4, v___x_1039_);
v___x_1042_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_x_900_);
lean_ctor_set(v___x_1042_, 2, v_x_901_);
lean_ctor_set(v___x_1042_, 3, v_x_902_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*4, v_color_1031_);
return v___x_1042_;
}
}
}
else
{
if (lean_obj_tag(v_x_902_) == 1)
{
uint8_t v_color_1045_; 
v_color_1045_ = lean_ctor_get_uint8(v_x_902_, sizeof(void*)*4);
if (v_color_1045_ == 0)
{
lean_object* v_lchild_1046_; 
v_lchild_1046_ = lean_ctor_get(v_x_902_, 0);
if (lean_obj_tag(v_lchild_1046_) == 1)
{
uint8_t v_color_1047_; 
v_color_1047_ = lean_ctor_get_uint8(v_lchild_1046_, sizeof(void*)*4);
if (v_color_1047_ == 1)
{
lean_object* v_key_1048_; lean_object* v_val_1049_; lean_object* v_rchild_1050_; lean_object* v_lchild_1051_; lean_object* v_key_1052_; lean_object* v_val_1053_; lean_object* v_rchild_1054_; 
lean_inc_ref(v_lchild_1046_);
v_key_1048_ = lean_ctor_get(v_x_902_, 1);
lean_inc(v_key_1048_);
v_val_1049_ = lean_ctor_get(v_x_902_, 2);
lean_inc(v_val_1049_);
v_rchild_1050_ = lean_ctor_get(v_x_902_, 3);
lean_inc(v_rchild_1050_);
lean_dec_ref_known(v_x_902_, 4);
v_lchild_1051_ = lean_ctor_get(v_lchild_1046_, 0);
lean_inc(v_lchild_1051_);
v_key_1052_ = lean_ctor_get(v_lchild_1046_, 1);
lean_inc(v_key_1052_);
v_val_1053_ = lean_ctor_get(v_lchild_1046_, 2);
lean_inc(v_val_1053_);
v_rchild_1054_ = lean_ctor_get(v_lchild_1046_, 3);
lean_inc(v_rchild_1054_);
lean_dec_ref_known(v_lchild_1046_, 4);
v_l_984_ = v_x_899_;
v_k_985_ = v_x_900_;
v_v_986_ = v_x_901_;
v_a_987_ = v_lchild_1051_;
v_ky_988_ = v_key_1052_;
v_vy_989_ = v_val_1053_;
v_b_990_ = v_rchild_1054_;
v_kz_991_ = v_key_1048_;
v_vz_992_ = v_val_1049_;
v_c_993_ = v_rchild_1050_;
goto v___jp_983_;
}
else
{
v_l_1025_ = v_x_899_;
v_k_1026_ = v_x_900_;
v_v_1027_ = v_x_901_;
v_r_1028_ = v_x_902_;
goto v___jp_1024_;
}
}
else
{
v_l_1025_ = v_x_899_;
v_k_1026_ = v_x_900_;
v_v_1027_ = v_x_901_;
v_r_1028_ = v_x_902_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_lchild_1055_; lean_object* v_key_1056_; lean_object* v_val_1057_; lean_object* v_rchild_1058_; 
v_lchild_1055_ = lean_ctor_get(v_x_902_, 0);
lean_inc(v_lchild_1055_);
v_key_1056_ = lean_ctor_get(v_x_902_, 1);
lean_inc(v_key_1056_);
v_val_1057_ = lean_ctor_get(v_x_902_, 2);
lean_inc(v_val_1057_);
v_rchild_1058_ = lean_ctor_get(v_x_902_, 3);
lean_inc(v_rchild_1058_);
lean_dec_ref_known(v_x_902_, 4);
v_l_927_ = v_x_899_;
v_k_928_ = v_x_900_;
v_v_929_ = v_x_901_;
v_a_930_ = v_lchild_1055_;
v_ky_931_ = v_key_1056_;
v_vy_932_ = v_val_1057_;
v_b_933_ = v_rchild_1058_;
goto v___jp_926_;
}
}
else
{
v_l_1025_ = v_x_899_;
v_k_1026_ = v_x_900_;
v_v_1027_ = v_x_901_;
v_r_1028_ = v_x_902_;
goto v___jp_1024_;
}
}
}
else
{
if (lean_obj_tag(v_x_902_) == 1)
{
uint8_t v_color_1059_; 
v_color_1059_ = lean_ctor_get_uint8(v_x_902_, sizeof(void*)*4);
if (v_color_1059_ == 0)
{
lean_object* v_lchild_1060_; 
v_lchild_1060_ = lean_ctor_get(v_x_902_, 0);
if (lean_obj_tag(v_lchild_1060_) == 1)
{
uint8_t v_color_1061_; 
v_color_1061_ = lean_ctor_get_uint8(v_lchild_1060_, sizeof(void*)*4);
if (v_color_1061_ == 1)
{
lean_object* v_key_1062_; lean_object* v_val_1063_; lean_object* v_rchild_1064_; lean_object* v_lchild_1065_; lean_object* v_key_1066_; lean_object* v_val_1067_; lean_object* v_rchild_1068_; 
lean_inc_ref(v_lchild_1060_);
v_key_1062_ = lean_ctor_get(v_x_902_, 1);
lean_inc(v_key_1062_);
v_val_1063_ = lean_ctor_get(v_x_902_, 2);
lean_inc(v_val_1063_);
v_rchild_1064_ = lean_ctor_get(v_x_902_, 3);
lean_inc(v_rchild_1064_);
lean_dec_ref_known(v_x_902_, 4);
v_lchild_1065_ = lean_ctor_get(v_lchild_1060_, 0);
lean_inc(v_lchild_1065_);
v_key_1066_ = lean_ctor_get(v_lchild_1060_, 1);
lean_inc(v_key_1066_);
v_val_1067_ = lean_ctor_get(v_lchild_1060_, 2);
lean_inc(v_val_1067_);
v_rchild_1068_ = lean_ctor_get(v_lchild_1060_, 3);
lean_inc(v_rchild_1068_);
lean_dec_ref_known(v_lchild_1060_, 4);
v_l_984_ = v_x_899_;
v_k_985_ = v_x_900_;
v_v_986_ = v_x_901_;
v_a_987_ = v_lchild_1065_;
v_ky_988_ = v_key_1066_;
v_vy_989_ = v_val_1067_;
v_b_990_ = v_rchild_1068_;
v_kz_991_ = v_key_1062_;
v_vz_992_ = v_val_1063_;
v_c_993_ = v_rchild_1064_;
goto v___jp_983_;
}
else
{
v_l_1025_ = v_x_899_;
v_k_1026_ = v_x_900_;
v_v_1027_ = v_x_901_;
v_r_1028_ = v_x_902_;
goto v___jp_1024_;
}
}
else
{
v_l_1025_ = v_x_899_;
v_k_1026_ = v_x_900_;
v_v_1027_ = v_x_901_;
v_r_1028_ = v_x_902_;
goto v___jp_1024_;
}
}
else
{
lean_object* v_lchild_1069_; lean_object* v_key_1070_; lean_object* v_val_1071_; lean_object* v_rchild_1072_; 
v_lchild_1069_ = lean_ctor_get(v_x_902_, 0);
lean_inc(v_lchild_1069_);
v_key_1070_ = lean_ctor_get(v_x_902_, 1);
lean_inc(v_key_1070_);
v_val_1071_ = lean_ctor_get(v_x_902_, 2);
lean_inc(v_val_1071_);
v_rchild_1072_ = lean_ctor_get(v_x_902_, 3);
lean_inc(v_rchild_1072_);
lean_dec_ref_known(v_x_902_, 4);
v_l_927_ = v_x_899_;
v_k_928_ = v_x_900_;
v_v_929_ = v_x_901_;
v_a_930_ = v_lchild_1069_;
v_ky_931_ = v_key_1070_;
v_vy_932_ = v_val_1071_;
v_b_933_ = v_rchild_1072_;
goto v___jp_926_;
}
}
else
{
v_l_1025_ = v_x_899_;
v_k_1026_ = v_x_900_;
v_v_1027_ = v_x_901_;
v_r_1028_ = v_x_902_;
goto v___jp_1024_;
}
}
v___jp_903_:
{
uint8_t v___x_908_; lean_object* v___x_909_; 
v___x_908_ = 1;
v___x_909_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_909_, 0, v_a_904_);
lean_ctor_set(v___x_909_, 1, v_kx_905_);
lean_ctor_set(v___x_909_, 2, v_vx_906_);
lean_ctor_set(v___x_909_, 3, v_b_907_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*4, v___x_908_);
return v___x_909_;
}
v___jp_910_:
{
uint8_t v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_921_ = 0;
v___x_922_ = 1;
v___x_923_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_923_, 0, v_a_911_);
lean_ctor_set(v___x_923_, 1, v_kx_912_);
lean_ctor_set(v___x_923_, 2, v_vx_913_);
lean_ctor_set(v___x_923_, 3, v_b_914_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*4, v___x_922_);
v___x_924_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_924_, 0, v_c_917_);
lean_ctor_set(v___x_924_, 1, v_kz_918_);
lean_ctor_set(v___x_924_, 2, v_vz_919_);
lean_ctor_set(v___x_924_, 3, v_d_920_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*4, v___x_922_);
v___x_925_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v_ky_915_);
lean_ctor_set(v___x_925_, 2, v_vy_916_);
lean_ctor_set(v___x_925_, 3, v___x_924_);
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*4, v___x_921_);
return v___x_925_;
}
v___jp_926_:
{
uint8_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = 0;
lean_inc(v_b_933_);
lean_inc(v_vy_932_);
lean_inc(v_ky_931_);
lean_inc(v_a_930_);
v___x_935_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_935_, 0, v_a_930_);
lean_ctor_set(v___x_935_, 1, v_ky_931_);
lean_ctor_set(v___x_935_, 2, v_vy_932_);
lean_ctor_set(v___x_935_, 3, v_b_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*4, v___x_934_);
if (lean_obj_tag(v_a_930_) == 1)
{
uint8_t v_color_936_; 
v_color_936_ = lean_ctor_get_uint8(v_a_930_, sizeof(void*)*4);
if (v_color_936_ == 0)
{
lean_object* v_lchild_937_; lean_object* v_key_938_; lean_object* v_val_939_; lean_object* v_rchild_940_; 
lean_dec_ref_known(v___x_935_, 4);
v_lchild_937_ = lean_ctor_get(v_a_930_, 0);
lean_inc(v_lchild_937_);
v_key_938_ = lean_ctor_get(v_a_930_, 1);
lean_inc(v_key_938_);
v_val_939_ = lean_ctor_get(v_a_930_, 2);
lean_inc(v_val_939_);
v_rchild_940_ = lean_ctor_get(v_a_930_, 3);
lean_inc(v_rchild_940_);
lean_dec_ref_known(v_a_930_, 4);
v_a_911_ = v_l_927_;
v_kx_912_ = v_k_928_;
v_vx_913_ = v_v_929_;
v_b_914_ = v_lchild_937_;
v_ky_915_ = v_key_938_;
v_vy_916_ = v_val_939_;
v_c_917_ = v_rchild_940_;
v_kz_918_ = v_ky_931_;
v_vz_919_ = v_vy_932_;
v_d_920_ = v_b_933_;
goto v___jp_910_;
}
else
{
if (lean_obj_tag(v_b_933_) == 1)
{
uint8_t v_color_941_; 
v_color_941_ = lean_ctor_get_uint8(v_b_933_, sizeof(void*)*4);
if (v_color_941_ == 0)
{
lean_object* v_lchild_942_; lean_object* v_key_943_; lean_object* v_val_944_; lean_object* v_rchild_945_; 
lean_dec_ref_known(v___x_935_, 4);
v_lchild_942_ = lean_ctor_get(v_b_933_, 0);
lean_inc(v_lchild_942_);
v_key_943_ = lean_ctor_get(v_b_933_, 1);
lean_inc(v_key_943_);
v_val_944_ = lean_ctor_get(v_b_933_, 2);
lean_inc(v_val_944_);
v_rchild_945_ = lean_ctor_get(v_b_933_, 3);
lean_inc(v_rchild_945_);
lean_dec_ref_known(v_b_933_, 4);
v_a_911_ = v_l_927_;
v_kx_912_ = v_k_928_;
v_vx_913_ = v_v_929_;
v_b_914_ = v_a_930_;
v_ky_915_ = v_ky_931_;
v_vy_916_ = v_vy_932_;
v_c_917_ = v_lchild_942_;
v_kz_918_ = v_key_943_;
v_vz_919_ = v_val_944_;
v_d_920_ = v_rchild_945_;
goto v___jp_910_;
}
else
{
lean_dec_ref_known(v_b_933_, 4);
lean_dec_ref_known(v_a_930_, 4);
lean_dec(v_vy_932_);
lean_dec(v_ky_931_);
v_a_904_ = v_l_927_;
v_kx_905_ = v_k_928_;
v_vx_906_ = v_v_929_;
v_b_907_ = v___x_935_;
goto v___jp_903_;
}
}
else
{
lean_dec_ref_known(v_a_930_, 4);
lean_dec(v_b_933_);
lean_dec(v_vy_932_);
lean_dec(v_ky_931_);
v_a_904_ = v_l_927_;
v_kx_905_ = v_k_928_;
v_vx_906_ = v_v_929_;
v_b_907_ = v___x_935_;
goto v___jp_903_;
}
}
}
else
{
if (lean_obj_tag(v_b_933_) == 1)
{
uint8_t v_color_946_; 
v_color_946_ = lean_ctor_get_uint8(v_b_933_, sizeof(void*)*4);
if (v_color_946_ == 0)
{
lean_object* v_lchild_947_; lean_object* v_key_948_; lean_object* v_val_949_; lean_object* v_rchild_950_; 
lean_dec_ref_known(v___x_935_, 4);
v_lchild_947_ = lean_ctor_get(v_b_933_, 0);
lean_inc(v_lchild_947_);
v_key_948_ = lean_ctor_get(v_b_933_, 1);
lean_inc(v_key_948_);
v_val_949_ = lean_ctor_get(v_b_933_, 2);
lean_inc(v_val_949_);
v_rchild_950_ = lean_ctor_get(v_b_933_, 3);
lean_inc(v_rchild_950_);
lean_dec_ref_known(v_b_933_, 4);
v_a_911_ = v_l_927_;
v_kx_912_ = v_k_928_;
v_vx_913_ = v_v_929_;
v_b_914_ = v_a_930_;
v_ky_915_ = v_ky_931_;
v_vy_916_ = v_vy_932_;
v_c_917_ = v_lchild_947_;
v_kz_918_ = v_key_948_;
v_vz_919_ = v_val_949_;
v_d_920_ = v_rchild_950_;
goto v___jp_910_;
}
else
{
lean_dec_ref_known(v_b_933_, 4);
lean_dec(v_vy_932_);
lean_dec(v_ky_931_);
lean_dec(v_a_930_);
v_a_904_ = v_l_927_;
v_kx_905_ = v_k_928_;
v_vx_906_ = v_v_929_;
v_b_907_ = v___x_935_;
goto v___jp_903_;
}
}
else
{
lean_dec(v_b_933_);
lean_dec(v_vy_932_);
lean_dec(v_ky_931_);
lean_dec(v_a_930_);
v_a_904_ = v_l_927_;
v_kx_905_ = v_k_928_;
v_vx_906_ = v_v_929_;
v_b_907_ = v___x_935_;
goto v___jp_903_;
}
}
}
v___jp_951_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_967_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_967_, 0, v_a_957_);
lean_ctor_set(v___x_967_, 1, v_kx_958_);
lean_ctor_set(v___x_967_, 2, v_vx_959_);
lean_ctor_set(v___x_967_, 3, v_b_960_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*4, v___y_952_);
v___x_968_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_968_, 0, v_c_963_);
lean_ctor_set(v___x_968_, 1, v_kz_964_);
lean_ctor_set(v___x_968_, 2, v_vz_965_);
lean_ctor_set(v___x_968_, 3, v_d_966_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*4, v___y_952_);
v___x_969_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v_ky_961_);
lean_ctor_set(v___x_969_, 2, v_vy_962_);
lean_ctor_set(v___x_969_, 3, v___x_968_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*4, v___y_954_);
v___x_970_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_970_, 0, v___y_953_);
lean_ctor_set(v___x_970_, 1, v___y_956_);
lean_ctor_set(v___x_970_, 2, v___y_955_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*4, v___y_954_);
return v___x_970_;
}
v___jp_971_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_981_, 0, v_a_977_);
lean_ctor_set(v___x_981_, 1, v_kx_978_);
lean_ctor_set(v___x_981_, 2, v_vx_979_);
lean_ctor_set(v___x_981_, 3, v_b_980_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*4, v___y_972_);
v___x_982_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_982_, 0, v___y_973_);
lean_ctor_set(v___x_982_, 1, v___y_976_);
lean_ctor_set(v___x_982_, 2, v___y_975_);
lean_ctor_set(v___x_982_, 3, v___x_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*4, v___y_974_);
return v___x_982_;
}
v___jp_983_:
{
uint8_t v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = 0;
v___x_995_ = 1;
v___x_996_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_996_, 0, v_l_984_);
lean_ctor_set(v___x_996_, 1, v_k_985_);
lean_ctor_set(v___x_996_, 2, v_v_986_);
lean_ctor_set(v___x_996_, 3, v_a_987_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*4, v___x_995_);
v___x_997_ = l_Lean_RBNode_setRed___redArg(v_c_993_);
if (lean_obj_tag(v___x_997_) == 1)
{
uint8_t v_color_998_; 
v_color_998_ = lean_ctor_get_uint8(v___x_997_, sizeof(void*)*4);
if (v_color_998_ == 0)
{
lean_object* v_lchild_999_; 
v_lchild_999_ = lean_ctor_get(v___x_997_, 0);
if (lean_obj_tag(v_lchild_999_) == 1)
{
uint8_t v_color_1000_; 
v_color_1000_ = lean_ctor_get_uint8(v_lchild_999_, sizeof(void*)*4);
if (v_color_1000_ == 0)
{
lean_object* v_key_1001_; lean_object* v_val_1002_; lean_object* v_rchild_1003_; lean_object* v_lchild_1004_; lean_object* v_key_1005_; lean_object* v_val_1006_; lean_object* v_rchild_1007_; 
lean_inc_ref(v_lchild_999_);
v_key_1001_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_key_1001_);
v_val_1002_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_val_1002_);
v_rchild_1003_ = lean_ctor_get(v___x_997_, 3);
lean_inc(v_rchild_1003_);
lean_dec_ref_known(v___x_997_, 4);
v_lchild_1004_ = lean_ctor_get(v_lchild_999_, 0);
lean_inc(v_lchild_1004_);
v_key_1005_ = lean_ctor_get(v_lchild_999_, 1);
lean_inc(v_key_1005_);
v_val_1006_ = lean_ctor_get(v_lchild_999_, 2);
lean_inc(v_val_1006_);
v_rchild_1007_ = lean_ctor_get(v_lchild_999_, 3);
lean_inc(v_rchild_1007_);
lean_dec_ref_known(v_lchild_999_, 4);
v___y_952_ = v___x_995_;
v___y_953_ = v___x_996_;
v___y_954_ = v___x_994_;
v___y_955_ = v_vy_989_;
v___y_956_ = v_ky_988_;
v_a_957_ = v_b_990_;
v_kx_958_ = v_kz_991_;
v_vx_959_ = v_vz_992_;
v_b_960_ = v_lchild_1004_;
v_ky_961_ = v_key_1005_;
v_vy_962_ = v_val_1006_;
v_c_963_ = v_rchild_1007_;
v_kz_964_ = v_key_1001_;
v_vz_965_ = v_val_1002_;
v_d_966_ = v_rchild_1003_;
goto v___jp_951_;
}
else
{
lean_object* v_rchild_1008_; 
v_rchild_1008_ = lean_ctor_get(v___x_997_, 3);
if (lean_obj_tag(v_rchild_1008_) == 1)
{
uint8_t v_color_1009_; 
v_color_1009_ = lean_ctor_get_uint8(v_rchild_1008_, sizeof(void*)*4);
if (v_color_1009_ == 0)
{
lean_object* v_key_1010_; lean_object* v_val_1011_; lean_object* v_lchild_1012_; lean_object* v_key_1013_; lean_object* v_val_1014_; lean_object* v_rchild_1015_; 
lean_inc_ref(v_rchild_1008_);
lean_inc_ref(v_lchild_999_);
v_key_1010_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_key_1010_);
v_val_1011_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_val_1011_);
lean_dec_ref_known(v___x_997_, 4);
v_lchild_1012_ = lean_ctor_get(v_rchild_1008_, 0);
lean_inc(v_lchild_1012_);
v_key_1013_ = lean_ctor_get(v_rchild_1008_, 1);
lean_inc(v_key_1013_);
v_val_1014_ = lean_ctor_get(v_rchild_1008_, 2);
lean_inc(v_val_1014_);
v_rchild_1015_ = lean_ctor_get(v_rchild_1008_, 3);
lean_inc(v_rchild_1015_);
lean_dec_ref_known(v_rchild_1008_, 4);
v___y_952_ = v___x_995_;
v___y_953_ = v___x_996_;
v___y_954_ = v___x_994_;
v___y_955_ = v_vy_989_;
v___y_956_ = v_ky_988_;
v_a_957_ = v_b_990_;
v_kx_958_ = v_kz_991_;
v_vx_959_ = v_vz_992_;
v_b_960_ = v_lchild_999_;
v_ky_961_ = v_key_1010_;
v_vy_962_ = v_val_1011_;
v_c_963_ = v_lchild_1012_;
v_kz_964_ = v_key_1013_;
v_vz_965_ = v_val_1014_;
v_d_966_ = v_rchild_1015_;
goto v___jp_951_;
}
else
{
v___y_972_ = v___x_995_;
v___y_973_ = v___x_996_;
v___y_974_ = v___x_994_;
v___y_975_ = v_vy_989_;
v___y_976_ = v_ky_988_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v___x_995_;
v___y_973_ = v___x_996_;
v___y_974_ = v___x_994_;
v___y_975_ = v_vy_989_;
v___y_976_ = v_ky_988_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
}
else
{
lean_object* v_rchild_1016_; 
v_rchild_1016_ = lean_ctor_get(v___x_997_, 3);
if (lean_obj_tag(v_rchild_1016_) == 1)
{
uint8_t v_color_1017_; 
v_color_1017_ = lean_ctor_get_uint8(v_rchild_1016_, sizeof(void*)*4);
if (v_color_1017_ == 0)
{
lean_object* v_key_1018_; lean_object* v_val_1019_; lean_object* v_lchild_1020_; lean_object* v_key_1021_; lean_object* v_val_1022_; lean_object* v_rchild_1023_; 
lean_inc_ref(v_rchild_1016_);
lean_inc(v_lchild_999_);
v_key_1018_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_key_1018_);
v_val_1019_ = lean_ctor_get(v___x_997_, 2);
lean_inc(v_val_1019_);
lean_dec_ref_known(v___x_997_, 4);
v_lchild_1020_ = lean_ctor_get(v_rchild_1016_, 0);
lean_inc(v_lchild_1020_);
v_key_1021_ = lean_ctor_get(v_rchild_1016_, 1);
lean_inc(v_key_1021_);
v_val_1022_ = lean_ctor_get(v_rchild_1016_, 2);
lean_inc(v_val_1022_);
v_rchild_1023_ = lean_ctor_get(v_rchild_1016_, 3);
lean_inc(v_rchild_1023_);
lean_dec_ref_known(v_rchild_1016_, 4);
v___y_952_ = v___x_995_;
v___y_953_ = v___x_996_;
v___y_954_ = v___x_994_;
v___y_955_ = v_vy_989_;
v___y_956_ = v_ky_988_;
v_a_957_ = v_b_990_;
v_kx_958_ = v_kz_991_;
v_vx_959_ = v_vz_992_;
v_b_960_ = v_lchild_999_;
v_ky_961_ = v_key_1018_;
v_vy_962_ = v_val_1019_;
v_c_963_ = v_lchild_1020_;
v_kz_964_ = v_key_1021_;
v_vz_965_ = v_val_1022_;
v_d_966_ = v_rchild_1023_;
goto v___jp_951_;
}
else
{
v___y_972_ = v___x_995_;
v___y_973_ = v___x_996_;
v___y_974_ = v___x_994_;
v___y_975_ = v_vy_989_;
v___y_976_ = v_ky_988_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v___x_995_;
v___y_973_ = v___x_996_;
v___y_974_ = v___x_994_;
v___y_975_ = v_vy_989_;
v___y_976_ = v_ky_988_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
}
else
{
v___y_972_ = v___x_995_;
v___y_973_ = v___x_996_;
v___y_974_ = v___x_994_;
v___y_975_ = v_vy_989_;
v___y_976_ = v_ky_988_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v___x_995_;
v___y_973_ = v___x_996_;
v___y_974_ = v___x_994_;
v___y_975_ = v_vy_989_;
v___y_976_ = v_ky_988_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
v___jp_1024_:
{
uint8_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = 0;
v___x_1030_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1030_, 0, v_l_1025_);
lean_ctor_set(v___x_1030_, 1, v_k_1026_);
lean_ctor_set(v___x_1030_, 2, v_v_1027_);
lean_ctor_set(v___x_1030_, 3, v_r_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*4, v___x_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balLeft(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_RBNode_balLeft___redArg(v_x_1075_, v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight___redArg(lean_object* v_l_1080_, lean_object* v_k_1081_, lean_object* v_v_1082_, lean_object* v_r_1083_){
_start:
{
uint8_t v___y_1088_; lean_object* v_a_1089_; lean_object* v_kx_1090_; lean_object* v_vx_1091_; lean_object* v_b_1092_; lean_object* v_ky_1093_; lean_object* v_vy_1094_; lean_object* v_c_1095_; lean_object* v_kz_1096_; lean_object* v_vz_1097_; lean_object* v_d_1098_; uint8_t v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; uint8_t v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v_a_1118_; lean_object* v_kx_1119_; lean_object* v_vx_1120_; lean_object* v_b_1121_; lean_object* v_ky_1122_; lean_object* v_vy_1123_; lean_object* v_c_1124_; lean_object* v_kz_1125_; lean_object* v_vz_1126_; lean_object* v_d_1127_; uint8_t v___y_1132_; uint8_t v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v_a_1137_; lean_object* v_kx_1138_; lean_object* v_vx_1139_; lean_object* v_b_1140_; 
if (lean_obj_tag(v_r_1083_) == 1)
{
uint8_t v_color_1241_; 
v_color_1241_ = lean_ctor_get_uint8(v_r_1083_, sizeof(void*)*4);
if (v_color_1241_ == 0)
{
lean_object* v_lchild_1242_; lean_object* v_key_1243_; lean_object* v_val_1244_; lean_object* v_rchild_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1254_; 
v_lchild_1242_ = lean_ctor_get(v_r_1083_, 0);
v_key_1243_ = lean_ctor_get(v_r_1083_, 1);
v_val_1244_ = lean_ctor_get(v_r_1083_, 2);
v_rchild_1245_ = lean_ctor_get(v_r_1083_, 3);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_r_1083_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1247_ = v_r_1083_;
v_isShared_1248_ = v_isSharedCheck_1254_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_rchild_1245_);
lean_inc(v_val_1244_);
lean_inc(v_key_1243_);
lean_inc(v_lchild_1242_);
lean_dec(v_r_1083_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1254_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
uint8_t v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = 1;
if (v_isShared_1248_ == 0)
{
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_lchild_1242_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_key_1243_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_val_1244_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_rchild_1245_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*4, v___x_1249_);
v___x_1252_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1252_, 0, v_l_1080_);
lean_ctor_set(v___x_1252_, 1, v_k_1081_);
lean_ctor_set(v___x_1252_, 2, v_v_1082_);
lean_ctor_set(v___x_1252_, 3, v___x_1251_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*4, v_color_1241_);
return v___x_1252_;
}
}
}
else
{
goto v___jp_1142_;
}
}
else
{
goto v___jp_1142_;
}
v___jp_1084_:
{
uint8_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = 0;
v___x_1086_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1086_, 0, v_l_1080_);
lean_ctor_set(v___x_1086_, 1, v_k_1081_);
lean_ctor_set(v___x_1086_, 2, v_v_1082_);
lean_ctor_set(v___x_1086_, 3, v_r_1083_);
lean_ctor_set_uint8(v___x_1086_, sizeof(void*)*4, v___x_1085_);
return v___x_1086_;
}
v___jp_1087_:
{
uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = 0;
v___x_1100_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1100_, 0, v_a_1089_);
lean_ctor_set(v___x_1100_, 1, v_kx_1090_);
lean_ctor_set(v___x_1100_, 2, v_vx_1091_);
lean_ctor_set(v___x_1100_, 3, v_b_1092_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*4, v___y_1088_);
v___x_1101_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1101_, 0, v_c_1095_);
lean_ctor_set(v___x_1101_, 1, v_kz_1096_);
lean_ctor_set(v___x_1101_, 2, v_vz_1097_);
lean_ctor_set(v___x_1101_, 3, v_d_1098_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*4, v___y_1088_);
v___x_1102_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v_ky_1093_);
lean_ctor_set(v___x_1102_, 2, v_vy_1094_);
lean_ctor_set(v___x_1102_, 3, v___x_1101_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*4, v___x_1099_);
return v___x_1102_;
}
v___jp_1103_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1110_, 0, v___y_1108_);
lean_ctor_set(v___x_1110_, 1, v_k_1081_);
lean_ctor_set(v___x_1110_, 2, v_v_1082_);
lean_ctor_set(v___x_1110_, 3, v_r_1083_);
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*4, v___y_1104_);
v___x_1111_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1111_, 0, v___y_1109_);
lean_ctor_set(v___x_1111_, 1, v___y_1107_);
lean_ctor_set(v___x_1111_, 2, v___y_1106_);
lean_ctor_set(v___x_1111_, 3, v___x_1110_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*4, v___y_1105_);
return v___x_1111_;
}
v___jp_1112_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1128_, 0, v_a_1118_);
lean_ctor_set(v___x_1128_, 1, v_kx_1119_);
lean_ctor_set(v___x_1128_, 2, v_vx_1120_);
lean_ctor_set(v___x_1128_, 3, v_b_1121_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*4, v___y_1113_);
v___x_1129_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1129_, 0, v_c_1124_);
lean_ctor_set(v___x_1129_, 1, v_kz_1125_);
lean_ctor_set(v___x_1129_, 2, v_vz_1126_);
lean_ctor_set(v___x_1129_, 3, v_d_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*4, v___y_1113_);
v___x_1130_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v_ky_1122_);
lean_ctor_set(v___x_1130_, 2, v_vy_1123_);
lean_ctor_set(v___x_1130_, 3, v___x_1129_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*4, v___y_1114_);
v___y_1104_ = v___y_1113_;
v___y_1105_ = v___y_1114_;
v___y_1106_ = v___y_1115_;
v___y_1107_ = v___y_1117_;
v___y_1108_ = v___y_1116_;
v___y_1109_ = v___x_1130_;
goto v___jp_1103_;
}
v___jp_1131_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1141_, 0, v_a_1137_);
lean_ctor_set(v___x_1141_, 1, v_kx_1138_);
lean_ctor_set(v___x_1141_, 2, v_vx_1139_);
lean_ctor_set(v___x_1141_, 3, v_b_1140_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*4, v___y_1132_);
v___y_1104_ = v___y_1132_;
v___y_1105_ = v___y_1133_;
v___y_1106_ = v___y_1134_;
v___y_1107_ = v___y_1136_;
v___y_1108_ = v___y_1135_;
v___y_1109_ = v___x_1141_;
goto v___jp_1103_;
}
v___jp_1142_:
{
if (lean_obj_tag(v_l_1080_) == 1)
{
uint8_t v_color_1143_; 
v_color_1143_ = lean_ctor_get_uint8(v_l_1080_, sizeof(void*)*4);
if (v_color_1143_ == 0)
{
lean_object* v_rchild_1144_; 
v_rchild_1144_ = lean_ctor_get(v_l_1080_, 3);
if (lean_obj_tag(v_rchild_1144_) == 1)
{
uint8_t v_color_1145_; 
v_color_1145_ = lean_ctor_get_uint8(v_rchild_1144_, sizeof(void*)*4);
if (v_color_1145_ == 1)
{
lean_object* v_lchild_1146_; lean_object* v_key_1147_; lean_object* v_val_1148_; lean_object* v_lchild_1149_; lean_object* v_key_1150_; lean_object* v_val_1151_; lean_object* v_rchild_1152_; lean_object* v___x_1153_; 
lean_inc_ref(v_rchild_1144_);
v_lchild_1146_ = lean_ctor_get(v_l_1080_, 0);
lean_inc(v_lchild_1146_);
v_key_1147_ = lean_ctor_get(v_l_1080_, 1);
lean_inc(v_key_1147_);
v_val_1148_ = lean_ctor_get(v_l_1080_, 2);
lean_inc(v_val_1148_);
lean_dec_ref_known(v_l_1080_, 4);
v_lchild_1149_ = lean_ctor_get(v_rchild_1144_, 0);
lean_inc(v_lchild_1149_);
v_key_1150_ = lean_ctor_get(v_rchild_1144_, 1);
lean_inc(v_key_1150_);
v_val_1151_ = lean_ctor_get(v_rchild_1144_, 2);
lean_inc(v_val_1151_);
v_rchild_1152_ = lean_ctor_get(v_rchild_1144_, 3);
lean_inc(v_rchild_1152_);
lean_dec_ref_known(v_rchild_1144_, 4);
v___x_1153_ = l_Lean_RBNode_setRed___redArg(v_lchild_1146_);
if (lean_obj_tag(v___x_1153_) == 1)
{
uint8_t v_color_1154_; 
v_color_1154_ = lean_ctor_get_uint8(v___x_1153_, sizeof(void*)*4);
if (v_color_1154_ == 0)
{
lean_object* v_lchild_1155_; 
v_lchild_1155_ = lean_ctor_get(v___x_1153_, 0);
if (lean_obj_tag(v_lchild_1155_) == 1)
{
uint8_t v_color_1156_; 
v_color_1156_ = lean_ctor_get_uint8(v_lchild_1155_, sizeof(void*)*4);
if (v_color_1156_ == 0)
{
lean_object* v_key_1157_; lean_object* v_val_1158_; lean_object* v_rchild_1159_; lean_object* v_lchild_1160_; lean_object* v_key_1161_; lean_object* v_val_1162_; lean_object* v_rchild_1163_; 
lean_inc_ref(v_lchild_1155_);
v_key_1157_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_key_1157_);
v_val_1158_ = lean_ctor_get(v___x_1153_, 2);
lean_inc(v_val_1158_);
v_rchild_1159_ = lean_ctor_get(v___x_1153_, 3);
lean_inc(v_rchild_1159_);
lean_dec_ref_known(v___x_1153_, 4);
v_lchild_1160_ = lean_ctor_get(v_lchild_1155_, 0);
lean_inc(v_lchild_1160_);
v_key_1161_ = lean_ctor_get(v_lchild_1155_, 1);
lean_inc(v_key_1161_);
v_val_1162_ = lean_ctor_get(v_lchild_1155_, 2);
lean_inc(v_val_1162_);
v_rchild_1163_ = lean_ctor_get(v_lchild_1155_, 3);
lean_inc(v_rchild_1163_);
lean_dec_ref_known(v_lchild_1155_, 4);
v___y_1113_ = v_color_1145_;
v___y_1114_ = v_color_1143_;
v___y_1115_ = v_val_1151_;
v___y_1116_ = v_rchild_1152_;
v___y_1117_ = v_key_1150_;
v_a_1118_ = v_lchild_1160_;
v_kx_1119_ = v_key_1161_;
v_vx_1120_ = v_val_1162_;
v_b_1121_ = v_rchild_1163_;
v_ky_1122_ = v_key_1157_;
v_vy_1123_ = v_val_1158_;
v_c_1124_ = v_rchild_1159_;
v_kz_1125_ = v_key_1147_;
v_vz_1126_ = v_val_1148_;
v_d_1127_ = v_lchild_1149_;
goto v___jp_1112_;
}
else
{
lean_object* v_rchild_1164_; 
v_rchild_1164_ = lean_ctor_get(v___x_1153_, 3);
if (lean_obj_tag(v_rchild_1164_) == 1)
{
uint8_t v_color_1165_; 
v_color_1165_ = lean_ctor_get_uint8(v_rchild_1164_, sizeof(void*)*4);
if (v_color_1165_ == 0)
{
lean_object* v_key_1166_; lean_object* v_val_1167_; lean_object* v_lchild_1168_; lean_object* v_key_1169_; lean_object* v_val_1170_; lean_object* v_rchild_1171_; 
lean_inc_ref(v_rchild_1164_);
lean_inc_ref(v_lchild_1155_);
v_key_1166_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_key_1166_);
v_val_1167_ = lean_ctor_get(v___x_1153_, 2);
lean_inc(v_val_1167_);
lean_dec_ref_known(v___x_1153_, 4);
v_lchild_1168_ = lean_ctor_get(v_rchild_1164_, 0);
lean_inc(v_lchild_1168_);
v_key_1169_ = lean_ctor_get(v_rchild_1164_, 1);
lean_inc(v_key_1169_);
v_val_1170_ = lean_ctor_get(v_rchild_1164_, 2);
lean_inc(v_val_1170_);
v_rchild_1171_ = lean_ctor_get(v_rchild_1164_, 3);
lean_inc(v_rchild_1171_);
lean_dec_ref_known(v_rchild_1164_, 4);
v___y_1113_ = v_color_1145_;
v___y_1114_ = v_color_1143_;
v___y_1115_ = v_val_1151_;
v___y_1116_ = v_rchild_1152_;
v___y_1117_ = v_key_1150_;
v_a_1118_ = v_lchild_1155_;
v_kx_1119_ = v_key_1166_;
v_vx_1120_ = v_val_1167_;
v_b_1121_ = v_lchild_1168_;
v_ky_1122_ = v_key_1169_;
v_vy_1123_ = v_val_1170_;
v_c_1124_ = v_rchild_1171_;
v_kz_1125_ = v_key_1147_;
v_vz_1126_ = v_val_1148_;
v_d_1127_ = v_lchild_1149_;
goto v___jp_1112_;
}
else
{
v___y_1132_ = v_color_1145_;
v___y_1133_ = v_color_1143_;
v___y_1134_ = v_val_1151_;
v___y_1135_ = v_rchild_1152_;
v___y_1136_ = v_key_1150_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
v___y_1132_ = v_color_1145_;
v___y_1133_ = v_color_1143_;
v___y_1134_ = v_val_1151_;
v___y_1135_ = v_rchild_1152_;
v___y_1136_ = v_key_1150_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
}
else
{
lean_object* v_rchild_1172_; 
v_rchild_1172_ = lean_ctor_get(v___x_1153_, 3);
if (lean_obj_tag(v_rchild_1172_) == 1)
{
uint8_t v_color_1173_; 
v_color_1173_ = lean_ctor_get_uint8(v_rchild_1172_, sizeof(void*)*4);
if (v_color_1173_ == 0)
{
lean_object* v_key_1174_; lean_object* v_val_1175_; lean_object* v_lchild_1176_; lean_object* v_key_1177_; lean_object* v_val_1178_; lean_object* v_rchild_1179_; 
lean_inc_ref(v_rchild_1172_);
lean_inc(v_lchild_1155_);
v_key_1174_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_key_1174_);
v_val_1175_ = lean_ctor_get(v___x_1153_, 2);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1153_, 4);
v_lchild_1176_ = lean_ctor_get(v_rchild_1172_, 0);
lean_inc(v_lchild_1176_);
v_key_1177_ = lean_ctor_get(v_rchild_1172_, 1);
lean_inc(v_key_1177_);
v_val_1178_ = lean_ctor_get(v_rchild_1172_, 2);
lean_inc(v_val_1178_);
v_rchild_1179_ = lean_ctor_get(v_rchild_1172_, 3);
lean_inc(v_rchild_1179_);
lean_dec_ref_known(v_rchild_1172_, 4);
v___y_1113_ = v_color_1145_;
v___y_1114_ = v_color_1143_;
v___y_1115_ = v_val_1151_;
v___y_1116_ = v_rchild_1152_;
v___y_1117_ = v_key_1150_;
v_a_1118_ = v_lchild_1155_;
v_kx_1119_ = v_key_1174_;
v_vx_1120_ = v_val_1175_;
v_b_1121_ = v_lchild_1176_;
v_ky_1122_ = v_key_1177_;
v_vy_1123_ = v_val_1178_;
v_c_1124_ = v_rchild_1179_;
v_kz_1125_ = v_key_1147_;
v_vz_1126_ = v_val_1148_;
v_d_1127_ = v_lchild_1149_;
goto v___jp_1112_;
}
else
{
v___y_1132_ = v_color_1145_;
v___y_1133_ = v_color_1143_;
v___y_1134_ = v_val_1151_;
v___y_1135_ = v_rchild_1152_;
v___y_1136_ = v_key_1150_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
v___y_1132_ = v_color_1145_;
v___y_1133_ = v_color_1143_;
v___y_1134_ = v_val_1151_;
v___y_1135_ = v_rchild_1152_;
v___y_1136_ = v_key_1150_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
}
else
{
v___y_1132_ = v_color_1145_;
v___y_1133_ = v_color_1143_;
v___y_1134_ = v_val_1151_;
v___y_1135_ = v_rchild_1152_;
v___y_1136_ = v_key_1150_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
v___y_1132_ = v_color_1145_;
v___y_1133_ = v_color_1143_;
v___y_1134_ = v_val_1151_;
v___y_1135_ = v_rchild_1152_;
v___y_1136_ = v_key_1150_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
goto v___jp_1084_;
}
}
else
{
goto v___jp_1084_;
}
}
else
{
lean_object* v_lchild_1180_; lean_object* v_key_1181_; lean_object* v_val_1182_; lean_object* v_rchild_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1240_; 
v_lchild_1180_ = lean_ctor_get(v_l_1080_, 0);
v_key_1181_ = lean_ctor_get(v_l_1080_, 1);
v_val_1182_ = lean_ctor_get(v_l_1080_, 2);
v_rchild_1183_ = lean_ctor_get(v_l_1080_, 3);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_l_1080_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1185_ = v_l_1080_;
v_isShared_1186_ = v_isSharedCheck_1240_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_rchild_1183_);
lean_inc(v_val_1182_);
lean_inc(v_key_1181_);
lean_inc(v_lchild_1180_);
lean_dec(v_l_1080_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1240_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
uint8_t v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = 0;
lean_inc(v_rchild_1183_);
lean_inc(v_val_1182_);
lean_inc(v_key_1181_);
lean_inc(v_lchild_1180_);
if (v_isShared_1186_ == 0)
{
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_lchild_1180_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_key_1181_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_val_1182_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_rchild_1183_);
v___x_1189_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*4, v___x_1187_);
if (lean_obj_tag(v_lchild_1180_) == 1)
{
uint8_t v_color_1190_; 
v_color_1190_ = lean_ctor_get_uint8(v_lchild_1180_, sizeof(void*)*4);
if (v_color_1190_ == 0)
{
lean_object* v_lchild_1191_; lean_object* v_key_1192_; lean_object* v_val_1193_; lean_object* v_rchild_1194_; 
lean_dec_ref(v___x_1189_);
v_lchild_1191_ = lean_ctor_get(v_lchild_1180_, 0);
lean_inc(v_lchild_1191_);
v_key_1192_ = lean_ctor_get(v_lchild_1180_, 1);
lean_inc(v_key_1192_);
v_val_1193_ = lean_ctor_get(v_lchild_1180_, 2);
lean_inc(v_val_1193_);
v_rchild_1194_ = lean_ctor_get(v_lchild_1180_, 3);
lean_inc(v_rchild_1194_);
lean_dec_ref_known(v_lchild_1180_, 4);
v___y_1088_ = v_color_1143_;
v_a_1089_ = v_lchild_1191_;
v_kx_1090_ = v_key_1192_;
v_vx_1091_ = v_val_1193_;
v_b_1092_ = v_rchild_1194_;
v_ky_1093_ = v_key_1181_;
v_vy_1094_ = v_val_1182_;
v_c_1095_ = v_rchild_1183_;
v_kz_1096_ = v_k_1081_;
v_vz_1097_ = v_v_1082_;
v_d_1098_ = v_r_1083_;
goto v___jp_1087_;
}
else
{
if (lean_obj_tag(v_rchild_1183_) == 1)
{
uint8_t v_color_1195_; 
v_color_1195_ = lean_ctor_get_uint8(v_rchild_1183_, sizeof(void*)*4);
if (v_color_1195_ == 0)
{
lean_object* v_lchild_1196_; lean_object* v_key_1197_; lean_object* v_val_1198_; lean_object* v_rchild_1199_; 
lean_dec_ref(v___x_1189_);
v_lchild_1196_ = lean_ctor_get(v_rchild_1183_, 0);
lean_inc(v_lchild_1196_);
v_key_1197_ = lean_ctor_get(v_rchild_1183_, 1);
lean_inc(v_key_1197_);
v_val_1198_ = lean_ctor_get(v_rchild_1183_, 2);
lean_inc(v_val_1198_);
v_rchild_1199_ = lean_ctor_get(v_rchild_1183_, 3);
lean_inc(v_rchild_1199_);
lean_dec_ref_known(v_rchild_1183_, 4);
v___y_1088_ = v_color_1143_;
v_a_1089_ = v_lchild_1180_;
v_kx_1090_ = v_key_1181_;
v_vx_1091_ = v_val_1182_;
v_b_1092_ = v_lchild_1196_;
v_ky_1093_ = v_key_1197_;
v_vy_1094_ = v_val_1198_;
v_c_1095_ = v_rchild_1199_;
v_kz_1096_ = v_k_1081_;
v_vz_1097_ = v_v_1082_;
v_d_1098_ = v_r_1083_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref_known(v_lchild_1180_, 4);
lean_dec(v_val_1182_);
lean_dec(v_key_1181_);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_rchild_1183_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; lean_object* v_unused_1209_; lean_object* v_unused_1210_; 
v_unused_1207_ = lean_ctor_get(v_rchild_1183_, 3);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_rchild_1183_, 2);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_rchild_1183_, 1);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_rchild_1183_, 0);
lean_dec(v_unused_1210_);
v___x_1201_ = v_rchild_1183_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_dec(v_rchild_1183_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 3, v_r_1083_);
lean_ctor_set(v___x_1201_, 2, v_v_1082_);
lean_ctor_set(v___x_1201_, 1, v_k_1081_);
lean_ctor_set(v___x_1201_, 0, v___x_1189_);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_r_1083_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*4, v_color_1143_);
return v___x_1204_;
}
}
}
}
else
{
lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_rchild_1183_);
lean_dec(v_val_1182_);
lean_dec(v_key_1181_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_lchild_1180_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; lean_object* v_unused_1219_; lean_object* v_unused_1220_; lean_object* v_unused_1221_; 
v_unused_1218_ = lean_ctor_get(v_lchild_1180_, 3);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_lchild_1180_, 2);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_lchild_1180_, 1);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_lchild_1180_, 0);
lean_dec(v_unused_1221_);
v___x_1212_ = v_lchild_1180_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v_lchild_1180_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 3, v_r_1083_);
lean_ctor_set(v___x_1212_, 2, v_v_1082_);
lean_ctor_set(v___x_1212_, 1, v_k_1081_);
lean_ctor_set(v___x_1212_, 0, v___x_1189_);
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_r_1083_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*4, v_color_1143_);
return v___x_1215_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_1183_) == 1)
{
uint8_t v_color_1222_; 
v_color_1222_ = lean_ctor_get_uint8(v_rchild_1183_, sizeof(void*)*4);
if (v_color_1222_ == 0)
{
lean_object* v_lchild_1223_; lean_object* v_key_1224_; lean_object* v_val_1225_; lean_object* v_rchild_1226_; 
lean_dec_ref(v___x_1189_);
v_lchild_1223_ = lean_ctor_get(v_rchild_1183_, 0);
lean_inc(v_lchild_1223_);
v_key_1224_ = lean_ctor_get(v_rchild_1183_, 1);
lean_inc(v_key_1224_);
v_val_1225_ = lean_ctor_get(v_rchild_1183_, 2);
lean_inc(v_val_1225_);
v_rchild_1226_ = lean_ctor_get(v_rchild_1183_, 3);
lean_inc(v_rchild_1226_);
lean_dec_ref_known(v_rchild_1183_, 4);
v___y_1088_ = v_color_1143_;
v_a_1089_ = v_lchild_1180_;
v_kx_1090_ = v_key_1181_;
v_vx_1091_ = v_val_1182_;
v_b_1092_ = v_lchild_1223_;
v_ky_1093_ = v_key_1224_;
v_vy_1094_ = v_val_1225_;
v_c_1095_ = v_rchild_1226_;
v_kz_1096_ = v_k_1081_;
v_vz_1097_ = v_v_1082_;
v_d_1098_ = v_r_1083_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_val_1182_);
lean_dec(v_key_1181_);
lean_dec(v_lchild_1180_);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_rchild_1183_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; lean_object* v_unused_1235_; lean_object* v_unused_1236_; lean_object* v_unused_1237_; 
v_unused_1234_ = lean_ctor_get(v_rchild_1183_, 3);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_rchild_1183_, 2);
lean_dec(v_unused_1235_);
v_unused_1236_ = lean_ctor_get(v_rchild_1183_, 1);
lean_dec(v_unused_1236_);
v_unused_1237_ = lean_ctor_get(v_rchild_1183_, 0);
lean_dec(v_unused_1237_);
v___x_1228_ = v_rchild_1183_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v_rchild_1183_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 3, v_r_1083_);
lean_ctor_set(v___x_1228_, 2, v_v_1082_);
lean_ctor_set(v___x_1228_, 1, v_k_1081_);
lean_ctor_set(v___x_1228_, 0, v___x_1189_);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_k_1081_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_v_1082_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_r_1083_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_ctor_set_uint8(v___x_1231_, sizeof(void*)*4, v_color_1143_);
return v___x_1231_;
}
}
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_rchild_1183_);
lean_dec(v_val_1182_);
lean_dec(v_key_1181_);
lean_dec(v_lchild_1180_);
v___x_1238_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1238_, 0, v___x_1189_);
lean_ctor_set(v___x_1238_, 1, v_k_1081_);
lean_ctor_set(v___x_1238_, 2, v_v_1082_);
lean_ctor_set(v___x_1238_, 3, v_r_1083_);
lean_ctor_set_uint8(v___x_1238_, sizeof(void*)*4, v_color_1143_);
return v___x_1238_;
}
}
}
}
}
}
else
{
goto v___jp_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_balRight(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_l_1257_, lean_object* v_k_1258_, lean_object* v_v_1259_, lean_object* v_r_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_RBNode_balRight___redArg(v_l_1257_, v_k_1258_, v_v_1259_, v_r_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg(lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
return v___x_1263_;
}
else
{
lean_object* v_lchild_1264_; lean_object* v_rchild_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_lchild_1264_ = lean_ctor_get(v_x_1262_, 0);
v_rchild_1265_ = lean_ctor_get(v_x_1262_, 3);
v___x_1266_ = l_Lean_RBNode_size___redArg(v_lchild_1264_);
v___x_1267_ = l_Lean_RBNode_size___redArg(v_rchild_1265_);
v___x_1268_ = lean_nat_add(v___x_1266_, v___x_1267_);
lean_dec(v___x_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v___x_1268_, v___x_1269_);
lean_dec(v___x_1268_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___redArg___boxed(lean_object* v_x_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_RBNode_size___redArg(v_x_1271_);
lean_dec(v_x_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size(lean_object* v_00_u03b1_1273_, lean_object* v_00_u03b2_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_RBNode_size___redArg(v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_size___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_RBNode_size(v_00_u03b1_1277_, v_00_u03b2_1278_, v_x_1279_);
lean_dec(v_x_1279_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
return v_x_1282_;
}
else
{
if (lean_obj_tag(v_x_1282_) == 0)
{
return v_x_1281_;
}
else
{
uint8_t v_color_1283_; lean_object* v_lchild_1284_; lean_object* v_key_1285_; lean_object* v_val_1286_; lean_object* v_rchild_1287_; uint8_t v_color_1288_; lean_object* v_lchild_1289_; lean_object* v_key_1290_; lean_object* v_val_1291_; lean_object* v_rchild_1292_; lean_object* v_bc_1294_; lean_object* v_bc_1298_; 
v_color_1283_ = lean_ctor_get_uint8(v_x_1281_, sizeof(void*)*4);
v_lchild_1284_ = lean_ctor_get(v_x_1281_, 0);
v_key_1285_ = lean_ctor_get(v_x_1281_, 1);
v_val_1286_ = lean_ctor_get(v_x_1281_, 2);
v_rchild_1287_ = lean_ctor_get(v_x_1281_, 3);
v_color_1288_ = lean_ctor_get_uint8(v_x_1282_, sizeof(void*)*4);
v_lchild_1289_ = lean_ctor_get(v_x_1282_, 0);
v_key_1290_ = lean_ctor_get(v_x_1282_, 1);
v_val_1291_ = lean_ctor_get(v_x_1282_, 2);
v_rchild_1292_ = lean_ctor_get(v_x_1282_, 3);
if (v_color_1288_ == 0)
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1335_; 
lean_inc(v_rchild_1292_);
lean_inc(v_val_1291_);
lean_inc(v_key_1290_);
lean_inc(v_lchild_1289_);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1282_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1336_ = lean_ctor_get(v_x_1282_, 3);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_x_1282_, 2);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_x_1282_, 1);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_x_1282_, 0);
lean_dec(v_unused_1339_);
v___x_1302_ = v_x_1282_;
v_isShared_1303_ = v_isSharedCheck_1335_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v_x_1282_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1335_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
if (v_color_1283_ == 0)
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1326_; 
lean_inc(v_rchild_1287_);
lean_inc(v_val_1286_);
lean_inc(v_key_1285_);
lean_inc(v_lchild_1284_);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; lean_object* v_unused_1328_; lean_object* v_unused_1329_; lean_object* v_unused_1330_; 
v_unused_1327_ = lean_ctor_get(v_x_1281_, 3);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_x_1281_, 2);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_x_1281_, 1);
lean_dec(v_unused_1329_);
v_unused_1330_ = lean_ctor_get(v_x_1281_, 0);
lean_dec(v_unused_1330_);
v___x_1305_ = v_x_1281_;
v_isShared_1306_ = v_isSharedCheck_1326_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_x_1281_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1326_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1287_, v_lchild_1289_);
if (lean_obj_tag(v___x_1307_) == 1)
{
uint8_t v_color_1308_; 
v_color_1308_ = lean_ctor_get_uint8(v___x_1307_, sizeof(void*)*4);
if (v_color_1308_ == 0)
{
lean_object* v_lchild_1309_; lean_object* v_key_1310_; lean_object* v_val_1311_; lean_object* v_rchild_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1325_; 
v_lchild_1309_ = lean_ctor_get(v___x_1307_, 0);
v_key_1310_ = lean_ctor_get(v___x_1307_, 1);
v_val_1311_ = lean_ctor_get(v___x_1307_, 2);
v_rchild_1312_ = lean_ctor_get(v___x_1307_, 3);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1314_ = v___x_1307_;
v_isShared_1315_ = v_isSharedCheck_1325_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_rchild_1312_);
lean_inc(v_val_1311_);
lean_inc(v_key_1310_);
lean_inc(v_lchild_1309_);
lean_dec(v___x_1307_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1325_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 3, v_lchild_1309_);
lean_ctor_set(v___x_1314_, 2, v_val_1286_);
lean_ctor_set(v___x_1314_, 1, v_key_1285_);
lean_ctor_set(v___x_1314_, 0, v_lchild_1284_);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_lchild_1284_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_key_1285_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_val_1286_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_lchild_1309_);
lean_ctor_set_uint8(v_reuseFailAlloc_1324_, sizeof(void*)*4, v_color_1308_);
v___x_1317_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v_rchild_1312_);
v___x_1319_ = v___x_1302_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_rchild_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_key_1290_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_val_1291_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_rchild_1292_);
v___x_1319_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*4, v_color_1308_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 3, v___x_1319_);
lean_ctor_set(v___x_1305_, 2, v_val_1311_);
lean_ctor_set(v___x_1305_, 1, v_key_1310_);
lean_ctor_set(v___x_1305_, 0, v___x_1317_);
v___x_1321_ = v___x_1305_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_key_1310_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_val_1311_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*4, v_color_1308_);
return v___x_1321_;
}
}
}
}
}
else
{
lean_del_object(v___x_1305_);
lean_del_object(v___x_1302_);
v_bc_1298_ = v___x_1307_;
goto v___jp_1297_;
}
}
else
{
lean_del_object(v___x_1305_);
lean_del_object(v___x_1302_);
v_bc_1298_ = v___x_1307_;
goto v___jp_1297_;
}
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = l_Lean_RBNode_appendTrees___redArg(v_x_1281_, v_lchild_1289_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1331_);
v___x_1333_ = v___x_1302_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_key_1290_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_val_1291_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_rchild_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*4, v_color_1288_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1374_; 
lean_inc(v_rchild_1287_);
lean_inc(v_val_1286_);
lean_inc(v_key_1285_);
lean_inc(v_lchild_1284_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1375_ = lean_ctor_get(v_x_1281_, 3);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_x_1281_, 2);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_x_1281_, 1);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_x_1281_, 0);
lean_dec(v_unused_1378_);
v___x_1341_ = v_x_1281_;
v_isShared_1342_ = v_isSharedCheck_1374_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v_x_1281_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1374_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
if (v_color_1283_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1287_, v_x_1282_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 3, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_lchild_1284_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_key_1285_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_val_1286_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v___x_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*4, v_color_1283_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1369_; 
lean_inc(v_rchild_1292_);
lean_inc(v_val_1291_);
lean_inc(v_key_1290_);
lean_inc(v_lchild_1289_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_x_1282_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; 
v_unused_1370_ = lean_ctor_get(v_x_1282_, 3);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_x_1282_, 2);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_x_1282_, 1);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_x_1282_, 0);
lean_dec(v_unused_1373_);
v___x_1348_ = v_x_1282_;
v_isShared_1349_ = v_isSharedCheck_1369_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v_x_1282_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1369_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1287_, v_lchild_1289_);
if (lean_obj_tag(v___x_1350_) == 1)
{
uint8_t v_color_1351_; 
v_color_1351_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*4);
if (v_color_1351_ == 0)
{
lean_object* v_lchild_1352_; lean_object* v_key_1353_; lean_object* v_val_1354_; lean_object* v_rchild_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1368_; 
v_lchild_1352_ = lean_ctor_get(v___x_1350_, 0);
v_key_1353_ = lean_ctor_get(v___x_1350_, 1);
v_val_1354_ = lean_ctor_get(v___x_1350_, 2);
v_rchild_1355_ = lean_ctor_get(v___x_1350_, 3);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1357_ = v___x_1350_;
v_isShared_1358_ = v_isSharedCheck_1368_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_rchild_1355_);
lean_inc(v_val_1354_);
lean_inc(v_key_1353_);
lean_inc(v_lchild_1352_);
lean_dec(v___x_1350_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1368_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 3, v_lchild_1352_);
lean_ctor_set(v___x_1357_, 2, v_val_1286_);
lean_ctor_set(v___x_1357_, 1, v_key_1285_);
lean_ctor_set(v___x_1357_, 0, v_lchild_1284_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_lchild_1284_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_key_1285_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_val_1286_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_lchild_1352_);
v___x_1360_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*4, v_color_1283_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v_rchild_1355_);
v___x_1362_ = v___x_1348_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_rchild_1355_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_key_1290_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_val_1291_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_rchild_1292_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*4, v_color_1283_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 3, v___x_1362_);
lean_ctor_set(v___x_1341_, 2, v_val_1354_);
lean_ctor_set(v___x_1341_, 1, v_key_1353_);
lean_ctor_set(v___x_1341_, 0, v___x_1360_);
v___x_1364_ = v___x_1341_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_key_1353_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_val_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*4, v_color_1351_);
return v___x_1364_;
}
}
}
}
}
else
{
lean_del_object(v___x_1348_);
lean_del_object(v___x_1341_);
v_bc_1294_ = v___x_1350_;
goto v___jp_1293_;
}
}
else
{
lean_del_object(v___x_1348_);
lean_del_object(v___x_1341_);
v_bc_1294_ = v___x_1350_;
goto v___jp_1293_;
}
}
}
}
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1295_, 0, v_bc_1294_);
lean_ctor_set(v___x_1295_, 1, v_key_1290_);
lean_ctor_set(v___x_1295_, 2, v_val_1291_);
lean_ctor_set(v___x_1295_, 3, v_rchild_1292_);
lean_ctor_set_uint8(v___x_1295_, sizeof(void*)*4, v_color_1283_);
v___x_1296_ = l_Lean_RBNode_balLeft___redArg(v_lchild_1284_, v_key_1285_, v_val_1286_, v___x_1295_);
return v___x_1296_;
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1299_, 0, v_bc_1298_);
lean_ctor_set(v___x_1299_, 1, v_key_1290_);
lean_ctor_set(v___x_1299_, 2, v_val_1291_);
lean_ctor_set(v___x_1299_, 3, v_rchild_1292_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*4, v_color_1283_);
v___x_1300_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1300_, 0, v_lchild_1284_);
lean_ctor_set(v___x_1300_, 1, v_key_1285_);
lean_ctor_set(v___x_1300_, 2, v_val_1286_);
lean_ctor_set(v___x_1300_, 3, v___x_1299_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*4, v_color_1283_);
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_RBNode_appendTrees___redArg(v_x_1381_, v_x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v_h__1_1386_, lean_object* v_h__2_1387_, lean_object* v_h__3_1388_, lean_object* v_h__4_1389_, lean_object* v_h__5_1390_, lean_object* v_h__6_1391_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v___x_1392_; 
lean_dec(v_h__6_1391_);
lean_dec(v_h__5_1390_);
lean_dec(v_h__4_1389_);
lean_dec(v_h__3_1388_);
lean_dec(v_h__2_1387_);
v___x_1392_ = lean_apply_1(v_h__1_1386_, v_x_1385_);
return v___x_1392_;
}
else
{
lean_dec(v_h__1_1386_);
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v___x_1393_; 
lean_dec(v_h__6_1391_);
lean_dec(v_h__5_1390_);
lean_dec(v_h__4_1389_);
lean_dec(v_h__3_1388_);
v___x_1393_ = lean_apply_2(v_h__2_1387_, v_x_1384_, lean_box(0));
return v___x_1393_;
}
else
{
uint8_t v_color_1394_; 
lean_dec(v_h__2_1387_);
v_color_1394_ = lean_ctor_get_uint8(v_x_1385_, sizeof(void*)*4);
if (v_color_1394_ == 0)
{
uint8_t v_color_1395_; 
lean_dec(v_h__6_1391_);
lean_dec(v_h__4_1389_);
v_color_1395_ = lean_ctor_get_uint8(v_x_1384_, sizeof(void*)*4);
if (v_color_1395_ == 0)
{
lean_object* v_lchild_1396_; lean_object* v_key_1397_; lean_object* v_val_1398_; lean_object* v_rchild_1399_; lean_object* v_lchild_1400_; lean_object* v_key_1401_; lean_object* v_val_1402_; lean_object* v_rchild_1403_; lean_object* v___x_1404_; 
lean_dec(v_h__5_1390_);
v_lchild_1396_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_lchild_1396_);
v_key_1397_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_key_1397_);
v_val_1398_ = lean_ctor_get(v_x_1384_, 2);
lean_inc(v_val_1398_);
v_rchild_1399_ = lean_ctor_get(v_x_1384_, 3);
lean_inc(v_rchild_1399_);
lean_dec_ref_known(v_x_1384_, 4);
v_lchild_1400_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_lchild_1400_);
v_key_1401_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_key_1401_);
v_val_1402_ = lean_ctor_get(v_x_1385_, 2);
lean_inc(v_val_1402_);
v_rchild_1403_ = lean_ctor_get(v_x_1385_, 3);
lean_inc(v_rchild_1403_);
lean_dec_ref_known(v_x_1385_, 4);
v___x_1404_ = lean_apply_8(v_h__3_1388_, v_lchild_1396_, v_key_1397_, v_val_1398_, v_rchild_1399_, v_lchild_1400_, v_key_1401_, v_val_1402_, v_rchild_1403_);
return v___x_1404_;
}
else
{
lean_object* v_lchild_1405_; lean_object* v_key_1406_; lean_object* v_val_1407_; lean_object* v_rchild_1408_; lean_object* v___x_1409_; 
lean_dec(v_h__3_1388_);
v_lchild_1405_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_lchild_1405_);
v_key_1406_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_key_1406_);
v_val_1407_ = lean_ctor_get(v_x_1385_, 2);
lean_inc(v_val_1407_);
v_rchild_1408_ = lean_ctor_get(v_x_1385_, 3);
lean_inc(v_rchild_1408_);
lean_dec_ref_known(v_x_1385_, 4);
v___x_1409_ = lean_apply_7(v_h__5_1390_, v_x_1384_, v_lchild_1405_, v_key_1406_, v_val_1407_, v_rchild_1408_, lean_box(0), lean_box(0));
return v___x_1409_;
}
}
else
{
uint8_t v_color_1410_; 
lean_dec(v_h__5_1390_);
lean_dec(v_h__3_1388_);
v_color_1410_ = lean_ctor_get_uint8(v_x_1384_, sizeof(void*)*4);
if (v_color_1410_ == 0)
{
lean_object* v_lchild_1411_; lean_object* v_key_1412_; lean_object* v_val_1413_; lean_object* v_rchild_1414_; lean_object* v___x_1415_; 
lean_dec(v_h__4_1389_);
v_lchild_1411_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_lchild_1411_);
v_key_1412_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_key_1412_);
v_val_1413_ = lean_ctor_get(v_x_1384_, 2);
lean_inc(v_val_1413_);
v_rchild_1414_ = lean_ctor_get(v_x_1384_, 3);
lean_inc(v_rchild_1414_);
lean_dec_ref_known(v_x_1384_, 4);
v___x_1415_ = lean_apply_7(v_h__6_1391_, v_lchild_1411_, v_key_1412_, v_val_1413_, v_rchild_1414_, v_x_1385_, lean_box(0), lean_box(0));
return v___x_1415_;
}
else
{
lean_object* v_lchild_1416_; lean_object* v_key_1417_; lean_object* v_val_1418_; lean_object* v_rchild_1419_; lean_object* v_lchild_1420_; lean_object* v_key_1421_; lean_object* v_val_1422_; lean_object* v_rchild_1423_; lean_object* v___x_1424_; 
lean_dec(v_h__6_1391_);
v_lchild_1416_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_lchild_1416_);
v_key_1417_ = lean_ctor_get(v_x_1384_, 1);
lean_inc(v_key_1417_);
v_val_1418_ = lean_ctor_get(v_x_1384_, 2);
lean_inc(v_val_1418_);
v_rchild_1419_ = lean_ctor_get(v_x_1384_, 3);
lean_inc(v_rchild_1419_);
lean_dec_ref_known(v_x_1384_, 4);
v_lchild_1420_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_lchild_1420_);
v_key_1421_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_key_1421_);
v_val_1422_ = lean_ctor_get(v_x_1385_, 2);
lean_inc(v_val_1422_);
v_rchild_1423_ = lean_ctor_get(v_x_1385_, 3);
lean_inc(v_rchild_1423_);
lean_dec_ref_known(v_x_1385_, 4);
v___x_1424_ = lean_apply_8(v_h__4_1389_, v_lchild_1416_, v_key_1417_, v_val_1418_, v_rchild_1419_, v_lchild_1420_, v_key_1421_, v_val_1422_, v_rchild_1423_);
return v___x_1424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_motive_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_h__1_1430_, lean_object* v_h__2_1431_, lean_object* v_h__3_1432_, lean_object* v_h__4_1433_, lean_object* v_h__5_1434_, lean_object* v_h__6_1435_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_h__6_1435_);
lean_dec(v_h__5_1434_);
lean_dec(v_h__4_1433_);
lean_dec(v_h__3_1432_);
lean_dec(v_h__2_1431_);
v___x_1436_ = lean_apply_1(v_h__1_1430_, v_x_1429_);
return v___x_1436_;
}
else
{
lean_dec(v_h__1_1430_);
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v___x_1437_; 
lean_dec(v_h__6_1435_);
lean_dec(v_h__5_1434_);
lean_dec(v_h__4_1433_);
lean_dec(v_h__3_1432_);
v___x_1437_ = lean_apply_2(v_h__2_1431_, v_x_1428_, lean_box(0));
return v___x_1437_;
}
else
{
uint8_t v_color_1438_; 
lean_dec(v_h__2_1431_);
v_color_1438_ = lean_ctor_get_uint8(v_x_1429_, sizeof(void*)*4);
if (v_color_1438_ == 0)
{
uint8_t v_color_1439_; 
lean_dec(v_h__6_1435_);
lean_dec(v_h__4_1433_);
v_color_1439_ = lean_ctor_get_uint8(v_x_1428_, sizeof(void*)*4);
if (v_color_1439_ == 0)
{
lean_object* v_lchild_1440_; lean_object* v_key_1441_; lean_object* v_val_1442_; lean_object* v_rchild_1443_; lean_object* v_lchild_1444_; lean_object* v_key_1445_; lean_object* v_val_1446_; lean_object* v_rchild_1447_; lean_object* v___x_1448_; 
lean_dec(v_h__5_1434_);
v_lchild_1440_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_lchild_1440_);
v_key_1441_ = lean_ctor_get(v_x_1428_, 1);
lean_inc(v_key_1441_);
v_val_1442_ = lean_ctor_get(v_x_1428_, 2);
lean_inc(v_val_1442_);
v_rchild_1443_ = lean_ctor_get(v_x_1428_, 3);
lean_inc(v_rchild_1443_);
lean_dec_ref_known(v_x_1428_, 4);
v_lchild_1444_ = lean_ctor_get(v_x_1429_, 0);
lean_inc(v_lchild_1444_);
v_key_1445_ = lean_ctor_get(v_x_1429_, 1);
lean_inc(v_key_1445_);
v_val_1446_ = lean_ctor_get(v_x_1429_, 2);
lean_inc(v_val_1446_);
v_rchild_1447_ = lean_ctor_get(v_x_1429_, 3);
lean_inc(v_rchild_1447_);
lean_dec_ref_known(v_x_1429_, 4);
v___x_1448_ = lean_apply_8(v_h__3_1432_, v_lchild_1440_, v_key_1441_, v_val_1442_, v_rchild_1443_, v_lchild_1444_, v_key_1445_, v_val_1446_, v_rchild_1447_);
return v___x_1448_;
}
else
{
lean_object* v_lchild_1449_; lean_object* v_key_1450_; lean_object* v_val_1451_; lean_object* v_rchild_1452_; lean_object* v___x_1453_; 
lean_dec(v_h__3_1432_);
v_lchild_1449_ = lean_ctor_get(v_x_1429_, 0);
lean_inc(v_lchild_1449_);
v_key_1450_ = lean_ctor_get(v_x_1429_, 1);
lean_inc(v_key_1450_);
v_val_1451_ = lean_ctor_get(v_x_1429_, 2);
lean_inc(v_val_1451_);
v_rchild_1452_ = lean_ctor_get(v_x_1429_, 3);
lean_inc(v_rchild_1452_);
lean_dec_ref_known(v_x_1429_, 4);
v___x_1453_ = lean_apply_7(v_h__5_1434_, v_x_1428_, v_lchild_1449_, v_key_1450_, v_val_1451_, v_rchild_1452_, lean_box(0), lean_box(0));
return v___x_1453_;
}
}
else
{
uint8_t v_color_1454_; 
lean_dec(v_h__5_1434_);
lean_dec(v_h__3_1432_);
v_color_1454_ = lean_ctor_get_uint8(v_x_1428_, sizeof(void*)*4);
if (v_color_1454_ == 0)
{
lean_object* v_lchild_1455_; lean_object* v_key_1456_; lean_object* v_val_1457_; lean_object* v_rchild_1458_; lean_object* v___x_1459_; 
lean_dec(v_h__4_1433_);
v_lchild_1455_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_lchild_1455_);
v_key_1456_ = lean_ctor_get(v_x_1428_, 1);
lean_inc(v_key_1456_);
v_val_1457_ = lean_ctor_get(v_x_1428_, 2);
lean_inc(v_val_1457_);
v_rchild_1458_ = lean_ctor_get(v_x_1428_, 3);
lean_inc(v_rchild_1458_);
lean_dec_ref_known(v_x_1428_, 4);
v___x_1459_ = lean_apply_7(v_h__6_1435_, v_lchild_1455_, v_key_1456_, v_val_1457_, v_rchild_1458_, v_x_1429_, lean_box(0), lean_box(0));
return v___x_1459_;
}
else
{
lean_object* v_lchild_1460_; lean_object* v_key_1461_; lean_object* v_val_1462_; lean_object* v_rchild_1463_; lean_object* v_lchild_1464_; lean_object* v_key_1465_; lean_object* v_val_1466_; lean_object* v_rchild_1467_; lean_object* v___x_1468_; 
lean_dec(v_h__6_1435_);
v_lchild_1460_ = lean_ctor_get(v_x_1428_, 0);
lean_inc(v_lchild_1460_);
v_key_1461_ = lean_ctor_get(v_x_1428_, 1);
lean_inc(v_key_1461_);
v_val_1462_ = lean_ctor_get(v_x_1428_, 2);
lean_inc(v_val_1462_);
v_rchild_1463_ = lean_ctor_get(v_x_1428_, 3);
lean_inc(v_rchild_1463_);
lean_dec_ref_known(v_x_1428_, 4);
v_lchild_1464_ = lean_ctor_get(v_x_1429_, 0);
lean_inc(v_lchild_1464_);
v_key_1465_ = lean_ctor_get(v_x_1429_, 1);
lean_inc(v_key_1465_);
v_val_1466_ = lean_ctor_get(v_x_1429_, 2);
lean_inc(v_val_1466_);
v_rchild_1467_ = lean_ctor_get(v_x_1429_, 3);
lean_inc(v_rchild_1467_);
lean_dec_ref_known(v_x_1429_, 4);
v___x_1468_ = lean_apply_8(v_h__4_1433_, v_lchild_1460_, v_key_1461_, v_val_1462_, v_rchild_1463_, v_lchild_1464_, v_key_1465_, v_val_1466_, v_rchild_1467_);
return v___x_1468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* v_x_1469_, lean_object* v_h__1_1470_, lean_object* v_h__2_1471_){
_start:
{
if (lean_obj_tag(v_x_1469_) == 1)
{
uint8_t v_color_1472_; 
v_color_1472_ = lean_ctor_get_uint8(v_x_1469_, sizeof(void*)*4);
if (v_color_1472_ == 0)
{
lean_object* v_lchild_1473_; lean_object* v_key_1474_; lean_object* v_val_1475_; lean_object* v_rchild_1476_; lean_object* v___x_1477_; 
lean_dec(v_h__2_1471_);
v_lchild_1473_ = lean_ctor_get(v_x_1469_, 0);
lean_inc(v_lchild_1473_);
v_key_1474_ = lean_ctor_get(v_x_1469_, 1);
lean_inc(v_key_1474_);
v_val_1475_ = lean_ctor_get(v_x_1469_, 2);
lean_inc(v_val_1475_);
v_rchild_1476_ = lean_ctor_get(v_x_1469_, 3);
lean_inc(v_rchild_1476_);
lean_dec_ref_known(v_x_1469_, 4);
v___x_1477_ = lean_apply_4(v_h__1_1470_, v_lchild_1473_, v_key_1474_, v_val_1475_, v_rchild_1476_);
return v___x_1477_;
}
else
{
lean_object* v___x_1478_; 
lean_dec(v_h__1_1470_);
v___x_1478_ = lean_apply_2(v_h__2_1471_, v_x_1469_, lean_box(0));
return v___x_1478_;
}
}
else
{
lean_object* v___x_1479_; 
lean_dec(v_h__1_1470_);
v___x_1479_ = lean_apply_2(v_h__2_1471_, v_x_1469_, lean_box(0));
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* v_00_u03b1_1480_, lean_object* v_00_u03b2_1481_, lean_object* v_motive_1482_, lean_object* v_x_1483_, lean_object* v_h__1_1484_, lean_object* v_h__2_1485_){
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
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* v_cmp_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 0)
{
lean_dec(v_x_1495_);
lean_dec_ref(v_cmp_1494_);
return v_x_1496_;
}
else
{
lean_object* v_lchild_1497_; lean_object* v_key_1498_; lean_object* v_val_1499_; lean_object* v_rchild_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1523_; 
v_lchild_1497_ = lean_ctor_get(v_x_1496_, 0);
v_key_1498_ = lean_ctor_get(v_x_1496_, 1);
v_val_1499_ = lean_ctor_get(v_x_1496_, 2);
v_rchild_1500_ = lean_ctor_get(v_x_1496_, 3);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1496_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1502_ = v_x_1496_;
v_isShared_1503_ = v_isSharedCheck_1523_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_rchild_1500_);
lean_inc(v_val_1499_);
lean_inc(v_key_1498_);
lean_inc(v_lchild_1497_);
lean_dec(v_x_1496_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1523_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
lean_inc_ref(v_cmp_1494_);
lean_inc(v_key_1498_);
lean_inc(v_x_1495_);
v___x_1504_ = lean_apply_2(v_cmp_1494_, v_x_1495_, v_key_1498_);
v___x_1505_ = lean_unbox(v___x_1504_);
switch(v___x_1505_)
{
case 0:
{
uint8_t v___x_1506_; 
v___x_1506_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1497_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = 0;
v___x_1508_ = l_Lean_RBNode_del___redArg(v_cmp_1494_, v_x_1495_, v_lchild_1497_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1508_);
v___x_1510_ = v___x_1502_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_key_1498_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_val_1499_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_rchild_1500_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_ctor_set_uint8(v___x_1510_, sizeof(void*)*4, v___x_1507_);
return v___x_1510_;
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_del_object(v___x_1502_);
v___x_1512_ = l_Lean_RBNode_del___redArg(v_cmp_1494_, v_x_1495_, v_lchild_1497_);
v___x_1513_ = l_Lean_RBNode_balLeft___redArg(v___x_1512_, v_key_1498_, v_val_1499_, v_rchild_1500_);
return v___x_1513_;
}
}
case 1:
{
lean_object* v___x_1514_; 
lean_del_object(v___x_1502_);
lean_dec(v_val_1499_);
lean_dec(v_key_1498_);
lean_dec(v_x_1495_);
lean_dec_ref(v_cmp_1494_);
v___x_1514_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_1497_, v_rchild_1500_);
return v___x_1514_;
}
default: 
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1500_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1516_ = 0;
v___x_1517_ = l_Lean_RBNode_del___redArg(v_cmp_1494_, v_x_1495_, v_rchild_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 3, v___x_1517_);
v___x_1519_ = v___x_1502_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_lchild_1497_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_key_1498_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_val_1499_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_ctor_set_uint8(v___x_1519_, sizeof(void*)*4, v___x_1516_);
return v___x_1519_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_del_object(v___x_1502_);
v___x_1521_ = l_Lean_RBNode_del___redArg(v_cmp_1494_, v_x_1495_, v_rchild_1500_);
v___x_1522_ = l_Lean_RBNode_balRight___redArg(v_lchild_1497_, v_key_1498_, v_val_1499_, v___x_1521_);
return v___x_1522_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_cmp_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_RBNode_del___redArg(v_cmp_1526_, v_x_1527_, v_x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* v_cmp_1530_, lean_object* v_x_1531_, lean_object* v_t_1532_){
_start:
{
lean_object* v_t_1533_; lean_object* v___x_1534_; 
v_t_1533_ = l_Lean_RBNode_del___redArg(v_cmp_1530_, v_x_1531_, v_t_1532_);
v___x_1534_ = l_Lean_RBNode_setBlack___redArg(v_t_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_cmp_1537_, lean_object* v_x_1538_, lean_object* v_t_1539_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l_Lean_RBNode_erase___redArg(v_cmp_1537_, v_x_1538_, v_t_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* v_cmp_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v___x_1544_; 
lean_dec(v_x_1543_);
lean_dec_ref(v_cmp_1541_);
v___x_1544_ = lean_box(0);
return v___x_1544_;
}
else
{
lean_object* v_lchild_1545_; lean_object* v_key_1546_; lean_object* v_val_1547_; lean_object* v_rchild_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_lchild_1545_ = lean_ctor_get(v_x_1542_, 0);
lean_inc(v_lchild_1545_);
v_key_1546_ = lean_ctor_get(v_x_1542_, 1);
lean_inc_n(v_key_1546_, 2);
v_val_1547_ = lean_ctor_get(v_x_1542_, 2);
lean_inc(v_val_1547_);
v_rchild_1548_ = lean_ctor_get(v_x_1542_, 3);
lean_inc(v_rchild_1548_);
lean_dec_ref_known(v_x_1542_, 4);
lean_inc_ref(v_cmp_1541_);
lean_inc(v_x_1543_);
v___x_1549_ = lean_apply_2(v_cmp_1541_, v_x_1543_, v_key_1546_);
v___x_1550_ = lean_unbox(v___x_1549_);
switch(v___x_1550_)
{
case 0:
{
lean_dec(v_rchild_1548_);
lean_dec(v_val_1547_);
lean_dec(v_key_1546_);
v_x_1542_ = v_lchild_1545_;
goto _start;
}
case 1:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_rchild_1548_);
lean_dec(v_lchild_1545_);
lean_dec(v_x_1543_);
lean_dec_ref(v_cmp_1541_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_key_1546_);
lean_ctor_set(v___x_1552_, 1, v_val_1547_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
default: 
{
lean_dec(v_val_1547_);
lean_dec(v_key_1546_);
lean_dec(v_lchild_1545_);
v_x_1542_ = v_rchild_1548_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* v_00_u03b1_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_cmp_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_RBNode_findCore___redArg(v_cmp_1557_, v_x_1558_, v_x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* v_cmp_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1562_) == 0)
{
lean_object* v___x_1564_; 
lean_dec(v_x_1563_);
lean_dec_ref(v_cmp_1561_);
v___x_1564_ = lean_box(0);
return v___x_1564_;
}
else
{
lean_object* v_lchild_1565_; lean_object* v_key_1566_; lean_object* v_val_1567_; lean_object* v_rchild_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_lchild_1565_ = lean_ctor_get(v_x_1562_, 0);
lean_inc(v_lchild_1565_);
v_key_1566_ = lean_ctor_get(v_x_1562_, 1);
lean_inc(v_key_1566_);
v_val_1567_ = lean_ctor_get(v_x_1562_, 2);
lean_inc(v_val_1567_);
v_rchild_1568_ = lean_ctor_get(v_x_1562_, 3);
lean_inc(v_rchild_1568_);
lean_dec_ref_known(v_x_1562_, 4);
lean_inc_ref(v_cmp_1561_);
lean_inc(v_x_1563_);
v___x_1569_ = lean_apply_2(v_cmp_1561_, v_x_1563_, v_key_1566_);
v___x_1570_ = lean_unbox(v___x_1569_);
switch(v___x_1570_)
{
case 0:
{
lean_dec(v_rchild_1568_);
lean_dec(v_val_1567_);
v_x_1562_ = v_lchild_1565_;
goto _start;
}
case 1:
{
lean_object* v___x_1572_; 
lean_dec(v_rchild_1568_);
lean_dec(v_lchild_1565_);
lean_dec(v_x_1563_);
lean_dec_ref(v_cmp_1561_);
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_val_1567_);
return v___x_1572_;
}
default: 
{
lean_dec(v_val_1567_);
lean_dec(v_lchild_1565_);
v_x_1562_ = v_rchild_1568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* v_00_u03b1_1574_, lean_object* v_cmp_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_RBNode_find___redArg(v_cmp_1575_, v_x_1577_, v_x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* v_cmp_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 0)
{
lean_dec(v_x_1582_);
lean_dec_ref(v_cmp_1580_);
return v_x_1583_;
}
else
{
lean_object* v_lchild_1584_; lean_object* v_key_1585_; lean_object* v_val_1586_; lean_object* v_rchild_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_lchild_1584_ = lean_ctor_get(v_x_1581_, 0);
lean_inc(v_lchild_1584_);
v_key_1585_ = lean_ctor_get(v_x_1581_, 1);
lean_inc_n(v_key_1585_, 2);
v_val_1586_ = lean_ctor_get(v_x_1581_, 2);
lean_inc(v_val_1586_);
v_rchild_1587_ = lean_ctor_get(v_x_1581_, 3);
lean_inc(v_rchild_1587_);
lean_dec_ref_known(v_x_1581_, 4);
lean_inc_ref(v_cmp_1580_);
lean_inc(v_x_1582_);
v___x_1588_ = lean_apply_2(v_cmp_1580_, v_x_1582_, v_key_1585_);
v___x_1589_ = lean_unbox(v___x_1588_);
switch(v___x_1589_)
{
case 0:
{
lean_dec(v_rchild_1587_);
lean_dec(v_val_1586_);
lean_dec(v_key_1585_);
v_x_1581_ = v_lchild_1584_;
goto _start;
}
case 1:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_rchild_1587_);
lean_dec(v_lchild_1584_);
lean_dec(v_x_1583_);
lean_dec(v_x_1582_);
lean_dec_ref(v_cmp_1580_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_key_1585_);
lean_ctor_set(v___x_1591_, 1, v_val_1586_);
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
default: 
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_lchild_1584_);
lean_dec(v_x_1583_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v_key_1585_);
lean_ctor_set(v___x_1593_, 1, v_val_1586_);
v___x_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
v_x_1581_ = v_rchild_1587_;
v_x_1583_ = v___x_1594_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* v_00_u03b1_1596_, lean_object* v_00_u03b2_1597_, lean_object* v_cmp_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_1598_, v_x_1599_, v_x_1600_, v_x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t v_color_1603_, lean_object* v_key_1604_, lean_object* v_x1_1605_, lean_object* v_x2_1606_, lean_object* v_x3_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1608_, 0, v_x1_1605_);
lean_ctor_set(v___x_1608_, 1, v_key_1604_);
lean_ctor_set(v___x_1608_, 2, v_x2_1606_);
lean_ctor_set(v___x_1608_, 3, v_x3_1607_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*4, v_color_1603_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* v_color_1609_, lean_object* v_key_1610_, lean_object* v_x1_1611_, lean_object* v_x2_1612_, lean_object* v_x3_1613_){
_start:
{
uint8_t v_color_88__boxed_1614_; lean_object* v_res_1615_; 
v_color_88__boxed_1614_ = lean_unbox(v_color_1609_);
v_res_1615_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_88__boxed_1614_, v_key_1610_, v_x1_1611_, v_x2_1612_, v_x3_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* v_f_1616_, lean_object* v_key_1617_, lean_object* v_val_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_apply_2(v_f_1616_, v_key_1617_, v_val_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* v_inst_1621_, lean_object* v_f_1622_, lean_object* v_lchild_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_RBNode_mapM___redArg(v_inst_1621_, v_f_1622_, v_lchild_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* v_inst_1626_, lean_object* v_f_1627_, lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 0)
{
lean_object* v_toPure_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v_f_1627_);
v_toPure_1629_ = lean_ctor_get(v_inst_1626_, 1);
lean_inc(v_toPure_1629_);
lean_dec_ref(v_inst_1626_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_apply_2(v_toPure_1629_, lean_box(0), v___x_1630_);
return v___x_1631_;
}
else
{
lean_object* v_toPure_1632_; lean_object* v_toSeq_1633_; uint8_t v_color_1634_; lean_object* v_lchild_1635_; lean_object* v_key_1636_; lean_object* v_val_1637_; lean_object* v_rchild_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___f_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_toPure_1632_ = lean_ctor_get(v_inst_1626_, 1);
lean_inc(v_toPure_1632_);
v_toSeq_1633_ = lean_ctor_get(v_inst_1626_, 2);
lean_inc_n(v_toSeq_1633_, 3);
v_color_1634_ = lean_ctor_get_uint8(v_x_1628_, sizeof(void*)*4);
v_lchild_1635_ = lean_ctor_get(v_x_1628_, 0);
lean_inc(v_lchild_1635_);
v_key_1636_ = lean_ctor_get(v_x_1628_, 1);
lean_inc_n(v_key_1636_, 2);
v_val_1637_ = lean_ctor_get(v_x_1628_, 2);
lean_inc(v_val_1637_);
v_rchild_1638_ = lean_ctor_get(v_x_1628_, 3);
lean_inc(v_rchild_1638_);
lean_dec_ref_known(v_x_1628_, 4);
lean_inc_n(v_f_1627_, 2);
lean_inc_ref(v_inst_1626_);
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1639_, 0, v_inst_1626_);
lean_closure_set(v___f_1639_, 1, v_f_1627_);
lean_closure_set(v___f_1639_, 2, v_rchild_1638_);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1640_, 0, v_f_1627_);
lean_closure_set(v___f_1640_, 1, v_key_1636_);
lean_closure_set(v___f_1640_, 2, v_val_1637_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1641_, 0, v_inst_1626_);
lean_closure_set(v___f_1641_, 1, v_f_1627_);
lean_closure_set(v___f_1641_, 2, v_lchild_1635_);
v___x_1642_ = lean_box(v_color_1634_);
v___f_1643_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1643_, 0, v___x_1642_);
lean_closure_set(v___f_1643_, 1, v_key_1636_);
v___x_1644_ = lean_apply_2(v_toPure_1632_, lean_box(0), v___f_1643_);
v___x_1645_ = lean_apply_4(v_toSeq_1633_, lean_box(0), lean_box(0), v___x_1644_, v___f_1641_);
v___x_1646_ = lean_apply_4(v_toSeq_1633_, lean_box(0), lean_box(0), v___x_1645_, v___f_1640_);
v___x_1647_ = lean_apply_4(v_toSeq_1633_, lean_box(0), lean_box(0), v___x_1646_, v___f_1639_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* v_inst_1648_, lean_object* v_f_1649_, lean_object* v_rchild_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_RBNode_mapM___redArg(v_inst_1648_, v_f_1649_, v_rchild_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_00_u03b3_1655_, lean_object* v_M_1656_, lean_object* v_inst_1657_, lean_object* v_f_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_RBNode_mapM___redArg(v_inst_1657_, v_f_1658_, v_x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* v_f_1661_, lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec(v_f_1661_);
v___x_1663_ = lean_box(0);
return v___x_1663_;
}
else
{
uint8_t v_color_1664_; lean_object* v_lchild_1665_; lean_object* v_key_1666_; lean_object* v_val_1667_; lean_object* v_rchild_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1678_; 
v_color_1664_ = lean_ctor_get_uint8(v_x_1662_, sizeof(void*)*4);
v_lchild_1665_ = lean_ctor_get(v_x_1662_, 0);
v_key_1666_ = lean_ctor_get(v_x_1662_, 1);
v_val_1667_ = lean_ctor_get(v_x_1662_, 2);
v_rchild_1668_ = lean_ctor_get(v_x_1662_, 3);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1662_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1670_ = v_x_1662_;
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_rchild_1668_);
lean_inc(v_val_1667_);
lean_inc(v_key_1666_);
lean_inc(v_lchild_1665_);
lean_dec(v_x_1662_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
lean_inc_n(v_f_1661_, 2);
v___x_1672_ = l_Lean_RBNode_map___redArg(v_f_1661_, v_lchild_1665_);
lean_inc(v_key_1666_);
v___x_1673_ = lean_apply_2(v_f_1661_, v_key_1666_, v_val_1667_);
v___x_1674_ = l_Lean_RBNode_map___redArg(v_f_1661_, v_rchild_1668_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 3, v___x_1674_);
lean_ctor_set(v___x_1670_, 2, v___x_1673_);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_key_1666_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v___x_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1677_, sizeof(void*)*4, v_color_1664_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_00_u03b3_1681_, lean_object* v_f_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_RBNode_map___redArg(v_f_1682_, v_x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* v_x_1685_, lean_object* v_x_1686_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 0)
{
return v_x_1685_;
}
else
{
lean_object* v_lchild_1687_; lean_object* v_key_1688_; lean_object* v_val_1689_; lean_object* v_rchild_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_lchild_1687_ = lean_ctor_get(v_x_1686_, 0);
v_key_1688_ = lean_ctor_get(v_x_1686_, 1);
v_val_1689_ = lean_ctor_get(v_x_1686_, 2);
v_rchild_1690_ = lean_ctor_get(v_x_1686_, 3);
v___x_1691_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1685_, v_lchild_1687_);
lean_inc(v_val_1689_);
lean_inc(v_key_1688_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_key_1688_);
lean_ctor_set(v___x_1692_, 1, v_val_1689_);
v___x_1693_ = lean_array_push(v___x_1691_, v___x_1692_);
v_x_1685_ = v___x_1693_;
v_x_1686_ = v_rchild_1690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1695_, v_x_1696_);
lean_dec(v_x_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* v_n_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
v___x_1702_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_1701_, v_n_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* v_n_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_RBNode_toArray___redArg(v_n_1703_);
lean_dec(v_n_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_n_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_RBNode_toArray___redArg(v_n_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* v_00_u03b1_1709_, lean_object* v_00_u03b2_1710_, lean_object* v_n_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_RBNode_toArray(v_00_u03b1_1709_, v_00_u03b2_1710_, v_n_1711_);
lean_dec(v_n_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1715_, v_x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(v_00_u03b1_1718_, v_00_u03b2_1719_, v_x_1720_, v_x_1721_);
lean_dec(v_x_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_box(0);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg___boxed(lean_object* v___dummy_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_RBNode_instEmptyCollection___redArg();
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_box(0);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg(){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_box(0);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg___boxed(lean_object* v___dummy_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_mkRBMap___redArg();
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_cmp_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_box(0);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_cmp_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_mkRBMap(v_00_u03b1_1738_, v_00_u03b2_1739_, v_cmp_1740_);
lean_dec_ref(v_cmp_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg(){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_box(0);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg___boxed(lean_object* v___dummy_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_RBMap_empty___redArg();
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_box(0);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_RBMap_empty(v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec_ref(v___y_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg(){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_box(0);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg___boxed(lean_object* v___dummy_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_instEmptyCollectionRBMap___redArg();
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_cmp_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_box(0);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_00_u03b2_1763_, lean_object* v_cmp_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_1762_, v_00_u03b2_1763_, v_cmp_1764_);
lean_dec_ref(v_cmp_1764_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg(){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_box(0);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg___boxed(lean_object* v___dummy_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_instInhabitedRBMap___redArg();
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_, lean_object* v_cmp_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_box(0);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_cmp_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_instInhabitedRBMap(v_00_u03b1_1774_, v_00_u03b2_1775_, v_cmp_1776_);
lean_dec_ref(v_cmp_1776_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* v_f_1778_, lean_object* v_t_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_RBNode_depth___redArg(v_f_1778_, v_t_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* v_f_1781_, lean_object* v_t_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_RBMap_depth___redArg(v_f_1781_, v_t_1782_);
lean_dec(v_t_1782_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* v_00_u03b1_1784_, lean_object* v_00_u03b2_1785_, lean_object* v_cmp_1786_, lean_object* v_f_1787_, lean_object* v_t_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_RBNode_depth___redArg(v_f_1787_, v_t_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_cmp_1792_, lean_object* v_f_1793_, lean_object* v_t_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_RBMap_depth(v_00_u03b1_1790_, v_00_u03b2_1791_, v_cmp_1792_, v_f_1793_, v_t_1794_);
lean_dec(v_t_1794_);
lean_dec_ref(v_cmp_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* v_t_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_RBNode_isSingleton___redArg(v_t_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* v_t_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l_Lean_RBMap_isSingleton___redArg(v_t_1798_);
lean_dec(v_t_1798_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* v_00_u03b1_1801_, lean_object* v_00_u03b2_1802_, lean_object* v_cmp_1803_, lean_object* v_t_1804_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Lean_RBNode_isSingleton___redArg(v_t_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_00_u03b2_1807_, lean_object* v_cmp_1808_, lean_object* v_t_1809_){
_start:
{
uint8_t v_res_1810_; lean_object* v_r_1811_; 
v_res_1810_ = l_Lean_RBMap_isSingleton(v_00_u03b1_1806_, v_00_u03b2_1807_, v_cmp_1808_, v_t_1809_);
lean_dec(v_t_1809_);
lean_dec_ref(v_cmp_1808_);
v_r_1811_ = lean_box(v_res_1810_);
return v_r_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* v_f_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_RBNode_fold___redArg(v_f_1812_, v_x_1813_, v_x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* v_00_u03b1_1816_, lean_object* v_00_u03b2_1817_, lean_object* v_00_u03c3_1818_, lean_object* v_cmp_1819_, lean_object* v_f_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_RBNode_fold___redArg(v_f_1820_, v_x_1821_, v_x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_00_u03c3_1826_, lean_object* v_cmp_1827_, lean_object* v_f_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_RBMap_fold(v_00_u03b1_1824_, v_00_u03b2_1825_, v_00_u03c3_1826_, v_cmp_1827_, v_f_1828_, v_x_1829_, v_x_1830_);
lean_dec_ref(v_cmp_1827_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* v_f_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_RBNode_revFold___redArg(v_f_1832_, v_x_1833_, v_x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_00_u03c3_1838_, lean_object* v_cmp_1839_, lean_object* v_f_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_RBNode_revFold___redArg(v_f_1840_, v_x_1841_, v_x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* v_00_u03b1_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_00_u03c3_1846_, lean_object* v_cmp_1847_, lean_object* v_f_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_RBMap_revFold(v_00_u03b1_1844_, v_00_u03b2_1845_, v_00_u03c3_1846_, v_cmp_1847_, v_f_1848_, v_x_1849_, v_x_1850_);
lean_dec_ref(v_cmp_1847_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* v_inst_1852_, lean_object* v_f_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_RBNode_foldM___redArg(v_inst_1852_, v_f_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* v_00_u03b1_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_00_u03c3_1859_, lean_object* v_cmp_1860_, lean_object* v_m_1861_, lean_object* v_inst_1862_, lean_object* v_f_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_RBNode_foldM___redArg(v_inst_1862_, v_f_1863_, v_x_1864_, v_x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_00_u03c3_1869_, lean_object* v_cmp_1870_, lean_object* v_m_1871_, lean_object* v_inst_1872_, lean_object* v_f_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_RBMap_foldM(v_00_u03b1_1867_, v_00_u03b2_1868_, v_00_u03c3_1869_, v_cmp_1870_, v_m_1871_, v_inst_1872_, v_f_1873_, v_x_1874_, v_x_1875_);
lean_dec_ref(v_cmp_1870_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* v_f_1877_, lean_object* v_x_1878_, lean_object* v_k_1879_, lean_object* v_v_1880_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_apply_2(v_f_1877_, v_k_1879_, v_v_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* v_inst_1882_, lean_object* v_f_1883_, lean_object* v_t_1884_){
_start:
{
lean_object* v___f_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1885_, 0, v_f_1883_);
v___x_1886_ = lean_box(0);
v___x_1887_ = l_Lean_RBNode_foldM___redArg(v_inst_1882_, v___f_1885_, v___x_1886_, v_t_1884_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* v_00_u03b1_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_cmp_1890_, lean_object* v_m_1891_, lean_object* v_inst_1892_, lean_object* v_f_1893_, lean_object* v_t_1894_){
_start:
{
lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1895_, 0, v_f_1893_);
v___x_1896_ = lean_box(0);
v___x_1897_ = l_Lean_RBNode_foldM___redArg(v_inst_1892_, v___f_1895_, v___x_1896_, v_t_1894_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_cmp_1900_, lean_object* v_m_1901_, lean_object* v_inst_1902_, lean_object* v_f_1903_, lean_object* v_t_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_RBMap_forM(v_00_u03b1_1898_, v_00_u03b2_1899_, v_cmp_1900_, v_m_1901_, v_inst_1902_, v_f_1903_, v_t_1904_);
lean_dec_ref(v_cmp_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* v_f_1906_, lean_object* v_a_1907_, lean_object* v_b_1908_, lean_object* v_acc_1909_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1907_);
lean_ctor_set(v___x_1910_, 1, v_b_1908_);
v___x_1911_ = lean_apply_2(v_f_1906_, v___x_1910_, v_acc_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* v_inst_1912_, lean_object* v_t_1913_, lean_object* v_init_1914_, lean_object* v_f_1915_){
_start:
{
lean_object* v_toApplicative_1916_; lean_object* v_toBind_1917_; lean_object* v_toPure_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; 
v_toApplicative_1916_ = lean_ctor_get(v_inst_1912_, 0);
v_toBind_1917_ = lean_ctor_get(v_inst_1912_, 1);
lean_inc(v_toBind_1917_);
v_toPure_1918_ = lean_ctor_get(v_toApplicative_1916_, 1);
lean_inc(v_toPure_1918_);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1919_, 0, v_f_1915_);
v___x_1920_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1912_, v___f_1919_, v_t_1913_, v_init_1914_);
v___f_1921_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1921_, 0, v_toPure_1918_);
v___x_1922_ = lean_apply_4(v_toBind_1917_, lean_box(0), lean_box(0), v___x_1920_, v___f_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* v_00_u03b1_1923_, lean_object* v_00_u03b2_1924_, lean_object* v_00_u03c3_1925_, lean_object* v_cmp_1926_, lean_object* v_m_1927_, lean_object* v_inst_1928_, lean_object* v_t_1929_, lean_object* v_init_1930_, lean_object* v_f_1931_){
_start:
{
lean_object* v_toApplicative_1932_; lean_object* v_toBind_1933_; lean_object* v_toPure_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v_toApplicative_1932_ = lean_ctor_get(v_inst_1928_, 0);
v_toBind_1933_ = lean_ctor_get(v_inst_1928_, 1);
lean_inc(v_toBind_1933_);
v_toPure_1934_ = lean_ctor_get(v_toApplicative_1932_, 1);
lean_inc(v_toPure_1934_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1935_, 0, v_f_1931_);
v___x_1936_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1928_, v___f_1935_, v_t_1929_, v_init_1930_);
v___f_1937_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1937_, 0, v_toPure_1934_);
v___x_1938_ = lean_apply_4(v_toBind_1933_, lean_box(0), lean_box(0), v___x_1936_, v___f_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* v_00_u03b1_1939_, lean_object* v_00_u03b2_1940_, lean_object* v_00_u03c3_1941_, lean_object* v_cmp_1942_, lean_object* v_m_1943_, lean_object* v_inst_1944_, lean_object* v_t_1945_, lean_object* v_init_1946_, lean_object* v_f_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_RBMap_forIn(v_00_u03b1_1939_, v_00_u03b2_1940_, v_00_u03c3_1941_, v_cmp_1942_, v_m_1943_, v_inst_1944_, v_t_1945_, v_init_1946_, v_f_1947_);
lean_dec_ref(v_cmp_1942_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* v___y_1949_, lean_object* v_a_1950_, lean_object* v_b_1951_, lean_object* v_acc_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1950_);
lean_ctor_set(v___x_1953_, 1, v_b_1951_);
v___x_1954_ = lean_apply_2(v___y_1949_, v___x_1953_, v_acc_1952_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1955_, lean_object* v_00_u03b2_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_toApplicative_1960_; lean_object* v_toBind_1961_; lean_object* v_toPure_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; 
v_toApplicative_1960_ = lean_ctor_get(v_inst_1955_, 0);
v_toBind_1961_ = lean_ctor_get(v_inst_1955_, 1);
lean_inc(v_toBind_1961_);
v_toPure_1962_ = lean_ctor_get(v_toApplicative_1960_, 1);
lean_inc(v_toPure_1962_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1963_, 0, v___y_1959_);
v___x_1964_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1955_, v___f_1963_, v___y_1957_, v___y_1958_);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1965_, 0, v_toPure_1962_);
v___x_1966_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v___x_1964_, v___f_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* v_inst_1967_){
_start:
{
lean_object* v___f_1968_; 
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1968_, 0, v_inst_1967_);
return v___f_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* v_00_u03b1_1969_, lean_object* v_00_u03b2_1970_, lean_object* v_cmp_1971_, lean_object* v_m_1972_, lean_object* v_inst_1973_){
_start:
{
lean_object* v___f_1974_; 
v___f_1974_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1974_, 0, v_inst_1973_);
return v___f_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_cmp_1977_, lean_object* v_m_1978_, lean_object* v_inst_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_RBMap_instForInProdOfMonad(v_00_u03b1_1975_, v_00_u03b2_1976_, v_cmp_1977_, v_m_1978_, v_inst_1979_);
lean_dec_ref(v_cmp_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = 1;
return v___x_1982_;
}
else
{
uint8_t v___x_1983_; 
v___x_1983_ = 0;
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* v_x_1984_){
_start:
{
uint8_t v_res_1985_; lean_object* v_r_1986_; 
v_res_1985_ = l_Lean_RBMap_isEmpty___redArg(v_x_1984_);
lean_dec(v_x_1984_);
v_r_1986_ = lean_box(v_res_1985_);
return v_r_1986_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_cmp_1989_, lean_object* v_x_1990_){
_start:
{
if (lean_obj_tag(v_x_1990_) == 0)
{
uint8_t v___x_1991_; 
v___x_1991_ = 1;
return v___x_1991_;
}
else
{
uint8_t v___x_1992_; 
v___x_1992_ = 0;
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* v_00_u03b1_1993_, lean_object* v_00_u03b2_1994_, lean_object* v_cmp_1995_, lean_object* v_x_1996_){
_start:
{
uint8_t v_res_1997_; lean_object* v_r_1998_; 
v_res_1997_ = l_Lean_RBMap_isEmpty(v_00_u03b1_1993_, v_00_u03b2_1994_, v_cmp_1995_, v_x_1996_);
lean_dec(v_x_1996_);
lean_dec_ref(v_cmp_1995_);
v_r_1998_ = lean_box(v_res_1997_);
return v_r_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* v_ps_1999_, lean_object* v_k_2000_, lean_object* v_v_2001_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v_k_2000_);
lean_ctor_set(v___x_2002_, 1, v_v_2001_);
v___x_2003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v_ps_1999_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* v_x_2005_){
_start:
{
lean_object* v___f_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___f_2006_ = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
v___x_2007_ = lean_box(0);
v___x_2008_ = l_Lean_RBNode_revFold___redArg(v___f_2006_, v___x_2007_, v_x_2005_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* v_00_u03b1_2009_, lean_object* v_00_u03b2_2010_, lean_object* v_cmp_2011_, lean_object* v_x_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_RBMap_toList___redArg(v_x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* v_00_u03b1_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_cmp_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_RBMap_toList(v_00_u03b1_2014_, v_00_u03b2_2015_, v_cmp_2016_, v_x_2017_);
lean_dec_ref(v_cmp_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* v_ps_2019_, lean_object* v_k_2020_, lean_object* v_v_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_k_2020_);
lean_ctor_set(v___x_2022_, 1, v_v_2021_);
v___x_2023_ = lean_array_push(v_ps_2019_, v___x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* v_x_2027_){
_start:
{
lean_object* v___f_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___f_2028_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
v___x_2029_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
v___x_2030_ = l_Lean_RBNode_fold___redArg(v___f_2028_, v___x_2029_, v_x_2027_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* v_00_u03b1_2031_, lean_object* v_00_u03b2_2032_, lean_object* v_cmp_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_RBMap_toArray___redArg(v_x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* v_00_u03b1_2036_, lean_object* v_00_u03b2_2037_, lean_object* v_cmp_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_RBMap_toArray(v_00_u03b1_2036_, v_00_u03b2_2037_, v_cmp_2038_, v_x_2039_);
lean_dec_ref(v_cmp_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* v_x_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_RBNode_min___redArg(v_x_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_box(0);
return v___x_2043_;
}
else
{
lean_object* v_val_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2060_; 
v_val_2044_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2046_ = v___x_2042_;
v_isShared_2047_ = v_isSharedCheck_2060_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_val_2044_);
lean_dec(v___x_2042_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2060_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_fst_2048_; lean_object* v_snd_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2059_; 
v_fst_2048_ = lean_ctor_get(v_val_2044_, 0);
v_snd_2049_ = lean_ctor_get(v_val_2044_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_val_2044_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2051_ = v_val_2044_;
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snd_2049_);
lean_inc(v_fst_2048_);
lean_dec(v_val_2044_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2059_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_fst_2048_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_snd_2049_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2054_);
v___x_2056_ = v___x_2046_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* v_x_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_RBMap_min___redArg(v_x_2061_);
lean_dec(v_x_2061_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_cmp_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_RBNode_min___redArg(v_x_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_box(0);
return v___x_2068_;
}
else
{
lean_object* v_val_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2085_; 
v_val_2069_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2071_ = v___x_2067_;
v_isShared_2072_ = v_isSharedCheck_2085_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_val_2069_);
lean_dec(v___x_2067_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2085_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2084_; 
v_fst_2073_ = lean_ctor_get(v_val_2069_, 0);
v_snd_2074_ = lean_ctor_get(v_val_2069_, 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_val_2069_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2076_ = v_val_2069_;
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_snd_2074_);
lean_inc(v_fst_2073_);
lean_dec(v_val_2069_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_fst_2073_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_snd_2074_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2079_);
v___x_2081_ = v___x_2071_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_00_u03b2_2087_, lean_object* v_cmp_2088_, lean_object* v_x_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_RBMap_min(v_00_u03b1_2086_, v_00_u03b2_2087_, v_cmp_2088_, v_x_2089_);
lean_dec(v_x_2089_);
lean_dec_ref(v_cmp_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* v_x_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_RBNode_max___redArg(v_x_2091_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_box(0);
return v___x_2093_;
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2110_; 
v_val_2094_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2096_ = v___x_2092_;
v_isShared_2097_ = v_isSharedCheck_2110_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_val_2094_);
lean_dec(v___x_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2110_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2109_; 
v_fst_2098_ = lean_ctor_get(v_val_2094_, 0);
v_snd_2099_ = lean_ctor_get(v_val_2094_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_val_2094_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2101_ = v_val_2094_;
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_dec(v_val_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fst_2098_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_snd_2099_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2104_);
v___x_2106_ = v___x_2096_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* v_x_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_RBMap_max___redArg(v_x_2111_);
lean_dec(v_x_2111_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_cmp_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_RBNode_max___redArg(v_x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_box(0);
return v___x_2118_;
}
else
{
lean_object* v_val_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2135_; 
v_val_2119_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2121_ = v___x_2117_;
v_isShared_2122_ = v_isSharedCheck_2135_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_val_2119_);
lean_dec(v___x_2117_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2135_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_fst_2123_; lean_object* v_snd_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2134_; 
v_fst_2123_ = lean_ctor_get(v_val_2119_, 0);
v_snd_2124_ = lean_ctor_get(v_val_2119_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_val_2119_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2126_ = v_val_2119_;
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_snd_2124_);
lean_inc(v_fst_2123_);
lean_dec(v_val_2119_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2134_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_fst_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_snd_2124_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2129_);
v___x_2131_ = v___x_2121_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_00_u03b2_2137_, lean_object* v_cmp_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_RBMap_max(v_00_u03b1_2136_, v_00_u03b2_2137_, v_cmp_2138_, v_x_2139_);
lean_dec(v_x_2139_);
lean_dec_ref(v_cmp_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* v___x_2144_, lean_object* v_m_2145_, lean_object* v_prec_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2147_ = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
v___x_2148_ = l_Lean_RBMap_toList___redArg(v_m_2145_);
v___x_2149_ = l_List_repr___redArg(v___x_2144_, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2147_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Repr_addAppParen(v___x_2150_, v_prec_2146_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* v___x_2152_, lean_object* v_m_2153_, lean_object* v_prec_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_2152_, v_m_2153_, v_prec_2154_);
lean_dec(v_prec_2154_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* v_inst_2156_, lean_object* v_inst_2157_){
_start:
{
lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___f_2160_; 
v___f_2158_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2158_, 0, v_inst_2157_);
v___x_2159_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2159_, 0, lean_box(0));
lean_closure_set(v___x_2159_, 1, lean_box(0));
lean_closure_set(v___x_2159_, 2, v_inst_2156_);
lean_closure_set(v___x_2159_, 3, v___f_2158_);
v___f_2160_ = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2160_, 0, v___x_2159_);
return v___f_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* v_00_u03b1_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_cmp_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_RBMap_instRepr___redArg(v_inst_2164_, v_inst_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_00_u03b2_2168_, lean_object* v_cmp_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_RBMap_instRepr(v_00_u03b1_2167_, v_00_u03b2_2168_, v_cmp_2169_, v_inst_2170_, v_inst_2171_);
lean_dec_ref(v_cmp_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* v_cmp_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_RBNode_insert___redArg(v_cmp_2173_, v_x_2174_, v_x_2175_, v_x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* v_00_u03b1_2178_, lean_object* v_00_u03b2_2179_, lean_object* v_cmp_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_RBNode_insert___redArg(v_cmp_2180_, v_x_2181_, v_x_2182_, v_x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* v_cmp_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_RBNode_erase___redArg(v_cmp_2185_, v_x_2187_, v_x_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* v_00_u03b1_2189_, lean_object* v_00_u03b2_2190_, lean_object* v_cmp_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_RBNode_erase___redArg(v_cmp_2191_, v_x_2193_, v_x_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* v_cmp_2195_, lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 0)
{
lean_object* v___x_2197_; 
lean_dec_ref(v_cmp_2195_);
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
else
{
lean_object* v_head_2198_; lean_object* v_tail_2199_; lean_object* v_fst_2200_; lean_object* v_snd_2201_; lean_object* v_val_2202_; lean_object* v___x_2203_; 
v_head_2198_ = lean_ctor_get(v_x_2196_, 0);
lean_inc(v_head_2198_);
v_tail_2199_ = lean_ctor_get(v_x_2196_, 1);
lean_inc(v_tail_2199_);
lean_dec_ref_known(v_x_2196_, 2);
v_fst_2200_ = lean_ctor_get(v_head_2198_, 0);
lean_inc(v_fst_2200_);
v_snd_2201_ = lean_ctor_get(v_head_2198_, 1);
lean_inc(v_snd_2201_);
lean_dec(v_head_2198_);
lean_inc_ref(v_cmp_2195_);
v_val_2202_ = l_Lean_RBMap_ofList___redArg(v_cmp_2195_, v_tail_2199_);
v___x_2203_ = l_Lean_RBNode_insert___redArg(v_cmp_2195_, v_val_2202_, v_fst_2200_, v_snd_2201_);
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* v_00_u03b1_2204_, lean_object* v_00_u03b2_2205_, lean_object* v_cmp_2206_, lean_object* v_x_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_RBMap_ofList___redArg(v_cmp_2206_, v_x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* v_cmp_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_RBNode_findCore___redArg(v_cmp_2209_, v_x_2210_, v_x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* v_00_u03b1_2213_, lean_object* v_00_u03b2_2214_, lean_object* v_cmp_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_RBNode_findCore___redArg(v_cmp_2215_, v_x_2216_, v_x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* v_cmp_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_RBNode_find___redArg(v_cmp_2219_, v_x_2220_, v_x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* v_00_u03b1_2223_, lean_object* v_00_u03b2_2224_, lean_object* v_cmp_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_RBNode_find___redArg(v_cmp_2225_, v_x_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* v_cmp_2229_, lean_object* v_t_2230_, lean_object* v_k_2231_, lean_object* v_v_u2080_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_RBNode_find___redArg(v_cmp_2229_, v_t_2230_, v_k_2231_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_inc(v_v_u2080_2232_);
return v_v_u2080_2232_;
}
else
{
lean_object* v_val_2234_; 
v_val_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v___x_2233_, 1);
return v_val_2234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* v_cmp_2235_, lean_object* v_t_2236_, lean_object* v_k_2237_, lean_object* v_v_u2080_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_RBMap_findD___redArg(v_cmp_2235_, v_t_2236_, v_k_2237_, v_v_u2080_2238_);
lean_dec(v_v_u2080_2238_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* v_00_u03b1_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_cmp_2242_, lean_object* v_t_2243_, lean_object* v_k_2244_, lean_object* v_v_u2080_2245_){
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
lean_dec_ref_known(v___x_2246_, 1);
return v_val_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_cmp_2250_, lean_object* v_t_2251_, lean_object* v_k_2252_, lean_object* v_v_u2080_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_RBMap_findD(v_00_u03b1_2248_, v_00_u03b2_2249_, v_cmp_2250_, v_t_2251_, v_k_2252_, v_v_u2080_2253_);
lean_dec(v_v_u2080_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* v_cmp_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_box(0);
v___x_2259_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2255_, v_x_2256_, v_x_2257_, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* v_00_u03b1_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_cmp_2262_, lean_object* v_x_2263_, lean_object* v_x_2264_){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_box(0);
v___x_2266_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2262_, v_x_2263_, v_x_2264_, v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object* v_cmp_2267_, lean_object* v_t_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_RBNode_find___redArg(v_cmp_2267_, v_t_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
uint8_t v___x_2271_; 
v___x_2271_ = 0;
return v___x_2271_;
}
else
{
uint8_t v___x_2272_; 
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = 1;
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* v_cmp_2273_, lean_object* v_t_2274_, lean_object* v_a_2275_){
_start:
{
uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_res_2276_ = l_Lean_RBMap_contains___redArg(v_cmp_2273_, v_t_2274_, v_a_2275_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object* v_00_u03b1_2278_, lean_object* v_00_u03b2_2279_, lean_object* v_cmp_2280_, lean_object* v_t_2281_, lean_object* v_a_2282_){
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
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = 1;
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_cmp_2288_, lean_object* v_t_2289_, lean_object* v_a_2290_){
_start:
{
uint8_t v_res_2291_; lean_object* v_r_2292_; 
v_res_2291_ = l_Lean_RBMap_contains(v_00_u03b1_2286_, v_00_u03b2_2287_, v_cmp_2288_, v_t_2289_, v_a_2290_);
v_r_2292_ = lean_box(v_res_2291_);
return v_r_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* v_cmp_2293_, lean_object* v_r_2294_, lean_object* v_p_2295_){
_start:
{
lean_object* v_fst_2296_; lean_object* v_snd_2297_; lean_object* v___x_2298_; 
v_fst_2296_ = lean_ctor_get(v_p_2295_, 0);
lean_inc(v_fst_2296_);
v_snd_2297_ = lean_ctor_get(v_p_2295_, 1);
lean_inc(v_snd_2297_);
lean_dec_ref(v_p_2295_);
v___x_2298_ = l_Lean_RBNode_insert___redArg(v_cmp_2293_, v_r_2294_, v_fst_2296_, v_snd_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* v_l_2299_, lean_object* v_cmp_2300_){
_start:
{
lean_object* v___f_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2301_, 0, v_cmp_2300_);
v___x_2302_ = lean_box(0);
v___x_2303_ = l_List_foldl___redArg(v___f_2301_, v___x_2302_, v_l_2299_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* v_00_u03b1_2304_, lean_object* v_00_u03b2_2305_, lean_object* v_l_2306_, lean_object* v_cmp_2307_){
_start:
{
lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2308_, 0, v_cmp_2307_);
v___x_2309_ = lean_box(0);
v___x_2310_ = l_List_foldl___redArg(v___f_2308_, v___x_2309_, v_l_2306_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* v_cmp_2311_, lean_object* v_x1_2312_, lean_object* v_x2_2313_){
_start:
{
lean_object* v_fst_2314_; lean_object* v_snd_2315_; lean_object* v___x_2316_; 
v_fst_2314_ = lean_ctor_get(v_x2_2313_, 0);
lean_inc(v_fst_2314_);
v_snd_2315_ = lean_ctor_get(v_x2_2313_, 1);
lean_inc(v_snd_2315_);
lean_dec_ref(v_x2_2313_);
v___x_2316_ = l_Lean_RBNode_insert___redArg(v_cmp_2311_, v_x1_2312_, v_fst_2314_, v_snd_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* v_l_2336_, lean_object* v_cmp_2337_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_unsigned_to_nat(0u);
v___x_2340_ = lean_array_get_size(v_l_2336_);
v___x_2341_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2342_ = lean_nat_dec_lt(v___x_2339_, v___x_2340_);
if (v___x_2342_ == 0)
{
lean_dec_ref(v_cmp_2337_);
lean_dec_ref(v_l_2336_);
return v___x_2338_;
}
else
{
lean_object* v___f_2343_; size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___f_2343_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2343_, 0, v_cmp_2337_);
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2340_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2341_, v___f_2343_, v_l_2336_, v___x_2344_, v___x_2345_, v___x_2338_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* v_00_u03b1_2347_, lean_object* v_00_u03b2_2348_, lean_object* v_l_2349_, lean_object* v_cmp_2350_){
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
lean_object* v___f_2356_; size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2356_, 0, v_cmp_2350_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = lean_usize_of_nat(v___x_2353_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2354_, v___f_2356_, v_l_2349_, v___x_2357_, v___x_2358_, v___x_2351_);
return v___x_2359_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object* v_x_2360_, lean_object* v_x_2361_){
_start:
{
uint8_t v___x_2362_; 
v___x_2362_ = l_Lean_RBNode_all___redArg(v_x_2361_, v_x_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___redArg___boxed(lean_object* v_x_2363_, lean_object* v_x_2364_){
_start:
{
uint8_t v_res_2365_; lean_object* v_r_2366_; 
v_res_2365_ = l_Lean_RBMap_all___redArg(v_x_2363_, v_x_2364_);
v_r_2366_ = lean_box(v_res_2365_);
return v_r_2366_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object* v_00_u03b1_2367_, lean_object* v_00_u03b2_2368_, lean_object* v_cmp_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = l_Lean_RBNode_all___redArg(v_x_2371_, v_x_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* v_00_u03b1_2373_, lean_object* v_00_u03b2_2374_, lean_object* v_cmp_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
uint8_t v_res_2378_; lean_object* v_r_2379_; 
v_res_2378_ = l_Lean_RBMap_all(v_00_u03b1_2373_, v_00_u03b2_2374_, v_cmp_2375_, v_x_2376_, v_x_2377_);
lean_dec_ref(v_cmp_2375_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object* v_x_2380_, lean_object* v_x_2381_){
_start:
{
uint8_t v___x_2382_; 
v___x_2382_ = l_Lean_RBNode_any___redArg(v_x_2381_, v_x_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Lean_RBMap_any___redArg(v_x_2383_, v_x_2384_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object* v_00_u03b1_2387_, lean_object* v_00_u03b2_2388_, lean_object* v_cmp_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
uint8_t v___x_2392_; 
v___x_2392_ = l_Lean_RBNode_any___redArg(v_x_2391_, v_x_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* v_00_u03b1_2393_, lean_object* v_00_u03b2_2394_, lean_object* v_cmp_2395_, lean_object* v_x_2396_, lean_object* v_x_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Lean_RBMap_any(v_00_u03b1_2393_, v_00_u03b2_2394_, v_cmp_2395_, v_x_2396_, v_x_2397_);
lean_dec_ref(v_cmp_2395_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* v_x_2400_, lean_object* v_x_2401_){
_start:
{
if (lean_obj_tag(v_x_2401_) == 0)
{
return v_x_2400_;
}
else
{
lean_object* v_lchild_2402_; lean_object* v_rchild_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_lchild_2402_ = lean_ctor_get(v_x_2401_, 0);
v_rchild_2403_ = lean_ctor_get(v_x_2401_, 3);
v___x_2404_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2400_, v_lchild_2402_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_add(v___x_2404_, v___x_2405_);
lean_dec(v___x_2404_);
v_x_2400_ = v___x_2406_;
v_x_2401_ = v_rchild_2403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2408_, v_x_2409_);
lean_dec(v_x_2409_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* v_m_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_2412_, v_m_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* v_m_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_RBMap_size___redArg(v_m_2414_);
lean_dec(v_m_2414_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* v_00_u03b1_2416_, lean_object* v_00_u03b2_2417_, lean_object* v_cmp_2418_, lean_object* v_m_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_RBMap_size___redArg(v_m_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_00_u03b2_2422_, lean_object* v_cmp_2423_, lean_object* v_m_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_RBMap_size(v_00_u03b1_2421_, v_00_u03b2_2422_, v_cmp_2423_, v_m_2424_);
lean_dec(v_m_2424_);
lean_dec_ref(v_cmp_2423_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* v_00_u03b1_2426_, lean_object* v_00_u03b2_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2428_, v_x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_00_u03b2_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(v_00_u03b1_2431_, v_00_u03b2_2432_, v_x_2433_, v_x_2434_);
lean_dec(v_x_2434_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_le(v___y_2436_, v___y_2437_);
if (v___x_2438_ == 0)
{
lean_inc(v___y_2436_);
return v___y_2436_;
}
else
{
lean_inc(v___y_2437_);
return v___y_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec(v___y_2439_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* v_t_2443_){
_start:
{
lean_object* v___f_2444_; lean_object* v___x_2445_; 
v___f_2444_ = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
v___x_2445_ = l_Lean_RBNode_depth___redArg(v___f_2444_, v_t_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* v_t_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_RBMap_maxDepth___redArg(v_t_2446_);
lean_dec(v_t_2446_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* v_00_u03b1_2448_, lean_object* v_00_u03b2_2449_, lean_object* v_cmp_2450_, lean_object* v_t_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_RBMap_maxDepth___redArg(v_t_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_00_u03b2_2454_, lean_object* v_cmp_2455_, lean_object* v_t_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_RBMap_maxDepth(v_00_u03b1_2453_, v_00_u03b2_2454_, v_cmp_2455_, v_t_2456_);
lean_dec(v_t_2456_);
lean_dec_ref(v_cmp_2455_);
return v_res_2457_;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2461_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2462_ = lean_unsigned_to_nat(14u);
v___x_2463_ = lean_unsigned_to_nat(386u);
v___x_2464_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
v___x_2465_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2466_ = l_mkPanicMessageWithDecl(v___x_2465_, v___x_2464_, v___x_2463_, v___x_2462_, v___x_2461_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_t_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_RBNode_min___redArg(v_t_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_inst_2467_);
lean_ctor_set(v___x_2471_, 1, v_inst_2468_);
v___x_2472_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2473_ = l_panic___redArg(v___x_2471_, v___x_2472_);
lean_dec_ref_known(v___x_2471_, 2);
return v___x_2473_;
}
else
{
lean_object* v_val_2474_; lean_object* v_fst_2475_; lean_object* v_snd_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v_inst_2468_);
lean_dec(v_inst_2467_);
v_val_2474_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2470_, 1);
v_fst_2475_ = lean_ctor_get(v_val_2474_, 0);
v_snd_2476_ = lean_ctor_get(v_val_2474_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_val_2474_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v_val_2474_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_snd_2476_);
lean_inc(v_fst_2475_);
lean_dec(v_val_2474_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_fst_2475_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_snd_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_t_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_RBMap_min_x21___redArg(v_inst_2484_, v_inst_2485_, v_t_2486_);
lean_dec(v_t_2486_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* v_00_u03b1_2488_, lean_object* v_00_u03b2_2489_, lean_object* v_cmp_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_t_2493_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_RBNode_min___redArg(v_t_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_inst_2491_);
lean_ctor_set(v___x_2495_, 1, v_inst_2492_);
v___x_2496_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2497_ = l_panic___redArg(v___x_2495_, v___x_2496_);
lean_dec_ref_known(v___x_2495_, 2);
return v___x_2497_;
}
else
{
lean_object* v_val_2498_; lean_object* v_fst_2499_; lean_object* v_snd_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_inst_2492_);
lean_dec(v_inst_2491_);
v_val_2498_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v___x_2494_, 1);
v_fst_2499_ = lean_ctor_get(v_val_2498_, 0);
v_snd_2500_ = lean_ctor_get(v_val_2498_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_val_2498_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v_val_2498_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_snd_2500_);
lean_inc(v_fst_2499_);
lean_dec(v_val_2498_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_fst_2499_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_snd_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_00_u03b2_2509_, lean_object* v_cmp_2510_, lean_object* v_inst_2511_, lean_object* v_inst_2512_, lean_object* v_t_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_RBMap_min_x21(v_00_u03b1_2508_, v_00_u03b2_2509_, v_cmp_2510_, v_inst_2511_, v_inst_2512_, v_t_2513_);
lean_dec(v_t_2513_);
lean_dec_ref(v_cmp_2510_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2516_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2517_ = lean_unsigned_to_nat(14u);
v___x_2518_ = lean_unsigned_to_nat(391u);
v___x_2519_ = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
v___x_2520_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2521_ = l_mkPanicMessageWithDecl(v___x_2520_, v___x_2519_, v___x_2518_, v___x_2517_, v___x_2516_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_t_2524_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_RBNode_max___redArg(v_t_2524_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_inst_2522_);
lean_ctor_set(v___x_2526_, 1, v_inst_2523_);
v___x_2527_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2528_ = l_panic___redArg(v___x_2526_, v___x_2527_);
lean_dec_ref_known(v___x_2526_, 2);
return v___x_2528_;
}
else
{
lean_object* v_val_2529_; lean_object* v_fst_2530_; lean_object* v_snd_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_inst_2523_);
lean_dec(v_inst_2522_);
v_val_2529_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_val_2529_);
lean_dec_ref_known(v___x_2525_, 1);
v_fst_2530_ = lean_ctor_get(v_val_2529_, 0);
v_snd_2531_ = lean_ctor_get(v_val_2529_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_val_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v_val_2529_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_snd_2531_);
lean_inc(v_fst_2530_);
lean_dec(v_val_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_fst_2530_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_snd_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* v_inst_2539_, lean_object* v_inst_2540_, lean_object* v_t_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_RBMap_max_x21___redArg(v_inst_2539_, v_inst_2540_, v_t_2541_);
lean_dec(v_t_2541_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* v_00_u03b1_2543_, lean_object* v_00_u03b2_2544_, lean_object* v_cmp_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_t_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_RBNode_max___redArg(v_t_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_inst_2546_);
lean_ctor_set(v___x_2550_, 1, v_inst_2547_);
v___x_2551_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2552_ = l_panic___redArg(v___x_2550_, v___x_2551_);
lean_dec_ref_known(v___x_2550_, 2);
return v___x_2552_;
}
else
{
lean_object* v_val_2553_; lean_object* v_fst_2554_; lean_object* v_snd_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_inst_2547_);
lean_dec(v_inst_2546_);
v_val_2553_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v___x_2549_, 1);
v_fst_2554_ = lean_ctor_get(v_val_2553_, 0);
v_snd_2555_ = lean_ctor_get(v_val_2553_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_val_2553_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v_val_2553_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_snd_2555_);
lean_inc(v_fst_2554_);
lean_dec(v_val_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_fst_2554_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_snd_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* v_00_u03b1_2563_, lean_object* v_00_u03b2_2564_, lean_object* v_cmp_2565_, lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_t_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_RBMap_max_x21(v_00_u03b1_2563_, v_00_u03b2_2564_, v_cmp_2565_, v_inst_2566_, v_inst_2567_, v_t_2568_);
lean_dec(v_t_2568_);
lean_dec_ref(v_cmp_2565_);
return v_res_2569_;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2572_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
v___x_2573_ = lean_unsigned_to_nat(14u);
v___x_2574_ = lean_unsigned_to_nat(397u);
v___x_2575_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
v___x_2576_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2577_ = l_mkPanicMessageWithDecl(v___x_2576_, v___x_2575_, v___x_2574_, v___x_2573_, v___x_2572_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* v_cmp_2578_, lean_object* v_inst_2579_, lean_object* v_t_2580_, lean_object* v_k_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_RBNode_find___redArg(v_cmp_2578_, v_t_2580_, v_k_2581_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2584_ = l_panic___redArg(v_inst_2579_, v___x_2583_);
return v___x_2584_;
}
else
{
lean_object* v_val_2585_; 
v_val_2585_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v___x_2582_, 1);
return v_val_2585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg___boxed(lean_object* v_cmp_2586_, lean_object* v_inst_2587_, lean_object* v_t_2588_, lean_object* v_k_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_RBMap_find_x21___redArg(v_cmp_2586_, v_inst_2587_, v_t_2588_, v_k_2589_);
lean_dec(v_inst_2587_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* v_00_u03b1_2591_, lean_object* v_00_u03b2_2592_, lean_object* v_cmp_2593_, lean_object* v_inst_2594_, lean_object* v_t_2595_, lean_object* v_k_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_RBNode_find___redArg(v_cmp_2593_, v_t_2595_, v_k_2596_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2599_ = l_panic___redArg(v_inst_2594_, v___x_2598_);
return v___x_2599_;
}
else
{
lean_object* v_val_2600_; 
v_val_2600_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_val_2600_);
lean_dec_ref_known(v___x_2597_, 1);
return v_val_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___boxed(lean_object* v_00_u03b1_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_cmp_2603_, lean_object* v_inst_2604_, lean_object* v_t_2605_, lean_object* v_k_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_RBMap_find_x21(v_00_u03b1_2601_, v_00_u03b2_2602_, v_cmp_2603_, v_inst_2604_, v_t_2605_, v_k_2606_);
lean_dec(v_inst_2604_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* v_cmp_2608_, lean_object* v_x_2609_, lean_object* v_x_2610_, lean_object* v_x_2611_){
_start:
{
if (lean_obj_tag(v_x_2609_) == 0)
{
uint8_t v___x_2612_; lean_object* v___x_2613_; 
lean_dec_ref(v_cmp_2608_);
v___x_2612_ = 0;
v___x_2613_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2613_, 0, v_x_2609_);
lean_ctor_set(v___x_2613_, 1, v_x_2610_);
lean_ctor_set(v___x_2613_, 2, v_x_2611_);
lean_ctor_set(v___x_2613_, 3, v_x_2609_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*4, v___x_2612_);
return v___x_2613_;
}
else
{
uint8_t v_color_2614_; 
v_color_2614_ = lean_ctor_get_uint8(v_x_2609_, sizeof(void*)*4);
if (v_color_2614_ == 0)
{
lean_object* v_lchild_2615_; lean_object* v_key_2616_; lean_object* v_val_2617_; lean_object* v_rchild_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2635_; 
v_lchild_2615_ = lean_ctor_get(v_x_2609_, 0);
v_key_2616_ = lean_ctor_get(v_x_2609_, 1);
v_val_2617_ = lean_ctor_get(v_x_2609_, 2);
v_rchild_2618_ = lean_ctor_get(v_x_2609_, 3);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_x_2609_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2620_ = v_x_2609_;
v_isShared_2621_ = v_isSharedCheck_2635_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_rchild_2618_);
lean_inc(v_val_2617_);
lean_inc(v_key_2616_);
lean_inc(v_lchild_2615_);
lean_dec(v_x_2609_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2635_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; uint8_t v___x_2623_; 
lean_inc_ref(v_cmp_2608_);
lean_inc(v_key_2616_);
lean_inc(v_x_2610_);
v___x_2622_ = lean_apply_2(v_cmp_2608_, v_x_2610_, v_key_2616_);
v___x_2623_ = lean_unbox(v___x_2622_);
switch(v___x_2623_)
{
case 0:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2608_, v_lchild_2615_, v_x_2610_, v_x_2611_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2624_);
v___x_2626_ = v___x_2620_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_key_2616_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v_val_2617_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v_rchild_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2627_, sizeof(void*)*4, v_color_2614_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
case 1:
{
lean_object* v___x_2629_; 
lean_dec(v_val_2617_);
lean_dec(v_key_2616_);
lean_dec_ref(v_cmp_2608_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 2, v_x_2611_);
lean_ctor_set(v___x_2620_, 1, v_x_2610_);
v___x_2629_ = v___x_2620_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_lchild_2615_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_x_2610_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_x_2611_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_rchild_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2630_, sizeof(void*)*4, v_color_2614_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
default: 
{
lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2631_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2608_, v_rchild_2618_, v_x_2610_, v_x_2611_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 3, v___x_2631_);
v___x_2633_ = v___x_2620_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_lchild_2615_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_key_2616_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v_val_2617_);
lean_ctor_set(v_reuseFailAlloc_2634_, 3, v___x_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2634_, sizeof(void*)*4, v_color_2614_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
else
{
lean_object* v_lchild_2636_; lean_object* v_key_2637_; lean_object* v_val_2638_; lean_object* v_rchild_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2798_; 
v_lchild_2636_ = lean_ctor_get(v_x_2609_, 0);
v_key_2637_ = lean_ctor_get(v_x_2609_, 1);
v_val_2638_ = lean_ctor_get(v_x_2609_, 2);
v_rchild_2639_ = lean_ctor_get(v_x_2609_, 3);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_x_2609_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2641_ = v_x_2609_;
v_isShared_2642_ = v_isSharedCheck_2798_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_rchild_2639_);
lean_inc(v_val_2638_);
lean_inc(v_key_2637_);
lean_inc(v_lchild_2636_);
lean_dec(v_x_2609_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2798_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
lean_inc_ref(v_cmp_2608_);
lean_inc(v_key_2637_);
lean_inc(v_x_2610_);
v___x_2643_ = lean_apply_2(v_cmp_2608_, v_x_2610_, v_key_2637_);
v___x_2644_ = lean_unbox(v___x_2643_);
switch(v___x_2644_)
{
case 0:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2608_, v_lchild_2636_, v_x_2610_, v_x_2611_);
if (lean_obj_tag(v___x_2645_) == 1)
{
uint8_t v_color_2646_; lean_object* v_lchild_2647_; lean_object* v_key_2648_; lean_object* v_val_2649_; lean_object* v_rchild_2650_; lean_object* v_a_2652_; lean_object* v_kx_2653_; lean_object* v_vx_2654_; lean_object* v_b_2655_; lean_object* v_ky_2656_; lean_object* v_vy_2657_; lean_object* v_c_2658_; lean_object* v_kz_2659_; lean_object* v_vz_2660_; lean_object* v_d_2661_; 
v_color_2646_ = lean_ctor_get_uint8(v___x_2645_, sizeof(void*)*4);
v_lchild_2647_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_lchild_2647_);
v_key_2648_ = lean_ctor_get(v___x_2645_, 1);
v_val_2649_ = lean_ctor_get(v___x_2645_, 2);
v_rchild_2650_ = lean_ctor_get(v___x_2645_, 3);
lean_inc(v_rchild_2650_);
if (v_color_2646_ == 0)
{
if (lean_obj_tag(v_lchild_2647_) == 1)
{
uint8_t v_color_2667_; 
v_color_2667_ = lean_ctor_get_uint8(v_lchild_2647_, sizeof(void*)*4);
if (v_color_2667_ == 0)
{
lean_object* v_lchild_2668_; lean_object* v_key_2669_; lean_object* v_val_2670_; lean_object* v_rchild_2671_; 
lean_inc(v_val_2649_);
lean_inc(v_key_2648_);
lean_dec_ref_known(v___x_2645_, 4);
v_lchild_2668_ = lean_ctor_get(v_lchild_2647_, 0);
lean_inc(v_lchild_2668_);
v_key_2669_ = lean_ctor_get(v_lchild_2647_, 1);
lean_inc(v_key_2669_);
v_val_2670_ = lean_ctor_get(v_lchild_2647_, 2);
lean_inc(v_val_2670_);
v_rchild_2671_ = lean_ctor_get(v_lchild_2647_, 3);
lean_inc(v_rchild_2671_);
lean_dec_ref_known(v_lchild_2647_, 4);
v_a_2652_ = v_lchild_2668_;
v_kx_2653_ = v_key_2669_;
v_vx_2654_ = v_val_2670_;
v_b_2655_ = v_rchild_2671_;
v_ky_2656_ = v_key_2648_;
v_vy_2657_ = v_val_2649_;
v_c_2658_ = v_rchild_2650_;
v_kz_2659_ = v_key_2637_;
v_vz_2660_ = v_val_2638_;
v_d_2661_ = v_rchild_2639_;
goto v___jp_2651_;
}
else
{
if (lean_obj_tag(v_rchild_2650_) == 1)
{
uint8_t v_color_2672_; 
v_color_2672_ = lean_ctor_get_uint8(v_rchild_2650_, sizeof(void*)*4);
if (v_color_2672_ == 0)
{
lean_object* v_lchild_2673_; lean_object* v_key_2674_; lean_object* v_val_2675_; lean_object* v_rchild_2676_; 
lean_inc(v_val_2649_);
lean_inc(v_key_2648_);
lean_dec_ref_known(v___x_2645_, 4);
v_lchild_2673_ = lean_ctor_get(v_rchild_2650_, 0);
lean_inc(v_lchild_2673_);
v_key_2674_ = lean_ctor_get(v_rchild_2650_, 1);
lean_inc(v_key_2674_);
v_val_2675_ = lean_ctor_get(v_rchild_2650_, 2);
lean_inc(v_val_2675_);
v_rchild_2676_ = lean_ctor_get(v_rchild_2650_, 3);
lean_inc(v_rchild_2676_);
lean_dec_ref_known(v_rchild_2650_, 4);
v_a_2652_ = v_lchild_2647_;
v_kx_2653_ = v_key_2648_;
v_vx_2654_ = v_val_2649_;
v_b_2655_ = v_lchild_2673_;
v_ky_2656_ = v_key_2674_;
v_vy_2657_ = v_val_2675_;
v_c_2658_ = v_rchild_2676_;
v_kz_2659_ = v_key_2637_;
v_vz_2660_ = v_val_2638_;
v_d_2661_ = v_rchild_2639_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref_known(v_lchild_2647_, 4);
lean_del_object(v___x_2641_);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_rchild_2650_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; lean_object* v_unused_2685_; lean_object* v_unused_2686_; lean_object* v_unused_2687_; 
v_unused_2684_ = lean_ctor_get(v_rchild_2650_, 3);
lean_dec(v_unused_2684_);
v_unused_2685_ = lean_ctor_get(v_rchild_2650_, 2);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_rchild_2650_, 1);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_rchild_2650_, 0);
lean_dec(v_unused_2687_);
v___x_2678_ = v_rchild_2650_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v_rchild_2650_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 3, v_rchild_2639_);
lean_ctor_set(v___x_2678_, 2, v_val_2638_);
lean_ctor_set(v___x_2678_, 1, v_key_2637_);
lean_ctor_set(v___x_2678_, 0, v___x_2645_);
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_rchild_2639_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*4, v_color_2614_);
return v___x_2681_;
}
}
}
}
else
{
lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_rchild_2650_);
lean_del_object(v___x_2641_);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_lchild_2647_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; lean_object* v_unused_2696_; lean_object* v_unused_2697_; lean_object* v_unused_2698_; 
v_unused_2695_ = lean_ctor_get(v_lchild_2647_, 3);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v_lchild_2647_, 2);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_lchild_2647_, 1);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_lchild_2647_, 0);
lean_dec(v_unused_2698_);
v___x_2689_ = v_lchild_2647_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_dec(v_lchild_2647_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 3, v_rchild_2639_);
lean_ctor_set(v___x_2689_, 2, v_val_2638_);
lean_ctor_set(v___x_2689_, 1, v_key_2637_);
lean_ctor_set(v___x_2689_, 0, v___x_2645_);
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_rchild_2639_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_ctor_set_uint8(v___x_2692_, sizeof(void*)*4, v_color_2614_);
return v___x_2692_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2650_) == 1)
{
uint8_t v_color_2699_; 
v_color_2699_ = lean_ctor_get_uint8(v_rchild_2650_, sizeof(void*)*4);
if (v_color_2699_ == 0)
{
lean_object* v_lchild_2700_; lean_object* v_key_2701_; lean_object* v_val_2702_; lean_object* v_rchild_2703_; 
lean_inc(v_val_2649_);
lean_inc(v_key_2648_);
lean_dec_ref_known(v___x_2645_, 4);
v_lchild_2700_ = lean_ctor_get(v_rchild_2650_, 0);
lean_inc(v_lchild_2700_);
v_key_2701_ = lean_ctor_get(v_rchild_2650_, 1);
lean_inc(v_key_2701_);
v_val_2702_ = lean_ctor_get(v_rchild_2650_, 2);
lean_inc(v_val_2702_);
v_rchild_2703_ = lean_ctor_get(v_rchild_2650_, 3);
lean_inc(v_rchild_2703_);
lean_dec_ref_known(v_rchild_2650_, 4);
v_a_2652_ = v_lchild_2647_;
v_kx_2653_ = v_key_2648_;
v_vx_2654_ = v_val_2649_;
v_b_2655_ = v_lchild_2700_;
v_ky_2656_ = v_key_2701_;
v_vy_2657_ = v_val_2702_;
v_c_2658_ = v_rchild_2703_;
v_kz_2659_ = v_key_2637_;
v_vz_2660_ = v_val_2638_;
v_d_2661_ = v_rchild_2639_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_lchild_2647_);
lean_del_object(v___x_2641_);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_rchild_2650_);
if (v_isSharedCheck_2710_ == 0)
{
lean_object* v_unused_2711_; lean_object* v_unused_2712_; lean_object* v_unused_2713_; lean_object* v_unused_2714_; 
v_unused_2711_ = lean_ctor_get(v_rchild_2650_, 3);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_rchild_2650_, 2);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_rchild_2650_, 1);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_rchild_2650_, 0);
lean_dec(v_unused_2714_);
v___x_2705_ = v_rchild_2650_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v_rchild_2650_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 3, v_rchild_2639_);
lean_ctor_set(v___x_2705_, 2, v_val_2638_);
lean_ctor_set(v___x_2705_, 1, v_key_2637_);
lean_ctor_set(v___x_2705_, 0, v___x_2645_);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_rchild_2639_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*4, v_color_2614_);
return v___x_2708_;
}
}
}
}
else
{
lean_object* v___x_2715_; 
lean_dec(v_rchild_2650_);
lean_dec(v_lchild_2647_);
lean_del_object(v___x_2641_);
v___x_2715_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2715_, 0, v___x_2645_);
lean_ctor_set(v___x_2715_, 1, v_key_2637_);
lean_ctor_set(v___x_2715_, 2, v_val_2638_);
lean_ctor_set(v___x_2715_, 3, v_rchild_2639_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*4, v_color_2614_);
return v___x_2715_;
}
}
}
else
{
lean_object* v___x_2716_; 
lean_dec(v_rchild_2650_);
lean_dec(v_lchild_2647_);
lean_del_object(v___x_2641_);
v___x_2716_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2716_, 0, v___x_2645_);
lean_ctor_set(v___x_2716_, 1, v_key_2637_);
lean_ctor_set(v___x_2716_, 2, v_val_2638_);
lean_ctor_set(v___x_2716_, 3, v_rchild_2639_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*4, v_color_2614_);
return v___x_2716_;
}
v___jp_2651_:
{
lean_object* v___x_2663_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 3, v_b_2655_);
lean_ctor_set(v___x_2641_, 2, v_vx_2654_);
lean_ctor_set(v___x_2641_, 1, v_kx_2653_);
lean_ctor_set(v___x_2641_, 0, v_a_2652_);
v___x_2663_ = v___x_2641_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2652_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_kx_2653_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_vx_2654_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v_b_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2666_, sizeof(void*)*4, v_color_2614_);
v___x_2663_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2664_, 0, v_c_2658_);
lean_ctor_set(v___x_2664_, 1, v_kz_2659_);
lean_ctor_set(v___x_2664_, 2, v_vz_2660_);
lean_ctor_set(v___x_2664_, 3, v_d_2661_);
lean_ctor_set_uint8(v___x_2664_, sizeof(void*)*4, v_color_2614_);
v___x_2665_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v_ky_2656_);
lean_ctor_set(v___x_2665_, 2, v_vy_2657_);
lean_ctor_set(v___x_2665_, 3, v___x_2664_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*4, v_color_2646_);
return v___x_2665_;
}
}
}
else
{
lean_object* v___x_2718_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2645_);
v___x_2718_ = v___x_2641_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2719_, 3, v_rchild_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2719_, sizeof(void*)*4, v_color_2614_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
case 1:
{
lean_object* v___x_2721_; 
lean_dec(v_val_2638_);
lean_dec(v_key_2637_);
lean_dec_ref(v_cmp_2608_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 2, v_x_2611_);
lean_ctor_set(v___x_2641_, 1, v_x_2610_);
v___x_2721_ = v___x_2641_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_x_2610_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_x_2611_);
lean_ctor_set(v_reuseFailAlloc_2722_, 3, v_rchild_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, sizeof(void*)*4, v_color_2614_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
default: 
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2608_, v_rchild_2639_, v_x_2610_, v_x_2611_);
if (lean_obj_tag(v___x_2723_) == 1)
{
uint8_t v_color_2724_; lean_object* v_lchild_2725_; lean_object* v_key_2726_; lean_object* v_val_2727_; lean_object* v_rchild_2728_; lean_object* v_a_2730_; lean_object* v_kx_2731_; lean_object* v_vx_2732_; lean_object* v_b_2733_; lean_object* v_ky_2734_; lean_object* v_vy_2735_; lean_object* v_c_2736_; lean_object* v_kz_2737_; lean_object* v_vz_2738_; lean_object* v_d_2739_; 
v_color_2724_ = lean_ctor_get_uint8(v___x_2723_, sizeof(void*)*4);
v_lchild_2725_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_lchild_2725_);
v_key_2726_ = lean_ctor_get(v___x_2723_, 1);
v_val_2727_ = lean_ctor_get(v___x_2723_, 2);
v_rchild_2728_ = lean_ctor_get(v___x_2723_, 3);
lean_inc(v_rchild_2728_);
if (v_color_2724_ == 0)
{
if (lean_obj_tag(v_lchild_2725_) == 1)
{
uint8_t v_color_2745_; 
v_color_2745_ = lean_ctor_get_uint8(v_lchild_2725_, sizeof(void*)*4);
if (v_color_2745_ == 0)
{
lean_object* v_lchild_2746_; lean_object* v_key_2747_; lean_object* v_val_2748_; lean_object* v_rchild_2749_; 
lean_inc(v_val_2727_);
lean_inc(v_key_2726_);
lean_dec_ref_known(v___x_2723_, 4);
v_lchild_2746_ = lean_ctor_get(v_lchild_2725_, 0);
lean_inc(v_lchild_2746_);
v_key_2747_ = lean_ctor_get(v_lchild_2725_, 1);
lean_inc(v_key_2747_);
v_val_2748_ = lean_ctor_get(v_lchild_2725_, 2);
lean_inc(v_val_2748_);
v_rchild_2749_ = lean_ctor_get(v_lchild_2725_, 3);
lean_inc(v_rchild_2749_);
lean_dec_ref_known(v_lchild_2725_, 4);
v_a_2730_ = v_lchild_2636_;
v_kx_2731_ = v_key_2637_;
v_vx_2732_ = v_val_2638_;
v_b_2733_ = v_lchild_2746_;
v_ky_2734_ = v_key_2747_;
v_vy_2735_ = v_val_2748_;
v_c_2736_ = v_rchild_2749_;
v_kz_2737_ = v_key_2726_;
v_vz_2738_ = v_val_2727_;
v_d_2739_ = v_rchild_2728_;
goto v___jp_2729_;
}
else
{
if (lean_obj_tag(v_rchild_2728_) == 1)
{
uint8_t v_color_2750_; 
v_color_2750_ = lean_ctor_get_uint8(v_rchild_2728_, sizeof(void*)*4);
if (v_color_2750_ == 0)
{
lean_object* v_lchild_2751_; lean_object* v_key_2752_; lean_object* v_val_2753_; lean_object* v_rchild_2754_; 
lean_inc(v_val_2727_);
lean_inc(v_key_2726_);
lean_dec_ref_known(v___x_2723_, 4);
v_lchild_2751_ = lean_ctor_get(v_rchild_2728_, 0);
lean_inc(v_lchild_2751_);
v_key_2752_ = lean_ctor_get(v_rchild_2728_, 1);
lean_inc(v_key_2752_);
v_val_2753_ = lean_ctor_get(v_rchild_2728_, 2);
lean_inc(v_val_2753_);
v_rchild_2754_ = lean_ctor_get(v_rchild_2728_, 3);
lean_inc(v_rchild_2754_);
lean_dec_ref_known(v_rchild_2728_, 4);
v_a_2730_ = v_lchild_2636_;
v_kx_2731_ = v_key_2637_;
v_vx_2732_ = v_val_2638_;
v_b_2733_ = v_lchild_2725_;
v_ky_2734_ = v_key_2726_;
v_vy_2735_ = v_val_2727_;
v_c_2736_ = v_lchild_2751_;
v_kz_2737_ = v_key_2752_;
v_vz_2738_ = v_val_2753_;
v_d_2739_ = v_rchild_2754_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec_ref_known(v_lchild_2725_, 4);
lean_del_object(v___x_2641_);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_rchild_2728_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; 
v_unused_2762_ = lean_ctor_get(v_rchild_2728_, 3);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_rchild_2728_, 2);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_rchild_2728_, 1);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_rchild_2728_, 0);
lean_dec(v_unused_2765_);
v___x_2756_ = v_rchild_2728_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v_rchild_2728_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 3, v___x_2723_);
lean_ctor_set(v___x_2756_, 2, v_val_2638_);
lean_ctor_set(v___x_2756_, 1, v_key_2637_);
lean_ctor_set(v___x_2756_, 0, v_lchild_2636_);
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2760_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2760_, 3, v___x_2723_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*4, v_color_2614_);
return v___x_2759_;
}
}
}
}
else
{
lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_rchild_2728_);
lean_del_object(v___x_2641_);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_lchild_2725_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; lean_object* v_unused_2774_; lean_object* v_unused_2775_; lean_object* v_unused_2776_; 
v_unused_2773_ = lean_ctor_get(v_lchild_2725_, 3);
lean_dec(v_unused_2773_);
v_unused_2774_ = lean_ctor_get(v_lchild_2725_, 2);
lean_dec(v_unused_2774_);
v_unused_2775_ = lean_ctor_get(v_lchild_2725_, 1);
lean_dec(v_unused_2775_);
v_unused_2776_ = lean_ctor_get(v_lchild_2725_, 0);
lean_dec(v_unused_2776_);
v___x_2767_ = v_lchild_2725_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_dec(v_lchild_2725_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 3, v___x_2723_);
lean_ctor_set(v___x_2767_, 2, v_val_2638_);
lean_ctor_set(v___x_2767_, 1, v_key_2637_);
lean_ctor_set(v___x_2767_, 0, v_lchild_2636_);
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v___x_2723_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*4, v_color_2614_);
return v___x_2770_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2728_) == 1)
{
uint8_t v_color_2777_; 
v_color_2777_ = lean_ctor_get_uint8(v_rchild_2728_, sizeof(void*)*4);
if (v_color_2777_ == 0)
{
lean_object* v_lchild_2778_; lean_object* v_key_2779_; lean_object* v_val_2780_; lean_object* v_rchild_2781_; 
lean_inc(v_val_2727_);
lean_inc(v_key_2726_);
lean_dec_ref_known(v___x_2723_, 4);
v_lchild_2778_ = lean_ctor_get(v_rchild_2728_, 0);
lean_inc(v_lchild_2778_);
v_key_2779_ = lean_ctor_get(v_rchild_2728_, 1);
lean_inc(v_key_2779_);
v_val_2780_ = lean_ctor_get(v_rchild_2728_, 2);
lean_inc(v_val_2780_);
v_rchild_2781_ = lean_ctor_get(v_rchild_2728_, 3);
lean_inc(v_rchild_2781_);
lean_dec_ref_known(v_rchild_2728_, 4);
v_a_2730_ = v_lchild_2636_;
v_kx_2731_ = v_key_2637_;
v_vx_2732_ = v_val_2638_;
v_b_2733_ = v_lchild_2725_;
v_ky_2734_ = v_key_2726_;
v_vy_2735_ = v_val_2727_;
v_c_2736_ = v_lchild_2778_;
v_kz_2737_ = v_key_2779_;
v_vz_2738_ = v_val_2780_;
v_d_2739_ = v_rchild_2781_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_lchild_2725_);
lean_del_object(v___x_2641_);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_rchild_2728_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; 
v_unused_2789_ = lean_ctor_get(v_rchild_2728_, 3);
lean_dec(v_unused_2789_);
v_unused_2790_ = lean_ctor_get(v_rchild_2728_, 2);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_rchild_2728_, 1);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_rchild_2728_, 0);
lean_dec(v_unused_2792_);
v___x_2783_ = v_rchild_2728_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v_rchild_2728_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 3, v___x_2723_);
lean_ctor_set(v___x_2783_, 2, v_val_2638_);
lean_ctor_set(v___x_2783_, 1, v_key_2637_);
lean_ctor_set(v___x_2783_, 0, v_lchild_2636_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2787_, 3, v___x_2723_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*4, v_color_2614_);
return v___x_2786_;
}
}
}
}
else
{
lean_object* v___x_2793_; 
lean_dec(v_rchild_2728_);
lean_dec(v_lchild_2725_);
lean_del_object(v___x_2641_);
v___x_2793_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2793_, 0, v_lchild_2636_);
lean_ctor_set(v___x_2793_, 1, v_key_2637_);
lean_ctor_set(v___x_2793_, 2, v_val_2638_);
lean_ctor_set(v___x_2793_, 3, v___x_2723_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*4, v_color_2614_);
return v___x_2793_;
}
}
}
else
{
lean_object* v___x_2794_; 
lean_dec(v_rchild_2728_);
lean_dec(v_lchild_2725_);
lean_del_object(v___x_2641_);
v___x_2794_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2794_, 0, v_lchild_2636_);
lean_ctor_set(v___x_2794_, 1, v_key_2637_);
lean_ctor_set(v___x_2794_, 2, v_val_2638_);
lean_ctor_set(v___x_2794_, 3, v___x_2723_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*4, v_color_2614_);
return v___x_2794_;
}
v___jp_2729_:
{
lean_object* v___x_2741_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 3, v_b_2733_);
lean_ctor_set(v___x_2641_, 2, v_vx_2732_);
lean_ctor_set(v___x_2641_, 1, v_kx_2731_);
lean_ctor_set(v___x_2641_, 0, v_a_2730_);
v___x_2741_ = v___x_2641_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2730_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_kx_2731_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_vx_2732_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_b_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*4, v_color_2614_);
v___x_2741_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2742_, 0, v_c_2736_);
lean_ctor_set(v___x_2742_, 1, v_kz_2737_);
lean_ctor_set(v___x_2742_, 2, v_vz_2738_);
lean_ctor_set(v___x_2742_, 3, v_d_2739_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*4, v_color_2614_);
v___x_2743_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v_ky_2734_);
lean_ctor_set(v___x_2743_, 2, v_vy_2735_);
lean_ctor_set(v___x_2743_, 3, v___x_2742_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*4, v_color_2724_);
return v___x_2743_;
}
}
}
else
{
lean_object* v___x_2796_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 3, v___x_2723_);
v___x_2796_ = v___x_2641_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_lchild_2636_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_key_2637_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_val_2638_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v___x_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2797_, sizeof(void*)*4, v_color_2614_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* v_cmp_2799_, lean_object* v_t_2800_, lean_object* v_k_2801_, lean_object* v_v_2802_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Lean_RBNode_isRed___redArg(v_t_2800_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2799_, v_t_2800_, v_k_2801_, v_v_2802_);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2799_, v_t_2800_, v_k_2801_, v_v_2802_);
v___x_2806_ = l_Lean_RBNode_setBlack___redArg(v___x_2805_);
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* v_cmp_2807_, lean_object* v_x_2808_, lean_object* v_x_2809_){
_start:
{
if (lean_obj_tag(v_x_2808_) == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_x_2809_);
lean_dec_ref(v_cmp_2807_);
v___x_2810_ = lean_box(0);
return v___x_2810_;
}
else
{
lean_object* v_lchild_2811_; lean_object* v_key_2812_; lean_object* v_val_2813_; lean_object* v_rchild_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_lchild_2811_ = lean_ctor_get(v_x_2808_, 0);
lean_inc(v_lchild_2811_);
v_key_2812_ = lean_ctor_get(v_x_2808_, 1);
lean_inc(v_key_2812_);
v_val_2813_ = lean_ctor_get(v_x_2808_, 2);
lean_inc(v_val_2813_);
v_rchild_2814_ = lean_ctor_get(v_x_2808_, 3);
lean_inc(v_rchild_2814_);
lean_dec_ref_known(v_x_2808_, 4);
lean_inc_ref(v_cmp_2807_);
lean_inc(v_x_2809_);
v___x_2815_ = lean_apply_2(v_cmp_2807_, v_x_2809_, v_key_2812_);
v___x_2816_ = lean_unbox(v___x_2815_);
switch(v___x_2816_)
{
case 0:
{
lean_dec(v_rchild_2814_);
lean_dec(v_val_2813_);
v_x_2808_ = v_lchild_2811_;
goto _start;
}
case 1:
{
lean_object* v___x_2818_; 
lean_dec(v_rchild_2814_);
lean_dec(v_lchild_2811_);
lean_dec(v_x_2809_);
lean_dec_ref(v_cmp_2807_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_val_2813_);
return v___x_2818_;
}
default: 
{
lean_dec(v_val_2813_);
lean_dec(v_lchild_2811_);
v_x_2808_ = v_rchild_2814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* v_cmp_2820_, lean_object* v_mergeFn_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_){
_start:
{
if (lean_obj_tag(v_x_2823_) == 0)
{
lean_dec(v_mergeFn_2821_);
lean_dec_ref(v_cmp_2820_);
return v_x_2822_;
}
else
{
lean_object* v_lchild_2824_; lean_object* v_key_2825_; lean_object* v_val_2826_; lean_object* v_rchild_2827_; lean_object* v_val_2828_; lean_object* v___y_2830_; lean_object* v___x_2833_; 
v_lchild_2824_ = lean_ctor_get(v_x_2823_, 0);
lean_inc(v_lchild_2824_);
v_key_2825_ = lean_ctor_get(v_x_2823_, 1);
lean_inc_n(v_key_2825_, 2);
v_val_2826_ = lean_ctor_get(v_x_2823_, 2);
lean_inc(v_val_2826_);
v_rchild_2827_ = lean_ctor_get(v_x_2823_, 3);
lean_inc(v_rchild_2827_);
lean_dec_ref_known(v_x_2823_, 4);
lean_inc(v_mergeFn_2821_);
lean_inc_ref_n(v_cmp_2820_, 2);
v_val_2828_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2820_, v_mergeFn_2821_, v_x_2822_, v_lchild_2824_);
lean_inc(v_val_2828_);
v___x_2833_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2820_, v_val_2828_, v_key_2825_);
if (lean_obj_tag(v___x_2833_) == 0)
{
v___y_2830_ = v_val_2826_;
goto v___jp_2829_;
}
else
{
lean_object* v_val_2834_; lean_object* v___x_2835_; 
v_val_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v___x_2833_, 1);
lean_inc(v_mergeFn_2821_);
lean_inc(v_key_2825_);
v___x_2835_ = lean_apply_3(v_mergeFn_2821_, v_key_2825_, v_val_2834_, v_val_2826_);
v___y_2830_ = v___x_2835_;
goto v___jp_2829_;
}
v___jp_2829_:
{
lean_object* v___x_2831_; 
lean_inc_ref(v_cmp_2820_);
v___x_2831_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2820_, v_val_2828_, v_key_2825_, v___y_2830_);
v_x_2822_ = v___x_2831_;
v_x_2823_ = v_rchild_2827_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* v_cmp_2836_, lean_object* v_mergeFn_2837_, lean_object* v_t_u2081_2838_, lean_object* v_t_u2082_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2836_, v_mergeFn_2837_, v_t_u2081_2838_, v_t_u2082_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* v_00_u03b1_2841_, lean_object* v_00_u03b2_2842_, lean_object* v_cmp_2843_, lean_object* v_mergeFn_2844_, lean_object* v_t_u2081_2845_, lean_object* v_t_u2082_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2843_, v_mergeFn_2844_, v_t_u2081_2845_, v_t_u2082_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* v_00_u03b1_2848_, lean_object* v_cmp_2849_, lean_object* v_00_u03b2_2850_, lean_object* v_t_2851_, lean_object* v_k_2852_, lean_object* v_v_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2849_, v_t_2851_, v_k_2852_, v_v_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* v_00_u03b1_2855_, lean_object* v_cmp_2856_, lean_object* v_00_u03b2_2857_, lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2856_, v_x_2858_, v_x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* v_00_u03b1_2861_, lean_object* v_00_u03b2_2862_, lean_object* v_cmp_2863_, lean_object* v_mergeFn_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2863_, v_mergeFn_2864_, v_x_2865_, v_x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* v_00_u03b1_2868_, lean_object* v_cmp_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_, lean_object* v_x_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2869_, v_x_2871_, v_x_2872_, v_x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* v_t_u2082_2875_, lean_object* v_cmp_2876_, lean_object* v_mergeFn_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_){
_start:
{
if (lean_obj_tag(v_x_2879_) == 0)
{
lean_dec(v_mergeFn_2877_);
lean_dec_ref(v_cmp_2876_);
lean_dec(v_t_u2082_2875_);
return v_x_2878_;
}
else
{
lean_object* v_lchild_2880_; lean_object* v_key_2881_; lean_object* v_val_2882_; lean_object* v_rchild_2883_; lean_object* v_val_2884_; lean_object* v___x_2885_; 
v_lchild_2880_ = lean_ctor_get(v_x_2879_, 0);
lean_inc(v_lchild_2880_);
v_key_2881_ = lean_ctor_get(v_x_2879_, 1);
lean_inc_n(v_key_2881_, 2);
v_val_2882_ = lean_ctor_get(v_x_2879_, 2);
lean_inc(v_val_2882_);
v_rchild_2883_ = lean_ctor_get(v_x_2879_, 3);
lean_inc(v_rchild_2883_);
lean_dec_ref_known(v_x_2879_, 4);
lean_inc(v_mergeFn_2877_);
lean_inc_ref_n(v_cmp_2876_, 2);
lean_inc_n(v_t_u2082_2875_, 2);
v_val_2884_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2875_, v_cmp_2876_, v_mergeFn_2877_, v_x_2878_, v_lchild_2880_);
v___x_2885_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2876_, v_t_u2082_2875_, v_key_2881_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_dec(v_val_2882_);
lean_dec(v_key_2881_);
v_x_2878_ = v_val_2884_;
v_x_2879_ = v_rchild_2883_;
goto _start;
}
else
{
lean_object* v_val_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_val_2887_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_val_2887_);
lean_dec_ref_known(v___x_2885_, 1);
lean_inc(v_mergeFn_2877_);
lean_inc(v_key_2881_);
v___x_2888_ = lean_apply_3(v_mergeFn_2877_, v_key_2881_, v_val_2882_, v_val_2887_);
lean_inc_ref(v_cmp_2876_);
v___x_2889_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2876_, v_val_2884_, v_key_2881_, v___x_2888_);
v_x_2878_ = v___x_2889_;
v_x_2879_ = v_rchild_2883_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* v_cmp_2891_, lean_object* v_mergeFn_2892_, lean_object* v_t_u2081_2893_, lean_object* v_t_u2082_2894_){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2894_, v_cmp_2891_, v_mergeFn_2892_, v___x_2895_, v_t_u2081_2893_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* v_00_u03b1_2897_, lean_object* v_00_u03b2_2898_, lean_object* v_cmp_2899_, lean_object* v_00_u03b3_2900_, lean_object* v_00_u03b4_2901_, lean_object* v_mergeFn_2902_, lean_object* v_t_u2081_2903_, lean_object* v_t_u2082_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_RBMap_intersectBy___redArg(v_cmp_2899_, v_mergeFn_2902_, v_t_u2081_2903_, v_t_u2082_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* v_00_u03b1_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_00_u03b4_2908_, lean_object* v_00_u03b3_2909_, lean_object* v_t_u2082_2910_, lean_object* v_cmp_2911_, lean_object* v_mergeFn_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2910_, v_cmp_2911_, v_mergeFn_2912_, v_x_2913_, v_x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* v_f_2916_, lean_object* v_cmp_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_){
_start:
{
if (lean_obj_tag(v_x_2919_) == 0)
{
lean_dec_ref(v_cmp_2917_);
lean_dec_ref(v_f_2916_);
return v_x_2918_;
}
else
{
lean_object* v_lchild_2920_; lean_object* v_key_2921_; lean_object* v_val_2922_; lean_object* v_rchild_2923_; lean_object* v_val_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_lchild_2920_ = lean_ctor_get(v_x_2919_, 0);
lean_inc(v_lchild_2920_);
v_key_2921_ = lean_ctor_get(v_x_2919_, 1);
lean_inc_n(v_key_2921_, 2);
v_val_2922_ = lean_ctor_get(v_x_2919_, 2);
lean_inc_n(v_val_2922_, 2);
v_rchild_2923_ = lean_ctor_get(v_x_2919_, 3);
lean_inc(v_rchild_2923_);
lean_dec_ref_known(v_x_2919_, 4);
lean_inc_ref(v_cmp_2917_);
lean_inc_ref_n(v_f_2916_, 2);
v_val_2924_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2916_, v_cmp_2917_, v_x_2918_, v_lchild_2920_);
v___x_2925_ = lean_apply_2(v_f_2916_, v_key_2921_, v_val_2922_);
v___x_2926_ = lean_unbox(v___x_2925_);
if (v___x_2926_ == 0)
{
lean_dec(v_val_2922_);
lean_dec(v_key_2921_);
v_x_2918_ = v_val_2924_;
v_x_2919_ = v_rchild_2923_;
goto _start;
}
else
{
lean_object* v___x_2928_; 
lean_inc_ref(v_cmp_2917_);
v___x_2928_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2917_, v_val_2924_, v_key_2921_, v_val_2922_);
v_x_2918_ = v___x_2928_;
v_x_2919_ = v_rchild_2923_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* v_cmp_2930_, lean_object* v_f_2931_, lean_object* v_m_2932_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_box(0);
v___x_2934_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2931_, v_cmp_2930_, v___x_2933_, v_m_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* v_00_u03b1_2935_, lean_object* v_00_u03b2_2936_, lean_object* v_cmp_2937_, lean_object* v_f_2938_, lean_object* v_m_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_RBMap_filter___redArg(v_cmp_2937_, v_f_2938_, v_m_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* v_00_u03b1_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_f_2943_, lean_object* v_cmp_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2943_, v_cmp_2944_, v_x_2945_, v_x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* v_f_2948_, lean_object* v_cmp_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
lean_dec_ref(v_cmp_2949_);
lean_dec_ref(v_f_2948_);
return v_x_2950_;
}
else
{
lean_object* v_lchild_2952_; lean_object* v_key_2953_; lean_object* v_val_2954_; lean_object* v_rchild_2955_; lean_object* v_val_2956_; lean_object* v___x_2957_; 
v_lchild_2952_ = lean_ctor_get(v_x_2951_, 0);
lean_inc(v_lchild_2952_);
v_key_2953_ = lean_ctor_get(v_x_2951_, 1);
lean_inc_n(v_key_2953_, 2);
v_val_2954_ = lean_ctor_get(v_x_2951_, 2);
lean_inc(v_val_2954_);
v_rchild_2955_ = lean_ctor_get(v_x_2951_, 3);
lean_inc(v_rchild_2955_);
lean_dec_ref_known(v_x_2951_, 4);
lean_inc_ref(v_cmp_2949_);
lean_inc_ref_n(v_f_2948_, 2);
v_val_2956_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2948_, v_cmp_2949_, v_x_2950_, v_lchild_2952_);
v___x_2957_ = lean_apply_2(v_f_2948_, v_key_2953_, v_val_2954_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_dec(v_key_2953_);
v_x_2950_ = v_val_2956_;
v_x_2951_ = v_rchild_2955_;
goto _start;
}
else
{
lean_object* v_val_2959_; lean_object* v___x_2960_; 
v_val_2959_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_val_2959_);
lean_dec_ref_known(v___x_2957_, 1);
lean_inc_ref(v_cmp_2949_);
v___x_2960_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2949_, v_val_2956_, v_key_2953_, v_val_2959_);
v_x_2950_ = v___x_2960_;
v_x_2951_ = v_rchild_2955_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* v_cmp_2962_, lean_object* v_f_2963_, lean_object* v_m_2964_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_box(0);
v___x_2966_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2963_, v_cmp_2962_, v___x_2965_, v_m_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* v_00_u03b1_2967_, lean_object* v_00_u03b2_2968_, lean_object* v_cmp_2969_, lean_object* v_00_u03b3_2970_, lean_object* v_f_2971_, lean_object* v_m_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_RBMap_filterMap___redArg(v_cmp_2969_, v_f_2971_, v_m_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* v_00_u03b1_2974_, lean_object* v_00_u03b2_2975_, lean_object* v_00_u03b3_2976_, lean_object* v_f_2977_, lean_object* v_cmp_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2977_, v_cmp_2978_, v_x_2979_, v_x_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* v_cmp_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_){
_start:
{
if (lean_obj_tag(v_x_2984_) == 0)
{
lean_dec_ref(v_cmp_2982_);
return v_x_2983_;
}
else
{
lean_object* v_head_2985_; lean_object* v_tail_2986_; lean_object* v_fst_2987_; lean_object* v_snd_2988_; lean_object* v___x_2989_; 
v_head_2985_ = lean_ctor_get(v_x_2984_, 0);
lean_inc(v_head_2985_);
v_tail_2986_ = lean_ctor_get(v_x_2984_, 1);
lean_inc(v_tail_2986_);
lean_dec_ref_known(v_x_2984_, 2);
v_fst_2987_ = lean_ctor_get(v_head_2985_, 0);
lean_inc(v_fst_2987_);
v_snd_2988_ = lean_ctor_get(v_head_2985_, 1);
lean_inc(v_snd_2988_);
lean_dec(v_head_2985_);
lean_inc_ref(v_cmp_2982_);
v___x_2989_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2982_, v_x_2983_, v_fst_2987_, v_snd_2988_);
v_x_2983_ = v___x_2989_;
v_x_2984_ = v_tail_2986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* v_l_2991_, lean_object* v_cmp_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_2992_, v___x_2993_, v_l_2991_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* v_00_u03b1_2995_, lean_object* v_00_u03b2_2996_, lean_object* v_l_2997_, lean_object* v_cmp_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_rbmapOf___redArg(v_l_2997_, v_cmp_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* v_00_u03b1_3000_, lean_object* v_00_u03b2_3001_, lean_object* v_cmp_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3002_, v_x_3003_, v_x_3004_);
return v___x_3005_;
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
