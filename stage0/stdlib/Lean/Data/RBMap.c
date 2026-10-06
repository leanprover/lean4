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
lean_object* v_a_904_; lean_object* v_kx_905_; lean_object* v_vx_906_; lean_object* v_b_907_; lean_object* v_a_911_; lean_object* v_kx_912_; lean_object* v_vx_913_; lean_object* v_b_914_; lean_object* v_ky_915_; lean_object* v_vy_916_; lean_object* v_c_917_; lean_object* v_kz_918_; lean_object* v_vz_919_; lean_object* v_d_920_; lean_object* v_l_927_; lean_object* v_k_928_; lean_object* v_v_929_; lean_object* v_a_930_; lean_object* v_ky_931_; lean_object* v_vy_932_; lean_object* v_b_933_; lean_object* v___y_952_; uint8_t v___y_953_; lean_object* v___y_954_; uint8_t v___y_955_; lean_object* v___y_956_; lean_object* v_a_957_; lean_object* v_kx_958_; lean_object* v_vx_959_; lean_object* v_b_960_; lean_object* v_ky_961_; lean_object* v_vy_962_; lean_object* v_c_963_; lean_object* v_kz_964_; lean_object* v_vz_965_; lean_object* v_d_966_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v_a_977_; lean_object* v_kx_978_; lean_object* v_vx_979_; lean_object* v_b_980_; lean_object* v_l_984_; lean_object* v_k_985_; lean_object* v_v_986_; lean_object* v_a_987_; lean_object* v_ky_988_; lean_object* v_vy_989_; lean_object* v_b_990_; lean_object* v_kz_991_; lean_object* v_vz_992_; lean_object* v_c_993_; lean_object* v_l_1025_; lean_object* v_k_1026_; lean_object* v_v_1027_; lean_object* v_r_1028_; 
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
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*4, v___y_953_);
v___x_968_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_968_, 0, v_c_963_);
lean_ctor_set(v___x_968_, 1, v_kz_964_);
lean_ctor_set(v___x_968_, 2, v_vz_965_);
lean_ctor_set(v___x_968_, 3, v_d_966_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*4, v___y_953_);
v___x_969_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v_ky_961_);
lean_ctor_set(v___x_969_, 2, v_vy_962_);
lean_ctor_set(v___x_969_, 3, v___x_968_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*4, v___y_955_);
v___x_970_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_970_, 0, v___y_956_);
lean_ctor_set(v___x_970_, 1, v___y_952_);
lean_ctor_set(v___x_970_, 2, v___y_954_);
lean_ctor_set(v___x_970_, 3, v___x_969_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*4, v___y_955_);
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
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*4, v___y_973_);
v___x_982_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_982_, 0, v___y_976_);
lean_ctor_set(v___x_982_, 1, v___y_972_);
lean_ctor_set(v___x_982_, 2, v___y_974_);
lean_ctor_set(v___x_982_, 3, v___x_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*4, v___y_975_);
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
v___y_952_ = v_ky_988_;
v___y_953_ = v___x_995_;
v___y_954_ = v_vy_989_;
v___y_955_ = v___x_994_;
v___y_956_ = v___x_996_;
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
v___y_952_ = v_ky_988_;
v___y_953_ = v___x_995_;
v___y_954_ = v_vy_989_;
v___y_955_ = v___x_994_;
v___y_956_ = v___x_996_;
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
v___y_972_ = v_ky_988_;
v___y_973_ = v___x_995_;
v___y_974_ = v_vy_989_;
v___y_975_ = v___x_994_;
v___y_976_ = v___x_996_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v_ky_988_;
v___y_973_ = v___x_995_;
v___y_974_ = v_vy_989_;
v___y_975_ = v___x_994_;
v___y_976_ = v___x_996_;
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
v___y_952_ = v_ky_988_;
v___y_953_ = v___x_995_;
v___y_954_ = v_vy_989_;
v___y_955_ = v___x_994_;
v___y_956_ = v___x_996_;
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
v___y_972_ = v_ky_988_;
v___y_973_ = v___x_995_;
v___y_974_ = v_vy_989_;
v___y_975_ = v___x_994_;
v___y_976_ = v___x_996_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v_ky_988_;
v___y_973_ = v___x_995_;
v___y_974_ = v_vy_989_;
v___y_975_ = v___x_994_;
v___y_976_ = v___x_996_;
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
v___y_972_ = v_ky_988_;
v___y_973_ = v___x_995_;
v___y_974_ = v_vy_989_;
v___y_975_ = v___x_994_;
v___y_976_ = v___x_996_;
v_a_977_ = v_b_990_;
v_kx_978_ = v_kz_991_;
v_vx_979_ = v_vz_992_;
v_b_980_ = v___x_997_;
goto v___jp_971_;
}
}
else
{
v___y_972_ = v_ky_988_;
v___y_973_ = v___x_995_;
v___y_974_ = v_vy_989_;
v___y_975_ = v___x_994_;
v___y_976_ = v___x_996_;
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
uint8_t v___y_1088_; lean_object* v_a_1089_; lean_object* v_kx_1090_; lean_object* v_vx_1091_; lean_object* v_b_1092_; lean_object* v_ky_1093_; lean_object* v_vy_1094_; lean_object* v_c_1095_; lean_object* v_kz_1096_; lean_object* v_vz_1097_; lean_object* v_d_1098_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___y_1107_; uint8_t v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; uint8_t v___y_1116_; uint8_t v___y_1117_; lean_object* v_a_1118_; lean_object* v_kx_1119_; lean_object* v_vx_1120_; lean_object* v_b_1121_; lean_object* v_ky_1122_; lean_object* v_vy_1123_; lean_object* v_c_1124_; lean_object* v_kz_1125_; lean_object* v_vz_1126_; lean_object* v_d_1127_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; uint8_t v___y_1136_; lean_object* v_a_1137_; lean_object* v_kx_1138_; lean_object* v_vx_1139_; lean_object* v_b_1140_; 
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
lean_ctor_set(v___x_1110_, 0, v___y_1106_);
lean_ctor_set(v___x_1110_, 1, v_k_1081_);
lean_ctor_set(v___x_1110_, 2, v_v_1082_);
lean_ctor_set(v___x_1110_, 3, v_r_1083_);
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*4, v___y_1108_);
v___x_1111_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1111_, 0, v___y_1109_);
lean_ctor_set(v___x_1111_, 1, v___y_1105_);
lean_ctor_set(v___x_1111_, 2, v___y_1104_);
lean_ctor_set(v___x_1111_, 3, v___x_1110_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*4, v___y_1107_);
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
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*4, v___y_1117_);
v___x_1129_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1129_, 0, v_c_1124_);
lean_ctor_set(v___x_1129_, 1, v_kz_1125_);
lean_ctor_set(v___x_1129_, 2, v_vz_1126_);
lean_ctor_set(v___x_1129_, 3, v_d_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*4, v___y_1117_);
v___x_1130_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v_ky_1122_);
lean_ctor_set(v___x_1130_, 2, v_vy_1123_);
lean_ctor_set(v___x_1130_, 3, v___x_1129_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*4, v___y_1116_);
v___y_1104_ = v___y_1113_;
v___y_1105_ = v___y_1114_;
v___y_1106_ = v___y_1115_;
v___y_1107_ = v___y_1116_;
v___y_1108_ = v___y_1117_;
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
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*4, v___y_1136_);
v___y_1104_ = v___y_1132_;
v___y_1105_ = v___y_1133_;
v___y_1106_ = v___y_1134_;
v___y_1107_ = v___y_1135_;
v___y_1108_ = v___y_1136_;
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
v___y_1113_ = v_val_1151_;
v___y_1114_ = v_key_1150_;
v___y_1115_ = v_rchild_1152_;
v___y_1116_ = v_color_1143_;
v___y_1117_ = v_color_1145_;
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
v___y_1113_ = v_val_1151_;
v___y_1114_ = v_key_1150_;
v___y_1115_ = v_rchild_1152_;
v___y_1116_ = v_color_1143_;
v___y_1117_ = v_color_1145_;
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
v___y_1132_ = v_val_1151_;
v___y_1133_ = v_key_1150_;
v___y_1134_ = v_rchild_1152_;
v___y_1135_ = v_color_1143_;
v___y_1136_ = v_color_1145_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
v___y_1132_ = v_val_1151_;
v___y_1133_ = v_key_1150_;
v___y_1134_ = v_rchild_1152_;
v___y_1135_ = v_color_1143_;
v___y_1136_ = v_color_1145_;
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
v___y_1113_ = v_val_1151_;
v___y_1114_ = v_key_1150_;
v___y_1115_ = v_rchild_1152_;
v___y_1116_ = v_color_1143_;
v___y_1117_ = v_color_1145_;
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
v___y_1132_ = v_val_1151_;
v___y_1133_ = v_key_1150_;
v___y_1134_ = v_rchild_1152_;
v___y_1135_ = v_color_1143_;
v___y_1136_ = v_color_1145_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
v___y_1132_ = v_val_1151_;
v___y_1133_ = v_key_1150_;
v___y_1134_ = v_rchild_1152_;
v___y_1135_ = v_color_1143_;
v___y_1136_ = v_color_1145_;
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
v___y_1132_ = v_val_1151_;
v___y_1133_ = v_key_1150_;
v___y_1134_ = v_rchild_1152_;
v___y_1135_ = v_color_1143_;
v___y_1136_ = v_color_1145_;
v_a_1137_ = v___x_1153_;
v_kx_1138_ = v_key_1147_;
v_vx_1139_ = v_val_1148_;
v_b_1140_ = v_lchild_1149_;
goto v___jp_1131_;
}
}
else
{
v___y_1132_ = v_val_1151_;
v___y_1133_ = v_key_1150_;
v___y_1134_ = v_rchild_1152_;
v___y_1135_ = v_color_1143_;
v___y_1136_ = v_color_1145_;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter___redArg(lean_object* v_x_1281_, lean_object* v_h__1_1282_, lean_object* v_h__2_1283_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_h__2_1283_);
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_apply_1(v_h__1_1282_, v___x_1284_);
return v___x_1285_;
}
else
{
uint8_t v_color_1286_; lean_object* v_lchild_1287_; lean_object* v_key_1288_; lean_object* v_val_1289_; lean_object* v_rchild_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec(v_h__1_1282_);
v_color_1286_ = lean_ctor_get_uint8(v_x_1281_, sizeof(void*)*4);
v_lchild_1287_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_lchild_1287_);
v_key_1288_ = lean_ctor_get(v_x_1281_, 1);
lean_inc(v_key_1288_);
v_val_1289_ = lean_ctor_get(v_x_1281_, 2);
lean_inc(v_val_1289_);
v_rchild_1290_ = lean_ctor_get(v_x_1281_, 3);
lean_inc(v_rchild_1290_);
lean_dec_ref_known(v_x_1281_, 4);
v___x_1291_ = lean_box(v_color_1286_);
v___x_1292_ = lean_apply_5(v_h__2_1283_, v___x_1291_, v_lchild_1287_, v_key_1288_, v_val_1289_, v_rchild_1290_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_depth_match__1_splitter(lean_object* v_00_u03b1_1293_, lean_object* v_00_u03b2_1294_, lean_object* v_motive_1295_, lean_object* v_x_1296_, lean_object* v_h__1_1297_, lean_object* v_h__2_1298_){
_start:
{
if (lean_obj_tag(v_x_1296_) == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_h__2_1298_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_apply_1(v_h__1_1297_, v___x_1299_);
return v___x_1300_;
}
else
{
uint8_t v_color_1301_; lean_object* v_lchild_1302_; lean_object* v_key_1303_; lean_object* v_val_1304_; lean_object* v_rchild_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v_h__1_1297_);
v_color_1301_ = lean_ctor_get_uint8(v_x_1296_, sizeof(void*)*4);
v_lchild_1302_ = lean_ctor_get(v_x_1296_, 0);
lean_inc(v_lchild_1302_);
v_key_1303_ = lean_ctor_get(v_x_1296_, 1);
lean_inc(v_key_1303_);
v_val_1304_ = lean_ctor_get(v_x_1296_, 2);
lean_inc(v_val_1304_);
v_rchild_1305_ = lean_ctor_get(v_x_1296_, 3);
lean_inc(v_rchild_1305_);
lean_dec_ref_known(v_x_1296_, 4);
v___x_1306_ = lean_box(v_color_1301_);
v___x_1307_ = lean_apply_5(v_h__2_1298_, v___x_1306_, v_lchild_1302_, v_key_1303_, v_val_1304_, v_rchild_1305_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1308_) == 0)
{
return v_x_1309_;
}
else
{
if (lean_obj_tag(v_x_1309_) == 0)
{
return v_x_1308_;
}
else
{
uint8_t v_color_1310_; lean_object* v_lchild_1311_; lean_object* v_key_1312_; lean_object* v_val_1313_; lean_object* v_rchild_1314_; uint8_t v_color_1315_; lean_object* v_lchild_1316_; lean_object* v_key_1317_; lean_object* v_val_1318_; lean_object* v_rchild_1319_; lean_object* v_bc_1321_; lean_object* v_bc_1325_; 
v_color_1310_ = lean_ctor_get_uint8(v_x_1308_, sizeof(void*)*4);
v_lchild_1311_ = lean_ctor_get(v_x_1308_, 0);
v_key_1312_ = lean_ctor_get(v_x_1308_, 1);
v_val_1313_ = lean_ctor_get(v_x_1308_, 2);
v_rchild_1314_ = lean_ctor_get(v_x_1308_, 3);
v_color_1315_ = lean_ctor_get_uint8(v_x_1309_, sizeof(void*)*4);
v_lchild_1316_ = lean_ctor_get(v_x_1309_, 0);
v_key_1317_ = lean_ctor_get(v_x_1309_, 1);
v_val_1318_ = lean_ctor_get(v_x_1309_, 2);
v_rchild_1319_ = lean_ctor_get(v_x_1309_, 3);
if (v_color_1315_ == 0)
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1362_; 
lean_inc(v_rchild_1319_);
lean_inc(v_val_1318_);
lean_inc(v_key_1317_);
lean_inc(v_lchild_1316_);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; lean_object* v_unused_1366_; 
v_unused_1363_ = lean_ctor_get(v_x_1309_, 3);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_x_1309_, 2);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_x_1309_, 1);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_x_1309_, 0);
lean_dec(v_unused_1366_);
v___x_1329_ = v_x_1309_;
v_isShared_1330_ = v_isSharedCheck_1362_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v_x_1309_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1362_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
if (v_color_1310_ == 0)
{
lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1353_; 
lean_inc(v_rchild_1314_);
lean_inc(v_val_1313_);
lean_inc(v_key_1312_);
lean_inc(v_lchild_1311_);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1308_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; lean_object* v_unused_1357_; 
v_unused_1354_ = lean_ctor_get(v_x_1308_, 3);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_x_1308_, 2);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_x_1308_, 1);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_x_1308_, 0);
lean_dec(v_unused_1357_);
v___x_1332_ = v_x_1308_;
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v_x_1308_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1314_, v_lchild_1316_);
if (lean_obj_tag(v___x_1334_) == 1)
{
uint8_t v_color_1335_; 
v_color_1335_ = lean_ctor_get_uint8(v___x_1334_, sizeof(void*)*4);
if (v_color_1335_ == 0)
{
lean_object* v_lchild_1336_; lean_object* v_key_1337_; lean_object* v_val_1338_; lean_object* v_rchild_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1352_; 
v_lchild_1336_ = lean_ctor_get(v___x_1334_, 0);
v_key_1337_ = lean_ctor_get(v___x_1334_, 1);
v_val_1338_ = lean_ctor_get(v___x_1334_, 2);
v_rchild_1339_ = lean_ctor_get(v___x_1334_, 3);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1341_ = v___x_1334_;
v_isShared_1342_ = v_isSharedCheck_1352_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_rchild_1339_);
lean_inc(v_val_1338_);
lean_inc(v_key_1337_);
lean_inc(v_lchild_1336_);
lean_dec(v___x_1334_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1352_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 3, v_lchild_1336_);
lean_ctor_set(v___x_1341_, 2, v_val_1313_);
lean_ctor_set(v___x_1341_, 1, v_key_1312_);
lean_ctor_set(v___x_1341_, 0, v_lchild_1311_);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_lchild_1311_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_key_1312_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_val_1313_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_lchild_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*4, v_color_1335_);
v___x_1344_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_rchild_1339_);
v___x_1346_ = v___x_1329_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_rchild_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_key_1317_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_val_1318_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_rchild_1319_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*4, v_color_1335_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 3, v___x_1346_);
lean_ctor_set(v___x_1332_, 2, v_val_1338_);
lean_ctor_set(v___x_1332_, 1, v_key_1337_);
lean_ctor_set(v___x_1332_, 0, v___x_1344_);
v___x_1348_ = v___x_1332_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_key_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_val_1338_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*4, v_color_1335_);
return v___x_1348_;
}
}
}
}
}
else
{
lean_del_object(v___x_1332_);
lean_del_object(v___x_1329_);
v_bc_1325_ = v___x_1334_;
goto v___jp_1324_;
}
}
else
{
lean_del_object(v___x_1332_);
lean_del_object(v___x_1329_);
v_bc_1325_ = v___x_1334_;
goto v___jp_1324_;
}
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = l_Lean_RBNode_appendTrees___redArg(v_x_1308_, v_lchild_1316_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1358_);
v___x_1360_ = v___x_1329_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_key_1317_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_val_1318_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_rchild_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, sizeof(void*)*4, v_color_1315_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1401_; 
lean_inc(v_rchild_1314_);
lean_inc(v_val_1313_);
lean_inc(v_key_1312_);
lean_inc(v_lchild_1311_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_x_1308_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1402_ = lean_ctor_get(v_x_1308_, 3);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_x_1308_, 2);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_x_1308_, 1);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_x_1308_, 0);
lean_dec(v_unused_1405_);
v___x_1368_ = v_x_1308_;
v_isShared_1369_ = v_isSharedCheck_1401_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v_x_1308_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1401_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
if (v_color_1310_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1314_, v_x_1309_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 3, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_lchild_1311_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_key_1312_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_val_1313_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v___x_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1373_, sizeof(void*)*4, v_color_1310_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1396_; 
lean_inc(v_rchild_1319_);
lean_inc(v_val_1318_);
lean_inc(v_key_1317_);
lean_inc(v_lchild_1316_);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_x_1309_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1397_ = lean_ctor_get(v_x_1309_, 3);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_x_1309_, 2);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_x_1309_, 1);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_x_1309_, 0);
lean_dec(v_unused_1400_);
v___x_1375_ = v_x_1309_;
v_isShared_1376_ = v_isSharedCheck_1396_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v_x_1309_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1396_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_RBNode_appendTrees___redArg(v_rchild_1314_, v_lchild_1316_);
if (lean_obj_tag(v___x_1377_) == 1)
{
uint8_t v_color_1378_; 
v_color_1378_ = lean_ctor_get_uint8(v___x_1377_, sizeof(void*)*4);
if (v_color_1378_ == 0)
{
lean_object* v_lchild_1379_; lean_object* v_key_1380_; lean_object* v_val_1381_; lean_object* v_rchild_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1395_; 
v_lchild_1379_ = lean_ctor_get(v___x_1377_, 0);
v_key_1380_ = lean_ctor_get(v___x_1377_, 1);
v_val_1381_ = lean_ctor_get(v___x_1377_, 2);
v_rchild_1382_ = lean_ctor_get(v___x_1377_, 3);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1384_ = v___x_1377_;
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_rchild_1382_);
lean_inc(v_val_1381_);
lean_inc(v_key_1380_);
lean_inc(v_lchild_1379_);
lean_dec(v___x_1377_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 3, v_lchild_1379_);
lean_ctor_set(v___x_1384_, 2, v_val_1313_);
lean_ctor_set(v___x_1384_, 1, v_key_1312_);
lean_ctor_set(v___x_1384_, 0, v_lchild_1311_);
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_lchild_1311_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_key_1312_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_val_1313_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_lchild_1379_);
v___x_1387_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*4, v_color_1310_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_rchild_1382_);
v___x_1389_ = v___x_1375_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_rchild_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_key_1317_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_val_1318_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_rchild_1319_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*4, v_color_1310_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 3, v___x_1389_);
lean_ctor_set(v___x_1368_, 2, v_val_1381_);
lean_ctor_set(v___x_1368_, 1, v_key_1380_);
lean_ctor_set(v___x_1368_, 0, v___x_1387_);
v___x_1391_ = v___x_1368_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_key_1380_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_val_1381_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*4, v_color_1378_);
return v___x_1391_;
}
}
}
}
}
else
{
lean_del_object(v___x_1375_);
lean_del_object(v___x_1368_);
v_bc_1321_ = v___x_1377_;
goto v___jp_1320_;
}
}
else
{
lean_del_object(v___x_1375_);
lean_del_object(v___x_1368_);
v_bc_1321_ = v___x_1377_;
goto v___jp_1320_;
}
}
}
}
}
v___jp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1322_, 0, v_bc_1321_);
lean_ctor_set(v___x_1322_, 1, v_key_1317_);
lean_ctor_set(v___x_1322_, 2, v_val_1318_);
lean_ctor_set(v___x_1322_, 3, v_rchild_1319_);
lean_ctor_set_uint8(v___x_1322_, sizeof(void*)*4, v_color_1310_);
v___x_1323_ = l_Lean_RBNode_balLeft___redArg(v_lchild_1311_, v_key_1312_, v_val_1313_, v___x_1322_);
return v___x_1323_;
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1326_, 0, v_bc_1325_);
lean_ctor_set(v___x_1326_, 1, v_key_1317_);
lean_ctor_set(v___x_1326_, 2, v_val_1318_);
lean_ctor_set(v___x_1326_, 3, v_rchild_1319_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*4, v_color_1310_);
v___x_1327_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1327_, 0, v_lchild_1311_);
lean_ctor_set(v___x_1327_, 1, v_key_1312_);
lean_ctor_set(v___x_1327_, 2, v_val_1313_);
lean_ctor_set(v___x_1327_, 3, v___x_1326_);
lean_ctor_set_uint8(v___x_1327_, sizeof(void*)*4, v_color_1310_);
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_appendTrees(lean_object* v_00_u03b1_1406_, lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_RBNode_appendTrees___redArg(v_x_1408_, v_x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter___redArg(lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_h__1_1413_, lean_object* v_h__2_1414_, lean_object* v_h__3_1415_, lean_object* v_h__4_1416_, lean_object* v_h__5_1417_, lean_object* v_h__6_1418_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v___x_1419_; 
lean_dec(v_h__6_1418_);
lean_dec(v_h__5_1417_);
lean_dec(v_h__4_1416_);
lean_dec(v_h__3_1415_);
lean_dec(v_h__2_1414_);
v___x_1419_ = lean_apply_1(v_h__1_1413_, v_x_1412_);
return v___x_1419_;
}
else
{
lean_dec(v_h__1_1413_);
if (lean_obj_tag(v_x_1412_) == 0)
{
lean_object* v___x_1420_; 
lean_dec(v_h__6_1418_);
lean_dec(v_h__5_1417_);
lean_dec(v_h__4_1416_);
lean_dec(v_h__3_1415_);
v___x_1420_ = lean_apply_2(v_h__2_1414_, v_x_1411_, lean_box(0));
return v___x_1420_;
}
else
{
uint8_t v_color_1421_; 
lean_dec(v_h__2_1414_);
v_color_1421_ = lean_ctor_get_uint8(v_x_1412_, sizeof(void*)*4);
if (v_color_1421_ == 0)
{
uint8_t v_color_1422_; 
lean_dec(v_h__6_1418_);
lean_dec(v_h__4_1416_);
v_color_1422_ = lean_ctor_get_uint8(v_x_1411_, sizeof(void*)*4);
if (v_color_1422_ == 0)
{
lean_object* v_lchild_1423_; lean_object* v_key_1424_; lean_object* v_val_1425_; lean_object* v_rchild_1426_; lean_object* v_lchild_1427_; lean_object* v_key_1428_; lean_object* v_val_1429_; lean_object* v_rchild_1430_; lean_object* v___x_1431_; 
lean_dec(v_h__5_1417_);
v_lchild_1423_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_lchild_1423_);
v_key_1424_ = lean_ctor_get(v_x_1411_, 1);
lean_inc(v_key_1424_);
v_val_1425_ = lean_ctor_get(v_x_1411_, 2);
lean_inc(v_val_1425_);
v_rchild_1426_ = lean_ctor_get(v_x_1411_, 3);
lean_inc(v_rchild_1426_);
lean_dec_ref_known(v_x_1411_, 4);
v_lchild_1427_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_lchild_1427_);
v_key_1428_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_key_1428_);
v_val_1429_ = lean_ctor_get(v_x_1412_, 2);
lean_inc(v_val_1429_);
v_rchild_1430_ = lean_ctor_get(v_x_1412_, 3);
lean_inc(v_rchild_1430_);
lean_dec_ref_known(v_x_1412_, 4);
v___x_1431_ = lean_apply_8(v_h__3_1415_, v_lchild_1423_, v_key_1424_, v_val_1425_, v_rchild_1426_, v_lchild_1427_, v_key_1428_, v_val_1429_, v_rchild_1430_);
return v___x_1431_;
}
else
{
lean_object* v_lchild_1432_; lean_object* v_key_1433_; lean_object* v_val_1434_; lean_object* v_rchild_1435_; lean_object* v___x_1436_; 
lean_dec(v_h__3_1415_);
v_lchild_1432_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_lchild_1432_);
v_key_1433_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_key_1433_);
v_val_1434_ = lean_ctor_get(v_x_1412_, 2);
lean_inc(v_val_1434_);
v_rchild_1435_ = lean_ctor_get(v_x_1412_, 3);
lean_inc(v_rchild_1435_);
lean_dec_ref_known(v_x_1412_, 4);
v___x_1436_ = lean_apply_7(v_h__5_1417_, v_x_1411_, v_lchild_1432_, v_key_1433_, v_val_1434_, v_rchild_1435_, lean_box(0), lean_box(0));
return v___x_1436_;
}
}
else
{
uint8_t v_color_1437_; 
lean_dec(v_h__5_1417_);
lean_dec(v_h__3_1415_);
v_color_1437_ = lean_ctor_get_uint8(v_x_1411_, sizeof(void*)*4);
if (v_color_1437_ == 0)
{
lean_object* v_lchild_1438_; lean_object* v_key_1439_; lean_object* v_val_1440_; lean_object* v_rchild_1441_; lean_object* v___x_1442_; 
lean_dec(v_h__4_1416_);
v_lchild_1438_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_lchild_1438_);
v_key_1439_ = lean_ctor_get(v_x_1411_, 1);
lean_inc(v_key_1439_);
v_val_1440_ = lean_ctor_get(v_x_1411_, 2);
lean_inc(v_val_1440_);
v_rchild_1441_ = lean_ctor_get(v_x_1411_, 3);
lean_inc(v_rchild_1441_);
lean_dec_ref_known(v_x_1411_, 4);
v___x_1442_ = lean_apply_7(v_h__6_1418_, v_lchild_1438_, v_key_1439_, v_val_1440_, v_rchild_1441_, v_x_1412_, lean_box(0), lean_box(0));
return v___x_1442_;
}
else
{
lean_object* v_lchild_1443_; lean_object* v_key_1444_; lean_object* v_val_1445_; lean_object* v_rchild_1446_; lean_object* v_lchild_1447_; lean_object* v_key_1448_; lean_object* v_val_1449_; lean_object* v_rchild_1450_; lean_object* v___x_1451_; 
lean_dec(v_h__6_1418_);
v_lchild_1443_ = lean_ctor_get(v_x_1411_, 0);
lean_inc(v_lchild_1443_);
v_key_1444_ = lean_ctor_get(v_x_1411_, 1);
lean_inc(v_key_1444_);
v_val_1445_ = lean_ctor_get(v_x_1411_, 2);
lean_inc(v_val_1445_);
v_rchild_1446_ = lean_ctor_get(v_x_1411_, 3);
lean_inc(v_rchild_1446_);
lean_dec_ref_known(v_x_1411_, 4);
v_lchild_1447_ = lean_ctor_get(v_x_1412_, 0);
lean_inc(v_lchild_1447_);
v_key_1448_ = lean_ctor_get(v_x_1412_, 1);
lean_inc(v_key_1448_);
v_val_1449_ = lean_ctor_get(v_x_1412_, 2);
lean_inc(v_val_1449_);
v_rchild_1450_ = lean_ctor_get(v_x_1412_, 3);
lean_inc(v_rchild_1450_);
lean_dec_ref_known(v_x_1412_, 4);
v___x_1451_ = lean_apply_8(v_h__4_1416_, v_lchild_1443_, v_key_1444_, v_val_1445_, v_rchild_1446_, v_lchild_1447_, v_key_1448_, v_val_1449_, v_rchild_1450_);
return v___x_1451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_appendTrees_match__1_splitter(lean_object* v_00_u03b1_1452_, lean_object* v_00_u03b2_1453_, lean_object* v_motive_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_h__1_1457_, lean_object* v_h__2_1458_, lean_object* v_h__3_1459_, lean_object* v_h__4_1460_, lean_object* v_h__5_1461_, lean_object* v_h__6_1462_){
_start:
{
if (lean_obj_tag(v_x_1455_) == 0)
{
lean_object* v___x_1463_; 
lean_dec(v_h__6_1462_);
lean_dec(v_h__5_1461_);
lean_dec(v_h__4_1460_);
lean_dec(v_h__3_1459_);
lean_dec(v_h__2_1458_);
v___x_1463_ = lean_apply_1(v_h__1_1457_, v_x_1456_);
return v___x_1463_;
}
else
{
lean_dec(v_h__1_1457_);
if (lean_obj_tag(v_x_1456_) == 0)
{
lean_object* v___x_1464_; 
lean_dec(v_h__6_1462_);
lean_dec(v_h__5_1461_);
lean_dec(v_h__4_1460_);
lean_dec(v_h__3_1459_);
v___x_1464_ = lean_apply_2(v_h__2_1458_, v_x_1455_, lean_box(0));
return v___x_1464_;
}
else
{
uint8_t v_color_1465_; 
lean_dec(v_h__2_1458_);
v_color_1465_ = lean_ctor_get_uint8(v_x_1456_, sizeof(void*)*4);
if (v_color_1465_ == 0)
{
uint8_t v_color_1466_; 
lean_dec(v_h__6_1462_);
lean_dec(v_h__4_1460_);
v_color_1466_ = lean_ctor_get_uint8(v_x_1455_, sizeof(void*)*4);
if (v_color_1466_ == 0)
{
lean_object* v_lchild_1467_; lean_object* v_key_1468_; lean_object* v_val_1469_; lean_object* v_rchild_1470_; lean_object* v_lchild_1471_; lean_object* v_key_1472_; lean_object* v_val_1473_; lean_object* v_rchild_1474_; lean_object* v___x_1475_; 
lean_dec(v_h__5_1461_);
v_lchild_1467_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_lchild_1467_);
v_key_1468_ = lean_ctor_get(v_x_1455_, 1);
lean_inc(v_key_1468_);
v_val_1469_ = lean_ctor_get(v_x_1455_, 2);
lean_inc(v_val_1469_);
v_rchild_1470_ = lean_ctor_get(v_x_1455_, 3);
lean_inc(v_rchild_1470_);
lean_dec_ref_known(v_x_1455_, 4);
v_lchild_1471_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_lchild_1471_);
v_key_1472_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_key_1472_);
v_val_1473_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_val_1473_);
v_rchild_1474_ = lean_ctor_get(v_x_1456_, 3);
lean_inc(v_rchild_1474_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1475_ = lean_apply_8(v_h__3_1459_, v_lchild_1467_, v_key_1468_, v_val_1469_, v_rchild_1470_, v_lchild_1471_, v_key_1472_, v_val_1473_, v_rchild_1474_);
return v___x_1475_;
}
else
{
lean_object* v_lchild_1476_; lean_object* v_key_1477_; lean_object* v_val_1478_; lean_object* v_rchild_1479_; lean_object* v___x_1480_; 
lean_dec(v_h__3_1459_);
v_lchild_1476_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_lchild_1476_);
v_key_1477_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_key_1477_);
v_val_1478_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_val_1478_);
v_rchild_1479_ = lean_ctor_get(v_x_1456_, 3);
lean_inc(v_rchild_1479_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1480_ = lean_apply_7(v_h__5_1461_, v_x_1455_, v_lchild_1476_, v_key_1477_, v_val_1478_, v_rchild_1479_, lean_box(0), lean_box(0));
return v___x_1480_;
}
}
else
{
uint8_t v_color_1481_; 
lean_dec(v_h__5_1461_);
lean_dec(v_h__3_1459_);
v_color_1481_ = lean_ctor_get_uint8(v_x_1455_, sizeof(void*)*4);
if (v_color_1481_ == 0)
{
lean_object* v_lchild_1482_; lean_object* v_key_1483_; lean_object* v_val_1484_; lean_object* v_rchild_1485_; lean_object* v___x_1486_; 
lean_dec(v_h__4_1460_);
v_lchild_1482_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_lchild_1482_);
v_key_1483_ = lean_ctor_get(v_x_1455_, 1);
lean_inc(v_key_1483_);
v_val_1484_ = lean_ctor_get(v_x_1455_, 2);
lean_inc(v_val_1484_);
v_rchild_1485_ = lean_ctor_get(v_x_1455_, 3);
lean_inc(v_rchild_1485_);
lean_dec_ref_known(v_x_1455_, 4);
v___x_1486_ = lean_apply_7(v_h__6_1462_, v_lchild_1482_, v_key_1483_, v_val_1484_, v_rchild_1485_, v_x_1456_, lean_box(0), lean_box(0));
return v___x_1486_;
}
else
{
lean_object* v_lchild_1487_; lean_object* v_key_1488_; lean_object* v_val_1489_; lean_object* v_rchild_1490_; lean_object* v_lchild_1491_; lean_object* v_key_1492_; lean_object* v_val_1493_; lean_object* v_rchild_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__6_1462_);
v_lchild_1487_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_lchild_1487_);
v_key_1488_ = lean_ctor_get(v_x_1455_, 1);
lean_inc(v_key_1488_);
v_val_1489_ = lean_ctor_get(v_x_1455_, 2);
lean_inc(v_val_1489_);
v_rchild_1490_ = lean_ctor_get(v_x_1455_, 3);
lean_inc(v_rchild_1490_);
lean_dec_ref_known(v_x_1455_, 4);
v_lchild_1491_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_lchild_1491_);
v_key_1492_ = lean_ctor_get(v_x_1456_, 1);
lean_inc(v_key_1492_);
v_val_1493_ = lean_ctor_get(v_x_1456_, 2);
lean_inc(v_val_1493_);
v_rchild_1494_ = lean_ctor_get(v_x_1456_, 3);
lean_inc(v_rchild_1494_);
lean_dec_ref_known(v_x_1456_, 4);
v___x_1495_ = lean_apply_8(v_h__4_1460_, v_lchild_1487_, v_key_1488_, v_val_1489_, v_rchild_1490_, v_lchild_1491_, v_key_1492_, v_val_1493_, v_rchild_1494_);
return v___x_1495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter___redArg(lean_object* v_x_1496_, lean_object* v_h__1_1497_, lean_object* v_h__2_1498_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 1)
{
uint8_t v_color_1499_; 
v_color_1499_ = lean_ctor_get_uint8(v_x_1496_, sizeof(void*)*4);
if (v_color_1499_ == 0)
{
lean_object* v_lchild_1500_; lean_object* v_key_1501_; lean_object* v_val_1502_; lean_object* v_rchild_1503_; lean_object* v___x_1504_; 
lean_dec(v_h__2_1498_);
v_lchild_1500_ = lean_ctor_get(v_x_1496_, 0);
lean_inc(v_lchild_1500_);
v_key_1501_ = lean_ctor_get(v_x_1496_, 1);
lean_inc(v_key_1501_);
v_val_1502_ = lean_ctor_get(v_x_1496_, 2);
lean_inc(v_val_1502_);
v_rchild_1503_ = lean_ctor_get(v_x_1496_, 3);
lean_inc(v_rchild_1503_);
lean_dec_ref_known(v_x_1496_, 4);
v___x_1504_ = lean_apply_4(v_h__1_1497_, v_lchild_1500_, v_key_1501_, v_val_1502_, v_rchild_1503_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_h__1_1497_);
v___x_1505_ = lean_apply_2(v_h__2_1498_, v_x_1496_, lean_box(0));
return v___x_1505_;
}
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_h__1_1497_);
v___x_1506_ = lean_apply_2(v_h__2_1498_, v_x_1496_, lean_box(0));
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_isRed_match__1_splitter(lean_object* v_00_u03b1_1507_, lean_object* v_00_u03b2_1508_, lean_object* v_motive_1509_, lean_object* v_x_1510_, lean_object* v_h__1_1511_, lean_object* v_h__2_1512_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 1)
{
uint8_t v_color_1513_; 
v_color_1513_ = lean_ctor_get_uint8(v_x_1510_, sizeof(void*)*4);
if (v_color_1513_ == 0)
{
lean_object* v_lchild_1514_; lean_object* v_key_1515_; lean_object* v_val_1516_; lean_object* v_rchild_1517_; lean_object* v___x_1518_; 
lean_dec(v_h__2_1512_);
v_lchild_1514_ = lean_ctor_get(v_x_1510_, 0);
lean_inc(v_lchild_1514_);
v_key_1515_ = lean_ctor_get(v_x_1510_, 1);
lean_inc(v_key_1515_);
v_val_1516_ = lean_ctor_get(v_x_1510_, 2);
lean_inc(v_val_1516_);
v_rchild_1517_ = lean_ctor_get(v_x_1510_, 3);
lean_inc(v_rchild_1517_);
lean_dec_ref_known(v_x_1510_, 4);
v___x_1518_ = lean_apply_4(v_h__1_1511_, v_lchild_1514_, v_key_1515_, v_val_1516_, v_rchild_1517_);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; 
lean_dec(v_h__1_1511_);
v___x_1519_ = lean_apply_2(v_h__2_1512_, v_x_1510_, lean_box(0));
return v___x_1519_;
}
}
else
{
lean_object* v___x_1520_; 
lean_dec(v_h__1_1511_);
v___x_1520_ = lean_apply_2(v_h__2_1512_, v_x_1510_, lean_box(0));
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___redArg(lean_object* v_cmp_1521_, lean_object* v_x_1522_, lean_object* v_x_1523_){
_start:
{
if (lean_obj_tag(v_x_1523_) == 0)
{
lean_dec(v_x_1522_);
lean_dec_ref(v_cmp_1521_);
return v_x_1523_;
}
else
{
lean_object* v_lchild_1524_; lean_object* v_key_1525_; lean_object* v_val_1526_; lean_object* v_rchild_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1550_; 
v_lchild_1524_ = lean_ctor_get(v_x_1523_, 0);
v_key_1525_ = lean_ctor_get(v_x_1523_, 1);
v_val_1526_ = lean_ctor_get(v_x_1523_, 2);
v_rchild_1527_ = lean_ctor_get(v_x_1523_, 3);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1529_ = v_x_1523_;
v_isShared_1530_ = v_isSharedCheck_1550_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_rchild_1527_);
lean_inc(v_val_1526_);
lean_inc(v_key_1525_);
lean_inc(v_lchild_1524_);
lean_dec(v_x_1523_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1550_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; uint8_t v___x_1532_; 
lean_inc_ref(v_cmp_1521_);
lean_inc(v_key_1525_);
lean_inc(v_x_1522_);
v___x_1531_ = lean_apply_2(v_cmp_1521_, v_x_1522_, v_key_1525_);
v___x_1532_ = lean_unbox(v___x_1531_);
switch(v___x_1532_)
{
case 0:
{
uint8_t v___x_1533_; 
v___x_1533_ = l_Lean_RBNode_isBlack___redArg(v_lchild_1524_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1534_ = 0;
v___x_1535_ = l_Lean_RBNode_del___redArg(v_cmp_1521_, v_x_1522_, v_lchild_1524_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1535_);
v___x_1537_ = v___x_1529_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_key_1525_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_val_1526_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_rchild_1527_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*4, v___x_1534_);
return v___x_1537_;
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_del_object(v___x_1529_);
v___x_1539_ = l_Lean_RBNode_del___redArg(v_cmp_1521_, v_x_1522_, v_lchild_1524_);
v___x_1540_ = l_Lean_RBNode_balLeft___redArg(v___x_1539_, v_key_1525_, v_val_1526_, v_rchild_1527_);
return v___x_1540_;
}
}
case 1:
{
lean_object* v___x_1541_; 
lean_del_object(v___x_1529_);
lean_dec(v_val_1526_);
lean_dec(v_key_1525_);
lean_dec(v_x_1522_);
lean_dec_ref(v_cmp_1521_);
v___x_1541_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_1524_, v_rchild_1527_);
return v___x_1541_;
}
default: 
{
uint8_t v___x_1542_; 
v___x_1542_ = l_Lean_RBNode_isBlack___redArg(v_rchild_1527_);
if (v___x_1542_ == 0)
{
uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = 0;
v___x_1544_ = l_Lean_RBNode_del___redArg(v_cmp_1521_, v_x_1522_, v_rchild_1527_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 3, v___x_1544_);
v___x_1546_ = v___x_1529_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_lchild_1524_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_key_1525_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_val_1526_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*4, v___x_1543_);
return v___x_1546_;
}
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1529_);
v___x_1548_ = l_Lean_RBNode_del___redArg(v_cmp_1521_, v_x_1522_, v_rchild_1527_);
v___x_1549_ = l_Lean_RBNode_balRight___redArg(v_lchild_1524_, v_key_1525_, v_val_1526_, v___x_1548_);
return v___x_1549_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del(lean_object* v_00_u03b1_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_cmp_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_RBNode_del___redArg(v_cmp_1553_, v_x_1554_, v_x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___redArg(lean_object* v_cmp_1557_, lean_object* v_x_1558_, lean_object* v_t_1559_){
_start:
{
lean_object* v_t_1560_; lean_object* v___x_1561_; 
v_t_1560_ = l_Lean_RBNode_del___redArg(v_cmp_1557_, v_x_1558_, v_t_1559_);
v___x_1561_ = l_Lean_RBNode_setBlack___redArg(v_t_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase(lean_object* v_00_u03b1_1562_, lean_object* v_00_u03b2_1563_, lean_object* v_cmp_1564_, lean_object* v_x_1565_, lean_object* v_t_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_RBNode_erase___redArg(v_cmp_1564_, v_x_1565_, v_t_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___redArg(lean_object* v_cmp_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v___x_1571_; 
lean_dec(v_x_1570_);
lean_dec_ref(v_cmp_1568_);
v___x_1571_ = lean_box(0);
return v___x_1571_;
}
else
{
lean_object* v_lchild_1572_; lean_object* v_key_1573_; lean_object* v_val_1574_; lean_object* v_rchild_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_lchild_1572_ = lean_ctor_get(v_x_1569_, 0);
lean_inc(v_lchild_1572_);
v_key_1573_ = lean_ctor_get(v_x_1569_, 1);
lean_inc_n(v_key_1573_, 2);
v_val_1574_ = lean_ctor_get(v_x_1569_, 2);
lean_inc(v_val_1574_);
v_rchild_1575_ = lean_ctor_get(v_x_1569_, 3);
lean_inc(v_rchild_1575_);
lean_dec_ref_known(v_x_1569_, 4);
lean_inc_ref(v_cmp_1568_);
lean_inc(v_x_1570_);
v___x_1576_ = lean_apply_2(v_cmp_1568_, v_x_1570_, v_key_1573_);
v___x_1577_ = lean_unbox(v___x_1576_);
switch(v___x_1577_)
{
case 0:
{
lean_dec(v_rchild_1575_);
lean_dec(v_val_1574_);
lean_dec(v_key_1573_);
v_x_1569_ = v_lchild_1572_;
goto _start;
}
case 1:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_rchild_1575_);
lean_dec(v_lchild_1572_);
lean_dec(v_x_1570_);
lean_dec_ref(v_cmp_1568_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_key_1573_);
lean_ctor_set(v___x_1579_, 1, v_val_1574_);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
default: 
{
lean_dec(v_val_1574_);
lean_dec(v_key_1573_);
lean_dec(v_lchild_1572_);
v_x_1569_ = v_rchild_1575_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore(lean_object* v_00_u03b1_1582_, lean_object* v_00_u03b2_1583_, lean_object* v_cmp_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_RBNode_findCore___redArg(v_cmp_1584_, v_x_1585_, v_x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___redArg(lean_object* v_cmp_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
if (lean_obj_tag(v_x_1589_) == 0)
{
lean_object* v___x_1591_; 
lean_dec(v_x_1590_);
lean_dec_ref(v_cmp_1588_);
v___x_1591_ = lean_box(0);
return v___x_1591_;
}
else
{
lean_object* v_lchild_1592_; lean_object* v_key_1593_; lean_object* v_val_1594_; lean_object* v_rchild_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_lchild_1592_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_lchild_1592_);
v_key_1593_ = lean_ctor_get(v_x_1589_, 1);
lean_inc(v_key_1593_);
v_val_1594_ = lean_ctor_get(v_x_1589_, 2);
lean_inc(v_val_1594_);
v_rchild_1595_ = lean_ctor_get(v_x_1589_, 3);
lean_inc(v_rchild_1595_);
lean_dec_ref_known(v_x_1589_, 4);
lean_inc_ref(v_cmp_1588_);
lean_inc(v_x_1590_);
v___x_1596_ = lean_apply_2(v_cmp_1588_, v_x_1590_, v_key_1593_);
v___x_1597_ = lean_unbox(v___x_1596_);
switch(v___x_1597_)
{
case 0:
{
lean_dec(v_rchild_1595_);
lean_dec(v_val_1594_);
v_x_1589_ = v_lchild_1592_;
goto _start;
}
case 1:
{
lean_object* v___x_1599_; 
lean_dec(v_rchild_1595_);
lean_dec(v_lchild_1592_);
lean_dec(v_x_1590_);
lean_dec_ref(v_cmp_1588_);
v___x_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_val_1594_);
return v___x_1599_;
}
default: 
{
lean_dec(v_val_1594_);
lean_dec(v_lchild_1592_);
v_x_1589_ = v_rchild_1595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find(lean_object* v_00_u03b1_1601_, lean_object* v_cmp_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_RBNode_find___redArg(v_cmp_1602_, v_x_1604_, v_x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound___redArg(lean_object* v_cmp_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_dec(v_x_1609_);
lean_dec_ref(v_cmp_1607_);
return v_x_1610_;
}
else
{
lean_object* v_lchild_1611_; lean_object* v_key_1612_; lean_object* v_val_1613_; lean_object* v_rchild_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_lchild_1611_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_lchild_1611_);
v_key_1612_ = lean_ctor_get(v_x_1608_, 1);
lean_inc_n(v_key_1612_, 2);
v_val_1613_ = lean_ctor_get(v_x_1608_, 2);
lean_inc(v_val_1613_);
v_rchild_1614_ = lean_ctor_get(v_x_1608_, 3);
lean_inc(v_rchild_1614_);
lean_dec_ref_known(v_x_1608_, 4);
lean_inc_ref(v_cmp_1607_);
lean_inc(v_x_1609_);
v___x_1615_ = lean_apply_2(v_cmp_1607_, v_x_1609_, v_key_1612_);
v___x_1616_ = lean_unbox(v___x_1615_);
switch(v___x_1616_)
{
case 0:
{
lean_dec(v_rchild_1614_);
lean_dec(v_val_1613_);
lean_dec(v_key_1612_);
v_x_1608_ = v_lchild_1611_;
goto _start;
}
case 1:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_rchild_1614_);
lean_dec(v_lchild_1611_);
lean_dec(v_x_1610_);
lean_dec(v_x_1609_);
lean_dec_ref(v_cmp_1607_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_key_1612_);
lean_ctor_set(v___x_1618_, 1, v_val_1613_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
default: 
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec(v_lchild_1611_);
lean_dec(v_x_1610_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_key_1612_);
lean_ctor_set(v___x_1620_, 1, v_val_1613_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
v_x_1608_ = v_rchild_1614_;
v_x_1610_ = v___x_1621_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_lowerBound(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_cmp_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_1625_, v_x_1626_, v_x_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3(uint8_t v_color_1630_, lean_object* v_key_1631_, lean_object* v_x1_1632_, lean_object* v_x2_1633_, lean_object* v_x3_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_1635_, 0, v_x1_1632_);
lean_ctor_set(v___x_1635_, 1, v_key_1631_);
lean_ctor_set(v___x_1635_, 2, v_x2_1633_);
lean_ctor_set(v___x_1635_, 3, v_x3_1634_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*4, v_color_1630_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__3___boxed(lean_object* v_color_1636_, lean_object* v_key_1637_, lean_object* v_x1_1638_, lean_object* v_x2_1639_, lean_object* v_x3_1640_){
_start:
{
uint8_t v_color_88__boxed_1641_; lean_object* v_res_1642_; 
v_color_88__boxed_1641_ = lean_unbox(v_color_1636_);
v_res_1642_ = l_Lean_RBNode_mapM___redArg___lam__3(v_color_88__boxed_1641_, v_key_1637_, v_x1_1638_, v_x2_1639_, v_x3_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__1(lean_object* v_f_1643_, lean_object* v_key_1644_, lean_object* v_val_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_apply_2(v_f_1643_, v_key_1644_, v_val_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__2(lean_object* v_inst_1648_, lean_object* v_f_1649_, lean_object* v_lchild_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_RBNode_mapM___redArg(v_inst_1648_, v_f_1649_, v_lchild_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg(lean_object* v_inst_1653_, lean_object* v_f_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 0)
{
lean_object* v_toPure_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_f_1654_);
v_toPure_1656_ = lean_ctor_get(v_inst_1653_, 1);
lean_inc(v_toPure_1656_);
lean_dec_ref(v_inst_1653_);
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_apply_2(v_toPure_1656_, lean_box(0), v___x_1657_);
return v___x_1658_;
}
else
{
lean_object* v_toPure_1659_; lean_object* v_toSeq_1660_; uint8_t v_color_1661_; lean_object* v_lchild_1662_; lean_object* v_key_1663_; lean_object* v_val_1664_; lean_object* v_rchild_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___f_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_toPure_1659_ = lean_ctor_get(v_inst_1653_, 1);
lean_inc(v_toPure_1659_);
v_toSeq_1660_ = lean_ctor_get(v_inst_1653_, 2);
lean_inc_n(v_toSeq_1660_, 3);
v_color_1661_ = lean_ctor_get_uint8(v_x_1655_, sizeof(void*)*4);
v_lchild_1662_ = lean_ctor_get(v_x_1655_, 0);
lean_inc(v_lchild_1662_);
v_key_1663_ = lean_ctor_get(v_x_1655_, 1);
lean_inc_n(v_key_1663_, 2);
v_val_1664_ = lean_ctor_get(v_x_1655_, 2);
lean_inc(v_val_1664_);
v_rchild_1665_ = lean_ctor_get(v_x_1655_, 3);
lean_inc(v_rchild_1665_);
lean_dec_ref_known(v_x_1655_, 4);
lean_inc_n(v_f_1654_, 2);
lean_inc_ref(v_inst_1653_);
v___f_1666_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1666_, 0, v_inst_1653_);
lean_closure_set(v___f_1666_, 1, v_f_1654_);
lean_closure_set(v___f_1666_, 2, v_rchild_1665_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1667_, 0, v_f_1654_);
lean_closure_set(v___f_1667_, 1, v_key_1663_);
lean_closure_set(v___f_1667_, 2, v_val_1664_);
v___f_1668_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1668_, 0, v_inst_1653_);
lean_closure_set(v___f_1668_, 1, v_f_1654_);
lean_closure_set(v___f_1668_, 2, v_lchild_1662_);
v___x_1669_ = lean_box(v_color_1661_);
v___f_1670_ = lean_alloc_closure((void*)(l_Lean_RBNode_mapM___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1670_, 0, v___x_1669_);
lean_closure_set(v___f_1670_, 1, v_key_1663_);
v___x_1671_ = lean_apply_2(v_toPure_1659_, lean_box(0), v___f_1670_);
v___x_1672_ = lean_apply_4(v_toSeq_1660_, lean_box(0), lean_box(0), v___x_1671_, v___f_1668_);
v___x_1673_ = lean_apply_4(v_toSeq_1660_, lean_box(0), lean_box(0), v___x_1672_, v___f_1667_);
v___x_1674_ = lean_apply_4(v_toSeq_1660_, lean_box(0), lean_box(0), v___x_1673_, v___f_1666_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM___redArg___lam__0(lean_object* v_inst_1675_, lean_object* v_f_1676_, lean_object* v_rchild_1677_, lean_object* v_x_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_RBNode_mapM___redArg(v_inst_1675_, v_f_1676_, v_rchild_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_mapM(lean_object* v_00_u03b1_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_00_u03b3_1682_, lean_object* v_M_1683_, lean_object* v_inst_1684_, lean_object* v_f_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_RBNode_mapM___redArg(v_inst_1684_, v_f_1685_, v_x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map___redArg(lean_object* v_f_1688_, lean_object* v_x_1689_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 0)
{
lean_object* v___x_1690_; 
lean_dec(v_f_1688_);
v___x_1690_ = lean_box(0);
return v___x_1690_;
}
else
{
uint8_t v_color_1691_; lean_object* v_lchild_1692_; lean_object* v_key_1693_; lean_object* v_val_1694_; lean_object* v_rchild_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1705_; 
v_color_1691_ = lean_ctor_get_uint8(v_x_1689_, sizeof(void*)*4);
v_lchild_1692_ = lean_ctor_get(v_x_1689_, 0);
v_key_1693_ = lean_ctor_get(v_x_1689_, 1);
v_val_1694_ = lean_ctor_get(v_x_1689_, 2);
v_rchild_1695_ = lean_ctor_get(v_x_1689_, 3);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1689_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1697_ = v_x_1689_;
v_isShared_1698_ = v_isSharedCheck_1705_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_rchild_1695_);
lean_inc(v_val_1694_);
lean_inc(v_key_1693_);
lean_inc(v_lchild_1692_);
lean_dec(v_x_1689_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1705_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_inc_n(v_f_1688_, 2);
v___x_1699_ = l_Lean_RBNode_map___redArg(v_f_1688_, v_lchild_1692_);
lean_inc(v_key_1693_);
v___x_1700_ = lean_apply_2(v_f_1688_, v_key_1693_, v_val_1694_);
v___x_1701_ = l_Lean_RBNode_map___redArg(v_f_1688_, v_rchild_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 3, v___x_1701_);
lean_ctor_set(v___x_1697_, 2, v___x_1700_);
lean_ctor_set(v___x_1697_, 0, v___x_1699_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_key_1693_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v___x_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1704_, sizeof(void*)*4, v_color_1691_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_map(lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_00_u03b3_1708_, lean_object* v_f_1709_, lean_object* v_x_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_RBNode_map___redArg(v_f_1709_, v_x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
return v_x_1712_;
}
else
{
lean_object* v_lchild_1714_; lean_object* v_key_1715_; lean_object* v_val_1716_; lean_object* v_rchild_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_lchild_1714_ = lean_ctor_get(v_x_1713_, 0);
v_key_1715_ = lean_ctor_get(v_x_1713_, 1);
v_val_1716_ = lean_ctor_get(v_x_1713_, 2);
v_rchild_1717_ = lean_ctor_get(v_x_1713_, 3);
v___x_1718_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1712_, v_lchild_1714_);
lean_inc(v_val_1716_);
lean_inc(v_key_1715_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_key_1715_);
lean_ctor_set(v___x_1719_, 1, v_val_1716_);
v___x_1720_ = lean_array_push(v___x_1718_, v___x_1719_);
v_x_1712_ = v___x_1720_;
v_x_1713_ = v_rchild_1717_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg___boxed(lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1722_, v_x_1723_);
lean_dec(v_x_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg(lean_object* v_n_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Lean_RBNode_toArray___redArg___closed__0));
v___x_1729_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v___x_1728_, v_n_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___redArg___boxed(lean_object* v_n_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_RBNode_toArray___redArg(v_n_1730_);
lean_dec(v_n_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_n_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_RBNode_toArray___redArg(v_n_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_toArray___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_n_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_RBNode_toArray(v_00_u03b1_1736_, v_00_u03b2_1737_, v_n_1738_);
lean_dec(v_n_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___redArg(v_x_1742_, v_x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_RBNode_fold___at___00Lean_RBNode_toArray_spec__0(v_00_u03b1_1745_, v_00_u03b2_1746_, v_x_1747_, v_x_1748_);
lean_dec(v_x_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_box(0);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection___redArg___boxed(lean_object* v___dummy_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_RBNode_instEmptyCollection___redArg();
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_instEmptyCollection(lean_object* v_00_u03b1_1754_, lean_object* v_00_u03b2_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg(){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_box(0);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___redArg___boxed(lean_object* v___dummy_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_mkRBMap___redArg();
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v_cmp_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_box(0);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBMap___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_cmp_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_mkRBMap(v_00_u03b1_1765_, v_00_u03b2_1766_, v_cmp_1767_);
lean_dec_ref(v_cmp_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg(){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___redArg___boxed(lean_object* v___dummy_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_RBMap_empty___redArg();
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty(lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_box(0);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_empty___boxed(lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_RBMap_empty(v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec_ref(v___y_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg(){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_box(0);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___redArg___boxed(lean_object* v___dummy_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_instEmptyCollectionRBMap___redArg();
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap(lean_object* v_00_u03b1_1785_, lean_object* v_00_u03b2_1786_, lean_object* v_cmp_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_box(0);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBMap___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_cmp_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_instEmptyCollectionRBMap(v_00_u03b1_1789_, v_00_u03b2_1790_, v_cmp_1791_);
lean_dec_ref(v_cmp_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg(){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_box(0);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___redArg___boxed(lean_object* v___dummy_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_instInhabitedRBMap___redArg();
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap(lean_object* v_00_u03b1_1797_, lean_object* v_00_u03b2_1798_, lean_object* v_cmp_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_box(0);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBMap___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_00_u03b2_1802_, lean_object* v_cmp_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_instInhabitedRBMap(v_00_u03b1_1801_, v_00_u03b2_1802_, v_cmp_1803_);
lean_dec_ref(v_cmp_1803_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg(lean_object* v_f_1805_, lean_object* v_t_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_RBNode_depth___redArg(v_f_1805_, v_t_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___redArg___boxed(lean_object* v_f_1808_, lean_object* v_t_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_RBMap_depth___redArg(v_f_1808_, v_t_1809_);
lean_dec(v_t_1809_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_cmp_1813_, lean_object* v_f_1814_, lean_object* v_t_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_RBNode_depth___redArg(v_f_1814_, v_t_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_depth___boxed(lean_object* v_00_u03b1_1817_, lean_object* v_00_u03b2_1818_, lean_object* v_cmp_1819_, lean_object* v_f_1820_, lean_object* v_t_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_RBMap_depth(v_00_u03b1_1817_, v_00_u03b2_1818_, v_cmp_1819_, v_f_1820_, v_t_1821_);
lean_dec(v_t_1821_);
lean_dec_ref(v_cmp_1819_);
return v_res_1822_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton___redArg(lean_object* v_t_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Lean_RBNode_isSingleton___redArg(v_t_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___redArg___boxed(lean_object* v_t_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Lean_RBMap_isSingleton___redArg(v_t_1825_);
lean_dec(v_t_1825_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isSingleton(lean_object* v_00_u03b1_1828_, lean_object* v_00_u03b2_1829_, lean_object* v_cmp_1830_, lean_object* v_t_1831_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_RBNode_isSingleton___redArg(v_t_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isSingleton___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_cmp_1835_, lean_object* v_t_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_Lean_RBMap_isSingleton(v_00_u03b1_1833_, v_00_u03b2_1834_, v_cmp_1835_, v_t_1836_);
lean_dec(v_t_1836_);
lean_dec_ref(v_cmp_1835_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___redArg(lean_object* v_f_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Lean_RBNode_fold___redArg(v_f_1839_, v_x_1840_, v_x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold(lean_object* v_00_u03b1_1843_, lean_object* v_00_u03b2_1844_, lean_object* v_00_u03c3_1845_, lean_object* v_cmp_1846_, lean_object* v_f_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_RBNode_fold___redArg(v_f_1847_, v_x_1848_, v_x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fold___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_00_u03b2_1852_, lean_object* v_00_u03c3_1853_, lean_object* v_cmp_1854_, lean_object* v_f_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_RBMap_fold(v_00_u03b1_1851_, v_00_u03b2_1852_, v_00_u03c3_1853_, v_cmp_1854_, v_f_1855_, v_x_1856_, v_x_1857_);
lean_dec_ref(v_cmp_1854_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___redArg(lean_object* v_f_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_RBNode_revFold___redArg(v_f_1859_, v_x_1860_, v_x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold(lean_object* v_00_u03b1_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_00_u03c3_1865_, lean_object* v_cmp_1866_, lean_object* v_f_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_RBNode_revFold___redArg(v_f_1867_, v_x_1868_, v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_revFold___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_00_u03c3_1873_, lean_object* v_cmp_1874_, lean_object* v_f_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_RBMap_revFold(v_00_u03b1_1871_, v_00_u03b2_1872_, v_00_u03c3_1873_, v_cmp_1874_, v_f_1875_, v_x_1876_, v_x_1877_);
lean_dec_ref(v_cmp_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___redArg(lean_object* v_inst_1879_, lean_object* v_f_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_RBNode_foldM___redArg(v_inst_1879_, v_f_1880_, v_x_1881_, v_x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM(lean_object* v_00_u03b1_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_00_u03c3_1886_, lean_object* v_cmp_1887_, lean_object* v_m_1888_, lean_object* v_inst_1889_, lean_object* v_f_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_RBNode_foldM___redArg(v_inst_1889_, v_f_1890_, v_x_1891_, v_x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_foldM___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_00_u03c3_1896_, lean_object* v_cmp_1897_, lean_object* v_m_1898_, lean_object* v_inst_1899_, lean_object* v_f_1900_, lean_object* v_x_1901_, lean_object* v_x_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_RBMap_foldM(v_00_u03b1_1894_, v_00_u03b2_1895_, v_00_u03c3_1896_, v_cmp_1897_, v_m_1898_, v_inst_1899_, v_f_1900_, v_x_1901_, v_x_1902_);
lean_dec_ref(v_cmp_1897_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg___lam__0(lean_object* v_f_1904_, lean_object* v_x_1905_, lean_object* v_k_1906_, lean_object* v_v_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_apply_2(v_f_1904_, v_k_1906_, v_v_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___redArg(lean_object* v_inst_1909_, lean_object* v_f_1910_, lean_object* v_t_1911_){
_start:
{
lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1912_, 0, v_f_1910_);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_RBNode_foldM___redArg(v_inst_1909_, v___f_1912_, v___x_1913_, v_t_1911_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM(lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_cmp_1917_, lean_object* v_m_1918_, lean_object* v_inst_1919_, lean_object* v_f_1920_, lean_object* v_t_1921_){
_start:
{
lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___f_1922_ = lean_alloc_closure((void*)(l_Lean_RBMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1922_, 0, v_f_1920_);
v___x_1923_ = lean_box(0);
v___x_1924_ = l_Lean_RBNode_foldM___redArg(v_inst_1919_, v___f_1922_, v___x_1923_, v_t_1921_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forM___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_cmp_1927_, lean_object* v_m_1928_, lean_object* v_inst_1929_, lean_object* v_f_1930_, lean_object* v_t_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_RBMap_forM(v_00_u03b1_1925_, v_00_u03b2_1926_, v_cmp_1927_, v_m_1928_, v_inst_1929_, v_f_1930_, v_t_1931_);
lean_dec_ref(v_cmp_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg___lam__0(lean_object* v_f_1933_, lean_object* v_a_1934_, lean_object* v_b_1935_, lean_object* v_acc_1936_){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_a_1934_);
lean_ctor_set(v___x_1937_, 1, v_b_1935_);
v___x_1938_ = lean_apply_2(v_f_1933_, v___x_1937_, v_acc_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___redArg(lean_object* v_inst_1939_, lean_object* v_t_1940_, lean_object* v_init_1941_, lean_object* v_f_1942_){
_start:
{
lean_object* v_toApplicative_1943_; lean_object* v_toBind_1944_; lean_object* v_toPure_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; 
v_toApplicative_1943_ = lean_ctor_get(v_inst_1939_, 0);
v_toBind_1944_ = lean_ctor_get(v_inst_1939_, 1);
lean_inc(v_toBind_1944_);
v_toPure_1945_ = lean_ctor_get(v_toApplicative_1943_, 1);
lean_inc(v_toPure_1945_);
v___f_1946_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1946_, 0, v_f_1942_);
v___x_1947_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1939_, v___f_1946_, v_t_1940_, v_init_1941_);
v___f_1948_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1948_, 0, v_toPure_1945_);
v___x_1949_ = lean_apply_4(v_toBind_1944_, lean_box(0), lean_box(0), v___x_1947_, v___f_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn(lean_object* v_00_u03b1_1950_, lean_object* v_00_u03b2_1951_, lean_object* v_00_u03c3_1952_, lean_object* v_cmp_1953_, lean_object* v_m_1954_, lean_object* v_inst_1955_, lean_object* v_t_1956_, lean_object* v_init_1957_, lean_object* v_f_1958_){
_start:
{
lean_object* v_toApplicative_1959_; lean_object* v_toBind_1960_; lean_object* v_toPure_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; 
v_toApplicative_1959_ = lean_ctor_get(v_inst_1955_, 0);
v_toBind_1960_ = lean_ctor_get(v_inst_1955_, 1);
lean_inc(v_toBind_1960_);
v_toPure_1961_ = lean_ctor_get(v_toApplicative_1959_, 1);
lean_inc(v_toPure_1961_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_RBMap_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1962_, 0, v_f_1958_);
v___x_1963_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1955_, v___f_1962_, v_t_1956_, v_init_1957_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1964_, 0, v_toPure_1961_);
v___x_1965_ = lean_apply_4(v_toBind_1960_, lean_box(0), lean_box(0), v___x_1963_, v___f_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_forIn___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_00_u03c3_1968_, lean_object* v_cmp_1969_, lean_object* v_m_1970_, lean_object* v_inst_1971_, lean_object* v_t_1972_, lean_object* v_init_1973_, lean_object* v_f_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_RBMap_forIn(v_00_u03b1_1966_, v_00_u03b2_1967_, v_00_u03c3_1968_, v_cmp_1969_, v_m_1970_, v_inst_1971_, v_t_1972_, v_init_1973_, v_f_1974_);
lean_dec_ref(v_cmp_1969_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0(lean_object* v___y_1976_, lean_object* v_a_1977_, lean_object* v_b_1978_, lean_object* v_acc_1979_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1977_);
lean_ctor_set(v___x_1980_, 1, v_b_1978_);
v___x_1981_ = lean_apply_2(v___y_1976_, v___x_1980_, v_acc_1979_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1982_, lean_object* v_00_u03b2_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_toApplicative_1987_; lean_object* v_toBind_1988_; lean_object* v_toPure_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; 
v_toApplicative_1987_ = lean_ctor_get(v_inst_1982_, 0);
v_toBind_1988_ = lean_ctor_get(v_inst_1982_, 1);
lean_inc(v_toBind_1988_);
v_toPure_1989_ = lean_ctor_get(v_toApplicative_1987_, 1);
lean_inc(v_toPure_1989_);
v___f_1990_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1990_, 0, v___y_1986_);
v___x_1991_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit___redArg(v_inst_1982_, v___f_1990_, v___y_1984_, v___y_1985_);
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_RBNode_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1992_, 0, v_toPure_1989_);
v___x_1993_ = lean_apply_4(v_toBind_1988_, lean_box(0), lean_box(0), v___x_1991_, v___f_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___redArg(lean_object* v_inst_1994_){
_start:
{
lean_object* v___f_1995_; 
v___f_1995_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1995_, 0, v_inst_1994_);
return v___f_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad(lean_object* v_00_u03b1_1996_, lean_object* v_00_u03b2_1997_, lean_object* v_cmp_1998_, lean_object* v_m_1999_, lean_object* v_inst_2000_){
_start:
{
lean_object* v___f_2001_; 
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_RBMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2001_, 0, v_inst_2000_);
return v___f_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_2002_, lean_object* v_00_u03b2_2003_, lean_object* v_cmp_2004_, lean_object* v_m_2005_, lean_object* v_inst_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_RBMap_instForInProdOfMonad(v_00_u03b1_2002_, v_00_u03b2_2003_, v_cmp_2004_, v_m_2005_, v_inst_2006_);
lean_dec_ref(v_cmp_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty___redArg(lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
uint8_t v___x_2009_; 
v___x_2009_ = 1;
return v___x_2009_;
}
else
{
uint8_t v___x_2010_; 
v___x_2010_ = 0;
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___redArg___boxed(lean_object* v_x_2011_){
_start:
{
uint8_t v_res_2012_; lean_object* v_r_2013_; 
v_res_2012_ = l_Lean_RBMap_isEmpty___redArg(v_x_2011_);
lean_dec(v_x_2011_);
v_r_2013_ = lean_box(v_res_2012_);
return v_r_2013_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_isEmpty(lean_object* v_00_u03b1_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_cmp_2016_, lean_object* v_x_2017_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
uint8_t v___x_2018_; 
v___x_2018_ = 1;
return v___x_2018_;
}
else
{
uint8_t v___x_2019_; 
v___x_2019_ = 0;
return v___x_2019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_isEmpty___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_00_u03b2_2021_, lean_object* v_cmp_2022_, lean_object* v_x_2023_){
_start:
{
uint8_t v_res_2024_; lean_object* v_r_2025_; 
v_res_2024_ = l_Lean_RBMap_isEmpty(v_00_u03b1_2020_, v_00_u03b2_2021_, v_cmp_2022_, v_x_2023_);
lean_dec(v_x_2023_);
lean_dec_ref(v_cmp_2022_);
v_r_2025_ = lean_box(v_res_2024_);
return v_r_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg___lam__0(lean_object* v_ps_2026_, lean_object* v_k_2027_, lean_object* v_v_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_k_2027_);
lean_ctor_set(v___x_2029_, 1, v_v_2028_);
v___x_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v_ps_2026_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___redArg(lean_object* v_x_2032_){
_start:
{
lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___f_2033_ = ((lean_object*)(l_Lean_RBMap_toList___redArg___closed__0));
v___x_2034_ = lean_box(0);
v___x_2035_ = l_Lean_RBNode_revFold___redArg(v___f_2033_, v___x_2034_, v_x_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList(lean_object* v_00_u03b1_2036_, lean_object* v_00_u03b2_2037_, lean_object* v_cmp_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_RBMap_toList___redArg(v_x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toList___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_00_u03b2_2042_, lean_object* v_cmp_2043_, lean_object* v_x_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_RBMap_toList(v_00_u03b1_2041_, v_00_u03b2_2042_, v_cmp_2043_, v_x_2044_);
lean_dec_ref(v_cmp_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg___lam__0(lean_object* v_ps_2046_, lean_object* v_k_2047_, lean_object* v_v_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_k_2047_);
lean_ctor_set(v___x_2049_, 1, v_v_2048_);
v___x_2050_ = lean_array_push(v_ps_2046_, v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___redArg(lean_object* v_x_2054_){
_start:
{
lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___f_2055_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__0));
v___x_2056_ = ((lean_object*)(l_Lean_RBMap_toArray___redArg___closed__1));
v___x_2057_ = l_Lean_RBNode_fold___redArg(v___f_2055_, v___x_2056_, v_x_2054_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray(lean_object* v_00_u03b1_2058_, lean_object* v_00_u03b2_2059_, lean_object* v_cmp_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_RBMap_toArray___redArg(v_x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_cmp_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_RBMap_toArray(v_00_u03b1_2063_, v_00_u03b2_2064_, v_cmp_2065_, v_x_2066_);
lean_dec_ref(v_cmp_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg(lean_object* v_x_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_RBNode_min___redArg(v_x_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_box(0);
return v___x_2070_;
}
else
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2087_; 
v_val_2071_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2087_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2087_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2086_; 
v_fst_2075_ = lean_ctor_get(v_val_2071_, 0);
v_snd_2076_ = lean_ctor_get(v_val_2071_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_val_2071_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2078_ = v_val_2071_;
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_inc(v_fst_2075_);
lean_dec(v_val_2071_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_fst_2075_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_snd_2076_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2081_);
v___x_2083_ = v___x_2073_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___redArg___boxed(lean_object* v_x_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_RBMap_min___redArg(v_x_2088_);
lean_dec(v_x_2088_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min(lean_object* v_00_u03b1_2090_, lean_object* v_00_u03b2_2091_, lean_object* v_cmp_2092_, lean_object* v_x_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_RBNode_min___redArg(v_x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2112_; 
v_val_2096_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2098_ = v___x_2094_;
v_isShared_2099_ = v_isSharedCheck_2112_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_val_2096_);
lean_dec(v___x_2094_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2112_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2111_; 
v_fst_2100_ = lean_ctor_get(v_val_2096_, 0);
v_snd_2101_ = lean_ctor_get(v_val_2096_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_val_2096_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2103_ = v_val_2096_;
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_snd_2101_);
lean_inc(v_fst_2100_);
lean_dec(v_val_2096_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2111_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_fst_2100_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_snd_2101_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2106_);
v___x_2108_ = v___x_2098_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_cmp_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_RBMap_min(v_00_u03b1_2113_, v_00_u03b2_2114_, v_cmp_2115_, v_x_2116_);
lean_dec(v_x_2116_);
lean_dec_ref(v_cmp_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg(lean_object* v_x_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_RBNode_max___redArg(v_x_2118_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_box(0);
return v___x_2120_;
}
else
{
lean_object* v_val_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2137_; 
v_val_2121_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2123_ = v___x_2119_;
v_isShared_2124_ = v_isSharedCheck_2137_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_val_2121_);
lean_dec(v___x_2119_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2137_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_fst_2125_; lean_object* v_snd_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2136_; 
v_fst_2125_ = lean_ctor_get(v_val_2121_, 0);
v_snd_2126_ = lean_ctor_get(v_val_2121_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_val_2121_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2128_ = v_val_2121_;
v_isShared_2129_ = v_isSharedCheck_2136_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snd_2126_);
lean_inc(v_fst_2125_);
lean_dec(v_val_2121_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2136_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_fst_2125_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_snd_2126_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2131_);
v___x_2133_ = v___x_2123_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___redArg___boxed(lean_object* v_x_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_RBMap_max___redArg(v_x_2138_);
lean_dec(v_x_2138_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max(lean_object* v_00_u03b1_2140_, lean_object* v_00_u03b2_2141_, lean_object* v_cmp_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_RBNode_max___redArg(v_x_2143_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; 
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
else
{
lean_object* v_val_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2162_; 
v_val_2146_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2162_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_val_2146_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2162_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_fst_2150_; lean_object* v_snd_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2161_; 
v_fst_2150_ = lean_ctor_get(v_val_2146_, 0);
v_snd_2151_ = lean_ctor_get(v_val_2146_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_val_2146_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2153_ = v_val_2146_;
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_snd_2151_);
lean_inc(v_fst_2150_);
lean_dec(v_val_2146_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_fst_2150_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_snd_2151_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2156_);
v___x_2158_ = v___x_2148_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_cmp_2165_, lean_object* v_x_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_RBMap_max(v_00_u03b1_2163_, v_00_u03b2_2164_, v_cmp_2165_, v_x_2166_);
lean_dec(v_x_2166_);
lean_dec_ref(v_cmp_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0(lean_object* v___x_2171_, lean_object* v_m_2172_, lean_object* v_prec_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2174_ = ((lean_object*)(l_Lean_RBMap_instRepr___redArg___lam__0___closed__1));
v___x_2175_ = l_Lean_RBMap_toList___redArg(v_m_2172_);
v___x_2176_ = l_List_repr___redArg(v___x_2171_, v___x_2175_);
v___x_2177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2174_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Repr_addAppParen(v___x_2177_, v_prec_2173_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg___lam__0___boxed(lean_object* v___x_2179_, lean_object* v_m_2180_, lean_object* v_prec_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_RBMap_instRepr___redArg___lam__0(v___x_2179_, v_m_2180_, v_prec_2181_);
lean_dec(v_prec_2181_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___redArg(lean_object* v_inst_2183_, lean_object* v_inst_2184_){
_start:
{
lean_object* v___f_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; 
v___f_2185_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2185_, 0, v_inst_2184_);
v___x_2186_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2186_, 0, lean_box(0));
lean_closure_set(v___x_2186_, 1, lean_box(0));
lean_closure_set(v___x_2186_, 2, v_inst_2183_);
lean_closure_set(v___x_2186_, 3, v___f_2185_);
v___f_2187_ = lean_alloc_closure((void*)(l_Lean_RBMap_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2187_, 0, v___x_2186_);
return v___f_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr(lean_object* v_00_u03b1_2188_, lean_object* v_00_u03b2_2189_, lean_object* v_cmp_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_RBMap_instRepr___redArg(v_inst_2191_, v_inst_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_instRepr___boxed(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_cmp_2196_, lean_object* v_inst_2197_, lean_object* v_inst_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_RBMap_instRepr(v_00_u03b1_2194_, v_00_u03b2_2195_, v_cmp_2196_, v_inst_2197_, v_inst_2198_);
lean_dec_ref(v_cmp_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert___redArg(lean_object* v_cmp_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_RBNode_insert___redArg(v_cmp_2200_, v_x_2201_, v_x_2202_, v_x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_insert(lean_object* v_00_u03b1_2205_, lean_object* v_00_u03b2_2206_, lean_object* v_cmp_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_RBNode_insert___redArg(v_cmp_2207_, v_x_2208_, v_x_2209_, v_x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase___redArg(lean_object* v_cmp_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_RBNode_erase___redArg(v_cmp_2212_, v_x_2214_, v_x_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_erase(lean_object* v_00_u03b1_2216_, lean_object* v_00_u03b2_2217_, lean_object* v_cmp_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_RBNode_erase___redArg(v_cmp_2218_, v_x_2220_, v_x_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList___redArg(lean_object* v_cmp_2222_, lean_object* v_x_2223_){
_start:
{
if (lean_obj_tag(v_x_2223_) == 0)
{
lean_object* v___x_2224_; 
lean_dec_ref(v_cmp_2222_);
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
else
{
lean_object* v_head_2225_; lean_object* v_tail_2226_; lean_object* v_fst_2227_; lean_object* v_snd_2228_; lean_object* v_val_2229_; lean_object* v___x_2230_; 
v_head_2225_ = lean_ctor_get(v_x_2223_, 0);
lean_inc(v_head_2225_);
v_tail_2226_ = lean_ctor_get(v_x_2223_, 1);
lean_inc(v_tail_2226_);
lean_dec_ref_known(v_x_2223_, 2);
v_fst_2227_ = lean_ctor_get(v_head_2225_, 0);
lean_inc(v_fst_2227_);
v_snd_2228_ = lean_ctor_get(v_head_2225_, 1);
lean_inc(v_snd_2228_);
lean_dec(v_head_2225_);
lean_inc_ref(v_cmp_2222_);
v_val_2229_ = l_Lean_RBMap_ofList___redArg(v_cmp_2222_, v_tail_2226_);
v___x_2230_ = l_Lean_RBNode_insert___redArg(v_cmp_2222_, v_val_2229_, v_fst_2227_, v_snd_2228_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_ofList(lean_object* v_00_u03b1_2231_, lean_object* v_00_u03b2_2232_, lean_object* v_cmp_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_RBMap_ofList___redArg(v_cmp_2233_, v_x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f___redArg(lean_object* v_cmp_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_RBNode_findCore___redArg(v_cmp_2236_, v_x_2237_, v_x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findCore_x3f(lean_object* v_00_u03b1_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_cmp_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_RBNode_findCore___redArg(v_cmp_2242_, v_x_2243_, v_x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f___redArg(lean_object* v_cmp_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_RBNode_find___redArg(v_cmp_2246_, v_x_2247_, v_x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x3f(lean_object* v_00_u03b1_2250_, lean_object* v_00_u03b2_2251_, lean_object* v_cmp_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_RBNode_find___redArg(v_cmp_2252_, v_x_2253_, v_x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg(lean_object* v_cmp_2256_, lean_object* v_t_2257_, lean_object* v_k_2258_, lean_object* v_v_u2080_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_RBNode_find___redArg(v_cmp_2256_, v_t_2257_, v_k_2258_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_inc(v_v_u2080_2259_);
return v_v_u2080_2259_;
}
else
{
lean_object* v_val_2261_; 
v_val_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v___x_2260_, 1);
return v_val_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___redArg___boxed(lean_object* v_cmp_2262_, lean_object* v_t_2263_, lean_object* v_k_2264_, lean_object* v_v_u2080_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_RBMap_findD___redArg(v_cmp_2262_, v_t_2263_, v_k_2264_, v_v_u2080_2265_);
lean_dec(v_v_u2080_2265_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD(lean_object* v_00_u03b1_2267_, lean_object* v_00_u03b2_2268_, lean_object* v_cmp_2269_, lean_object* v_t_2270_, lean_object* v_k_2271_, lean_object* v_v_u2080_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_RBNode_find___redArg(v_cmp_2269_, v_t_2270_, v_k_2271_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_inc(v_v_u2080_2272_);
return v_v_u2080_2272_;
}
else
{
lean_object* v_val_2274_; 
v_val_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_val_2274_);
lean_dec_ref_known(v___x_2273_, 1);
return v_val_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_findD___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_00_u03b2_2276_, lean_object* v_cmp_2277_, lean_object* v_t_2278_, lean_object* v_k_2279_, lean_object* v_v_u2080_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_RBMap_findD(v_00_u03b1_2275_, v_00_u03b2_2276_, v_cmp_2277_, v_t_2278_, v_k_2279_, v_v_u2080_2280_);
lean_dec(v_v_u2080_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound___redArg(lean_object* v_cmp_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_box(0);
v___x_2286_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2282_, v_x_2283_, v_x_2284_, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_lowerBound(lean_object* v_00_u03b1_2287_, lean_object* v_00_u03b2_2288_, lean_object* v_cmp_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = l_Lean_RBNode_lowerBound___redArg(v_cmp_2289_, v_x_2290_, v_x_2291_, v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains___redArg(lean_object* v_cmp_2294_, lean_object* v_t_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_RBNode_find___redArg(v_cmp_2294_, v_t_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
uint8_t v___x_2298_; 
v___x_2298_ = 0;
return v___x_2298_;
}
else
{
uint8_t v___x_2299_; 
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = 1;
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___redArg___boxed(lean_object* v_cmp_2300_, lean_object* v_t_2301_, lean_object* v_a_2302_){
_start:
{
uint8_t v_res_2303_; lean_object* v_r_2304_; 
v_res_2303_ = l_Lean_RBMap_contains___redArg(v_cmp_2300_, v_t_2301_, v_a_2302_);
v_r_2304_ = lean_box(v_res_2303_);
return v_r_2304_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_contains(lean_object* v_00_u03b1_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_cmp_2307_, lean_object* v_t_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_RBNode_find___redArg(v_cmp_2307_, v_t_2308_, v_a_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
uint8_t v___x_2311_; 
v___x_2311_ = 0;
return v___x_2311_;
}
else
{
uint8_t v___x_2312_; 
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = 1;
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_contains___boxed(lean_object* v_00_u03b1_2313_, lean_object* v_00_u03b2_2314_, lean_object* v_cmp_2315_, lean_object* v_t_2316_, lean_object* v_a_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Lean_RBMap_contains(v_00_u03b1_2313_, v_00_u03b2_2314_, v_cmp_2315_, v_t_2316_, v_a_2317_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg___lam__0(lean_object* v_cmp_2320_, lean_object* v_r_2321_, lean_object* v_p_2322_){
_start:
{
lean_object* v_fst_2323_; lean_object* v_snd_2324_; lean_object* v___x_2325_; 
v_fst_2323_ = lean_ctor_get(v_p_2322_, 0);
lean_inc(v_fst_2323_);
v_snd_2324_ = lean_ctor_get(v_p_2322_, 1);
lean_inc(v_snd_2324_);
lean_dec_ref(v_p_2322_);
v___x_2325_ = l_Lean_RBNode_insert___redArg(v_cmp_2320_, v_r_2321_, v_fst_2323_, v_snd_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList___redArg(lean_object* v_l_2326_, lean_object* v_cmp_2327_){
_start:
{
lean_object* v___f_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___f_2328_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2328_, 0, v_cmp_2327_);
v___x_2329_ = lean_box(0);
v___x_2330_ = l_List_foldl___redArg(v___f_2328_, v___x_2329_, v_l_2326_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromList(lean_object* v_00_u03b1_2331_, lean_object* v_00_u03b2_2332_, lean_object* v_l_2333_, lean_object* v_cmp_2334_){
_start:
{
lean_object* v___f_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___f_2335_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromList___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2335_, 0, v_cmp_2334_);
v___x_2336_ = lean_box(0);
v___x_2337_ = l_List_foldl___redArg(v___f_2335_, v___x_2336_, v_l_2333_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg___lam__0(lean_object* v_cmp_2338_, lean_object* v_x1_2339_, lean_object* v_x2_2340_){
_start:
{
lean_object* v_fst_2341_; lean_object* v_snd_2342_; lean_object* v___x_2343_; 
v_fst_2341_ = lean_ctor_get(v_x2_2340_, 0);
lean_inc(v_fst_2341_);
v_snd_2342_ = lean_ctor_get(v_x2_2340_, 1);
lean_inc(v_snd_2342_);
lean_dec_ref(v_x2_2340_);
v___x_2343_ = l_Lean_RBNode_insert___redArg(v_cmp_2338_, v_x1_2339_, v_fst_2341_, v_snd_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray___redArg(lean_object* v_l_2363_, lean_object* v_cmp_2364_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_array_get_size(v_l_2363_);
v___x_2368_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2369_ = lean_nat_dec_lt(v___x_2366_, v___x_2367_);
if (v___x_2369_ == 0)
{
lean_dec_ref(v_cmp_2364_);
lean_dec_ref(v_l_2363_);
return v___x_2365_;
}
else
{
lean_object* v___f_2370_; uint8_t v___x_2371_; 
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2370_, 0, v_cmp_2364_);
v___x_2371_ = lean_nat_dec_le(v___x_2367_, v___x_2367_);
if (v___x_2371_ == 0)
{
if (v___x_2369_ == 0)
{
lean_dec_ref(v___f_2370_);
lean_dec_ref(v_l_2363_);
return v___x_2365_;
}
else
{
size_t v___x_2372_; size_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = ((size_t)0ULL);
v___x_2373_ = lean_usize_of_nat(v___x_2367_);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2368_, v___f_2370_, v_l_2363_, v___x_2372_, v___x_2373_, v___x_2365_);
return v___x_2374_;
}
}
else
{
size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = ((size_t)0ULL);
v___x_2376_ = lean_usize_of_nat(v___x_2367_);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2368_, v___f_2370_, v_l_2363_, v___x_2375_, v___x_2376_, v___x_2365_);
return v___x_2377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_fromArray(lean_object* v_00_u03b1_2378_, lean_object* v_00_u03b2_2379_, lean_object* v_l_2380_, lean_object* v_cmp_2381_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_unsigned_to_nat(0u);
v___x_2384_ = lean_array_get_size(v_l_2380_);
v___x_2385_ = ((lean_object*)(l_Lean_RBMap_fromArray___redArg___closed__9));
v___x_2386_ = lean_nat_dec_lt(v___x_2383_, v___x_2384_);
if (v___x_2386_ == 0)
{
lean_dec_ref(v_cmp_2381_);
lean_dec_ref(v_l_2380_);
return v___x_2382_;
}
else
{
lean_object* v___f_2387_; uint8_t v___x_2388_; 
v___f_2387_ = lean_alloc_closure((void*)(l_Lean_RBMap_fromArray___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2387_, 0, v_cmp_2381_);
v___x_2388_ = lean_nat_dec_le(v___x_2384_, v___x_2384_);
if (v___x_2388_ == 0)
{
if (v___x_2386_ == 0)
{
lean_dec_ref(v___f_2387_);
lean_dec_ref(v_l_2380_);
return v___x_2382_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = lean_usize_of_nat(v___x_2384_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2385_, v___f_2387_, v_l_2380_, v___x_2389_, v___x_2390_, v___x_2382_);
return v___x_2391_;
}
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = lean_usize_of_nat(v___x_2384_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2385_, v___f_2387_, v_l_2380_, v___x_2392_, v___x_2393_, v___x_2382_);
return v___x_2394_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_all___redArg(lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = l_Lean_RBNode_all___redArg(v_x_2396_, v_x_2395_);
return v___x_2397_;
}
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
LEAN_EXPORT uint8_t l_Lean_RBMap_all(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_cmp_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_RBNode_all___redArg(v_x_2406_, v_x_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_all___boxed(lean_object* v_00_u03b1_2408_, lean_object* v_00_u03b2_2409_, lean_object* v_cmp_2410_, lean_object* v_x_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_Lean_RBMap_all(v_00_u03b1_2408_, v_00_u03b2_2409_, v_cmp_2410_, v_x_2411_, v_x_2412_);
lean_dec_ref(v_cmp_2410_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any___redArg(lean_object* v_x_2415_, lean_object* v_x_2416_){
_start:
{
uint8_t v___x_2417_; 
v___x_2417_ = l_Lean_RBNode_any___redArg(v_x_2416_, v_x_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___redArg___boxed(lean_object* v_x_2418_, lean_object* v_x_2419_){
_start:
{
uint8_t v_res_2420_; lean_object* v_r_2421_; 
v_res_2420_ = l_Lean_RBMap_any___redArg(v_x_2418_, v_x_2419_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBMap_any(lean_object* v_00_u03b1_2422_, lean_object* v_00_u03b2_2423_, lean_object* v_cmp_2424_, lean_object* v_x_2425_, lean_object* v_x_2426_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = l_Lean_RBNode_any___redArg(v_x_2426_, v_x_2425_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_any___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_cmp_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_Lean_RBMap_any(v_00_u03b1_2428_, v_00_u03b2_2429_, v_cmp_2430_, v_x_2431_, v_x_2432_);
lean_dec_ref(v_cmp_2430_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
if (lean_obj_tag(v_x_2436_) == 0)
{
return v_x_2435_;
}
else
{
lean_object* v_lchild_2437_; lean_object* v_rchild_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_lchild_2437_ = lean_ctor_get(v_x_2436_, 0);
v_rchild_2438_ = lean_ctor_get(v_x_2436_, 3);
v___x_2439_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2435_, v_lchild_2437_);
v___x_2440_ = lean_unsigned_to_nat(1u);
v___x_2441_ = lean_nat_add(v___x_2439_, v___x_2440_);
lean_dec(v___x_2439_);
v_x_2435_ = v___x_2441_;
v_x_2436_ = v_rchild_2438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg___boxed(lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2443_, v_x_2444_);
lean_dec(v_x_2444_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg(lean_object* v_m_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_unsigned_to_nat(0u);
v___x_2448_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v___x_2447_, v_m_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___redArg___boxed(lean_object* v_m_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_RBMap_size___redArg(v_m_2449_);
lean_dec(v_m_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size(lean_object* v_00_u03b1_2451_, lean_object* v_00_u03b2_2452_, lean_object* v_cmp_2453_, lean_object* v_m_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_RBMap_size___redArg(v_m_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_size___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_cmp_2458_, lean_object* v_m_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_RBMap_size(v_00_u03b1_2456_, v_00_u03b2_2457_, v_cmp_2458_, v_m_2459_);
lean_dec(v_m_2459_);
lean_dec_ref(v_cmp_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(lean_object* v_00_u03b1_2461_, lean_object* v_00_u03b2_2462_, lean_object* v_x_2463_, lean_object* v_x_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___redArg(v_x_2463_, v_x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_00_u03b2_2467_, lean_object* v_x_2468_, lean_object* v_x_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_RBNode_fold___at___00Lean_RBMap_size_spec__0(v_00_u03b1_2466_, v_00_u03b2_2467_, v_x_2468_, v_x_2469_);
lean_dec(v_x_2469_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0(lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_nat_dec_le(v___y_2471_, v___y_2472_);
if (v___x_2473_ == 0)
{
lean_inc(v___y_2471_);
return v___y_2471_;
}
else
{
lean_inc(v___y_2472_);
return v___y_2472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___lam__0___boxed(lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_RBMap_maxDepth___redArg___lam__0(v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg(lean_object* v_t_2478_){
_start:
{
lean_object* v___f_2479_; lean_object* v___x_2480_; 
v___f_2479_ = ((lean_object*)(l_Lean_RBMap_maxDepth___redArg___closed__0));
v___x_2480_ = l_Lean_RBNode_depth___redArg(v___f_2479_, v_t_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___redArg___boxed(lean_object* v_t_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_RBMap_maxDepth___redArg(v_t_2481_);
lean_dec(v_t_2481_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth(lean_object* v_00_u03b1_2483_, lean_object* v_00_u03b2_2484_, lean_object* v_cmp_2485_, lean_object* v_t_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_RBMap_maxDepth___redArg(v_t_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_maxDepth___boxed(lean_object* v_00_u03b1_2488_, lean_object* v_00_u03b2_2489_, lean_object* v_cmp_2490_, lean_object* v_t_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_RBMap_maxDepth(v_00_u03b1_2488_, v_00_u03b2_2489_, v_cmp_2490_, v_t_2491_);
lean_dec(v_t_2491_);
lean_dec_ref(v_cmp_2490_);
return v_res_2492_;
}
}
static lean_object* _init_l_Lean_RBMap_min_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2496_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2497_ = lean_unsigned_to_nat(14u);
v___x_2498_ = lean_unsigned_to_nat(386u);
v___x_2499_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__1));
v___x_2500_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2501_ = l_mkPanicMessageWithDecl(v___x_2500_, v___x_2499_, v___x_2498_, v___x_2497_, v___x_2496_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg(lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_t_2504_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_RBNode_min___redArg(v_t_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v_inst_2502_);
lean_ctor_set(v___x_2506_, 1, v_inst_2503_);
v___x_2507_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2508_ = l_panic___redArg(v___x_2506_, v___x_2507_);
lean_dec_ref_known(v___x_2506_, 2);
return v___x_2508_;
}
else
{
lean_object* v_val_2509_; lean_object* v_fst_2510_; lean_object* v_snd_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_inst_2503_);
lean_dec(v_inst_2502_);
v_val_2509_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___x_2505_, 1);
v_fst_2510_ = lean_ctor_get(v_val_2509_, 0);
v_snd_2511_ = lean_ctor_get(v_val_2509_, 1);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_val_2509_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v_val_2509_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snd_2511_);
lean_inc(v_fst_2510_);
lean_dec(v_val_2509_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_fst_2510_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_snd_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___redArg___boxed(lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_t_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_RBMap_min_x21___redArg(v_inst_2519_, v_inst_2520_, v_t_2521_);
lean_dec(v_t_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21(lean_object* v_00_u03b1_2523_, lean_object* v_00_u03b2_2524_, lean_object* v_cmp_2525_, lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_t_2528_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_RBNode_min___redArg(v_t_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_inst_2526_);
lean_ctor_set(v___x_2530_, 1, v_inst_2527_);
v___x_2531_ = lean_obj_once(&l_Lean_RBMap_min_x21___redArg___closed__3, &l_Lean_RBMap_min_x21___redArg___closed__3_once, _init_l_Lean_RBMap_min_x21___redArg___closed__3);
v___x_2532_ = l_panic___redArg(v___x_2530_, v___x_2531_);
lean_dec_ref_known(v___x_2530_, 2);
return v___x_2532_;
}
else
{
lean_object* v_val_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_inst_2527_);
lean_dec(v_inst_2526_);
v_val_2533_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2533_);
lean_dec_ref_known(v___x_2529_, 1);
v_fst_2534_ = lean_ctor_get(v_val_2533_, 0);
v_snd_2535_ = lean_ctor_get(v_val_2533_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_val_2533_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v_val_2533_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_snd_2535_);
lean_inc(v_fst_2534_);
lean_dec(v_val_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_fst_2534_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_snd_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_min_x21___boxed(lean_object* v_00_u03b1_2543_, lean_object* v_00_u03b2_2544_, lean_object* v_cmp_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_t_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_RBMap_min_x21(v_00_u03b1_2543_, v_00_u03b2_2544_, v_cmp_2545_, v_inst_2546_, v_inst_2547_, v_t_2548_);
lean_dec(v_t_2548_);
lean_dec_ref(v_cmp_2545_);
return v_res_2549_;
}
}
static lean_object* _init_l_Lean_RBMap_max_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2551_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__2));
v___x_2552_ = lean_unsigned_to_nat(14u);
v___x_2553_ = lean_unsigned_to_nat(391u);
v___x_2554_ = ((lean_object*)(l_Lean_RBMap_max_x21___redArg___closed__0));
v___x_2555_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2556_ = l_mkPanicMessageWithDecl(v___x_2555_, v___x_2554_, v___x_2553_, v___x_2552_, v___x_2551_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg(lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_t_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_RBNode_max___redArg(v_t_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_inst_2557_);
lean_ctor_set(v___x_2561_, 1, v_inst_2558_);
v___x_2562_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2563_ = l_panic___redArg(v___x_2561_, v___x_2562_);
lean_dec_ref_known(v___x_2561_, 2);
return v___x_2563_;
}
else
{
lean_object* v_val_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_inst_2558_);
lean_dec(v_inst_2557_);
v_val_2564_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v___x_2560_, 1);
v_fst_2565_ = lean_ctor_get(v_val_2564_, 0);
v_snd_2566_ = lean_ctor_get(v_val_2564_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_val_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v_val_2564_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_dec(v_val_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_fst_2565_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_snd_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___redArg___boxed(lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_t_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_RBMap_max_x21___redArg(v_inst_2574_, v_inst_2575_, v_t_2576_);
lean_dec(v_t_2576_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21(lean_object* v_00_u03b1_2578_, lean_object* v_00_u03b2_2579_, lean_object* v_cmp_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_t_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_RBNode_max___redArg(v_t_2583_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v_inst_2581_);
lean_ctor_set(v___x_2585_, 1, v_inst_2582_);
v___x_2586_ = lean_obj_once(&l_Lean_RBMap_max_x21___redArg___closed__1, &l_Lean_RBMap_max_x21___redArg___closed__1_once, _init_l_Lean_RBMap_max_x21___redArg___closed__1);
v___x_2587_ = l_panic___redArg(v___x_2585_, v___x_2586_);
lean_dec_ref_known(v___x_2585_, 2);
return v___x_2587_;
}
else
{
lean_object* v_val_2588_; lean_object* v_fst_2589_; lean_object* v_snd_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_inst_2582_);
lean_dec(v_inst_2581_);
v_val_2588_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v___x_2584_, 1);
v_fst_2589_ = lean_ctor_get(v_val_2588_, 0);
v_snd_2590_ = lean_ctor_get(v_val_2588_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_val_2588_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v_val_2588_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_snd_2590_);
lean_inc(v_fst_2589_);
lean_dec(v_val_2588_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_fst_2589_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_snd_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_max_x21___boxed(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b2_2599_, lean_object* v_cmp_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_t_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_RBMap_max_x21(v_00_u03b1_2598_, v_00_u03b2_2599_, v_cmp_2600_, v_inst_2601_, v_inst_2602_, v_t_2603_);
lean_dec(v_t_2603_);
lean_dec_ref(v_cmp_2600_);
return v_res_2604_;
}
}
static lean_object* _init_l_Lean_RBMap_find_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2607_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__1));
v___x_2608_ = lean_unsigned_to_nat(14u);
v___x_2609_ = lean_unsigned_to_nat(397u);
v___x_2610_ = ((lean_object*)(l_Lean_RBMap_find_x21___redArg___closed__0));
v___x_2611_ = ((lean_object*)(l_Lean_RBMap_min_x21___redArg___closed__0));
v___x_2612_ = l_mkPanicMessageWithDecl(v___x_2611_, v___x_2610_, v___x_2609_, v___x_2608_, v___x_2607_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg(lean_object* v_cmp_2613_, lean_object* v_inst_2614_, lean_object* v_t_2615_, lean_object* v_k_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_RBNode_find___redArg(v_cmp_2613_, v_t_2615_, v_k_2616_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2619_ = l_panic___redArg(v_inst_2614_, v___x_2618_);
return v___x_2619_;
}
else
{
lean_object* v_val_2620_; 
v_val_2620_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_val_2620_);
lean_dec_ref_known(v___x_2617_, 1);
return v_val_2620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___redArg___boxed(lean_object* v_cmp_2621_, lean_object* v_inst_2622_, lean_object* v_t_2623_, lean_object* v_k_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_RBMap_find_x21___redArg(v_cmp_2621_, v_inst_2622_, v_t_2623_, v_k_2624_);
lean_dec(v_inst_2622_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21(lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_cmp_2628_, lean_object* v_inst_2629_, lean_object* v_t_2630_, lean_object* v_k_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_RBNode_find___redArg(v_cmp_2628_, v_t_2630_, v_k_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = lean_obj_once(&l_Lean_RBMap_find_x21___redArg___closed__2, &l_Lean_RBMap_find_x21___redArg___closed__2_once, _init_l_Lean_RBMap_find_x21___redArg___closed__2);
v___x_2634_ = l_panic___redArg(v_inst_2629_, v___x_2633_);
return v___x_2634_;
}
else
{
lean_object* v_val_2635_; 
v_val_2635_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v___x_2632_, 1);
return v_val_2635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_find_x21___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_00_u03b2_2637_, lean_object* v_cmp_2638_, lean_object* v_inst_2639_, lean_object* v_t_2640_, lean_object* v_k_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_RBMap_find_x21(v_00_u03b1_2636_, v_00_u03b2_2637_, v_cmp_2638_, v_inst_2639_, v_t_2640_, v_k_2641_);
lean_dec(v_inst_2639_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(lean_object* v_cmp_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
uint8_t v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref(v_cmp_2643_);
v___x_2647_ = 0;
v___x_2648_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2648_, 0, v_x_2644_);
lean_ctor_set(v___x_2648_, 1, v_x_2645_);
lean_ctor_set(v___x_2648_, 2, v_x_2646_);
lean_ctor_set(v___x_2648_, 3, v_x_2644_);
lean_ctor_set_uint8(v___x_2648_, sizeof(void*)*4, v___x_2647_);
return v___x_2648_;
}
else
{
uint8_t v_color_2649_; 
v_color_2649_ = lean_ctor_get_uint8(v_x_2644_, sizeof(void*)*4);
if (v_color_2649_ == 0)
{
lean_object* v_lchild_2650_; lean_object* v_key_2651_; lean_object* v_val_2652_; lean_object* v_rchild_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2670_; 
v_lchild_2650_ = lean_ctor_get(v_x_2644_, 0);
v_key_2651_ = lean_ctor_get(v_x_2644_, 1);
v_val_2652_ = lean_ctor_get(v_x_2644_, 2);
v_rchild_2653_ = lean_ctor_get(v_x_2644_, 3);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2655_ = v_x_2644_;
v_isShared_2656_ = v_isSharedCheck_2670_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_rchild_2653_);
lean_inc(v_val_2652_);
lean_inc(v_key_2651_);
lean_inc(v_lchild_2650_);
lean_dec(v_x_2644_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2670_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
lean_inc_ref(v_cmp_2643_);
lean_inc(v_key_2651_);
lean_inc(v_x_2645_);
v___x_2657_ = lean_apply_2(v_cmp_2643_, v_x_2645_, v_key_2651_);
v___x_2658_ = lean_unbox(v___x_2657_);
switch(v___x_2658_)
{
case 0:
{
lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2659_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2643_, v_lchild_2650_, v_x_2645_, v_x_2646_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2659_);
v___x_2661_ = v___x_2655_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_key_2651_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_val_2652_);
lean_ctor_set(v_reuseFailAlloc_2662_, 3, v_rchild_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2662_, sizeof(void*)*4, v_color_2649_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
case 1:
{
lean_object* v___x_2664_; 
lean_dec(v_val_2652_);
lean_dec(v_key_2651_);
lean_dec_ref(v_cmp_2643_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 2, v_x_2646_);
lean_ctor_set(v___x_2655_, 1, v_x_2645_);
v___x_2664_ = v___x_2655_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_lchild_2650_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_x_2645_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_x_2646_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v_rchild_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2665_, sizeof(void*)*4, v_color_2649_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
default: 
{
lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2666_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2643_, v_rchild_2653_, v_x_2645_, v_x_2646_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 3, v___x_2666_);
v___x_2668_ = v___x_2655_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_lchild_2650_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_key_2651_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_val_2652_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v___x_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2669_, sizeof(void*)*4, v_color_2649_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
else
{
lean_object* v_lchild_2671_; lean_object* v_key_2672_; lean_object* v_val_2673_; lean_object* v_rchild_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2833_; 
v_lchild_2671_ = lean_ctor_get(v_x_2644_, 0);
v_key_2672_ = lean_ctor_get(v_x_2644_, 1);
v_val_2673_ = lean_ctor_get(v_x_2644_, 2);
v_rchild_2674_ = lean_ctor_get(v_x_2644_, 3);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2676_ = v_x_2644_;
v_isShared_2677_ = v_isSharedCheck_2833_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_rchild_2674_);
lean_inc(v_val_2673_);
lean_inc(v_key_2672_);
lean_inc(v_lchild_2671_);
lean_dec(v_x_2644_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2833_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; uint8_t v___x_2679_; 
lean_inc_ref(v_cmp_2643_);
lean_inc(v_key_2672_);
lean_inc(v_x_2645_);
v___x_2678_ = lean_apply_2(v_cmp_2643_, v_x_2645_, v_key_2672_);
v___x_2679_ = lean_unbox(v___x_2678_);
switch(v___x_2679_)
{
case 0:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2643_, v_lchild_2671_, v_x_2645_, v_x_2646_);
if (lean_obj_tag(v___x_2680_) == 1)
{
uint8_t v_color_2681_; lean_object* v_lchild_2682_; lean_object* v_key_2683_; lean_object* v_val_2684_; lean_object* v_rchild_2685_; lean_object* v_a_2687_; lean_object* v_kx_2688_; lean_object* v_vx_2689_; lean_object* v_b_2690_; lean_object* v_ky_2691_; lean_object* v_vy_2692_; lean_object* v_c_2693_; lean_object* v_kz_2694_; lean_object* v_vz_2695_; lean_object* v_d_2696_; 
v_color_2681_ = lean_ctor_get_uint8(v___x_2680_, sizeof(void*)*4);
v_lchild_2682_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_lchild_2682_);
v_key_2683_ = lean_ctor_get(v___x_2680_, 1);
v_val_2684_ = lean_ctor_get(v___x_2680_, 2);
v_rchild_2685_ = lean_ctor_get(v___x_2680_, 3);
lean_inc(v_rchild_2685_);
if (v_color_2681_ == 0)
{
if (lean_obj_tag(v_lchild_2682_) == 1)
{
uint8_t v_color_2702_; 
v_color_2702_ = lean_ctor_get_uint8(v_lchild_2682_, sizeof(void*)*4);
if (v_color_2702_ == 0)
{
lean_object* v_lchild_2703_; lean_object* v_key_2704_; lean_object* v_val_2705_; lean_object* v_rchild_2706_; 
lean_inc(v_val_2684_);
lean_inc(v_key_2683_);
lean_dec_ref_known(v___x_2680_, 4);
v_lchild_2703_ = lean_ctor_get(v_lchild_2682_, 0);
lean_inc(v_lchild_2703_);
v_key_2704_ = lean_ctor_get(v_lchild_2682_, 1);
lean_inc(v_key_2704_);
v_val_2705_ = lean_ctor_get(v_lchild_2682_, 2);
lean_inc(v_val_2705_);
v_rchild_2706_ = lean_ctor_get(v_lchild_2682_, 3);
lean_inc(v_rchild_2706_);
lean_dec_ref_known(v_lchild_2682_, 4);
v_a_2687_ = v_lchild_2703_;
v_kx_2688_ = v_key_2704_;
v_vx_2689_ = v_val_2705_;
v_b_2690_ = v_rchild_2706_;
v_ky_2691_ = v_key_2683_;
v_vy_2692_ = v_val_2684_;
v_c_2693_ = v_rchild_2685_;
v_kz_2694_ = v_key_2672_;
v_vz_2695_ = v_val_2673_;
v_d_2696_ = v_rchild_2674_;
goto v___jp_2686_;
}
else
{
if (lean_obj_tag(v_rchild_2685_) == 1)
{
uint8_t v_color_2707_; 
v_color_2707_ = lean_ctor_get_uint8(v_rchild_2685_, sizeof(void*)*4);
if (v_color_2707_ == 0)
{
lean_object* v_lchild_2708_; lean_object* v_key_2709_; lean_object* v_val_2710_; lean_object* v_rchild_2711_; 
lean_inc(v_val_2684_);
lean_inc(v_key_2683_);
lean_dec_ref_known(v___x_2680_, 4);
v_lchild_2708_ = lean_ctor_get(v_rchild_2685_, 0);
lean_inc(v_lchild_2708_);
v_key_2709_ = lean_ctor_get(v_rchild_2685_, 1);
lean_inc(v_key_2709_);
v_val_2710_ = lean_ctor_get(v_rchild_2685_, 2);
lean_inc(v_val_2710_);
v_rchild_2711_ = lean_ctor_get(v_rchild_2685_, 3);
lean_inc(v_rchild_2711_);
lean_dec_ref_known(v_rchild_2685_, 4);
v_a_2687_ = v_lchild_2682_;
v_kx_2688_ = v_key_2683_;
v_vx_2689_ = v_val_2684_;
v_b_2690_ = v_lchild_2708_;
v_ky_2691_ = v_key_2709_;
v_vy_2692_ = v_val_2710_;
v_c_2693_ = v_rchild_2711_;
v_kz_2694_ = v_key_2672_;
v_vz_2695_ = v_val_2673_;
v_d_2696_ = v_rchild_2674_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref_known(v_lchild_2682_, 4);
lean_del_object(v___x_2676_);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_rchild_2685_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; lean_object* v_unused_2720_; lean_object* v_unused_2721_; lean_object* v_unused_2722_; 
v_unused_2719_ = lean_ctor_get(v_rchild_2685_, 3);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_rchild_2685_, 2);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_rchild_2685_, 1);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_rchild_2685_, 0);
lean_dec(v_unused_2722_);
v___x_2713_ = v_rchild_2685_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_dec(v_rchild_2685_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 3, v_rchild_2674_);
lean_ctor_set(v___x_2713_, 2, v_val_2673_);
lean_ctor_set(v___x_2713_, 1, v_key_2672_);
lean_ctor_set(v___x_2713_, 0, v___x_2680_);
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2717_, 3, v_rchild_2674_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*4, v_color_2649_);
return v___x_2716_;
}
}
}
}
else
{
lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_rchild_2685_);
lean_del_object(v___x_2676_);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_lchild_2682_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; lean_object* v_unused_2731_; lean_object* v_unused_2732_; lean_object* v_unused_2733_; 
v_unused_2730_ = lean_ctor_get(v_lchild_2682_, 3);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_lchild_2682_, 2);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_lchild_2682_, 1);
lean_dec(v_unused_2732_);
v_unused_2733_ = lean_ctor_get(v_lchild_2682_, 0);
lean_dec(v_unused_2733_);
v___x_2724_ = v_lchild_2682_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_dec(v_lchild_2682_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 3, v_rchild_2674_);
lean_ctor_set(v___x_2724_, 2, v_val_2673_);
lean_ctor_set(v___x_2724_, 1, v_key_2672_);
lean_ctor_set(v___x_2724_, 0, v___x_2680_);
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_rchild_2674_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*4, v_color_2649_);
return v___x_2727_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2685_) == 1)
{
uint8_t v_color_2734_; 
v_color_2734_ = lean_ctor_get_uint8(v_rchild_2685_, sizeof(void*)*4);
if (v_color_2734_ == 0)
{
lean_object* v_lchild_2735_; lean_object* v_key_2736_; lean_object* v_val_2737_; lean_object* v_rchild_2738_; 
lean_inc(v_val_2684_);
lean_inc(v_key_2683_);
lean_dec_ref_known(v___x_2680_, 4);
v_lchild_2735_ = lean_ctor_get(v_rchild_2685_, 0);
lean_inc(v_lchild_2735_);
v_key_2736_ = lean_ctor_get(v_rchild_2685_, 1);
lean_inc(v_key_2736_);
v_val_2737_ = lean_ctor_get(v_rchild_2685_, 2);
lean_inc(v_val_2737_);
v_rchild_2738_ = lean_ctor_get(v_rchild_2685_, 3);
lean_inc(v_rchild_2738_);
lean_dec_ref_known(v_rchild_2685_, 4);
v_a_2687_ = v_lchild_2682_;
v_kx_2688_ = v_key_2683_;
v_vx_2689_ = v_val_2684_;
v_b_2690_ = v_lchild_2735_;
v_ky_2691_ = v_key_2736_;
v_vy_2692_ = v_val_2737_;
v_c_2693_ = v_rchild_2738_;
v_kz_2694_ = v_key_2672_;
v_vz_2695_ = v_val_2673_;
v_d_2696_ = v_rchild_2674_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_lchild_2682_);
lean_del_object(v___x_2676_);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_rchild_2685_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; 
v_unused_2746_ = lean_ctor_get(v_rchild_2685_, 3);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_rchild_2685_, 2);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_rchild_2685_, 1);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_rchild_2685_, 0);
lean_dec(v_unused_2749_);
v___x_2740_ = v_rchild_2685_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_dec(v_rchild_2685_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 3, v_rchild_2674_);
lean_ctor_set(v___x_2740_, 2, v_val_2673_);
lean_ctor_set(v___x_2740_, 1, v_key_2672_);
lean_ctor_set(v___x_2740_, 0, v___x_2680_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_rchild_2674_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*4, v_color_2649_);
return v___x_2743_;
}
}
}
}
else
{
lean_object* v___x_2750_; 
lean_dec(v_rchild_2685_);
lean_dec(v_lchild_2682_);
lean_del_object(v___x_2676_);
v___x_2750_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2750_, 0, v___x_2680_);
lean_ctor_set(v___x_2750_, 1, v_key_2672_);
lean_ctor_set(v___x_2750_, 2, v_val_2673_);
lean_ctor_set(v___x_2750_, 3, v_rchild_2674_);
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*4, v_color_2649_);
return v___x_2750_;
}
}
}
else
{
lean_object* v___x_2751_; 
lean_dec(v_rchild_2685_);
lean_dec(v_lchild_2682_);
lean_del_object(v___x_2676_);
v___x_2751_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2751_, 0, v___x_2680_);
lean_ctor_set(v___x_2751_, 1, v_key_2672_);
lean_ctor_set(v___x_2751_, 2, v_val_2673_);
lean_ctor_set(v___x_2751_, 3, v_rchild_2674_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*4, v_color_2649_);
return v___x_2751_;
}
v___jp_2686_:
{
lean_object* v___x_2698_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 3, v_b_2690_);
lean_ctor_set(v___x_2676_, 2, v_vx_2689_);
lean_ctor_set(v___x_2676_, 1, v_kx_2688_);
lean_ctor_set(v___x_2676_, 0, v_a_2687_);
v___x_2698_ = v___x_2676_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2687_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_kx_2688_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_vx_2689_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_b_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2701_, sizeof(void*)*4, v_color_2649_);
v___x_2698_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2699_, 0, v_c_2693_);
lean_ctor_set(v___x_2699_, 1, v_kz_2694_);
lean_ctor_set(v___x_2699_, 2, v_vz_2695_);
lean_ctor_set(v___x_2699_, 3, v_d_2696_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*4, v_color_2649_);
v___x_2700_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v_ky_2691_);
lean_ctor_set(v___x_2700_, 2, v_vy_2692_);
lean_ctor_set(v___x_2700_, 3, v___x_2699_);
lean_ctor_set_uint8(v___x_2700_, sizeof(void*)*4, v_color_2681_);
return v___x_2700_;
}
}
}
else
{
lean_object* v___x_2753_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2680_);
v___x_2753_ = v___x_2676_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_rchild_2674_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, sizeof(void*)*4, v_color_2649_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
case 1:
{
lean_object* v___x_2756_; 
lean_dec(v_val_2673_);
lean_dec(v_key_2672_);
lean_dec_ref(v_cmp_2643_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 2, v_x_2646_);
lean_ctor_set(v___x_2676_, 1, v_x_2645_);
v___x_2756_ = v___x_2676_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_lchild_2671_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_x_2645_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_x_2646_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_rchild_2674_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*4, v_color_2649_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
default: 
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2643_, v_rchild_2674_, v_x_2645_, v_x_2646_);
if (lean_obj_tag(v___x_2758_) == 1)
{
uint8_t v_color_2759_; lean_object* v_lchild_2760_; lean_object* v_key_2761_; lean_object* v_val_2762_; lean_object* v_rchild_2763_; lean_object* v_a_2765_; lean_object* v_kx_2766_; lean_object* v_vx_2767_; lean_object* v_b_2768_; lean_object* v_ky_2769_; lean_object* v_vy_2770_; lean_object* v_c_2771_; lean_object* v_kz_2772_; lean_object* v_vz_2773_; lean_object* v_d_2774_; 
v_color_2759_ = lean_ctor_get_uint8(v___x_2758_, sizeof(void*)*4);
v_lchild_2760_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_lchild_2760_);
v_key_2761_ = lean_ctor_get(v___x_2758_, 1);
v_val_2762_ = lean_ctor_get(v___x_2758_, 2);
v_rchild_2763_ = lean_ctor_get(v___x_2758_, 3);
lean_inc(v_rchild_2763_);
if (v_color_2759_ == 0)
{
if (lean_obj_tag(v_lchild_2760_) == 1)
{
uint8_t v_color_2780_; 
v_color_2780_ = lean_ctor_get_uint8(v_lchild_2760_, sizeof(void*)*4);
if (v_color_2780_ == 0)
{
lean_object* v_lchild_2781_; lean_object* v_key_2782_; lean_object* v_val_2783_; lean_object* v_rchild_2784_; 
lean_inc(v_val_2762_);
lean_inc(v_key_2761_);
lean_dec_ref_known(v___x_2758_, 4);
v_lchild_2781_ = lean_ctor_get(v_lchild_2760_, 0);
lean_inc(v_lchild_2781_);
v_key_2782_ = lean_ctor_get(v_lchild_2760_, 1);
lean_inc(v_key_2782_);
v_val_2783_ = lean_ctor_get(v_lchild_2760_, 2);
lean_inc(v_val_2783_);
v_rchild_2784_ = lean_ctor_get(v_lchild_2760_, 3);
lean_inc(v_rchild_2784_);
lean_dec_ref_known(v_lchild_2760_, 4);
v_a_2765_ = v_lchild_2671_;
v_kx_2766_ = v_key_2672_;
v_vx_2767_ = v_val_2673_;
v_b_2768_ = v_lchild_2781_;
v_ky_2769_ = v_key_2782_;
v_vy_2770_ = v_val_2783_;
v_c_2771_ = v_rchild_2784_;
v_kz_2772_ = v_key_2761_;
v_vz_2773_ = v_val_2762_;
v_d_2774_ = v_rchild_2763_;
goto v___jp_2764_;
}
else
{
if (lean_obj_tag(v_rchild_2763_) == 1)
{
uint8_t v_color_2785_; 
v_color_2785_ = lean_ctor_get_uint8(v_rchild_2763_, sizeof(void*)*4);
if (v_color_2785_ == 0)
{
lean_object* v_lchild_2786_; lean_object* v_key_2787_; lean_object* v_val_2788_; lean_object* v_rchild_2789_; 
lean_inc(v_val_2762_);
lean_inc(v_key_2761_);
lean_dec_ref_known(v___x_2758_, 4);
v_lchild_2786_ = lean_ctor_get(v_rchild_2763_, 0);
lean_inc(v_lchild_2786_);
v_key_2787_ = lean_ctor_get(v_rchild_2763_, 1);
lean_inc(v_key_2787_);
v_val_2788_ = lean_ctor_get(v_rchild_2763_, 2);
lean_inc(v_val_2788_);
v_rchild_2789_ = lean_ctor_get(v_rchild_2763_, 3);
lean_inc(v_rchild_2789_);
lean_dec_ref_known(v_rchild_2763_, 4);
v_a_2765_ = v_lchild_2671_;
v_kx_2766_ = v_key_2672_;
v_vx_2767_ = v_val_2673_;
v_b_2768_ = v_lchild_2760_;
v_ky_2769_ = v_key_2761_;
v_vy_2770_ = v_val_2762_;
v_c_2771_ = v_lchild_2786_;
v_kz_2772_ = v_key_2787_;
v_vz_2773_ = v_val_2788_;
v_d_2774_ = v_rchild_2789_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref_known(v_lchild_2760_, 4);
lean_del_object(v___x_2676_);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_rchild_2763_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; lean_object* v_unused_2800_; 
v_unused_2797_ = lean_ctor_get(v_rchild_2763_, 3);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_rchild_2763_, 2);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_rchild_2763_, 1);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_rchild_2763_, 0);
lean_dec(v_unused_2800_);
v___x_2791_ = v_rchild_2763_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_dec(v_rchild_2763_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 3, v___x_2758_);
lean_ctor_set(v___x_2791_, 2, v_val_2673_);
lean_ctor_set(v___x_2791_, 1, v_key_2672_);
lean_ctor_set(v___x_2791_, 0, v_lchild_2671_);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_lchild_2671_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v___x_2758_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*4, v_color_2649_);
return v___x_2794_;
}
}
}
}
else
{
lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_rchild_2763_);
lean_del_object(v___x_2676_);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_lchild_2760_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; 
v_unused_2808_ = lean_ctor_get(v_lchild_2760_, 3);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_lchild_2760_, 2);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_lchild_2760_, 1);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_lchild_2760_, 0);
lean_dec(v_unused_2811_);
v___x_2802_ = v_lchild_2760_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_dec(v_lchild_2760_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 3, v___x_2758_);
lean_ctor_set(v___x_2802_, 2, v_val_2673_);
lean_ctor_set(v___x_2802_, 1, v_key_2672_);
lean_ctor_set(v___x_2802_, 0, v_lchild_2671_);
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_lchild_2671_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v___x_2758_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*4, v_color_2649_);
return v___x_2805_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_2763_) == 1)
{
uint8_t v_color_2812_; 
v_color_2812_ = lean_ctor_get_uint8(v_rchild_2763_, sizeof(void*)*4);
if (v_color_2812_ == 0)
{
lean_object* v_lchild_2813_; lean_object* v_key_2814_; lean_object* v_val_2815_; lean_object* v_rchild_2816_; 
lean_inc(v_val_2762_);
lean_inc(v_key_2761_);
lean_dec_ref_known(v___x_2758_, 4);
v_lchild_2813_ = lean_ctor_get(v_rchild_2763_, 0);
lean_inc(v_lchild_2813_);
v_key_2814_ = lean_ctor_get(v_rchild_2763_, 1);
lean_inc(v_key_2814_);
v_val_2815_ = lean_ctor_get(v_rchild_2763_, 2);
lean_inc(v_val_2815_);
v_rchild_2816_ = lean_ctor_get(v_rchild_2763_, 3);
lean_inc(v_rchild_2816_);
lean_dec_ref_known(v_rchild_2763_, 4);
v_a_2765_ = v_lchild_2671_;
v_kx_2766_ = v_key_2672_;
v_vx_2767_ = v_val_2673_;
v_b_2768_ = v_lchild_2760_;
v_ky_2769_ = v_key_2761_;
v_vy_2770_ = v_val_2762_;
v_c_2771_ = v_lchild_2813_;
v_kz_2772_ = v_key_2814_;
v_vz_2773_ = v_val_2815_;
v_d_2774_ = v_rchild_2816_;
goto v___jp_2764_;
}
else
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_lchild_2760_);
lean_del_object(v___x_2676_);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_rchild_2763_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; lean_object* v_unused_2825_; lean_object* v_unused_2826_; lean_object* v_unused_2827_; 
v_unused_2824_ = lean_ctor_get(v_rchild_2763_, 3);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_rchild_2763_, 2);
lean_dec(v_unused_2825_);
v_unused_2826_ = lean_ctor_get(v_rchild_2763_, 1);
lean_dec(v_unused_2826_);
v_unused_2827_ = lean_ctor_get(v_rchild_2763_, 0);
lean_dec(v_unused_2827_);
v___x_2818_ = v_rchild_2763_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v_rchild_2763_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 3, v___x_2758_);
lean_ctor_set(v___x_2818_, 2, v_val_2673_);
lean_ctor_set(v___x_2818_, 1, v_key_2672_);
lean_ctor_set(v___x_2818_, 0, v_lchild_2671_);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_lchild_2671_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v___x_2758_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*4, v_color_2649_);
return v___x_2821_;
}
}
}
}
else
{
lean_object* v___x_2828_; 
lean_dec(v_rchild_2763_);
lean_dec(v_lchild_2760_);
lean_del_object(v___x_2676_);
v___x_2828_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2828_, 0, v_lchild_2671_);
lean_ctor_set(v___x_2828_, 1, v_key_2672_);
lean_ctor_set(v___x_2828_, 2, v_val_2673_);
lean_ctor_set(v___x_2828_, 3, v___x_2758_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*4, v_color_2649_);
return v___x_2828_;
}
}
}
else
{
lean_object* v___x_2829_; 
lean_dec(v_rchild_2763_);
lean_dec(v_lchild_2760_);
lean_del_object(v___x_2676_);
v___x_2829_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2829_, 0, v_lchild_2671_);
lean_ctor_set(v___x_2829_, 1, v_key_2672_);
lean_ctor_set(v___x_2829_, 2, v_val_2673_);
lean_ctor_set(v___x_2829_, 3, v___x_2758_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*4, v_color_2649_);
return v___x_2829_;
}
v___jp_2764_:
{
lean_object* v___x_2776_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 3, v_b_2768_);
lean_ctor_set(v___x_2676_, 2, v_vx_2767_);
lean_ctor_set(v___x_2676_, 1, v_kx_2766_);
lean_ctor_set(v___x_2676_, 0, v_a_2765_);
v___x_2776_ = v___x_2676_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2765_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_kx_2766_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_vx_2767_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v_b_2768_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, sizeof(void*)*4, v_color_2649_);
v___x_2776_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2777_, 0, v_c_2771_);
lean_ctor_set(v___x_2777_, 1, v_kz_2772_);
lean_ctor_set(v___x_2777_, 2, v_vz_2773_);
lean_ctor_set(v___x_2777_, 3, v_d_2774_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*4, v_color_2649_);
v___x_2778_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v_ky_2769_);
lean_ctor_set(v___x_2778_, 2, v_vy_2770_);
lean_ctor_set(v___x_2778_, 3, v___x_2777_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*4, v_color_2759_);
return v___x_2778_;
}
}
}
else
{
lean_object* v___x_2831_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 3, v___x_2758_);
v___x_2831_ = v___x_2676_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_lchild_2671_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_key_2672_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_val_2673_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v___x_2758_);
lean_ctor_set_uint8(v_reuseFailAlloc_2832_, sizeof(void*)*4, v_color_2649_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(lean_object* v_cmp_2834_, lean_object* v_t_2835_, lean_object* v_k_2836_, lean_object* v_v_2837_){
_start:
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_RBNode_isRed___redArg(v_t_2835_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2834_, v_t_2835_, v_k_2836_, v_v_2837_);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2834_, v_t_2835_, v_k_2836_, v_v_2837_);
v___x_2841_ = l_Lean_RBNode_setBlack___redArg(v___x_2840_);
return v___x_2841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(lean_object* v_cmp_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
if (lean_obj_tag(v_x_2843_) == 0)
{
lean_object* v___x_2845_; 
lean_dec(v_x_2844_);
lean_dec_ref(v_cmp_2842_);
v___x_2845_ = lean_box(0);
return v___x_2845_;
}
else
{
lean_object* v_lchild_2846_; lean_object* v_key_2847_; lean_object* v_val_2848_; lean_object* v_rchild_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_lchild_2846_ = lean_ctor_get(v_x_2843_, 0);
lean_inc(v_lchild_2846_);
v_key_2847_ = lean_ctor_get(v_x_2843_, 1);
lean_inc(v_key_2847_);
v_val_2848_ = lean_ctor_get(v_x_2843_, 2);
lean_inc(v_val_2848_);
v_rchild_2849_ = lean_ctor_get(v_x_2843_, 3);
lean_inc(v_rchild_2849_);
lean_dec_ref_known(v_x_2843_, 4);
lean_inc_ref(v_cmp_2842_);
lean_inc(v_x_2844_);
v___x_2850_ = lean_apply_2(v_cmp_2842_, v_x_2844_, v_key_2847_);
v___x_2851_ = lean_unbox(v___x_2850_);
switch(v___x_2851_)
{
case 0:
{
lean_dec(v_rchild_2849_);
lean_dec(v_val_2848_);
v_x_2843_ = v_lchild_2846_;
goto _start;
}
case 1:
{
lean_object* v___x_2853_; 
lean_dec(v_rchild_2849_);
lean_dec(v_lchild_2846_);
lean_dec(v_x_2844_);
lean_dec_ref(v_cmp_2842_);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v_val_2848_);
return v___x_2853_;
}
default: 
{
lean_dec(v_val_2848_);
lean_dec(v_lchild_2846_);
v_x_2843_ = v_rchild_2849_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(lean_object* v_cmp_2855_, lean_object* v_mergeFn_2856_, lean_object* v_x_2857_, lean_object* v_x_2858_){
_start:
{
if (lean_obj_tag(v_x_2858_) == 0)
{
lean_dec(v_mergeFn_2856_);
lean_dec_ref(v_cmp_2855_);
return v_x_2857_;
}
else
{
lean_object* v_lchild_2859_; lean_object* v_key_2860_; lean_object* v_val_2861_; lean_object* v_rchild_2862_; lean_object* v_val_2863_; lean_object* v___y_2865_; lean_object* v___x_2868_; 
v_lchild_2859_ = lean_ctor_get(v_x_2858_, 0);
lean_inc(v_lchild_2859_);
v_key_2860_ = lean_ctor_get(v_x_2858_, 1);
lean_inc_n(v_key_2860_, 2);
v_val_2861_ = lean_ctor_get(v_x_2858_, 2);
lean_inc(v_val_2861_);
v_rchild_2862_ = lean_ctor_get(v_x_2858_, 3);
lean_inc(v_rchild_2862_);
lean_dec_ref_known(v_x_2858_, 4);
lean_inc(v_mergeFn_2856_);
lean_inc_ref_n(v_cmp_2855_, 2);
v_val_2863_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2855_, v_mergeFn_2856_, v_x_2857_, v_lchild_2859_);
lean_inc(v_val_2863_);
v___x_2868_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2855_, v_val_2863_, v_key_2860_);
if (lean_obj_tag(v___x_2868_) == 0)
{
v___y_2865_ = v_val_2861_;
goto v___jp_2864_;
}
else
{
lean_object* v_val_2869_; lean_object* v___x_2870_; 
v_val_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_val_2869_);
lean_dec_ref_known(v___x_2868_, 1);
lean_inc(v_mergeFn_2856_);
lean_inc(v_key_2860_);
v___x_2870_ = lean_apply_3(v_mergeFn_2856_, v_key_2860_, v_val_2869_, v_val_2861_);
v___y_2865_ = v___x_2870_;
goto v___jp_2864_;
}
v___jp_2864_:
{
lean_object* v___x_2866_; 
lean_inc_ref(v_cmp_2855_);
v___x_2866_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2855_, v_val_2863_, v_key_2860_, v___y_2865_);
v_x_2857_ = v___x_2866_;
v_x_2858_ = v_rchild_2862_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy___redArg(lean_object* v_cmp_2871_, lean_object* v_mergeFn_2872_, lean_object* v_t_u2081_2873_, lean_object* v_t_u2082_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2871_, v_mergeFn_2872_, v_t_u2081_2873_, v_t_u2082_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_mergeBy(lean_object* v_00_u03b1_2876_, lean_object* v_00_u03b2_2877_, lean_object* v_cmp_2878_, lean_object* v_mergeFn_2879_, lean_object* v_t_u2081_2880_, lean_object* v_t_u2082_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2878_, v_mergeFn_2879_, v_t_u2081_2880_, v_t_u2082_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0(lean_object* v_00_u03b1_2883_, lean_object* v_cmp_2884_, lean_object* v_00_u03b2_2885_, lean_object* v_t_2886_, lean_object* v_k_2887_, lean_object* v_v_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2884_, v_t_2886_, v_k_2887_, v_v_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1(lean_object* v_00_u03b1_2890_, lean_object* v_cmp_2891_, lean_object* v_00_u03b2_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2891_, v_x_2893_, v_x_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2(lean_object* v_00_u03b1_2896_, lean_object* v_00_u03b2_2897_, lean_object* v_cmp_2898_, lean_object* v_mergeFn_2899_, lean_object* v_x_2900_, lean_object* v_x_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_RBNode_fold___at___00Lean_RBMap_mergeBy_spec__2___redArg(v_cmp_2898_, v_mergeFn_2899_, v_x_2900_, v_x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0(lean_object* v_00_u03b1_2903_, lean_object* v_cmp_2904_, lean_object* v_00_u03b2_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0_spec__0___redArg(v_cmp_2904_, v_x_2906_, v_x_2907_, v_x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(lean_object* v_t_u2082_2910_, lean_object* v_cmp_2911_, lean_object* v_mergeFn_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
if (lean_obj_tag(v_x_2914_) == 0)
{
lean_dec(v_mergeFn_2912_);
lean_dec_ref(v_cmp_2911_);
lean_dec(v_t_u2082_2910_);
return v_x_2913_;
}
else
{
lean_object* v_lchild_2915_; lean_object* v_key_2916_; lean_object* v_val_2917_; lean_object* v_rchild_2918_; lean_object* v_val_2919_; lean_object* v___x_2920_; 
v_lchild_2915_ = lean_ctor_get(v_x_2914_, 0);
lean_inc(v_lchild_2915_);
v_key_2916_ = lean_ctor_get(v_x_2914_, 1);
lean_inc_n(v_key_2916_, 2);
v_val_2917_ = lean_ctor_get(v_x_2914_, 2);
lean_inc(v_val_2917_);
v_rchild_2918_ = lean_ctor_get(v_x_2914_, 3);
lean_inc(v_rchild_2918_);
lean_dec_ref_known(v_x_2914_, 4);
lean_inc(v_mergeFn_2912_);
lean_inc_ref_n(v_cmp_2911_, 2);
lean_inc_n(v_t_u2082_2910_, 2);
v_val_2919_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2910_, v_cmp_2911_, v_mergeFn_2912_, v_x_2913_, v_lchild_2915_);
v___x_2920_ = l_Lean_RBNode_find___at___00Lean_RBMap_mergeBy_spec__1___redArg(v_cmp_2911_, v_t_u2082_2910_, v_key_2916_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_dec(v_val_2917_);
lean_dec(v_key_2916_);
v_x_2913_ = v_val_2919_;
v_x_2914_ = v_rchild_2918_;
goto _start;
}
else
{
lean_object* v_val_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_val_2922_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v___x_2920_, 1);
lean_inc(v_mergeFn_2912_);
lean_inc(v_key_2916_);
v___x_2923_ = lean_apply_3(v_mergeFn_2912_, v_key_2916_, v_val_2917_, v_val_2922_);
lean_inc_ref(v_cmp_2911_);
v___x_2924_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2911_, v_val_2919_, v_key_2916_, v___x_2923_);
v_x_2913_ = v___x_2924_;
v_x_2914_ = v_rchild_2918_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy___redArg(lean_object* v_cmp_2926_, lean_object* v_mergeFn_2927_, lean_object* v_t_u2081_2928_, lean_object* v_t_u2082_2929_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_box(0);
v___x_2931_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2929_, v_cmp_2926_, v_mergeFn_2927_, v___x_2930_, v_t_u2081_2928_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_intersectBy(lean_object* v_00_u03b1_2932_, lean_object* v_00_u03b2_2933_, lean_object* v_cmp_2934_, lean_object* v_00_u03b3_2935_, lean_object* v_00_u03b4_2936_, lean_object* v_mergeFn_2937_, lean_object* v_t_u2081_2938_, lean_object* v_t_u2082_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_RBMap_intersectBy___redArg(v_cmp_2934_, v_mergeFn_2937_, v_t_u2081_2938_, v_t_u2082_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0(lean_object* v_00_u03b1_2941_, lean_object* v_00_u03b2_2942_, lean_object* v_00_u03b4_2943_, lean_object* v_00_u03b3_2944_, lean_object* v_t_u2082_2945_, lean_object* v_cmp_2946_, lean_object* v_mergeFn_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_RBNode_fold___at___00Lean_RBMap_intersectBy_spec__0___redArg(v_t_u2082_2945_, v_cmp_2946_, v_mergeFn_2947_, v_x_2948_, v_x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(lean_object* v_f_2951_, lean_object* v_cmp_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
if (lean_obj_tag(v_x_2954_) == 0)
{
lean_dec_ref(v_cmp_2952_);
lean_dec_ref(v_f_2951_);
return v_x_2953_;
}
else
{
lean_object* v_lchild_2955_; lean_object* v_key_2956_; lean_object* v_val_2957_; lean_object* v_rchild_2958_; lean_object* v_val_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_lchild_2955_ = lean_ctor_get(v_x_2954_, 0);
lean_inc(v_lchild_2955_);
v_key_2956_ = lean_ctor_get(v_x_2954_, 1);
lean_inc_n(v_key_2956_, 2);
v_val_2957_ = lean_ctor_get(v_x_2954_, 2);
lean_inc_n(v_val_2957_, 2);
v_rchild_2958_ = lean_ctor_get(v_x_2954_, 3);
lean_inc(v_rchild_2958_);
lean_dec_ref_known(v_x_2954_, 4);
lean_inc_ref(v_cmp_2952_);
lean_inc_ref_n(v_f_2951_, 2);
v_val_2959_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2951_, v_cmp_2952_, v_x_2953_, v_lchild_2955_);
v___x_2960_ = lean_apply_2(v_f_2951_, v_key_2956_, v_val_2957_);
v___x_2961_ = lean_unbox(v___x_2960_);
if (v___x_2961_ == 0)
{
lean_dec(v_val_2957_);
lean_dec(v_key_2956_);
v_x_2953_ = v_val_2959_;
v_x_2954_ = v_rchild_2958_;
goto _start;
}
else
{
lean_object* v___x_2963_; 
lean_inc_ref(v_cmp_2952_);
v___x_2963_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2952_, v_val_2959_, v_key_2956_, v_val_2957_);
v_x_2953_ = v___x_2963_;
v_x_2954_ = v_rchild_2958_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter___redArg(lean_object* v_cmp_2965_, lean_object* v_f_2966_, lean_object* v_m_2967_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2966_, v_cmp_2965_, v___x_2968_, v_m_2967_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filter(lean_object* v_00_u03b1_2970_, lean_object* v_00_u03b2_2971_, lean_object* v_cmp_2972_, lean_object* v_f_2973_, lean_object* v_m_2974_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_RBMap_filter___redArg(v_cmp_2972_, v_f_2973_, v_m_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0(lean_object* v_00_u03b1_2976_, lean_object* v_00_u03b2_2977_, lean_object* v_f_2978_, lean_object* v_cmp_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filter_spec__0___redArg(v_f_2978_, v_cmp_2979_, v_x_2980_, v_x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(lean_object* v_f_2983_, lean_object* v_cmp_2984_, lean_object* v_x_2985_, lean_object* v_x_2986_){
_start:
{
if (lean_obj_tag(v_x_2986_) == 0)
{
lean_dec_ref(v_cmp_2984_);
lean_dec_ref(v_f_2983_);
return v_x_2985_;
}
else
{
lean_object* v_lchild_2987_; lean_object* v_key_2988_; lean_object* v_val_2989_; lean_object* v_rchild_2990_; lean_object* v_val_2991_; lean_object* v___x_2992_; 
v_lchild_2987_ = lean_ctor_get(v_x_2986_, 0);
lean_inc(v_lchild_2987_);
v_key_2988_ = lean_ctor_get(v_x_2986_, 1);
lean_inc_n(v_key_2988_, 2);
v_val_2989_ = lean_ctor_get(v_x_2986_, 2);
lean_inc(v_val_2989_);
v_rchild_2990_ = lean_ctor_get(v_x_2986_, 3);
lean_inc(v_rchild_2990_);
lean_dec_ref_known(v_x_2986_, 4);
lean_inc_ref(v_cmp_2984_);
lean_inc_ref_n(v_f_2983_, 2);
v_val_2991_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2983_, v_cmp_2984_, v_x_2985_, v_lchild_2987_);
v___x_2992_ = lean_apply_2(v_f_2983_, v_key_2988_, v_val_2989_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_dec(v_key_2988_);
v_x_2985_ = v_val_2991_;
v_x_2986_ = v_rchild_2990_;
goto _start;
}
else
{
lean_object* v_val_2994_; lean_object* v___x_2995_; 
v_val_2994_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_val_2994_);
lean_dec_ref_known(v___x_2992_, 1);
lean_inc_ref(v_cmp_2984_);
v___x_2995_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_2984_, v_val_2991_, v_key_2988_, v_val_2994_);
v_x_2985_ = v___x_2995_;
v_x_2986_ = v_rchild_2990_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap___redArg(lean_object* v_cmp_2997_, lean_object* v_f_2998_, lean_object* v_m_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_2998_, v_cmp_2997_, v___x_3000_, v_m_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_filterMap(lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_cmp_3004_, lean_object* v_00_u03b3_3005_, lean_object* v_f_3006_, lean_object* v_m_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_RBMap_filterMap___redArg(v_cmp_3004_, v_f_3006_, v_m_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0(lean_object* v_00_u03b1_3009_, lean_object* v_00_u03b2_3010_, lean_object* v_00_u03b3_3011_, lean_object* v_f_3012_, lean_object* v_cmp_3013_, lean_object* v_x_3014_, lean_object* v_x_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_RBNode_fold___at___00Lean_RBMap_filterMap_spec__0___redArg(v_f_3012_, v_cmp_3013_, v_x_3014_, v_x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(lean_object* v_cmp_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
if (lean_obj_tag(v_x_3019_) == 0)
{
lean_dec_ref(v_cmp_3017_);
return v_x_3018_;
}
else
{
lean_object* v_head_3020_; lean_object* v_tail_3021_; lean_object* v_fst_3022_; lean_object* v_snd_3023_; lean_object* v___x_3024_; 
v_head_3020_ = lean_ctor_get(v_x_3019_, 0);
lean_inc(v_head_3020_);
v_tail_3021_ = lean_ctor_get(v_x_3019_, 1);
lean_inc(v_tail_3021_);
lean_dec_ref_known(v_x_3019_, 2);
v_fst_3022_ = lean_ctor_get(v_head_3020_, 0);
lean_inc(v_fst_3022_);
v_snd_3023_ = lean_ctor_get(v_head_3020_, 1);
lean_inc(v_snd_3023_);
lean_dec(v_head_3020_);
lean_inc_ref(v_cmp_3017_);
v___x_3024_ = l_Lean_RBNode_insert___at___00Lean_RBMap_mergeBy_spec__0___redArg(v_cmp_3017_, v_x_3018_, v_fst_3022_, v_snd_3023_);
v_x_3018_ = v___x_3024_;
v_x_3019_ = v_tail_3021_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf___redArg(lean_object* v_l_3026_, lean_object* v_cmp_3027_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3027_, v___x_3028_, v_l_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbmapOf(lean_object* v_00_u03b1_3030_, lean_object* v_00_u03b2_3031_, lean_object* v_l_3032_, lean_object* v_cmp_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_rbmapOf___redArg(v_l_3032_, v_cmp_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_rbmapOf_spec__0(lean_object* v_00_u03b1_3035_, lean_object* v_00_u03b2_3036_, lean_object* v_cmp_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_List_foldl___at___00Lean_rbmapOf_spec__0___redArg(v_cmp_3037_, v_x_3038_, v_x_3039_);
return v___x_3040_;
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
