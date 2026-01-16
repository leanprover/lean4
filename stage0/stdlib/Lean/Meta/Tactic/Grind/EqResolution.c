// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EqResolution
// Imports: public import Lean.Meta.Basic import Lean.Meta.AppBuilder import Lean.Meta.MatchUtil import Lean.Util.ForEachExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_eqResolution___closed__0;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Grind_eqResolution___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__1;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = 0;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = l_Lean_Meta_forallMetaTelescopeReducing(x_1, x_7, x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_14);
x_16 = l_Lean_Meta_matchNot_x3f(x_14, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_16);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Meta_mkFreshExprMVar(x_18, x_8, x_19, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_array_push(x_12, x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_array_push(x_12, x_25);
x_27 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
lean_ctor_set(x_11, 1, x_27);
lean_ctor_set(x_11, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_11);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_11);
lean_dec(x_12);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_11, 0, x_12);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_mkFreshExprMVar(x_32, x_8, x_33, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_array_push(x_12, x_35);
x_38 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
lean_ctor_set(x_11, 1, x_38);
lean_ctor_set(x_11, 0, x_37);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_11);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_11);
lean_dec(x_12);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_41 = x_34;
} else {
 lean_dec_ref(x_34);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_11, 0, x_12);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_11);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_dec(x_11);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_47);
x_48 = l_Lean_Meta_matchNot_x3f(x_47, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_50);
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_mkFreshExprMVar(x_49, x_8, x_51, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_array_push(x_12, x_53);
x_56 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_47);
if (lean_is_scalar(x_50)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_50;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_48, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_65 = x_48;
} else {
 lean_dec_ref(x_48);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_67 = !lean_is_exclusive(x_9);
if (x_67 == 0)
{
return x_9;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_9, 0);
lean_inc(x_68);
lean_dec(x_9);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasMVar(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_instantiateMVarsCore(x_10, x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_st_ref_take(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_14);
x_18 = lean_st_ref_set(x_3, x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 2);
x_23 = lean_ctor_get(x_15, 3);
x_24 = lean_ctor_get(x_15, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_set(x_3, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_11);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_st_ref_take(x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 3);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_31, 4);
lean_inc_ref(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 lean_ctor_release(x_31, 4);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
x_38 = lean_st_ref_set(x_3, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_expr_eqv(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Expr_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_24; lean_object* x_28; lean_object* x_29; 
x_28 = lean_st_ref_get(x_3);
x_29 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(x_28, x_2);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_30 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_32, 0, x_29);
lean_inc_ref(x_32);
x_18 = x_30;
x_19 = x_32;
x_20 = x_29;
x_21 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_free_object(x_30);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
lean_dec_ref(x_34);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_47 = lean_box(0);
x_48 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
lean_ctor_set(x_32, 0, x_48);
x_10 = x_32;
x_11 = x_47;
x_12 = lean_box(0);
goto block_17;
}
else
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_49; lean_object* x_50; 
lean_free_object(x_32);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_50);
lean_inc_ref(x_49);
x_36 = x_49;
x_37 = x_50;
x_38 = x_3;
goto block_44;
}
case 6:
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_32);
x_51 = lean_ctor_get(x_2, 1);
x_52 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_52);
lean_inc_ref(x_51);
x_36 = x_51;
x_37 = x_52;
x_38 = x_3;
goto block_44;
}
case 8:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_32);
x_53 = lean_ctor_get(x_2, 1);
x_54 = lean_ctor_get(x_2, 2);
x_55 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_53);
lean_inc_ref(x_1);
x_56 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_53, x_3, x_35, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 0);
if (lean_obj_tag(x_58) == 0)
{
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_56;
goto block_27;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_54);
lean_inc_ref(x_1);
x_60 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_54, x_3, x_59, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_61);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_60;
goto block_27;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_60);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc_ref(x_55);
x_64 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_55, x_3, x_63, x_5, x_6, x_7, x_8);
x_24 = x_64;
goto block_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_60;
goto block_27;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_56;
goto block_27;
}
}
case 5:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_32);
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_65);
lean_inc_ref(x_1);
x_67 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_65, x_3, x_35, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
if (lean_obj_tag(x_69) == 0)
{
lean_dec(x_68);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_67;
goto block_27;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc_ref(x_66);
x_71 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_66, x_3, x_70, x_5, x_6, x_7, x_8);
x_24 = x_71;
goto block_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_67;
goto block_27;
}
}
case 10:
{
lean_object* x_72; lean_object* x_73; 
lean_free_object(x_32);
x_72 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_72);
x_73 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_72, x_3, x_35, x_5, x_6, x_7, x_8);
x_24 = x_73;
goto block_27;
}
case 11:
{
lean_object* x_74; lean_object* x_75; 
lean_free_object(x_32);
x_74 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_74);
x_75 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_74, x_3, x_35, x_5, x_6, x_7, x_8);
x_24 = x_75;
goto block_27;
}
default: 
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_76 = lean_box(0);
x_77 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
lean_ctor_set(x_32, 0, x_77);
x_10 = x_32;
x_11 = x_76;
x_12 = lean_box(0);
goto block_17;
}
}
}
}
block_44:
{
lean_object* x_39; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_39 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_36, x_38, x_35, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_40);
lean_dec_ref(x_37);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_39;
goto block_27;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_37, x_38, x_42, x_5, x_6, x_7, x_8);
x_24 = x_43;
goto block_27;
}
}
else
{
lean_dec_ref(x_37);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_39;
goto block_27;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_32, 0);
x_79 = lean_ctor_get(x_32, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_32);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_89; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_29);
lean_ctor_set(x_89, 1, x_79);
lean_inc_ref(x_89);
lean_ctor_set(x_30, 0, x_89);
x_18 = x_30;
x_19 = x_89;
x_20 = x_29;
x_21 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_90; uint8_t x_91; 
lean_free_object(x_30);
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
lean_dec_ref(x_78);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_92 = lean_box(0);
x_93 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_79);
x_10 = x_94;
x_11 = x_92;
x_12 = lean_box(0);
goto block_17;
}
else
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_2, 1);
x_96 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_96);
lean_inc_ref(x_95);
x_80 = x_95;
x_81 = x_96;
x_82 = x_3;
goto block_88;
}
case 6:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_2, 1);
x_98 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_98);
lean_inc_ref(x_97);
x_80 = x_97;
x_81 = x_98;
x_82 = x_3;
goto block_88;
}
case 8:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_2, 1);
x_100 = lean_ctor_get(x_2, 2);
x_101 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_99);
lean_inc_ref(x_1);
x_102 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_99, x_3, x_79, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 0);
if (lean_obj_tag(x_104) == 0)
{
lean_dec(x_103);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_102;
goto block_27;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_102);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_100);
lean_inc_ref(x_1);
x_106 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_100, x_3, x_105, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_107);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_106;
goto block_27;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_106);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc_ref(x_101);
x_110 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_101, x_3, x_109, x_5, x_6, x_7, x_8);
x_24 = x_110;
goto block_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_106;
goto block_27;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_102;
goto block_27;
}
}
case 5:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_2, 0);
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_111);
lean_inc_ref(x_1);
x_113 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_111, x_3, x_79, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 0);
if (lean_obj_tag(x_115) == 0)
{
lean_dec(x_114);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_113;
goto block_27;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_113);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc_ref(x_112);
x_117 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_112, x_3, x_116, x_5, x_6, x_7, x_8);
x_24 = x_117;
goto block_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_113;
goto block_27;
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_118);
x_119 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_118, x_3, x_79, x_5, x_6, x_7, x_8);
x_24 = x_119;
goto block_27;
}
case 11:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_120);
x_121 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_120, x_3, x_79, x_5, x_6, x_7, x_8);
x_24 = x_121;
goto block_27;
}
default: 
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_122 = lean_box(0);
x_123 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_79);
x_10 = x_124;
x_11 = x_122;
x_12 = lean_box(0);
goto block_17;
}
}
}
}
block_88:
{
lean_object* x_83; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_83 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_80, x_82, x_79, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_84);
lean_dec_ref(x_81);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_83;
goto block_27;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_81, x_82, x_86, x_5, x_6, x_7, x_8);
x_24 = x_87;
goto block_27;
}
}
else
{
lean_dec_ref(x_81);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_83;
goto block_27;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_30, 0);
lean_inc(x_125);
lean_dec(x_30);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
if (lean_is_scalar(x_128)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_128;
}
lean_ctor_set(x_138, 0, x_29);
lean_ctor_set(x_138, 1, x_127);
lean_inc_ref(x_138);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_18 = x_139;
x_19 = x_138;
x_20 = x_29;
x_21 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_126, 0);
lean_inc(x_140);
lean_dec_ref(x_126);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_142 = lean_box(0);
x_143 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
if (lean_is_scalar(x_128)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_128;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_127);
x_10 = x_144;
x_11 = x_142;
x_12 = lean_box(0);
goto block_17;
}
else
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_128);
x_145 = lean_ctor_get(x_2, 1);
x_146 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_146);
lean_inc_ref(x_145);
x_129 = x_145;
x_130 = x_146;
x_131 = x_3;
goto block_137;
}
case 6:
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_128);
x_147 = lean_ctor_get(x_2, 1);
x_148 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_148);
lean_inc_ref(x_147);
x_129 = x_147;
x_130 = x_148;
x_131 = x_3;
goto block_137;
}
case 8:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_128);
x_149 = lean_ctor_get(x_2, 1);
x_150 = lean_ctor_get(x_2, 2);
x_151 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_149);
lean_inc_ref(x_1);
x_152 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_149, x_3, x_127, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_153, 0);
if (lean_obj_tag(x_154) == 0)
{
lean_dec(x_153);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_152;
goto block_27;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_152);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_150);
lean_inc_ref(x_1);
x_156 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_150, x_3, x_155, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_157, 0);
if (lean_obj_tag(x_158) == 0)
{
lean_dec(x_157);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_156;
goto block_27;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_156);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc_ref(x_151);
x_160 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_151, x_3, x_159, x_5, x_6, x_7, x_8);
x_24 = x_160;
goto block_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_156;
goto block_27;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_152;
goto block_27;
}
}
case 5:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_128);
x_161 = lean_ctor_get(x_2, 0);
x_162 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_161);
lean_inc_ref(x_1);
x_163 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_161, x_3, x_127, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 0);
if (lean_obj_tag(x_165) == 0)
{
lean_dec(x_164);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_163;
goto block_27;
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_163);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc_ref(x_162);
x_167 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_162, x_3, x_166, x_5, x_6, x_7, x_8);
x_24 = x_167;
goto block_27;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_163;
goto block_27;
}
}
case 10:
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_128);
x_168 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_168);
x_169 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_168, x_3, x_127, x_5, x_6, x_7, x_8);
x_24 = x_169;
goto block_27;
}
case 11:
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_128);
x_170 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_170);
x_171 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_170, x_3, x_127, x_5, x_6, x_7, x_8);
x_24 = x_171;
goto block_27;
}
default: 
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_172 = lean_box(0);
x_173 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
if (lean_is_scalar(x_128)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_128;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_127);
x_10 = x_174;
x_11 = x_172;
x_12 = lean_box(0);
goto block_17;
}
}
}
}
block_137:
{
lean_object* x_132; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_132 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_129, x_131, x_127, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 0);
if (lean_obj_tag(x_134) == 0)
{
lean_dec(x_133);
lean_dec_ref(x_130);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_132;
goto block_27;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_132);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_130, x_131, x_135, x_5, x_6, x_7, x_8);
x_24 = x_136;
goto block_27;
}
}
else
{
lean_dec_ref(x_130);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = x_132;
goto block_27;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_175 = !lean_is_exclusive(x_30);
if (x_175 == 0)
{
return x_30;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_30, 0);
lean_inc(x_176);
lean_dec(x_30);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_29);
lean_ctor_set(x_178, 1, x_4);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_take(x_3);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(x_13, x_2, x_11);
x_15 = lean_st_ref_set(x_3, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_10);
return x_16;
}
block_23:
{
if (lean_obj_tag(x_20) == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_2);
return x_18;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_10 = x_19;
x_11 = x_22;
x_12 = lean_box(0);
goto block_17;
}
}
block_27:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_18 = x_24;
x_19 = x_25;
x_20 = x_26;
x_21 = lean_box(0);
goto block_23;
}
else
{
lean_dec_ref(x_2);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(x_10, x_3, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_14);
lean_free_object(x_11);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec_ref(x_14);
x_23 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1;
x_24 = lean_st_mk_ref(x_23);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0___boxed), 8, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_25, x_22, x_24, x_21, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_27);
lean_dec(x_24);
return x_26;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_st_ref_get(x_24);
lean_dec(x_24);
lean_dec(x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_32 = lean_st_ref_get(x_24);
lean_dec(x_24);
lean_dec(x_32);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_27);
return x_33;
}
}
}
else
{
lean_dec(x_24);
return x_26;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_35);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec_ref(x_35);
x_43 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1;
x_44 = lean_st_mk_ref(x_43);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0___boxed), 8, 1);
lean_closure_set(x_45, 0, x_1);
x_46 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(x_45, x_42, x_44, x_41, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_47);
lean_dec(x_44);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_st_ref_get(x_44);
lean_dec(x_44);
lean_dec(x_50);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
return x_51;
}
}
else
{
lean_dec(x_44);
return x_46;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(x_10, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(x_9, x_2);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc_ref(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_9);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_inc_ref(x_2);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_9, x_2, x_18);
lean_ctor_set(x_3, 0, x_19);
lean_inc_ref(x_2);
x_20 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_21);
lean_dec_ref(x_2);
return x_20;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_2);
x_31 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_29, x_2, x_18);
x_32 = lean_array_push(x_30, x_2);
lean_ctor_set(x_26, 2, x_32);
lean_ctor_set(x_26, 1, x_31);
x_33 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
lean_ctor_set(x_21, 0, x_33);
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
x_36 = lean_ctor_get(x_26, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
lean_inc_ref(x_2);
x_37 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_35, x_2, x_18);
x_38 = lean_array_push(x_36, x_2);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
lean_ctor_set(x_21, 1, x_39);
lean_ctor_set(x_21, 0, x_40);
return x_20;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
lean_inc_ref(x_2);
x_46 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_43, x_2, x_18);
x_47 = lean_array_push(x_44, x_2);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 3, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_20, 0, x_50);
return x_20;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_20);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_52 = x_21;
} else {
 lean_dec_ref(x_21);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
lean_inc_ref(x_2);
x_57 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_54, x_2, x_18);
x_58 = lean_array_push(x_55, x_2);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 3, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
x_63 = lean_box(0);
lean_inc_ref(x_2);
x_64 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_9, x_2, x_63);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_10);
lean_ctor_set(x_65, 2, x_11);
lean_inc_ref(x_2);
x_66 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(x_1, x_2, x_65, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_67);
lean_dec_ref(x_2);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_70, 2);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
lean_inc_ref(x_2);
x_76 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_73, x_2, x_63);
x_77 = lean_array_push(x_74, x_2);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 3, 0);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
if (lean_is_scalar(x_71)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_71;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
if (lean_is_scalar(x_69)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_69;
}
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
lean_dec_ref(x_2);
return x_66;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_85 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_9 = l_Lean_Expr_hasExprMVar(x_2);
if (x_9 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = lean_box(x_9);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isMVar(x_2);
if (x_45 == 0)
{
x_17 = x_45;
goto block_40;
}
else
{
uint8_t x_46; 
x_46 = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(x_1, x_2);
x_17 = x_46;
goto block_40;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_40:
{
if (x_17 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = x_3;
x_11 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
}
else
{
lean_object* x_28; 
lean_free_object(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_10 = x_28;
x_11 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_10 = x_36;
x_11 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(x_1, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_18;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_6 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_1);
x_10 = 0;
lean_inc_ref(x_1);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(x_1, x_8, x_1, x_9, x_10, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
lean_ctor_set(x_12, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_23 = x_12;
} else {
 lean_dec_ref(x_12);
 x_23 = lean_box(0);
}
x_24 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1;
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(x_1, x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_22 = x_21;
} else {
 lean_dec_ref(x_21);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_24);
lean_dec(x_23);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
lean_dec(x_8);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 8);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_2);
x_11 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_12 = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(x_11, x_5);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
size_t x_16; size_t x_17; 
lean_free_object(x_12);
lean_dec(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
goto _start;
}
else
{
return x_12;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
size_t x_21; size_t x_22; 
lean_dec(x_19);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
return x_24;
}
}
}
else
{
return x_12;
}
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_21; lean_object* x_22; 
x_17 = lean_array_uget(x_1, x_2);
x_21 = l_Lean_Expr_mvarId_x21(x_17);
x_22 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_21, x_6);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
x_18 = lean_box(0);
goto block_20;
}
else
{
lean_dec(x_17);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_17);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
else
{
x_18 = lean_box(0);
goto block_20;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec_ref(x_4);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
block_20:
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_17);
x_10 = x_19;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_4);
return x_30;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_19);
x_20 = lean_infer_type(x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_21, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_25 = x_5;
} else {
 lean_dec_ref(x_5);
 x_25 = lean_box(0);
}
x_29 = l_Lean_Expr_cleanupAnnotations(x_23);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec(x_19);
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec(x_19);
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_34);
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec(x_19);
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_38 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__1;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec_ref(x_37);
if (x_39 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_31);
lean_dec(x_19);
x_26 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_40; 
lean_dec(x_25);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_34);
x_40 = l_Lean_Meta_isExprDefEq(x_34, x_31, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_34);
lean_dec(x_19);
lean_inc(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_24);
x_11 = x_43;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_44; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_44 = l_Lean_Meta_mkEqRefl(x_34, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_47 = lean_checked_assign(x_46, x_45, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_51 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_24);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_free_object(x_47);
lean_dec(x_24);
x_53 = lean_box(x_39);
lean_inc(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
x_11 = x_54;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_57 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_24);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_24);
x_60 = lean_box(x_39);
lean_inc(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
x_11 = x_61;
x_12 = lean_box(0);
goto block_16;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
return x_47;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_44);
if (x_65 == 0)
{
return x_44;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_44, 0);
lean_inc(x_66);
lean_dec(x_44);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec_ref(x_34);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_40, 0);
lean_inc(x_69);
lean_dec(x_40);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
}
}
block_28:
{
lean_object* x_27; 
lean_inc(x_1);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_24);
x_11 = x_27;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
uint8_t x_71; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_22);
if (x_71 == 0)
{
return x_22;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_22, 0);
lean_inc(x_72);
lean_dec(x_22);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_20);
if (x_74 == 0)
{
return x_20;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_20, 0);
lean_inc(x_75);
lean_dec(x_20);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
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
x_14 = l_Array_isEmpty___redArg(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_free_object(x_8);
x_15 = lean_box(0);
x_16 = lean_box(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_size(x_11);
x_19 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(x_15, x_11, x_18, x_19, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_112; 
x_112 = lean_unbox(x_24);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_22)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_22;
}
lean_ctor_set(x_113, 0, x_15);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; uint8_t x_132; 
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_array_get_size(x_11);
x_132 = lean_nat_dec_lt(x_114, x_115);
if (x_132 == 0)
{
x_116 = x_14;
x_117 = lean_box(0);
goto block_131;
}
else
{
if (x_132 == 0)
{
x_116 = x_14;
x_117 = lean_box(0);
goto block_131;
}
else
{
size_t x_133; lean_object* x_134; 
x_133 = lean_usize_of_nat(x_115);
x_134 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(x_11, x_19, x_133, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
x_116 = x_136;
x_117 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_137; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_137 = !lean_is_exclusive(x_134);
if (x_137 == 0)
{
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_134, 0);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
}
block_131:
{
if (x_116 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_22);
x_118 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(x_12, x_4);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = l_Lean_mkAppN(x_2, x_11);
x_121 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(x_120, x_4);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
x_124 = lean_nat_dec_lt(x_114, x_115);
if (x_124 == 0)
{
lean_dec(x_11);
x_25 = x_122;
x_26 = x_119;
x_27 = x_123;
x_28 = lean_box(0);
goto block_103;
}
else
{
uint8_t x_125; 
x_125 = lean_nat_dec_le(x_115, x_115);
if (x_125 == 0)
{
if (x_124 == 0)
{
lean_dec(x_11);
x_25 = x_122;
x_26 = x_119;
x_27 = x_123;
x_28 = lean_box(0);
goto block_103;
}
else
{
size_t x_126; lean_object* x_127; 
x_126 = lean_usize_of_nat(x_115);
x_127 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(x_11, x_19, x_126, x_123, x_3, x_4, x_5, x_6);
lean_dec(x_11);
x_104 = x_122;
x_105 = x_119;
x_106 = x_127;
goto block_111;
}
}
else
{
size_t x_128; lean_object* x_129; 
x_128 = lean_usize_of_nat(x_115);
x_129 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(x_11, x_19, x_128, x_123, x_3, x_4, x_5, x_6);
lean_dec(x_11);
x_104 = x_122;
x_105 = x_119;
x_106 = x_129;
goto block_111;
}
}
}
else
{
lean_object* x_130; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_22)) {
 x_130 = lean_alloc_ctor(0, 1, 0);
} else {
 x_130 = x_22;
}
lean_ctor_set(x_130, 0, x_15);
return x_130;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_140 = lean_ctor_get(x_23, 0);
lean_inc(x_140);
lean_dec_ref(x_23);
if (lean_is_scalar(x_22)) {
 x_141 = lean_alloc_ctor(0, 1, 0);
} else {
 x_141 = x_22;
}
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
block_103:
{
lean_object* x_29; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_29 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(x_27, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_31) == 1)
{
uint8_t x_32; 
lean_free_object(x_29);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = 0;
x_35 = lean_unbox(x_24);
x_36 = lean_unbox(x_24);
x_37 = l_Lean_Meta_mkForallFVars(x_33, x_26, x_14, x_35, x_36, x_34, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = 1;
x_40 = lean_unbox(x_24);
x_41 = lean_unbox(x_24);
lean_dec(x_24);
x_42 = l_Lean_Meta_mkLambdaFVars(x_33, x_25, x_14, x_40, x_14, x_41, x_39, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_33);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
if (lean_is_scalar(x_13)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_13;
}
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_31, 0, x_45);
lean_ctor_set(x_42, 0, x_31);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
if (lean_is_scalar(x_13)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_13;
}
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_31, 0, x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_31);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_38);
lean_free_object(x_31);
lean_dec(x_13);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_31, 0);
lean_inc(x_55);
lean_dec(x_31);
x_56 = 0;
x_57 = lean_unbox(x_24);
x_58 = lean_unbox(x_24);
x_59 = l_Lean_Meta_mkForallFVars(x_55, x_26, x_14, x_57, x_58, x_56, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = 1;
x_62 = lean_unbox(x_24);
x_63 = lean_unbox(x_24);
lean_dec(x_24);
x_64 = l_Lean_Meta_mkLambdaFVars(x_55, x_25, x_14, x_62, x_14, x_63, x_61, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_55);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_13;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
lean_dec(x_13);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_55);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_73 = lean_ctor_get(x_59, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_74 = x_59;
} else {
 lean_dec_ref(x_59);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_ctor_set(x_29, 0, x_15);
return x_29;
}
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
lean_dec(x_29);
if (lean_obj_tag(x_76) == 1)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = 0;
x_80 = lean_unbox(x_24);
x_81 = lean_unbox(x_24);
x_82 = l_Lean_Meta_mkForallFVars(x_77, x_26, x_14, x_80, x_81, x_79, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = 1;
x_85 = lean_unbox(x_24);
x_86 = lean_unbox(x_24);
lean_dec(x_24);
x_87 = l_Lean_Meta_mkLambdaFVars(x_77, x_25, x_14, x_85, x_14, x_86, x_84, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_13;
}
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_88);
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_83);
lean_dec(x_78);
lean_dec(x_13);
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_97 = x_82;
} else {
 lean_dec_ref(x_82);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_76);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_15);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_100 = !lean_is_exclusive(x_29);
if (x_100 == 0)
{
return x_29;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_29, 0);
lean_inc(x_101);
lean_dec(x_29);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
block_111:
{
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_25 = x_104;
x_26 = x_105;
x_27 = x_107;
x_28 = lean_box(0);
goto block_103;
}
else
{
uint8_t x_108; 
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
return x_106;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_142 = !lean_is_exclusive(x_20);
if (x_142 == 0)
{
return x_20;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_20, 0);
lean_inc(x_143);
lean_dec(x_20);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_145 = lean_box(0);
lean_ctor_set(x_8, 0, x_145);
return x_8;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_146 = lean_ctor_get(x_8, 0);
lean_inc(x_146);
lean_dec(x_8);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = l_Array_isEmpty___redArg(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; size_t x_154; size_t x_155; lean_object* x_156; 
x_151 = lean_box(0);
x_152 = lean_box(x_150);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_size(x_147);
x_155 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_156 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(x_151, x_147, x_154, x_155, x_153, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_203; 
x_203 = lean_unbox(x_160);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_158)) {
 x_204 = lean_alloc_ctor(0, 1, 0);
} else {
 x_204 = x_158;
}
lean_ctor_set(x_204, 0, x_151);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; uint8_t x_223; 
x_205 = lean_unsigned_to_nat(0u);
x_206 = lean_array_get_size(x_147);
x_223 = lean_nat_dec_lt(x_205, x_206);
if (x_223 == 0)
{
x_207 = x_150;
x_208 = lean_box(0);
goto block_222;
}
else
{
if (x_223 == 0)
{
x_207 = x_150;
x_208 = lean_box(0);
goto block_222;
}
else
{
size_t x_224; lean_object* x_225; 
x_224 = lean_usize_of_nat(x_206);
x_225 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(x_147, x_155, x_224, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
x_207 = x_227;
x_208 = lean_box(0);
goto block_222;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_228 = lean_ctor_get(x_225, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_229 = x_225;
} else {
 lean_dec_ref(x_225);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
}
block_222:
{
if (x_207 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_dec(x_158);
x_209 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(x_148, x_4);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = l_Lean_mkAppN(x_2, x_147);
x_212 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(x_211, x_4);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
x_215 = lean_nat_dec_lt(x_205, x_206);
if (x_215 == 0)
{
lean_dec(x_147);
x_161 = x_213;
x_162 = x_210;
x_163 = x_214;
x_164 = lean_box(0);
goto block_194;
}
else
{
uint8_t x_216; 
x_216 = lean_nat_dec_le(x_206, x_206);
if (x_216 == 0)
{
if (x_215 == 0)
{
lean_dec(x_147);
x_161 = x_213;
x_162 = x_210;
x_163 = x_214;
x_164 = lean_box(0);
goto block_194;
}
else
{
size_t x_217; lean_object* x_218; 
x_217 = lean_usize_of_nat(x_206);
x_218 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(x_147, x_155, x_217, x_214, x_3, x_4, x_5, x_6);
lean_dec(x_147);
x_195 = x_213;
x_196 = x_210;
x_197 = x_218;
goto block_202;
}
}
else
{
size_t x_219; lean_object* x_220; 
x_219 = lean_usize_of_nat(x_206);
x_220 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(x_147, x_155, x_219, x_214, x_3, x_4, x_5, x_6);
lean_dec(x_147);
x_195 = x_213;
x_196 = x_210;
x_197 = x_220;
goto block_202;
}
}
}
else
{
lean_object* x_221; 
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_158)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_158;
}
lean_ctor_set(x_221, 0, x_151);
return x_221;
}
}
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_231 = lean_ctor_get(x_159, 0);
lean_inc(x_231);
lean_dec_ref(x_159);
if (lean_is_scalar(x_158)) {
 x_232 = lean_alloc_ctor(0, 1, 0);
} else {
 x_232 = x_158;
}
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
block_194:
{
lean_object* x_165; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_165 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(x_163, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
if (lean_obj_tag(x_166) == 1)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; 
lean_dec(x_167);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = 0;
x_171 = lean_unbox(x_160);
x_172 = lean_unbox(x_160);
x_173 = l_Lean_Meta_mkForallFVars(x_168, x_162, x_150, x_171, x_172, x_170, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = 1;
x_176 = lean_unbox(x_160);
x_177 = lean_unbox(x_160);
lean_dec(x_160);
x_178 = l_Lean_Meta_mkLambdaFVars(x_168, x_161, x_150, x_176, x_150, x_177, x_175, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_168);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_149;
}
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_179);
if (lean_is_scalar(x_169)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_169;
}
lean_ctor_set(x_182, 0, x_181);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_174);
lean_dec(x_169);
lean_dec(x_149);
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_187 = lean_ctor_get(x_173, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_188 = x_173;
} else {
 lean_dec_ref(x_173);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; 
lean_dec(x_166);
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_is_scalar(x_167)) {
 x_190 = lean_alloc_ctor(0, 1, 0);
} else {
 x_190 = x_167;
}
lean_ctor_set(x_190, 0, x_151);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec_ref(x_162);
lean_dec_ref(x_161);
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_191 = lean_ctor_get(x_165, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_192 = x_165;
} else {
 lean_dec_ref(x_165);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
}
block_202:
{
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_161 = x_195;
x_162 = x_196;
x_163 = x_198;
x_164 = lean_box(0);
goto block_194;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_196);
lean_dec_ref(x_195);
lean_dec(x_160);
lean_dec(x_149);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_233 = lean_ctor_get(x_156, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_234 = x_156;
} else {
 lean_dec_ref(x_156);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_238 = !lean_is_exclusive(x_8);
if (x_238 == 0)
{
return x_8;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_8, 0);
lean_inc(x_239);
lean_dec(x_8);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = 0;
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(x_8, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_eqResolution___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_8 = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
lean_free_object(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_17 = lean_array_push(x_16, x_2);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_17, x_15, x_18, x_19, x_18, x_19, x_20, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_21, 0, x_10);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_12, 1, x_24);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_12);
lean_dec(x_14);
lean_free_object(x_10);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_32 = lean_array_push(x_31, x_2);
x_33 = 0;
x_34 = 1;
x_35 = 1;
x_36 = l_Lean_Meta_mkLambdaFVars(x_32, x_30, x_33, x_34, x_33, x_34, x_35, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_10, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
lean_free_object(x_10);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
lean_dec(x_10);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_49 = lean_array_push(x_48, x_2);
x_50 = 0;
x_51 = 1;
x_52 = 1;
x_53 = l_Lean_Meta_mkLambdaFVars(x_49, x_46, x_50, x_51, x_50, x_51, x_52, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_47;
}
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_47);
lean_dec(x_45);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_62 = lean_box(0);
lean_ctor_set(x_8, 0, x_62);
return x_8;
}
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_8, 0);
lean_inc(x_63);
lean_dec(x_8);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = l_Lean_Meta_Grind_eqResolution___lam__0___closed__0;
x_70 = lean_array_push(x_69, x_2);
x_71 = 0;
x_72 = 1;
x_73 = 1;
x_74 = l_Lean_Meta_mkLambdaFVars(x_70, x_67, x_71, x_72, x_71, x_72, x_73, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_75);
if (lean_is_scalar(x_65)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_65;
}
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_eqResolution___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_eqResolution___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_eqResolution___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_eqResolution___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eqResolution___lam__0___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Grind_eqResolution___closed__1;
x_9 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(x_8, x_1, x_7, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eqResolution___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_eqResolution(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2);
l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0 = _init_l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0();
lean_mark_persistent(l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1);
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1();
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__0);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___closed__2);
l_Lean_Meta_Grind_eqResolution___lam__0___closed__0 = _init_l_Lean_Meta_Grind_eqResolution___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_eqResolution___lam__0___closed__0);
l_Lean_Meta_Grind_eqResolution___closed__0 = _init_l_Lean_Meta_Grind_eqResolution___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_eqResolution___closed__0);
l_Lean_Meta_Grind_eqResolution___closed__1 = _init_l_Lean_Meta_Grind_eqResolution___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_eqResolution___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
